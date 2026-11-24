// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAEvidenceRegistry} from "@ava-protocol/contracts/src/core/AVAEvidenceRegistry.sol";
import {SparkV15} from "./SparkV15ApplicationModule.sol";
import {SparkV15Booking} from "./SparkV15Booking.sol";
import {SparkV15Payments} from "./SparkV15Payments.sol";
import {ISparkV15SettlementRemedies, SparkV15Settlement} from "./SparkV15Settlement.sol";
import {SparkV15SettlementAlternatives} from "./SparkV15SettlementAlternatives.sol";
import {SparkV15SettlementOccurrences} from "./SparkV15SettlementOccurrences.sol";

/// @notice Compile a settlement from the same records and policies used by its authoritative writer.
contract SparkV15SettlementCompilation {
    function requireNoExistingRedress(bytes32 formId) external view {
        address remedies = address(SETTLEMENT.remedyPolicy());
        if (remedies != address(0)) {
            SETTLEMENT.ALTERNATIVES().OCCURRENCES().requireNoExistingRedress(remedies, formId, false);
        }
    }

    struct Policies {
        SparkV15SettlementAlternatives alternatives;
        ISparkV15SettlementRemedies remedies;
    }

    struct SeatCompilation {
        SparkV15Booking.Lesson lesson;
        uint64 startedAt;
        SparkV15Settlement.Route route;
        address tutorRecipient;
        address proposer;
        address approver;
        bytes32 serviceDocumentRef;
        bytes32 changeId;
        bool adoptAttendance;
        bytes32 verifiedProviderAmounts;
    }

    struct SeatTotals {
        uint256 normalTutorPay;
        uint256 tutorPay;
        uint256 newRows;
    }

    struct PaymentCompilation {
        bytes32 lessonId;
        uint256 packageId;
        address tutor;
        address proposer;
        address approver;
        uint64 deadlineAnchor;
        uint64 legalDeadline;
        bool legalDeadlineExact;
    }

    SparkV15Settlement private immutable SETTLEMENT;
    SparkV15Booking private immutable BOOKING;
    SparkV15Payments private immutable PAYMENTS;
    AVAEvidenceRegistry private immutable EVIDENCE_REGISTRY;

    constructor(SparkV15Booking booking, SparkV15Payments payments) {
        SETTLEMENT = SparkV15Settlement(msg.sender);
        BOOKING = booking;
        PAYMENTS = payments;
        EVIDENCE_REGISTRY = payments.REQUEST_ALLOCATION().EVIDENCE_REGISTRY();
    }

    function requireDisinterestedWageSource(bytes32 lessonId, bytes32 formId, address paidTo, address source)
        public
        view
    {
        _requireDisinterestedInLesson(BOOKING.getLesson(lessonId).terms, paidTo, source);
        _requireDisinterestedInSeat(BOOKING.getForm(formId).terms, source);
    }

    function confirmedSeatTerms(bytes32 formId)
        external
        view
        returns (bytes32 placeId, bytes32 debitAccount, uint128 normalFee, uint128 debited)
    {
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        return (form.terms.placeId, form.terms.creditAccount, form.terms.normalFee, form.confirmation.debitedUnits);
    }

    function compileGroup(
        bytes32 lessonId,
        SparkV15Settlement.GroupAssessment calldata assessment,
        address approver,
        SparkV15Settlement.LocalApproval calldata local
    ) external view returns (SparkV15Settlement.CompiledGroup memory compiled) {
        if (msg.sender != address(SETTLEMENT)) {
            revert SparkV15Settlement.InvalidApprovalCaller();
        }
        SparkV15Settlement.Proposal calldata proposal = local.proposal;
        if (
            proposal.proposer == address(0)
                || proposal.commitment != SETTLEMENT.proposalCommitment(lessonId, assessment)
        ) {
            revert SparkV15Settlement.InvalidGroupProposal();
        }
        Policies memory policies = Policies(SETTLEMENT.ALTERNATIVES(), SETTLEMENT.remedyPolicy());
        compiled.absence = _absenceReason(assessment.route);
        compiled.approvalAuthorityId = EVIDENCE_REGISTRY.AUTHORITY_MATRIX()
            .requireAuthorisedCanonicalSubject(
                approver, SparkV15.APP_ID, PAYMENTS.VERIFIER_ROLE(), SETTLEMENT.ACTION_APPROVE_GROUP_SETTLEMENT()
            );
        SparkV15Booking.Lesson memory lesson = BOOKING.getLesson(lessonId);
        compiled.packageId = lesson.packageId;
        bool group = lesson.terms.rosterRef != bytes32(0);
        bool providerStartedEarly = assessment.route == SparkV15Settlement.Route.ProviderStartedEarly;
        if (!providerStartedEarly && group != (assessment.route <= SparkV15Settlement.Route.VerifiedGroup)) {
            revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        }
        bytes32[] memory formIds = group ? BOOKING.getLockedForms(lessonId) : BOOKING.getPlannedForms(lessonId);
        if (
            formIds.length == 0 || (!group && formIds.length != 1) || formIds.length != assessment.seats.length
                || formIds.length != assessment.tutor.seats.length || assessment.clearanceRef == bytes32(0)
        ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        SparkV15SettlementOccurrences occurrences = policies.alternatives.OCCURRENCES();
        SparkV15SettlementOccurrences.Basis memory occurrence;
        if (providerStartedEarly) {
            if (
                lesson.terms.materialsTermsRef != bytes32(0) || assessment.effectiveChangeId != bytes32(0)
                    || assessment.clockBoundaryRef != bytes32(0) || assessment.clockEvidenceId != 0
            ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            occurrence = occurrences.readProviderStartBasis(lessonId);
            if (group) {
                SparkV15Booking.RosterLock memory roster = BOOKING.getRosterLock(lessonId);
                // An unauthorised start may precede the roster cutoff agreed by the parties.
                if (roster.lockedAt > occurrence.arrangement.startsAt) {
                    revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
                }
                _requireAvailable(roster.evidenceId, lesson.packageId);
                occurrence.evidenceRoot = keccak256(abi.encode(occurrence.evidenceRoot, roster.evidenceId));
            }
        } else {
            occurrence =
                occurrences.readBasis(lessonId, formIds[0], assessment.effectiveChangeId, group, uint8(compiled.absence));
        }
        if (local.completionRoot != bytes32(0)) {
            occurrence.evidenceRoot = keccak256(abi.encode(occurrence.evidenceRoot, local.completionRoot));
            occurrence.allOneToOneConfirmed = occurrence.tutorCompleted;
        }
        compiled.tutor = occurrence.arrangement.tutor;
        compiled.legalDeadlineEvidenceId = occurrence.legalDeadlineEvidenceId;
        lesson.terms.tutor = compiled.tutor;
        lesson.terms.tutorFee = occurrence.arrangement.tutorFee;
        lesson.terms.tutorAgreementRef = occurrence.arrangement.tutorAgreementRef;
        lesson.terms.tutorPayTermsRef = occurrence.arrangement.tutorPayTermsRef;
        _requireAgreedTerms(lesson, occurrence, assessment);
        if (approver == proposal.proposer) revert SparkV15Settlement.InterestedSettlementActor();
        _requireDisinterestedInLesson(lesson.terms, assessment.tutor.recipient, approver);
        _requireDisinterestedInLesson(lesson.terms, assessment.tutor.recipient, proposal.proposer);

        bytes32 redressRoot = _compileSeats(
            SeatCompilation(
                lesson,
                occurrence.startedAt,
                assessment.route,
                assessment.tutor.recipient,
                proposal.proposer,
                approver,
                assessment.refund.serviceDocumentRef,
                assessment.effectiveChangeId,
                local.adoptAttendance,
                assessment.verificationRef
            ),
            formIds,
            assessment,
            compiled,
            policies
        );
        if (redressRoot != bytes32(0)) {
            occurrence.evidenceRoot = keccak256(abi.encode(occurrence.evidenceRoot, redressRoot));
        }
        _requireRoute(
            lessonId,
            assessment,
            occurrence,
            compiled.preview.attendanceConfirmations,
            formIds.length,
            policies.alternatives
        );
        compiled.originalTutorFault = address(policies.remedies) != address(0)
            && !policies.remedies.allowsTutorWage(lessonId, lesson.terms.tutor);
        _compileNetWages(lesson, assessment, compiled, policies);
        _compilePayments(
            PaymentCompilation(
                lessonId,
                lesson.packageId,
                lesson.terms.tutor,
                proposal.proposer,
                approver,
                occurrence.deadlineAnchor,
                occurrence.legalDeadline,
                occurrence.legalDeadlineExact
            ),
            assessment,
            compiled
        );
        compiled.preview.basis = keccak256(
            abi.encode(
                SETTLEMENT.ACTION_APPROVE_GROUP_SETTLEMENT(),
                block.chainid,
                address(SETTLEMENT),
                lesson.commitment,
                proposal,
                approver,
                compiled.approvalAuthorityId,
                occurrence.evidenceRoot,
                compiled.seats,
                compiled.preview.totalTutorPay
            )
        );
    }

    function _compileNetWages(
        SparkV15Booking.Lesson memory lesson,
        SparkV15Settlement.GroupAssessment calldata assessment,
        SparkV15Settlement.CompiledGroup memory compiled,
        Policies memory policies
    ) private view {
        uint128 gross = compiled.preview.totalTutorPay;
        if (compiled.originalTutorFault) {
            if (assessment.agreedNetWages.length != 0) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
            return;
        }
        uint128 net = gross;
        if (
            gross != 0 && address(policies.remedies) != address(0)
                && compiled.absence == SparkV15SettlementAlternatives.AbsenceReason.Unverified
        ) {
            net = policies.remedies.previewTutorDeductions(lesson.terms.lessonId, lesson.terms.tutor, gross);
        }
        if (net > gross || (compiled.partialSettlement && net != gross)) {
            revert SparkV15Settlement.InvalidAgreedPaymentTerms();
        }
        compiled.preview.netTutorPay = net;
        bool allocate = net != gross && compiled.seats.length != 1;
        if (allocate) {
            if (
                assessment.agreedNetWages.length != compiled.seats.length
                    || !policies.alternatives
                    .wageAllocationAgreed(lesson.terms.lessonId, gross, net, assessment.agreedNetWages)
            ) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
        } else if (assessment.agreedNetWages.length != 0) {
            revert SparkV15Settlement.InvalidAgreedPaymentTerms();
        }
        uint256 total;
        for (uint256 i; i < compiled.seats.length; ++i) {
            SparkV15Settlement.SeatSettlement memory seat = compiled.seats[i];
            if (allocate && assessment.seats[i].disposition == SparkV15Settlement.SeatDisposition.PreviouslySettled) {
                revert SparkV15Settlement.InvalidAgreedPaymentTerms();
            }
            seat.tutorNetPay = allocate ? assessment.agreedNetWages[i] : (net == gross ? seat.tutorPay : net);
            if (seat.tutorNetPay > seat.tutorPay) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
            total += seat.tutorNetPay;
            compiled.seats[i] = seat;
        }
        if (total != net) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
    }

    function _compileSeats(
        SeatCompilation memory context,
        bytes32[] memory formIds,
        SparkV15Settlement.GroupAssessment calldata assessment,
        SparkV15Settlement.CompiledGroup memory compiled,
        Policies memory policies
    ) private view returns (bytes32 redressRoot) {
        compiled.seats = new SparkV15Settlement.SeatSettlement[](formIds.length);
        SeatTotals memory totals;
        for (uint256 i; i < formIds.length; ++i) {
            SparkV15Settlement.TutorSeatTerms calldata tutor = assessment.tutor.seats[i];
            SparkV15Settlement.SeatFinding calldata finding = assessment.seats[i];
            (SparkV15Settlement.SeatSettlement memory seat, bool counts, bytes32 redressBasis) =
                _compileSeat(context, formIds[i], finding, tutor, policies);
            if (redressBasis != bytes32(0)) redressRoot = keccak256(abi.encode(redressRoot, redressBasis));
            compiled.seats[i] = seat;
            if (counts) ++compiled.preview.attendanceConfirmations;
            if (seat.disposition == SparkV15Settlement.SeatDisposition.DeferredByHold) {
                compiled.partialSettlement = true;
            } else if (finding.disposition != SparkV15Settlement.SeatDisposition.PreviouslySettled) {
                ++totals.newRows;
            }
            totals.normalTutorPay += tutor.ordinaryPay;
            totals.tutorPay += seat.tutorPay;
        }
        if (totals.newRows == 0) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        if (totals.normalTutorPay != context.lesson.terms.tutorFee || totals.tutorPay > type(uint128).max) {
            revert SparkV15Settlement.InvalidAgreedPaymentTerms();
        }
        compiled.preview.totalTutorPay = uint128(totals.tutorPay);
    }

    function _requireRoute(
        bytes32 lessonId,
        SparkV15Settlement.GroupAssessment calldata assessment,
        SparkV15SettlementOccurrences.Basis memory occurrence,
        uint256 confirmations,
        uint256 rosterSize,
        SparkV15SettlementAlternatives alternatives
    ) private view {
        SparkV15Settlement.Route route = assessment.route;
        if (route >= SparkV15Settlement.Route.OneToOneAbsence) return;
        bool usual = route <= SparkV15Settlement.Route.VerifiedGroup
            ? occurrence.tutorCompleted && confirmations > rosterSize / 2
            : occurrence.allOneToOneConfirmed;
        if (route == SparkV15Settlement.Route.OrdinaryGroup || route == SparkV15Settlement.Route.OrdinaryOneToOne) {
            if (!usual) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            return;
        }
        if (
            usual || assessment.verificationRef == bytes32(0)
                || !alternatives.fallbackMature(
                    lessonId, occurrence.deadlineAnchor, assessment.clockBoundaryRef, assessment.clockEvidenceId
                )
        ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
    }

    function _absenceReason(SparkV15Settlement.Route route)
        private
        pure
        returns (SparkV15SettlementAlternatives.AbsenceReason)
    {
        if (route == SparkV15Settlement.Route.OneToOneAbsence) {
            return SparkV15SettlementAlternatives.AbsenceReason.NoGoodReason;
        }
        if (route == SparkV15Settlement.Route.OneToOneAgreedAbsence) {
            return SparkV15SettlementAlternatives.AbsenceReason.GoodReason;
        }
        return SparkV15SettlementAlternatives.AbsenceReason.Unverified;
    }

    function _compileSeat(
        SeatCompilation memory context,
        bytes32 formId,
        SparkV15Settlement.SeatFinding calldata finding,
        SparkV15Settlement.TutorSeatTerms calldata tutorTerms,
        Policies memory policies
    ) private view returns (SparkV15Settlement.SeatSettlement memory seat, bool counts, bytes32 redressBasis) {
        SparkV15Booking.Lesson memory lesson = context.lesson;
        SparkV15Settlement.Route route = context.route;
        bool providerStartedEarly = route == SparkV15Settlement.Route.ProviderStartedEarly;
        bytes32 lessonId = lesson.terms.lessonId;
        SparkV15Booking.Form memory form = BOOKING.getForm(formId);
        SparkV15Booking.PlaceTerms memory terms = form.terms;
        bool unconfirmed = form.confirmation.confirmedAt == 0;
        if (BOOKING.isCancelledAt(formId, uint64(block.timestamp))) {
            revert SparkV15Settlement.ApplicableArrangementChanged();
        }
        if (
            finding.formId != formId || tutorTerms.placeId != terms.placeId
                || (unconfirmed
                    ? !providerStartedEarly
                    : form.confirmation.confirmedAt >= context.startedAt || form.confirmation.debitedUnits != terms.payableFee)
        ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        _requireDisinterestedInSeat(terms, context.proposer);
        _requireDisinterestedInSeat(terms, context.approver);
        if (terms.payableFee == 0) _requireAvailable(form.confirmation.discountEvidenceId, lesson.packageId);

        SparkV15Booking.AttendanceReport memory attendance = BOOKING.getAttendance(formId);
        if (attendance.evidenceId != 0) _requireAvailable(attendance.evidenceId, lesson.packageId);
        counts = (context.adoptAttendance || (attendance.reportedAt != 0 && attendance.attended))
            && !finding.studentFaultFound;
        if (finding.disposition == SparkV15Settlement.SeatDisposition.DeferredByHold) {
            if (route > SparkV15Settlement.Route.VerifiedGroup && !providerStartedEarly) {
                revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            }
            seat.formId = formId;
            seat.disposition = SparkV15Settlement.SeatDisposition.DeferredByHold;
            seat.holdWitness = policies.alternatives
                .heldSeatWitness(
                    lessonId,
                    formId,
                    finding.feeHoldCaseId,
                    SETTLEMENT.tutorPaymentPart(lesson.terms.tutor, terms.placeId),
                    context.tutorRecipient,
                    lesson.packageId
                );
            if (seat.holdWitness == bytes32(0)) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            return (seat, counts, bytes32(0));
        }
        if (policies.alternatives.activeFeeHolds(formId) != 0) {
            revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        }
        bool faultTreatment = finding.disposition == SparkV15Settlement.SeatDisposition.TutorFaultFee;
        uint128 faultFee;
        bool applicable;
        if (address(policies.remedies) != address(0)) (applicable, faultFee) = policies.remedies.faultFee(formId);
        if (applicable != faultTreatment) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        if (finding.disposition == SparkV15Settlement.SeatDisposition.PreviouslySettled) {
            SparkV15Settlement.SeatSettlement memory prior = SETTLEMENT.getSeatSettlement(lessonId, formId);
            if (
                prior.formId == bytes32(0)
                    || providerStartedEarly != (prior.disposition == SparkV15Settlement.SeatDisposition.ProviderStartedEarly)
            ) revert SparkV15Settlement.InvalidGroupProposal();
            return (prior, counts, bytes32(0));
        }
        if (
            SETTLEMENT.hasSeatSettlement(lessonId, formId) || finding.serviceAvailabilityRef == bytes32(0)
                || finding.disposition == SparkV15Settlement.SeatDisposition.Unverified
                || finding.disposition == SparkV15Settlement.SeatDisposition.ProviderRedressFee
                || providerStartedEarly != (finding.disposition == SparkV15Settlement.SeatDisposition.ProviderStartedEarly)
                || finding.studentFaultFound
        ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();

        SparkV15Booking.ServiceFeedback memory feedback = BOOKING.getServiceFeedback(formId);
        if (feedback.evidenceId != 0) {
            BOOKING.OPENING().SERVICE_REPORTS().requireUsableFeedbackEvidence(formId, feedback.evidenceId, lesson.packageId);
        }
        bool absent = finding.disposition == SparkV15Settlement.SeatDisposition.VerifiedAbsence;
        seat.feeDue = absent ? terms.payableFee / 2 : terms.payableFee;
        SparkV15SettlementOccurrences occurrences = policies.alternatives.OCCURRENCES();
        bool absentAfterNoticeError;
        if (route <= SparkV15Settlement.Route.VerifiedOneToOne && !faultTreatment) {
            uint128 assessedFee;
            (redressBasis, assessedFee, seat.refundObligationId, seat.refundAlreadyReceived, absentAfterNoticeError) =
                occurrences.readProviderRedress(address(policies.remedies), formId, lesson.packageId);
            if (redressBasis != bytes32(0)) {
                if (finding.disposition != SparkV15Settlement.SeatDisposition.OrdinaryFee) {
                    revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
                }
                seat.feeDue = seat.refundObligationId == bytes32(0)
                    ? assessedFee
                    : form.confirmation.debitedUnits - PAYMENTS.getObligation(seat.refundObligationId).correctAmount;
            }
            absentAfterNoticeError = absentAfterNoticeError && route <= SparkV15Settlement.Route.VerifiedGroup
                && attendance.reportedAt != 0 && !attendance.attended;
        }
        if (providerStartedEarly) {
            occurrences.requireNoExistingRedress(address(policies.remedies), formId, true);
            if (lesson.terms.rosterRef == bytes32(0)) {
                uint256 verified = uint256(context.verifiedProviderAmounts);
                seat.feeDue = uint128(verified >> 128);
                seat.tutorPay = uint128(verified);
            } else {
                seat.feeDue = finding.agreedAbsenceFee;
                seat.tutorPay = finding.agreedAbsenceTutorPay;
            }
            if (
                (!unconfirmed && (form.confirmation.debitedUnits == 0 || seat.feeDue > form.confirmation.debitedUnits))
                    || finding.feeHoldCaseId != bytes32(0)
                    || (seat.feeDue != 0
                        && ((attendance.reportedAt != 0 && !attendance.attended)
                            || feedback.status == SparkV15Booking.ServiceStatus.NoneDelivered))
            ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
        } else if (faultTreatment) {
            if (route >= SparkV15Settlement.Route.OneToOneAbsence) {
                revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            }
            // The operative finding supplies this fee. Redress owns the refund principal for that finding.
            seat.feeDue = faultFee;
            seat.tutorPay = tutorTerms.ordinaryPay;
        } else if (route == SparkV15Settlement.Route.OneToOneAbsence) {
            if (!absent || terms.payableFee % 2 != 0 || lesson.terms.tutorFee % 2 != 0) {
                revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            }
            seat.tutorPay = lesson.terms.tutorFee / 2;
        } else if (route == SparkV15Settlement.Route.OneToOneAgreedAbsence) {
            if (
                !absent || terms.changeTermsRef == bytes32(0)
                    || context.serviceDocumentRef
                        != policies.alternatives
                            .agreedAbsenceCommitment(
                                lessonId,
                                terms.placeId,
                                lesson.terms.documentsRef,
                                terms.changeTermsRef,
                                finding.agreedAbsenceFee,
                                finding.agreedAbsenceTutorPay
                            )
            ) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
            seat.feeDue = finding.agreedAbsenceFee;
            seat.tutorPay = finding.agreedAbsenceTutorPay;
        } else if (absentAfterNoticeError) {
            seat.tutorPay = tutorTerms.absencePay;
        } else if (absent) {
            if (
                route > SparkV15Settlement.Route.VerifiedGroup || attendance.reportedAt == 0 || attendance.attended
                    || terms.payableFee % 2 != 0
                    || (feedback.evidenceId != 0 && feedback.status != SparkV15Booking.ServiceStatus.NoneDelivered)
            ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            seat.tutorPay = tutorTerms.absencePay;
        } else {
            if (attendance.reportedAt != 0 && !attendance.attended) {
                revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
            }
            seat.tutorPay = tutorTerms.ordinaryPay;
        }
        if (!providerStartedEarly && !absentAfterNoticeError) {
            (seat.noticeEvidenceId, seat.replacementNoticeEvidenceId) =
                occurrences.studentNoticeEvidence(formId, context.changeId, context.startedAt, lesson.packageId);
        }
        seat.formId = formId;
        seat.placeId = terms.placeId;
        seat.debitAccount = unconfirmed ? bytes32(0) : terms.creditAccount;
        // Booking permits exactly the customer or designated payer's original account for a positive debit.
        seat.debitOwner = unconfirmed || terms.payableFee == 0
            ? address(0)
            : (PAYMENTS.FUNDS().creditAccount(terms.payer) == terms.creditAccount ? terms.payer : terms.customer);
        seat.normalFee = terms.normalFee;
        seat.debited = form.confirmation.debitedUnits;
        seat.disposition = redressBasis == bytes32(0) ? finding.disposition : SparkV15Settlement.SeatDisposition.ProviderRedressFee;
        seat.refundDue = seat.debited > seat.feeDue ? seat.debited - seat.feeDue : 0;
        seat.attendanceEvidenceId = attendance.evidenceId;
        seat.serviceFeedbackEvidenceId = feedback.evidenceId;
        seat.serviceAvailabilityRef = finding.serviceAvailabilityRef;
    }

    function _compilePayments(
        PaymentCompilation memory context,
        SparkV15Settlement.GroupAssessment calldata assessment,
        SparkV15Settlement.CompiledGroup memory compiled
    ) private view {
        SparkV15Payments.PaymentTerms[] memory pending = new SparkV15Payments.PaymentTerms[](compiled.seats.length * 2);
        uint256 count;
        bool providerStartedEarly = assessment.route == SparkV15Settlement.Route.ProviderStartedEarly;
        for (uint256 i; i < compiled.seats.length; ++i) {
            SparkV15Settlement.SeatSettlement memory seat = compiled.seats[i];
            SparkV15Settlement.SeatDisposition disposition = assessment.seats[i].disposition;
            if (
                disposition == SparkV15Settlement.SeatDisposition.PreviouslySettled
                    || disposition == SparkV15Settlement.SeatDisposition.DeferredByHold
            ) {
                continue;
            }
            if (
                providerStartedEarly
                    || (seat.refundDue != 0 && seat.disposition == SparkV15Settlement.SeatDisposition.VerifiedAbsence)
            ) {
                SparkV15Payments.PaymentTerms memory refund = _paymentTerms(
                    context,
                    SETTLEMENT.refundPaymentPart(seat.placeId),
                    seat.debitOwner,
                    seat.refundDue,
                    assessment.refund.schedule
                );
                refund.originalDebitAccount = seat.debitAccount;
                refund.originalDebitAmount = seat.debited;
                (seat.refundObligationId, seat.refundAlreadyReceived) =
                    SETTLEMENT.retainedPayment(refund, context.packageId);
                if (providerStartedEarly) _requireUnheldProviderStartPart(seat.refundObligationId, refund.amount);
                if (seat.refundObligationId == bytes32(0) && refund.amount != 0) pending[count++] = refund;
            }
            if (providerStartedEarly || seat.tutorNetPay != 0) {
                SparkV15Payments.PaymentTerms memory wage = _paymentTerms(
                    context,
                    SETTLEMENT.tutorPaymentPart(context.tutor, seat.placeId),
                    assessment.tutor.recipient,
                    seat.tutorNetPay,
                    assessment.tutor.schedule
                );
                wage.agreedStart = context.deadlineAnchor;
                wage.legalDeadline = context.legalDeadline;
                wage.legalDeadlineExact = context.legalDeadlineExact;
                (seat.tutorObligationId,) = SETTLEMENT.retainedPayment(wage, context.packageId);
                if (providerStartedEarly) _requireUnheldProviderStartPart(seat.tutorObligationId, wage.amount);
                if (seat.tutorObligationId == bytes32(0) && wage.amount != 0) pending[count++] = wage;
            }
            compiled.seats[i] = seat;
        }
        compiled.preview.payments = new SparkV15Payments.PaymentTerms[](count);
        for (uint256 i; i < count; ++i) {
            compiled.preview.payments[i] = pending[i];
        }
    }

    function _requireUnheldProviderStartPart(bytes32 obligationId, uint128 amount) private view {
        if (
            obligationId != bytes32(0)
                && (PAYMENTS.HOLDS().getStatus(obligationId).active
                    || PAYMENTS.getObligation(obligationId).correctAmount != amount)
        ) revert SparkV15Settlement.OrdinaryGroupConditionsNotMet();
    }

    function _requireDisinterestedInLesson(SparkV15Booking.LessonTerms memory terms, address paidTo, address actor)
        private
        pure
    {
        if (actor == terms.provider || actor == terms.tutor || actor == paidTo) {
            revert SparkV15Settlement.InterestedSettlementActor();
        }
    }

    function _requireAgreedTerms(
        SparkV15Booking.Lesson memory lesson,
        SparkV15SettlementOccurrences.Basis memory occurrence,
        SparkV15Settlement.GroupAssessment calldata assessment
    ) private view {
        SparkV15Booking.LessonTerms memory terms = lesson.terms;
        // Booking requires both signatures before tutor acceptance and confirmation.
        if (
            assessment.tutor.agreementRef != terms.tutorAgreementRef || assessment.tutor.recipient == address(0)
                || assessment.refund.serviceDocumentRef == bytes32(0)
                || SETTLEMENT.tutorPayTermsCommitment(terms.lessonId, assessment.tutor) != terms.tutorPayTermsRef
                || SETTLEMENT.refundTermsCommitment(terms.lessonId, assessment.refund) != terms.serviceTermsRef
        ) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
        SparkV15Settlement.PaymentSchedule calldata tutorSchedule = assessment.tutor.schedule;
        if (occurrence.legalDeadline == 0) {
            _requireSchedule(tutorSchedule, uint256(occurrence.deadlineAnchor) + 30 days);
        } else {
            _requireSchedule(tutorSchedule, 1);
            if (
                tutorSchedule.dueAt > occurrence.legalDeadline
                    || (tutorSchedule.dueAt == occurrence.legalDeadline && !occurrence.legalDeadlineExact)
            ) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
        }
        _requireSchedule(assessment.refund.schedule, 0);
    }

    function _requireSchedule(SparkV15Settlement.PaymentSchedule calldata schedule, uint256 earliestDue) private pure {
        if (
            schedule.dueAt < earliestDue || schedule.dueAt > schedule.executionDeadline
                || (schedule.postLiftDeadline == 0) == (schedule.postLiftPeriod == 0)
        ) revert SparkV15Settlement.InvalidAgreedPaymentTerms();
    }

    function _requireDisinterestedInSeat(SparkV15Booking.PlaceTerms memory terms, address actor) private pure {
        if (
            actor == terms.customer || actor == terms.customerRepresentative || actor == terms.payer
                || actor == terms.student
        ) revert SparkV15Settlement.InterestedSettlementActor();
    }

    function _requireAvailable(uint256 evidenceId, uint256 packageId) private view {
        EVIDENCE_REGISTRY.requireUsableEvidenceReferenceForPackage(evidenceId, packageId);
    }

    function _paymentTerms(
        PaymentCompilation memory context,
        bytes32 paymentPart,
        address recipient,
        uint128 amount,
        SparkV15Settlement.PaymentSchedule calldata schedule
    ) private pure returns (SparkV15Payments.PaymentTerms memory terms) {
        terms.lessonId = context.lessonId;
        terms.paymentPart = paymentPart;
        terms.recipient = recipient;
        terms.amount = amount;
        terms.dueAt = schedule.dueAt;
        terms.executionDeadline = schedule.executionDeadline;
        terms.postLiftDeadline = schedule.postLiftDeadline;
        terms.postLiftPeriod = schedule.postLiftPeriod;
        terms.dueAtExact = true;
        terms.executionDeadlineExact = true;
        terms.postLiftDeadlineExact = schedule.postLiftDeadline != 0;
        terms.settlementProposer = context.proposer;
        terms.settlementApprover = context.approver;
    }
}
