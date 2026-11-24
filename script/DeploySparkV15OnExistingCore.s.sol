// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {AVAApplicationRegistry} from "@ava-protocol/contracts/src/AVAApplicationRegistry.sol";
import {AVAAuthorityMatrix} from "@ava-protocol/contracts/src/core/AVAAuthorityMatrix.sol";
import {AVACoreRulePackageRegistry} from "@ava-protocol/contracts/src/core/AVACoreRulePackageRegistry.sol";
import {AVACoreTypes} from "@ava-protocol/contracts/src/core/AVACoreTypes.sol";
import {AVAGovernanceKernel} from "@ava-protocol/contracts/src/core/AVAGovernanceKernel.sol";
import {DefaultAVACorePolicyBundle} from "@ava-protocol/contracts/src/core/modules/DefaultAVACoreRuleModules.sol";
import {AVARequestAllocation} from "@ava-protocol/contracts/src/extensions/requests/AVARequestAllocation.sol";
import {AVABoundRequestPolicy} from "@ava-protocol/contracts/src/extensions/requests/AVABoundRequestPolicy.sol";
import {DefaultAVAExtensionPolicyModule} from "@ava-protocol/contracts/src/extensions/shared/DefaultAVAExtensionPolicyModule.sol";
import {SparkV15, SparkV15ApplicationModule} from "../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {
    ISparkV15AdoptedDispositions,
    ISparkV15SettlementPaymentPolicy,
    SparkV15Payments
} from "../src/apps/spark/v15/SparkV15Payments.sol";
import {SparkV15Funds} from "../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15PaymentHolds} from "../src/apps/spark/v15/SparkV15PaymentHolds.sol";
import {SparkV15PaymentTakeover} from "../src/apps/spark/v15/SparkV15PaymentTakeover.sol";
import {SparkV15PaymentObservations} from "../src/apps/spark/v15/SparkV15PaymentObservations.sol";
import {
    SparkV15Booking,
    SparkV15BookingOpening,
    ISparkV15BookingFunds,
    ISparkV15BookingChanges
} from "../src/apps/spark/v15/SparkV15Booking.sol";
import {SparkV15BookingPrefunding} from "../src/apps/spark/v15/SparkV15BookingPrefunding.sol";
import {SparkV15CourseNotices} from "../src/apps/spark/v15/SparkV15CourseNotices.sol";
import {SparkV15TeachingEnd} from "../src/apps/spark/v15/SparkV15TeachingEnd.sol";
import {
    SparkV15BookingChanges,
    SparkV15BookingCancellations,
    ISparkV15RemedyBooking
} from "../src/apps/spark/v15/SparkV15BookingChanges.sol";
import {
    SparkV15ReviewCases,
    SparkV15ReviewActions,
    SparkV15ConcernIntake
} from "../src/apps/spark/v15/SparkV15ReviewCases.sol";
import {SparkV15Settlement, ISparkV15SettlementRemedies} from "../src/apps/spark/v15/SparkV15Settlement.sol";
import {
    SparkV15SettlementAlternatives,
    ISparkV15SettlementActors
} from "../src/apps/spark/v15/SparkV15SettlementAlternatives.sol";
import {
    SparkV15LessonRemedies,
    SparkV15CustomerRedress,
    SparkV15TutorDebt,
    SparkV15RemedyBookings
} from "../src/apps/spark/v15/SparkV15LessonRemedies.sol";
import {SparkV15Materials, SparkV15MaterialsUse, ISparkV15MaterialInterests} from "../src/apps/spark/v15/SparkV15Materials.sol";
import {
    SparkV15FundingCases,
    SparkV15MaterialProvisions,
    SparkV15MaterialBacking,
    SparkV15ServiceReserve
} from "../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {SparkV15MaterialRights} from "../src/apps/spark/v15/SparkV15MaterialRights.sol";
import {IERC20} from "../src/apps/spark/legacy/interfaces/IERC20.sol";
import {AVADefaultBindings} from "@ava-protocol/contracts/script/AVADefaultBindings.sol";

interface SparkV15DeployVm {
    function envAddress(string calldata name) external view returns (address);
    function envOr(string calldata name, address defaultValue) external view returns (address);
    function startBroadcast(address signer) external;
    function stopBroadcast() external;
}

/// @notice Installs Spark v1.5 on an existing local Core.
contract DeploySparkV15OnExistingCore {
    SparkV15DeployVm private constant vm = SparkV15DeployVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    bytes32 public constant SOURCE = keccak256("ava.spark.role.source.v1.5");
    bytes32 public constant VERIFIER = keccak256("ava.spark.role.verifier.v1.5");
    bytes32 public constant ALLOCATOR = keccak256("ava.spark.role.allocator.v1.5");
    bytes32 public constant PUBLISHER = keccak256("ava.spark.role.bootstrap-publisher.v1.5");
    bytes32 public constant COORDINATOR = keccak256("ava.spark.role.booking-coordinator.v1.5");
    bytes32 public constant CORE_PARTNER = keccak256("ava.spark.role.core-partner.v1.5");

    struct Deployment {
        AVAGovernanceKernel kernel;
        AVARequestAllocation requests;
        SparkV15ApplicationModule applicationModule;
        SparkV15Payments payments;
        SparkV15PaymentHolds holds;
        AVABoundRequestPolicy requestPolicy;
        DefaultAVACorePolicyBundle corePolicy;
        DefaultAVAExtensionPolicyModule extensionPolicy;
        SparkV15Booking booking;
        SparkV15ReviewCases cases;
        SparkV15Settlement settlement;
        SparkV15PaymentObservations observations;
        uint256 packageId;
        uint256 disclosurePolicyId;
        SparkV15PaymentTakeover paymentTakeover;
    }

    event ContractDeployed(bytes32 indexed name, address indexed deployed);
    event InitializationComplete(
        uint256 chainId, bytes32 appId, bytes32 workflowKey, uint256 packageId, uint256 policyId
    );

    function run() external returns (Deployment memory d) {
        require(block.chainid == 31337, "Local chain only");
        d.kernel = AVAGovernanceKernel(_address("AVA_EXISTING_KERNEL"));
        d.requests = AVARequestAllocation(_address("AVA_EXISTING_REQUESTS"));
        address admin = _address("AVA_ROOT_ADMIN");
        address token = _address("SPARK_V15_TOKEN");
        address alternate = vm.envOr("SPARK_V15_ALTERNATIVE_CONTACT", address(0));
        address provider = vm.envOr("SPARK_V15_COURSE_PROVIDER", address(0));
        address materialsDao = vm.envOr("SPARK_V15_MATERIALS_DAO", address(0));
        address serviceReserve = vm.envOr("SPARK_V15_SERVICE_RESERVE", address(0));
        require(
            (materialsDao == address(0)) == (serviceReserve == address(0))
                && (materialsDao == address(0) || provider != address(0)),
            "Materials require course and both reserve actors"
        );
        address coordinator;
        address corePartner;
        if (provider != address(0)) {
            coordinator = _address("SPARK_V15_BOOKING_COORDINATOR");
            corePartner = _address("SPARK_V15_CORE_PARTNER");
            require(
                provider != coordinator && provider != corePartner && coordinator != corePartner, "Actors must differ"
            );
            require(
                alternate == address(0)
                    || (alternate != provider && alternate != coordinator && alternate != corePartner),
                "Actors must differ"
            );
        }
        address[4] memory actors = [
            _address("SPARK_V15_SOURCE"),
            _address("SPARK_V15_VERIFIER"),
            _address("SPARK_V15_ALLOCATOR"),
            _address("SPARK_V15_REVIEWER")
        ];
        for (uint256 i; i < actors.length; ++i) {
            require(alternate == address(0) || alternate != actors[i], "Actors must differ");
            require(
                provider == address(0)
                    || ((actors[i] != provider || (materialsDao != address(0) && i == 2))
                        && actors[i] != coordinator
                        && actors[i] != corePartner),
                "Actors must differ"
            );
            for (uint256 j; j < i; ++j) {
                require(actors[i] != actors[j], "Actors must differ");
            }
        }
        _checkExisting(d, admin);
        require(token.code.length != 0, "Token code required");
        vm.startBroadcast(admin);
        d.applicationModule = new SparkV15ApplicationModule(SparkV15.WORKFLOW, SOURCE, VERIFIER, ALLOCATOR);
        d.payments = new SparkV15Payments(d.requests, IERC20(token), SparkV15.WORKFLOW, VERIFIER);
        d.holds = new SparkV15PaymentHolds(address(d.payments), d.requests, SparkV15.WORKFLOW, VERIFIER);
        d.observations = new SparkV15PaymentObservations(address(d.payments), d.requests, VERIFIER);
        if (provider != address(0)) {
            d.booking = new SparkV15Booking(
                d.requests,
                ISparkV15BookingFunds(address(d.payments.FUNDS())),
                SparkV15.WORKFLOW,
                COORDINATOR,
                VERIFIER,
                provider
            );
            d.booking.bindOpening(
                new SparkV15BookingOpening(
                    d.booking,
                    new SparkV15BookingPrefunding(d.booking),
                    new SparkV15TeachingEnd(d.booking),
                    new SparkV15CourseNotices(d.booking)
                )
            );
            d.cases = new SparkV15ReviewCases(d.payments, SOURCE);
            d.settlement = new SparkV15Settlement(d.booking, d.payments);
        }
        d.corePolicy = new DefaultAVACorePolicyBundle();
        d.extensionPolicy = new DefaultAVAExtensionPolicyModule();
        d.requestPolicy = new AVABoundRequestPolicy(
            address(d.requests),
            SparkV15.APP_ID,
            SparkV15.WORKFLOW,
            address(d.payments),
            SparkV15.RESPONSE_APPROVE_PAYMENT,
            SparkV15.APPROVAL_BURDEN
        );
        _configure(d, admin, actors, alternate);
        d.payments.bindHolds(d.holds);
        d.payments.bindPaymentObservations(address(d.observations));
        _grant(d, VERIFIER, d.observations.ACTION_VERIFY_OBSERVATION());
        if (provider != address(0)) {
            d.cases.bindIntake(new SparkV15ConcernIntake(d.payments, SOURCE, d.cases));
            d.paymentTakeover = new SparkV15PaymentTakeover(d.settlement, d.cases, SOURCE);
            _configureOptional(d, provider, coordinator, corePartner, alternate);
            d.payments.bindReviewCases(ISparkV15AdoptedDispositions(address(d.cases)));
            SparkV15CustomerRedress redress = _installCourseRules(d);
            if (materialsDao != address(0)) {
                _installMaterials(d, redress, materialsDao, serviceReserve);
            } else {
                SparkV15FundingCases coverage =
                    new SparkV15FundingCases(d.booking, d.payments, SparkV15Materials(address(0)));
                d.payments.FUNDS().bindOrdinaryBookingCoverage(address(coverage));
                emit ContractDeployed("ordinaryBookingCoverage", address(coverage));
            }
        }
        vm.stopBroadcast();
        d.kernel.requireStablePackageBindings(d.packageId);
        emit ContractDeployed("applicationModule", address(d.applicationModule));
        emit ContractDeployed("payments", address(d.payments));
        emit ContractDeployed("funds", address(d.payments.FUNDS()));
        emit ContractDeployed("returns", address(d.payments.RETURNS()));
        emit ContractDeployed("paymentHolds", address(d.holds));
        emit ContractDeployed("observations", address(d.observations));
        if (provider != address(0)) {
            emit ContractDeployed("booking", address(d.booking));
            emit ContractDeployed("reviewCases", address(d.cases));
            emit ContractDeployed("concernIntake", address(d.cases.INTAKE()));
            emit ContractDeployed("paymentTakeover", address(d.paymentTakeover));
            emit ContractDeployed("settlement", address(d.settlement));
        }
        emit ContractDeployed("requestPolicy", address(d.requestPolicy));
        emit ContractDeployed("corePolicy", address(d.corePolicy));
        emit ContractDeployed("extensionPolicy", address(d.extensionPolicy));
        emit InitializationComplete(
            block.chainid, SparkV15.APP_ID, SparkV15.WORKFLOW, d.packageId, d.disclosurePolicyId
        );
    }

    function _installCourseRules(Deployment memory d) private returns (SparkV15CustomerRedress redress) {
        d.settlement
            .bindAlternatives(
                new SparkV15SettlementAlternatives(
                    d.booking, d.payments, ISparkV15SettlementActors(address(d.settlement))
                )
            );
        SparkV15BookingChanges changes = new SparkV15BookingChanges(d.booking, d.payments);
        d.booking.bindBookingChanges(ISparkV15BookingChanges(address(changes)));
        _assign(d, address(changes.CREDIT_SELECTIONS()), d.payments.FUNDS().BOOKING_ROLE());
        SparkV15BookingCancellations cancellations = new SparkV15BookingCancellations(changes);
        changes.bindCancellations(cancellations);
        _assign(d, address(cancellations), d.payments.settlementRole());
        _grant(d, VERIFIER, cancellations.ACTION_VERIFY_CANCELLATION());
        SparkV15LessonRemedies remedies = new SparkV15LessonRemedies(d.booking, d.payments, d.cases, SOURCE);
        redress = new SparkV15CustomerRedress(remedies, SOURCE);
        SparkV15TutorDebt tutorDebt = new SparkV15TutorDebt(remedies, redress, SOURCE);
        SparkV15RemedyBookings remedyBookings = new SparkV15RemedyBookings(redress, SOURCE);
        remedies.bindCustomerRedress(redress);
        redress.bindRemedyBookings(remedyBookings);
        changes.bindRemedyBooking(ISparkV15RemedyBooking(address(remedyBookings)));
        d.settlement.setRemedyPolicy(ISparkV15SettlementRemedies(address(remedies)));
        d.payments.bindSettlementPolicy(ISparkV15SettlementPaymentPolicy(address(d.settlement)));
        _assign(d, address(redress), d.payments.settlementRole());
        _assign(d, address(redress), d.payments.FUNDS().COMPENSATION_ROLE());
        _grant(d, d.payments.FUNDS().COMPENSATION_ROLE(), d.payments.FUNDS().ACTION_GRANT_COMPENSATION());
        _grant(d, VERIFIER, remedies.ACTION_VERIFY_TUTOR_PAY_HISTORY());
        _grant(d, COORDINATOR, remedies.ACTION_RECORD_UNDISPUTED_PROVIDER_FAULT());
        _grant(d, VERIFIER, redress.ACTION_ASSESS_REFUND());
        _grant(d, VERIFIER, tutorDebt.ACTION_CONFIRM_TUTOR_LOSS());
        _grant(d, VERIFIER, tutorDebt.ACTION_VERIFY_CUSTOMER_DELIVERY());
        _grant(d, COORDINATOR, d.settlement.ALTERNATIVES().ACTION_CONFIRM_ONE_TO_ONE());
        _grant(d, VERIFIER, d.settlement.ALTERNATIVES().ACTION_VERIFY_ONE_TO_ONE_ABSENCE());
        _grant(d, VERIFIER, d.settlement.ALTERNATIVES().ACTION_IMPOSE_FEE_HOLD());
        _grant(d, VERIFIER, d.settlement.ALTERNATIVES().ACTION_LIFT_FEE_HOLD());
        _grant(d, VERIFIER, d.settlement.ALTERNATIVES().OCCURRENCES().ACTION_VERIFY_EARLIER_TUTOR_DEADLINE());
        emit ContractDeployed("bookingChanges", address(changes));
        emit ContractDeployed("bookingCreditSelection", address(changes.CREDIT_SELECTIONS()));
        emit ContractDeployed("bookingCancellations", address(cancellations));
        emit ContractDeployed("settlementAlternatives", address(d.settlement.ALTERNATIVES()));
        emit ContractDeployed("settlementOccurrences", address(d.settlement.ALTERNATIVES().OCCURRENCES()));
        emit ContractDeployed("lessonRemedies", address(remedies));
        emit ContractDeployed("customerRedress", address(redress));
        emit ContractDeployed("tutorDebt", address(tutorDebt));
        emit ContractDeployed("remedyBookings", address(remedyBookings));
    }

    function _installMaterials(Deployment memory d, SparkV15CustomerRedress redress, address dao, address reserveTo)
        private
    {
        SparkV15Materials materials = new SparkV15Materials(d.booking, d.cases);
        materials.bindMaterialUse(new SparkV15MaterialsUse(materials));
        SparkV15MaterialProvisions provisions = new SparkV15MaterialProvisions(materials, d.payments);
        SparkV15MaterialBacking backing = new SparkV15MaterialBacking(provisions, materials, d.booking, d.payments);
        provisions.bindMaterialBacking(backing);
        d.payments.FUNDS().bindMaterialProvisionsWithBookingCoverage(address(provisions));
        SparkV15MaterialRights rights = new SparkV15MaterialRights(materials, dao);
        provisions.bindMaterialRights(address(rights));
        materials.bindMaterialInterests(ISparkV15MaterialInterests(address(rights)));
        SparkV15ServiceReserve reserve = new SparkV15ServiceReserve(provisions, d.booking, d.payments);
        provisions.bindServiceReserveModule(reserve);
        reserve.bindServiceReserve(address(redress), reserveTo);
        _grant(d, COORDINATOR, materials.ACTION_CHECK_COMBINATIONS());
        _grant(d, COORDINATOR, materials.ACTION_VERIFY_USE());
        _grant(d, COORDINATOR, materials.ACTION_RECORD_GROSS());
        _grant(d, COORDINATOR, materials.ACTION_VERIFY_ATTRIBUTION());
        _grant(d, COORDINATOR, materials.ACTION_VERIFY_REVIEW_FOLLOW_UP());
        _grant(d, VERIFIER, provisions.ACTION_VERIFY_PROVISION());
        _grant(d, VERIFIER, provisions.ACTION_VERIFY_ENTITLEMENT());
        _grant(d, VERIFIER, provisions.ACTION_VERIFY_MATERIAL_RECEIPT());
        _grant(d, VERIFIER, backing.ACTION_VERIFY_RECEIPT_ALLOCATION());
        _grant(d, COORDINATOR, provisions.ACTION_FILE_MATERIAL_RECEIPT());
        _grant(d, VERIFIER, rights.ACTION_VERIFY_TRANSFER());
        _grant(d, VERIFIER, rights.ACTION_VERIFY_TRANSFER_COLLECTION());
        _grant(d, VERIFIER, reserve.ACTION_VERIFY_RESERVE_RELEASE());
        _grant(d, VERIFIER, reserve.ACTION_VERIFY_SERVICE_RESERVE());
        _grant(d, COORDINATOR, reserve.ACTION_FILE_SERVICE_RESERVE());
        emit ContractDeployed("materials", address(materials));
        emit ContractDeployed("materialUse", address(materials.MATERIAL_USE()));
        emit ContractDeployed("materialProvisions", address(provisions));
        emit ContractDeployed("materialBacking", address(backing));
        emit ContractDeployed("materialRights", address(rights));
        emit ContractDeployed("serviceReserve", address(reserve));
    }

    function _checkExisting(Deployment memory d, address admin) private view {
        require(address(d.kernel).code.length != 0 && address(d.requests).code.length != 0, "Existing code required");
        require(d.requests.REQUEST_POLICY_INTERFACE_VERSION() == 1, "Typed request policy required");
        require(
            address(d.requests.GOVERNANCE_KERNEL()) == address(d.kernel)
                && address(d.requests.AUTHORITY_MATRIX()) == address(d.kernel.AUTHORITY_MATRIX())
                && address(d.requests.IDENTITY_REGISTRY()) == address(d.kernel.IDENTITY_REGISTRY())
                && address(d.requests.RULE_PACKAGE_REGISTRY()) == address(d.kernel.RULE_PACKAGE_REGISTRY())
                && address(d.requests.EVIDENCE_REGISTRY()) == address(d.kernel.EVIDENCE_REGISTRY()),
            "Mixed Core"
        );
        require(d.kernel.IDENTITY_REGISTRY().APPLICATION_REGISTRY().ADMIN() == admin, "Root admin mismatch");
        try d.kernel.IDENTITY_REGISTRY().APPLICATION_REGISTRY().getApplication(SparkV15.APP_ID) returns (
            AVAApplicationRegistry.ApplicationRecord memory
        ) {
            revert("Spark v1.5 already registered");
        } catch {}
    }

    function _configure(Deployment memory d, address admin, address[4] memory actors, address alternate) private {
        d.kernel.IDENTITY_REGISTRY().APPLICATION_REGISTRY()
            .registerApplication(
                SparkV15.APP_ID,
                keccak256("spark.v1.5.application"),
                keccak256("spark.v1.5.authority"),
                admin,
                "local:spark/v1.5"
            );
        bytes32 publisher = _subject(admin, PUBLISHER);
        d.kernel.IDENTITY_REGISTRY()
            .assignSubject(admin, SparkV15.APP_ID, PUBLISHER, publisher, "local:spark/publisher");
        _publisherPermissions(d, true);
        d.packageId = d.kernel.RULE_PACKAGE_REGISTRY()
            .registerRulePackage(
                AVACoreRulePackageRegistry.PackageRegistrationInput(
                    SparkV15.APP_ID,
                    SparkV15.WORKFLOW,
                    PUBLISHER,
                    publisher,
                    1,
                    keccak256("spark.v1.5.compatibility"),
                    "local:spark/v1.5/rules"
                ),
                AVADefaultBindings.bindings(
                    address(d.applicationModule),
                    address(d.corePolicy),
                    address(d.extensionPolicy),
                    address(d.requestPolicy)
                )
            );
        d.disclosurePolicyId = d.kernel.DISCLOSURE_REGISTRY()
            .registerPolicy(
                SparkV15.APP_ID,
                PUBLISHER,
                publisher,
                keccak256("spark.v1.5.disclosure"),
                "Local payment evidence",
                "local:spark/v1.5/disclosure"
            );
        _publisherPermissions(d, false);
        d.kernel.IDENTITY_REGISTRY().deactivateSubject(publisher);
        bytes32[4] memory roles = [SOURCE, VERIFIER, ALLOCATOR, VERIFIER];
        for (uint256 i; i < actors.length; ++i) {
            d.kernel.IDENTITY_REGISTRY()
                .assignSubject(
                    actors[i], SparkV15.APP_ID, roles[i], _subject(actors[i], roles[i]), "local:spark/v1.5/actor"
                );
        }
        if (alternate != address(0)) {
            d.kernel.IDENTITY_REGISTRY()
                .assignSubject(
                    alternate,
                    SparkV15.APP_ID,
                    SparkV15.ALTERNATIVE_CONTACT_ROLE,
                    _subject(alternate, SparkV15.ALTERNATIVE_CONTACT_ROLE),
                    "local:spark/v1.5/alternative-contact"
                );
        }
        AVAAuthorityMatrix.PermissionUpdate[] memory updates =
            new AVAAuthorityMatrix.PermissionUpdate[](alternate == address(0) ? 11 : 12);
        updates[0] = AVAAuthorityMatrix.PermissionUpdate(SOURCE, AVACoreTypes.ACTION_REGISTER_EVIDENCE, true);
        updates[1] = AVAAuthorityMatrix.PermissionUpdate(SOURCE, AVACoreTypes.ACTION_REGISTER_GOVERNED_OBJECT, true);
        updates[2] = AVAAuthorityMatrix.PermissionUpdate(SOURCE, d.requests.ACTION_CREATE_REQUEST(), true);
        updates[3] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, AVACoreTypes.ACTION_FORM_RECOGNISED_STATE, true);
        updates[4] =
            AVAAuthorityMatrix.PermissionUpdate(VERIFIER, AVACoreTypes.ACTION_TRANSITION_RECOGNISED_STATE, true);
        updates[5] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, AVACoreTypes.ACTION_VEST_RECOGNISED_STATE, true);
        updates[6] = AVAAuthorityMatrix.PermissionUpdate(
            VERIFIER, SparkV15.ACTION_ESTABLISH_PAYMENT, address(d.booking) == address(0)
        );
        updates[7] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15.ACTION_FORMAL_HOLD, true);
        updates[8] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15.ACTION_LIFT_HOLD, true);
        updates[9] = AVAAuthorityMatrix.PermissionUpdate(ALLOCATOR, AVACoreTypes.ACTION_RECORD_ALLOCATION, true);
        updates[10] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15.ACTION_VERIFY_POST_LIFT_CLOCK, true);
        if (alternate != address(0)) {
            updates[11] = AVAAuthorityMatrix.PermissionUpdate(
                SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15.ACTION_TEMPORARY_HOLD, true
            );
        }
        d.kernel.AUTHORITY_MATRIX().setPermissions(SparkV15.APP_ID, updates);
    }

    function _configureOptional(
        Deployment memory d,
        address provider,
        address coordinator,
        address corePartner,
        address alternate
    ) private {
        SparkV15Funds funds = d.payments.FUNDS();
        _assign(d, address(d.booking), funds.BOOKING_ROLE());
        _assign(d, provider, funds.CREDIT_PROVIDER_ROLE());
        _assign(d, address(d.cases), d.payments.caseEffectRole());
        _assign(d, address(d.settlement), d.payments.settlementRole());
        _assign(d, coordinator, COORDINATOR);
        _assign(d, corePartner, CORE_PARTNER);
        AVAAuthorityMatrix.PermissionUpdate[] memory u =
            new AVAAuthorityMatrix.PermissionUpdate[](alternate == address(0) ? 23 : 25);
        u[0] = AVAAuthorityMatrix.PermissionUpdate(funds.BOOKING_ROLE(), funds.ACTION_MANAGE_LESSON_FUNDS(), true);
        u[1] = AVAAuthorityMatrix.PermissionUpdate(funds.CREDIT_PROVIDER_ROLE(), funds.ACTION_OFFER_RECHARGE(), true);
        u[2] = AVAAuthorityMatrix.PermissionUpdate(
            d.payments.caseEffectRole(), d.payments.ACTION_APPLY_CASE_EFFECT(), true
        );
        u[3] = AVAAuthorityMatrix.PermissionUpdate(COORDINATOR, d.booking.ACTION_COORDINATE_BOOKING(), true);
        u[4] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, d.booking.ACTION_VERIFY_PREFUNDING(), true);
        u[5] = AVAAuthorityMatrix.PermissionUpdate(
            funds.CREDIT_PROVIDER_ROLE(), SparkV15ReviewActions.ACTION_PUBLISH_CONTACTS, true
        );
        u[6] = AVAAuthorityMatrix.PermissionUpdate(COORDINATOR, SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN, true);
        u[7] = AVAAuthorityMatrix.PermissionUpdate(COORDINATOR, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, true);
        u[8] = AVAAuthorityMatrix.PermissionUpdate(COORDINATOR, SparkV15ReviewActions.ACTION_ADOPT_CORRECTION, true);
        u[9] = AVAAuthorityMatrix.PermissionUpdate(COORDINATOR, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true);
        u[10] = AVAAuthorityMatrix.PermissionUpdate(CORE_PARTNER, SparkV15ReviewActions.ACTION_APPOINT_CASE_ACTOR, true);
        u[11] = AVAAuthorityMatrix.PermissionUpdate(CORE_PARTNER, SparkV15ReviewActions.ACTION_ESCALATE_CASE, true);
        u[12] = AVAAuthorityMatrix.PermissionUpdate(
            CORE_PARTNER, SparkV15ReviewActions.ACTION_REQUIRE_CASE_APPOINTMENT, true
        );
        u[13] = AVAAuthorityMatrix.PermissionUpdate(CORE_PARTNER, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, true);
        u[14] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_INITIAL, true);
        u[15] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15ReviewActions.ACTION_DECIDE_REVIEW, true);
        u[16] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15ReviewActions.ACTION_RETAIN_ORIGINAL, true);
        u[17] = AVAAuthorityMatrix.PermissionUpdate(
            COORDINATOR, SparkV15ReviewActions.ACTION_REQUIRE_CASE_APPOINTMENT, true
        );
        u[18] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, SparkV15.ACTION_AUTHORISE_PAYMENT_RETURN, true);
        u[19] = AVAAuthorityMatrix.PermissionUpdate(
            d.payments.settlementRole(), d.payments.ACTION_RECORD_SETTLEMENT_OBLIGATION(), true
        );
        u[20] = AVAAuthorityMatrix.PermissionUpdate(COORDINATOR, d.settlement.ACTION_PROPOSE_GROUP_SETTLEMENT(), true);
        u[21] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, d.settlement.ACTION_APPROVE_GROUP_SETTLEMENT(), true);
        u[22] = AVAAuthorityMatrix.PermissionUpdate(VERIFIER, funds.ACTION_REPLENISH_PAYMENT_BACKING(), true);
        if (alternate != address(0)) {
            u[23] = AVAAuthorityMatrix.PermissionUpdate(
                SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15ReviewActions.ACTION_ACKNOWLEDGE_CONCERN, true
            );
            u[24] = AVAAuthorityMatrix.PermissionUpdate(
                SparkV15.ALTERNATIVE_CONTACT_ROLE, SparkV15ReviewActions.ACTION_REPLY_TO_CONCERN, true
            );
        }
        d.kernel.AUTHORITY_MATRIX().setPermissions(SparkV15.APP_ID, u);
        d.kernel.AUTHORITY_MATRIX().setPermission(SparkV15.APP_ID, VERIFIER, d.booking.ACTION_VERIFY_TEACHING(), true);
    }

    function _assign(Deployment memory d, address actor, bytes32 role) private {
        d.kernel.IDENTITY_REGISTRY()
            .assignSubject(actor, SparkV15.APP_ID, role, _subject(actor, role), "local:spark/v1.5/actor");
    }

    function _grant(Deployment memory d, bytes32 role, bytes32 action) private {
        d.kernel.AUTHORITY_MATRIX().setPermission(SparkV15.APP_ID, role, action, true);
    }

    function _publisherPermissions(Deployment memory d, bool allowed) private {
        AVAAuthorityMatrix.PermissionUpdate[] memory updates = new AVAAuthorityMatrix.PermissionUpdate[](2);
        updates[0] = AVAAuthorityMatrix.PermissionUpdate(PUBLISHER, AVACoreTypes.ACTION_REGISTER_RULE_PACKAGE, allowed);
        updates[1] =
            AVAAuthorityMatrix.PermissionUpdate(PUBLISHER, AVACoreTypes.ACTION_REGISTER_DISCLOSURE_POLICY, allowed);
        d.kernel.AUTHORITY_MATRIX().setPermissions(SparkV15.APP_ID, updates);
    }

    function _subject(address account, bytes32 role) private pure returns (bytes32) {
        return keccak256(abi.encode(SparkV15.APP_ID, role, account));
    }

    function _address(string memory name) private view returns (address a) {
        a = vm.envAddress(name);
        require(a != address(0), string.concat("Zero address: ", name));
    }
}
