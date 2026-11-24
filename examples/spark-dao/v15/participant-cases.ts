import { keccak256, toHex, zeroHash, type Address, type Hex, type PublicClient } from 'viem';
import { withCanonicalSnapshot, type CanonicalSnapshot } from '@ava-protocol/sdk';
import type { CourseInstallation, CourseOffer, createParticipantCourse } from './participant-course.ts';
import { sparkV15 } from './payments.ts';

const same = (a: unknown, b: string) => typeof a === 'string' && a.toLowerCase() === b.toLowerCase();
type Notice = { referenceHash: Hex; sentAt: bigint };
type Concern = { termsId: Hex; lessonId: Hex; obligationId: Hex; replyCutoff: bigint; reviewCutoff: bigint; reviewRequestedAt: bigint;
  appointmentRequiredAt: bigint; firstReplyAt: bigint; intake: { raisedBy: Address; receiver: Address; receivedAt: bigint; evidenceId: bigint };
  acknowledgment: { input: { handler: Address; notice: Notice }; evidenceId: bigint } };
type Case = { initial: { evidenceId: bigint; decidedAt: bigint; decider: Address; input: { issue: number; outcome: Hex } }; review: { evidenceId: bigint; decidedAt: bigint;
  input: { disposition: number; approvalRequestId: bigint; outcome: Hex } };
  original: { evidenceId: bigint; decider: Address; decidedAt: bigint; outcome: Hex }; adoptionNotice: Notice };
type Contacts = { terms: { coordinator: Address; leadAcademicTutor: Address; namedReviewer: Address; escalationContact: Address } };
const corePartner = keccak256(toHex('ava.spark.role.core-partner.v1.5'));

export function createParticipantCases(options: { client: PublicClient; modules: CourseInstallation;
  course: ReturnType<typeof createParticipantCourse> }) {
  const { client, modules, course } = options;
  const { intake, cases } = modules;
  const supportsPaymentRevision = cases.abi.some(entry => entry.type === 'function' && entry.name === 'decidePaymentRevision');
  const readsPaymentRevision = cases.abi.some(entry => entry.type === 'function' && entry.name === 'reviewedPaymentRevision');
  const readsAppointmentScope = cases.abi.some(entry => entry.type === 'function' && entry.name === 'isAppointedForCase');
  async function availableNotices(caseId: Hex, item: Concern, record: Case, snapshot: CanonicalSnapshot) {
    const rows = [];
    if (item.acknowledgment.evidenceId) rows.push({ kind: '受理通知', ...item.acknowledgment.input.notice });
    if (!same(record.adoptionNotice.referenceHash, zeroHash)) rows.push({ kind: '更正通知', ...record.adoptionNotice });
    // A reply notice cannot predate the concern. Keep time-zero notices readable on local chains.
    if (item.firstReplyAt === 0n && item.intake.receivedAt > 0n) return rows;
    const replies = await client.getContractEvents({ ...intake, eventName: 'ConcernReplyRecorded', args: { caseId },
      fromBlock: 0n, toBlock: snapshot.blockNumber, strict: true });
    const reads = await Promise.all(replies.map(entry => course.read<{ input: { notice: Notice } }>(
      intake, 'getReply', snapshot.point, [caseId, (entry.args as { index: bigint }).index])));
    rows.push(...reads.map(reply => ({ kind: '案件答复', ...reply.input.notice })));
    return rows;
  }
  async function inbox(account: Address) {
    return withCanonicalSnapshot(client, async snapshot => {
      const { point, blockNumber, blockHash, timestamp } = snapshot;
      const [events, coordinator, alternative, verifier, partner] = await Promise.all([
        client.getContractEvents({ ...intake, eventName: 'ConcernReceived', fromBlock: 0n, toBlock: blockNumber, strict: true }),
        course.authority(account, modules.coordinator, ['acknowledge-concern', 'reply-to-concern', 'adopt-review-correction'], point),
        course.authority(account, sparkV15.alternativeContactRole, ['acknowledge-concern', 'reply-to-concern'], point),
        course.authority(account, sparkV15.verifierRole, ['decide-initial-finding', 'decide-independent-review', 'retain-original-outcome'], point),
        course.authority(account, corePartner, ['appoint-case-actor', 'escalate-review-case', 'reply-to-concern'], point),
      ]);
      const records = await Promise.all(events.map(async event => {
        const caseId = (event.args as { caseId: Hex }).caseId;
        const item = await course.read<Concern>(intake, 'getConcern', point, [caseId]);
        const appointed = (purpose: number, afterReceipt: boolean) => readsAppointmentScope
          ? course.read<boolean>(cases, 'isAppointedForCase', point, [caseId, purpose, account, timestamp, afterReceipt])
          : course.read<boolean>(cases, 'isAppointed', point, [caseId, purpose, account, timestamp]);
        const [publication, progress, record, appointedInitial, appointedReview, appointedHandler] = await Promise.all([
          course.read<Contacts>(intake, 'getPublishedContacts', point, [item.termsId]),
          course.read<readonly [number, number]>(intake, 'getProgress', point, [caseId]),
          course.read<Case>(cases, 'getCase', point, [caseId]),
          appointed(1, false),
          appointed(2, item.appointmentRequiredAt !== 0n),
          appointed(0, true),
        ]);
        const { leadAcademicTutor, namedReviewer, escalationContact } = publication.terms;
        const filer = same(item.intake.raisedBy, account), receiver = same(item.intake.receiver, account);
        const handler = appointedHandler || (same(item.acknowledgment.input.handler, account)
          && (!readsAppointmentScope || item.appointmentRequiredAt === 0n || item.appointmentRequiredAt > timestamp));
        const lead = same(leadAcademicTutor, account) || appointedInitial;
        const reviewer = same(namedReviewer, account) || appointedReview;
        const escalator = same(escalationContact, account);
        if (!filer && !receiver && !handler && !lead && !reviewer && !escalator) return;
        const offers: CourseOffer[] = [];
        const acknowledged = item.acknowledgment.evidenceId !== 0n;
        if (receiver && !acknowledged && (coordinator.allowed.has('acknowledge-concern') || alternative.allowed.has('acknowledge-concern'))) {
          offers.push(course.offer('acknowledge', { caseId }));
        }
        if (acknowledged && handler
          && [coordinator, alternative, partner].some(role => role.allowed.has('reply-to-concern'))) offers.push(course.offer('reply', { caseId }));
        if (filer && item.reviewRequestedAt === 0n && record.review.decidedAt === 0n) offers.push(course.offer('requestReview', { caseId }));
        if (lead && record.initial.evidenceId === 0n && verifier.allowed.has('decide-initial-finding')) {
          offers.push(course.offer('decideInitial', { caseId }));
        }
        const initialFault = record.initial.evidenceId !== 0n && record.initial.input.issue === 1
          && same(record.initial.decider, account) && record.review.decidedAt === 0n;
        if (initialFault && modules.remedies && same(item.obligationId, zeroHash)
          && record.original.evidenceId === 0n && verifier.allowed.has('retain-original-outcome')) {
          offers.push(course.offer('retainOriginal'));
        }
        if (initialFault && modules.remedies && record.original.evidenceId !== 0n
          && same(record.original.decider, record.initial.decider) && same(record.original.outcome, record.initial.input.outcome)
          && record.original.decidedAt === record.initial.decidedAt
          && await course.read<bigint>(modules.remedies, 'latestFaultRevision', point, [caseId]) === 0n) {
          offers.push(course.offer('recordFault', { caseId }));
        }
        const canReview = appointedReview || (same(namedReviewer, account) && item.appointmentRequiredAt === 0n);
        if (canReview && (item.reviewRequestedAt !== 0n || record.original.evidenceId !== 0n)
          && record.review.decidedAt === 0n && verifier.allowed.has('decide-independent-review')) {
          offers.push(course.offer('decideReview', { caseId }));
          if (supportsPaymentRevision && !same(item.obligationId, zeroHash)) {
            offers.push(course.offer('decidePaymentRevision', { caseId }));
          }
        }
        if (escalator && partner.allowed.has('escalate-review-case') && progress.some(stage => stage === 2)) {
          offers.push(course.offer('escalate', { caseId }));
        }
        if (escalator && partner.allowed.has('appoint-case-actor') && item.appointmentRequiredAt !== 0n) {
          offers.push(course.offer('appoint', { caseId }));
        }
        const adopted = record.adoptionNotice.sentAt !== 0n;
        if (!adopted && record.original.evidenceId !== 0n && record.review.input.disposition === 2
          && same(publication.terms.coordinator, account) && coordinator.allowed.has('adopt-review-correction')) {
          const requestId = record.review.input.approvalRequestId;
          if (requestId !== 0n) offers.push(course.offer('adoptApprovalStop', { caseId, requestId }));
          else if (!readsPaymentRevision) {
            offers.push(course.offer(same(item.obligationId, zeroHash) ? 'adoptCorrection' : 'adoptPaymentRevision', { caseId }));
          } else {
            const revision = await course.read<Hex>(cases, 'reviewedPaymentRevision', point, [caseId]);
            if (same(revision, zeroHash)) offers.push(course.offer('adoptCorrection', { caseId }));
            else if (same(revision, record.review.input.outcome)) {
              offers.push(course.offer('adoptPaymentRevision', { caseId }));
            }
          }
        }
        return { caseId, lessonId: item.lessonId, obligationId: item.obligationId, acknowledged, adopted, receivedAt: item.intake.receivedAt,
          replyCutoff: item.replyCutoff, reviewCutoff: item.reviewCutoff, firstReplyAt: item.firstReplyAt, progress,
          reviewDecidedAt: record.review.decidedAt, receipts: await availableNotices(caseId, item, record, snapshot),
          offers, origin: { hash: event.transactionHash, blockNumber: event.blockNumber, logIndex: event.logIndex } };
      }));
      return { asOf: { blockNumber, blockHash, timestamp }, records: records.filter(record => record !== undefined) };
    });
  }
  async function noticeLinked({ caseId, obligationId, noticeHash }: { caseId: Hex; obligationId: Hex; noticeHash: Hex }) {
    return withCanonicalSnapshot(client, async snapshot => {
      const item = await course.read<Concern>(intake, 'getConcern', snapshot.point, [caseId]);
      if (item.intake.evidenceId === 0n || !same(item.obligationId, obligationId)) return false;
      const record = await course.read<Case>(cases, 'getCase', snapshot.point, [caseId]);
      return (await availableNotices(caseId, item, record, snapshot)).some(notice => same(notice.referenceHash, noticeHash));
    });
  }
  return { inbox, noticeLinked };
}
