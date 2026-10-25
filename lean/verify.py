#!/usr/bin/env python3
"""Compile this round in a clean directory and audit every named theorem."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'verification'
OUT.mkdir(exist_ok=True)
MODULES = ['Syntax', 'Schemes', 'Translation', 'SchemeTransfer', 'SetOperations', 'InfinityTransfer', 'BehaviorQuotient', 'WellFoundedParameters', 'DefinableKernel', 'InternalSyntax', 'PairCoding', 'RelationComprehension', 'InternalInverse', 'InternalComposition', 'InternalBehavior', 'InternalQuotient', 'WitnessCollection', 'InternalExtensionality', 'GraphAxioms', 'PairTransfer', 'GraphLifting', 'BoffaAxiom', 'BoffaSyntax', 'GraphBisimulation', 'GraphBisimProperties', 'GraphClasses', 'GraphQuotient', 'DecorationPullback', 'DecorationTransfer', 'BoundedAugmentedBisim', 'BoundedBisimUpTo', 'RelationSupport', 'InternalCoinduction', 'InternalAFA', 'ModelBridge', 'ChoiceAxiom', 'KernelClasses', 'ChoiceTransfer', 'ChoiceModelBridge', 'IdentityLoss', 'ParameterCriterion', 'FreshParameterLabels', 'RelativeRepresentatives', 'RelativeExtensionGraph', 'RelativeParameterExtension', 'LiftComparison', 'SolvabilityBridge', 'TheorySeparation', 'ParameterFamilies', 'ParameterSemantics', 'ChoiceFreeLifting', 'ChoiceFreeParameters', 'CoherentRestrictions', 'BehaviorChoice', 'FiberChoice', 'BafaFiberChoice', 'LocalChoiceLoss', 'FixedSolvability', 'LeastGraphRelation', 'BafaFixedSolvability', 'InternalFoundation', 'ChoiceFactorization', 'FunctionalPresentation', 'FunctionalNormalization', 'ClosedGraphPreservation', 'LeastGraphEquivariance', 'LeastQuotientMaps', 'MembershipSymmetry', 'ModelMaps', 'QuotientStability', 'SupportedChoice', 'BafaModelObstructions', 'LeastClosedRestriction', 'InternalOmega', 'InternalIteration', 'DefinableClosedCover', 'GlobalLeastQuotient', 'PrunedQuotientRows', 'PrunedBaseModel', 'GlobalClosedPreservation', 'PrunedTaggedLoops', 'ExcludedLabelFamilies', 'TaggedGraphSolutions', 'PrunedGraphPresentation', 'PrunedCodeTransfer', 'PrunedExtensionalRealization', 'ClosedMapConservation', 'PrunedFixedCover', 'JointTaggedSolutions', 'JointClassification', 'PrunedJointRealization', 'PrunedFixedDecoration', 'PrunedModelBridge', 'PrunedCarrierComparison', 'PrunedChoiceTransfer', 'PrunedChoiceModelBridge', 'CanonicalGraphEvaluation', 'PrunedEvaluationMap', 'PrunedEvaluationKernel', 'AfaInternalCoinduction', 'PrunedBehaviorEvaluation', 'PrunedRoundtrip', 'TheoryRetraction', 'DefinableRetraction', 'PartialIsoRelabeling', 'BafaPartialHomogeneity', 'CountableIsoChains', 'CountableBafaAutomorphisms', 'InvolutionCopies', 'InvolutionAmalgamGraph', 'LeastKernelDecoration', 'LeastDecorationSymmetry', 'BafaInvolutionExtension', 'CountableBafaInvolutions', 'DecorationActions', 'DecorationActionLaws', 'BafaCoherentRealization', 'FiniteCodedUnions', 'FiniteCopies', 'FiniteCopyGraph', 'FiniteGroupCopies', 'FiniteGroupAmalgam', 'BafaFiniteGroupExtension', 'CountableGroupChains', 'CountableBafaGroupActions', 'FiniteQuineLabels', 'FiniteRegularActions', 'FiniteCosets', 'InducedGroupFunctions', 'InducedGroupAmalgam', 'BafaSubgroupExtension', 'FiniteGroupExhaustions', 'GrowingGroupChains', 'GrowingGroupLimits', 'FreshFiniteRegularActions', 'DisjointGroupActions', 'FaithfulGroupExtensions', 'FaithfulGrowingGroupLimits', 'InternalQuinePairs', 'OmegaQuinePairs', 'InternalPairChoice', 'QuineDomainSwaps', 'InternalPairSwaps', 'HereditarySupport', 'SupportedCoding', 'SupportedPairCandidate', 'SupportedInfinity', 'BoundedSyntax', 'SupportedSeparation', 'SupportedPowerObstruction', 'RelativeInducedFunctions', 'RelativeInducedGraph', 'BafaRelativeGroupExtension', 'ControlledGroupChains', 'ControlledGroupLimits', 'FiniteBitGroups', 'FiniteInvolutionActions', 'CodedBitActions', 'PairBitCore', 'GlobalPairBitActions', 'SupportedInvariance', 'SupportedTraces', 'SupportedFullSeparation', 'SupportedRelativePower', 'SupportedTruthGap', 'UniformHereditarySupport', 'UniformSupportedPowers', 'UniformSupportedChoice', 'SupportedFixedRowsPowers', 'StandardOmegaCut', 'IndexedOmegaSwaps', 'IndexedSelectorPrefixes', 'NonstandardSupportedPowerFailure', 'InternalTailSupport', 'InternalTailChoice', 'InternalRowSwapFamily', 'InternalTailLocalSystem', 'BooleanGroupExhaustion', 'InternalMaskGroup', 'MaskedLabelActions', 'MaskedActionCodes', 'MaskedCoreActions', 'GlobalInternalMaskActions', 'InternalMaskBounds', 'HereditaryMaskSupport', 'MaskSupportedLabels', 'MaskRelativePower', 'MaskCarrierSchemes', 'MaskChoiceCandidate', 'JointFunctionCodes', 'JointMaskDomains', 'JointMaskPowers', 'JointMaskRelativePower', 'JointMaskPowerTowers', 'IndexedFunctionFamilies', 'InternalCopyValues', 'InternalCopyFamilies', 'JointMaskCopyFamilies', 'InternalCopyAmalgam', 'JointMaskAmalgams', 'GeneralCopyActions', 'MaskCopyTransitionSyntax', 'CodedMaskActions', 'JointMaskGraphActions', 'JointDecorationFamilies', 'BafaCodedMaskExtension', 'CodedMaskChains', 'GloballyJointMaskActions', 'PowerBoundedSyntax', 'PowerQuantifierBounds', 'PowerBoundedReduction', 'PowerBoundedSeparation', 'MaskPowerBoundedCandidate', 'MemberGraphAttachments', 'AttachmentActionCodes', 'AttachmentGroupActions', 'BafaEquivariantAttachments', 'JointAttachmentFamilies', 'JointBafaAttachments', 'FixedGraphAttachments', 'GraphEnrichedMaskCandidate', 'MaskEquivariantFunctions', 'MaskGraphAbsoluteness', 'InvariantGraphAttachments', 'MaskPartnerGraphs', 'MaskTwoCycleCandidate', 'JointMaskRestrictions', 'OrbitGraphParameters', 'OrbitDiagramCodes', 'OrbitDiagramComponents', 'JointOrbitDiagrams', 'OrbitDiagramInstances', 'OrbitComponentSolutions', 'OrbitBoundaryCodes', 'BoundaryRenamings', 'BoundaryGraphAttachments', 'AttachedOrbitComponents', 'FixedOrbitRealizations', 'BoundaryActionCodes', 'BoundaryGroupActions', 'JointBoundaryFamilies', 'JointBoundaryRealizations', 'JointOrbitRealizations', 'GlobalOrbitSolutions', 'JointUniverseStates', 'ScheduledRequestSteps', 'ScheduledUniverseChains', 'ScheduledMaskBAFA', 'ScheduledNoChoiceCandidate', 'MaskOrbitBounds', 'MaskSeparationTraces', 'MaskTruthGap', 'ScheduledSchemeCriteria', 'FiniteContextCollection', 'BoundedLocalDefinitions', 'CollectionFullSeparation', 'ScheduledCollectionReduction', 'InternalMaskCovers', 'JointInternalMaskCores', 'MaskCoveredWitnesses', 'ScheduledInternalCores', 'MaskCoveredCoding', 'MaskCoveredDecorations', 'CoveredBafaWitnesses', 'ScheduledCoveredRealizations', 'CoveredMaskCoding', 'CoveredMaskGraphs', 'CoveredMaskSchemes', 'CoveredMaskPowers', 'CoveredMaskBAFA', 'CoveredMaskChoice', 'CoveredMaskCollection', 'CoveredMaskCandidate', 'CoveredMaskActions', 'MaskTailOrbits', 'CoveredTailOrbitFamilies', 'CoveredFixedInputCollection', 'ScheduledFixedInputReduction', 'CodedMaskEmbeddings', 'CodedActionCovers', 'PrescribedCoveredCandidates', 'ActionEmbeddingSemantics', 'RecurrentEnumeration', 'CodedActionRequests', 'UniversalRequestSteps', 'UniversalMaskRealizations', 'UniversalCoveredCandidate', 'UniversalLocalWitnesses', 'RawMaskActionSyntax', 'RawMaskActionRepresentation', 'RawActionExtensions', 'LocalWitnessSourceSyntax', 'UniversalWitnessSource', 'LocalWitnessPackages', 'ActionFamilies', 'ActionFamilyDiagrams', 'ActionFamilyMoves', 'JointActionFamilyDiagrams', 'ActionFamilyBoundaries', 'ActionFamilyComponents', 'ActionFamilyAmalgamation', 'LocalWitnessAmalgamation', 'UniversalBoundedCollection', 'BoundedCollectionCandidate', 'InjectiveBoundaryCopies', 'EquivariantEmbeddingExtensions', 'CodedMaskIsomorphisms', 'GlobalActionImages', 'UniversalActionBackAndForth', 'UniversalActionSemantics', 'LocalActionTruth', 'LocalActionTruthInterfaces', 'LocalActionQuantifiers', 'LocalActionTruthLogic', 'FullActionSourceSyntax', 'UniversalFullSourceTruth', 'FullWitnessPackages', 'FullWitnessFamilies', 'UniversalFullCollection', 'CompleteCoveredModel', 'CoveredBehaviorAbsoluteness', 'TrivialActionRepresentatives', 'CoveredQuotientComparison', 'CompleteChoiceSeparation', 'ExactNoChoiceLifts', 'FormulaEnumeration', 'CountableElementaryHull', 'ElementaryModelTransfer', 'CountableAfaModels', 'UnrestrictedNoChoiceTransfer', 'MemberCoalgebraMaps', 'ModalObservations', 'ModalCountingBoundary', 'ModalPredicateDescent', 'CrossFieldBridge', 'PairChoicePrinciples', 'BafaPairChoice', 'AfaPairChoiceBoundary', 'CoveredPairChoiceFailure', 'PairChoiceScreening']
lean = shutil.which('lean') or str(Path.home() / '.elan/bin/lean')
env = os.environ.copy()
env['ELAN_TOOLCHAIN'] = (HERE.parent / 'lean-toolchain').read_text().strip()
log = []

def run(args, cwd):
    p = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
    log.append('$ ' + ' '.join([Path(args[0]).name, *args[1:]]) + '\n' + p.stdout + p.stderr)
    (OUT / 'lean-verification.txt').write_text('\n'.join(log))
    if p.returncode or 'sorryAx' in p.stdout + p.stderr:
        raise RuntimeError('Lean verification failed; see lean-verification.txt')
    return p.stdout.strip()

try:
    (OUT / 'proof-manifest.json').write_text(json.dumps({'status': 'RUNNING'}) + '\n')
    expected_files = {mod + '.lean' for mod in MODULES}
    actual_files = {p.name for p in HERE.glob('*.lean')}
    if len(MODULES) != len(set(MODULES)) or expected_files != actual_files:
        raise RuntimeError('Module inventory mismatch')
    version = run([lean, '--version'], HERE)
    entries = []
    names = []
    with tempfile.TemporaryDirectory(prefix='full-bridge-') as tmp:
        dest = Path(tmp)
        env['LEAN_PATH'] = str(dest)
        for mod in MODULES:
            src = HERE / (mod + '.lean')
            content = src.read_text()
            if re.search(r'\b(sorry|admit)\b|^\s*axiom\s', content, re.M):
                raise RuntimeError('Unproved declaration in ' + src.name)
            declared = re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+([A-Za-z_][A-Za-z_0-9]*)', content, re.M)
            names.extend(declared)
            entries.append({'file': src.name, 'sha256': hashlib.sha256(src.read_bytes()).hexdigest(), 'theorems': declared})
            shutil.copy2(src, dest / src.name)
            run([lean, '-o', mod + '.olean', mod + '.lean'], dest)
        (dest / 'Audit.lean').write_text('import PairChoiceScreening\n' + '\n'.join('#print axioms FullBridge.' + n for n in names) + '\n')
        audit = run([lean, 'Audit.lean'], dest)
        audited = re.findall(r"^'FullBridge\.([A-Za-z_][A-Za-z_0-9]*)'", audit, re.M)
        if len(names) != len(set(names)) or sorted(audited) != sorted(names):
            raise RuntimeError('Named theorem audit coverage mismatch')
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for group in re.findall(r'depends on axioms: \[([^\]]*)\]', audit, re.S):
            actual = {a.strip() for a in group.split(',') if a.strip()}
            if actual - allowed:
                raise RuntimeError('Unexpected axiom dependency: ' + str(actual - allowed))

    manifest = {'status': 'PASS', 'lean': version, 'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'toolchain_sha256': hashlib.sha256((HERE.parent / 'lean-toolchain').read_bytes()).hexdigest(), 'modules': entries, 'named_theorems': len(names),
                'scope': 'Stage 11: unchanged stage 10 baseline plus exact-two internal choice AC2, behavior-homogeneous pair choice FC2 and self-singleton pair choice QC2, actual finite first-order sentences and evaluation lemmas; BaseCollection+BAFA equivalences AC2 iff FC2 iff QC2 via one internal injective relabeling; AFA vacuity of FC2 and QC2; explicit supported quine-pair choice failure in a conditional full BAFA model, strengthened bridge and raw/behavior-translated sentence boundary. 32 new named theorems in 5 modules. No strict comparison with full AC, syntactic consistency, unqualified independence, external-bisimilarity identification or novelty claim.',
                'scope_history': 'Source files preserved from the completed internal stage 11 package.',
                'verification_only': True}
    (OUT / 'proof-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    print(f'PASS: {len(MODULES)} modules, {len(names)} named theorems; clean build and axiom audit.')
except Exception as exc:
    (OUT / 'proof-manifest.json').write_text(json.dumps({'status': 'FAILED', 'error': str(exc)}, ensure_ascii=False, indent=2) + '\n')
    raise
