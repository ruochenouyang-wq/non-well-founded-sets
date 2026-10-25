import ScheduledRequestSteps
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

noncomputable def scheduledUniverseNext (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w) (p : U)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) : JointUniverseState base w :=
  Classical.choose (scheduled_request_step_exists base hBAFA hw A p enum henum)

noncomputable def scheduledUniverseSequence (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) : Nat → JointUniverseState base w
  | 0 => A
  | n+1 => scheduledUniverseNext base hBAFA hw (scheduledUniverseSequence base hBAFA hw A enum henum n) (enum n) enum henum

structure ScheduledUniverseChain (base : BaseCollection s) (w : U) (enum : Nat → U) where
  stage : Nat → JointUniverseState base w
  step : ∀ n, ScheduledRequestStep base (stage n) (stage (n+1)) (enum n)

theorem scheduled_universe_chain_exists (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : ScheduledUniverseChain base w enum, C.stage 0 = A := by
  let seq := scheduledUniverseSequence base hBAFA hw A enum henum
  exact ⟨⟨seq, fun n => Classical.choose_spec
    (scheduled_request_step_exists base hBAFA hw (seq n) (enum n) enum henum)⟩, rfl⟩

def ScheduledUniverseChain.codedChain (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : ScheduledUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) : CoveringCodedMaskChain base w where
  stage := fun n => (C.stage n).retained
  step := fun n => (C.step n).1
  covers := by
    intro x
    obtain ⟨n, rfl⟩ := henum x
    exact ⟨n+1, (C.step n).2.1⟩

noncomputable def scheduledUniverseMap (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : ScheduledUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) : InternalMask s w → U → U :=
  codedMaskChainMap base (C.codedChain base henum)

theorem scheduled_chain_map_agreement (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : ScheduledUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) (n : Nat) :
    ∀ i x, s x (C.stage n).retained.domain → scheduledUniverseMap base C henum i x = (C.stage n).maps i x := by
  intro i x hx
  obtain ⟨y, hxy, _⟩ := ((C.stage n).retained.iso i).1.2 x hx
  exact (iso_chain_map_value ((C.codedChain base henum).isoChain base i) ⟨n, hxy⟩).trans
    ((C.stage n).agrees i x y hxy).symm

theorem scheduled_chain_support_agreement (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : ScheduledUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) (n : Nat)
    {x : U} (hx : s x (C.stage n).retained.domain) :
    HereditarilyMaskSupported s w (scheduledUniverseMap base C henum) x ↔
      HereditarilyMaskSupported s w (C.stage n).maps x :=
  hereditary_mask_agreement_on_transitive (C.stage n).retained.transitive hx
    (scheduled_chain_map_agreement base C henum n)

theorem scheduled_chain_all_supported_requests (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : ScheduledUniverseChain base w enum) (henum : ∀ x, ∃ n, enum n = x) :
    ∀ p, BafaRequestCode s p → HereditarilyMaskSupported s w (scheduledUniverseMap base C henum) p →
      ∃ t a r f, OrbitGraphParameters s p t a r ∧ DecorationCode s a r f ∧ InjectiveCode s f ∧
        (∀ x, s x t → CodedRelation s f x x) ∧
        HereditarilyMaskSupported s w (scheduledUniverseMap base C henum) f := by
  intro p hp hH
  obtain ⟨n, hn⟩ := henum p
  have hStep := C.step n
  rw [hn] at hStep
  have hStage := (scheduled_chain_support_agreement base C henum (n+1) hStep.2.1).mp hH
  obtain ⟨t, a, r, f, hpar, hfD, hf, hi, hfix, hfH⟩ := hStep.2.2 hp hStage
  exact ⟨t, a, r, f, hpar, hf, hi, hfix,
    (scheduled_chain_support_agreement base C henum (n+1) hfD).mpr hfH⟩

#print axioms scheduled_chain_all_supported_requests
end FullBridge
