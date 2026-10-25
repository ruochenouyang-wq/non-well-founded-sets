import CodedActionRequests
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem action_request_step_exists (base : BaseCollection s) (hBAFA : BAFACode s)
    {w : U} (A : JointUniverseState base w) (p : U)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ B : JointUniverseState base w, CodedMaskExtends base A.retained B.retained ∧
      ActionRequestSealed base A.retained B.retained p := by
  classical
  by_cases hg : ∃ t Q, ActionRequestCode base p t Q ∧ ActionRequestCompatible base A.retained Q t
  · obtain ⟨t, Q, hcode, ht, htA, htQ, hstable, hag⟩ := hg
    obtain ⟨C, f, hAC, _, hOld, hE, hfix⟩ :=
      bafa_coded_mask_amalgamation base hBAFA A.retained Q ht htA htQ hstable hag
    obtain ⟨B, hB⟩ := joint_universe_state_exists base hBAFA C enum henum
    refine ⟨B, ?_, ?_⟩
    · rw [hB]
      exact ⟨hAC, hOld⟩
    · intro t' Q' hcode' _
      obtain ⟨rfl, rfl⟩ := action_request_code_unique base hcode hcode'
      rw [hB]
      exact ⟨f, hE, hfix⟩
  · exact ⟨A, ⟨fun _ h => h, fun _ _ _ h => h⟩,
      fun t Q hcode hcompat => False.elim (hg ⟨t, Q, hcode, hcompat⟩)⟩

/-- Both requirements are retained: old BAFA requests and new whole-action
    realizations. Action admissibility is tested at the incoming stage. -/
def UniversalRequestStep (base : BaseCollection s) {w : U}
    (A B : JointUniverseState base w) (p : U) : Prop :=
  ScheduledRequestStep base A B p ∧ ActionRequestSealed base A.retained B.retained p

theorem universal_request_step_exists (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w) (p : U)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ B : JointUniverseState base w, UniversalRequestStep base A B p := by
  obtain ⟨M, hAM, hseal⟩ := action_request_step_exists base hBAFA A p enum henum
  obtain ⟨B, hMB, hpB, hsolve⟩ := scheduled_request_step_exists base hBAFA hw M p enum henum
  exact ⟨B, ⟨coded_mask_extends_trans base hAM hMB, hpB, hsolve⟩,
    action_request_sealed_mono base hseal hMB⟩

noncomputable def universalUniverseNext (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w) (p : U)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) : JointUniverseState base w :=
  Classical.choose (universal_request_step_exists base hBAFA hw A p enum henum)

noncomputable def universalUniverseSequence (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) : Nat → JointUniverseState base w
  | 0 => A
  | n+1 => universalUniverseNext base hBAFA hw (universalUniverseSequence base hBAFA hw A enum henum n)
      (recurrentEnum enum n) enum henum

structure UniversalUniverseChain (base : BaseCollection s) (w : U) (enum : Nat → U) where
  stage : Nat → JointUniverseState base w
  step : ∀ n, UniversalRequestStep base (stage n) (stage (n+1)) (recurrentEnum enum n)

def UniversalUniverseChain.scheduled (base : BaseCollection s) {w : U} {enum : Nat → U}
    (C : UniversalUniverseChain base w enum) : ScheduledUniverseChain base w (recurrentEnum enum) :=
  ⟨C.stage, fun n => (C.step n).1⟩

theorem universal_universe_chain_exists (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : UniversalUniverseChain base w enum, C.stage 0 = A := by
  let seq := universalUniverseSequence base hBAFA hw A enum henum
  exact ⟨⟨seq, fun n => Classical.choose_spec (universal_request_step_exists base hBAFA hw
    (seq n) (recurrentEnum enum n) enum henum)⟩, rfl⟩

#print axioms universal_request_step_exists
end FullBridge
