import FaithfulGroupExtensions
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

noncomputable def faithfulGrowingGroupNext (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (n : Nat) (P : TransitiveGroupAction s (E.group n)) (x : U) :
    TransitiveGroupAction s (E.group (n+1)) :=
  Classical.choose (bafa_subgroup_faithful_cover_extension base hB (exhaustionEmbedding E (Nat.le_succ n)) P x)

noncomputable def faithfulGrowingGroupSequence (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (P : TransitiveGroupAction s (E.group 0)) (enum : Nat → U) :
    ∀ n, TransitiveGroupAction s (E.group n)
  | 0 => P
  | n+1 => faithfulGrowingGroupNext base hB E n (faithfulGrowingGroupSequence base hB E P enum n) (enum n)

theorem faithful_growing_group_covering_chain (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (P : TransitiveGroupAction s (E.group 0)) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : GrowingGroupChain s E, C.stage 0 = P ∧ ∀ n, GroupActionFaithful (C.stage (n+1)) := by
  let seq := faithfulGrowingGroupSequence base hB E P enum
  have hn := fun n => Classical.choose_spec
    (bafa_subgroup_faithful_cover_extension base hB (exhaustionEmbedding E (Nat.le_succ n)) (seq n) (enum n))
  refine ⟨⟨seq, fun n => (hn n).1, fun n => (hn n).2.2.1, ?_⟩, rfl, fun n => (hn n).2.2.2⟩
  intro x
  obtain ⟨n, rfl⟩ := henum x
  exact ⟨n+1, (hn n).2.1⟩

theorem growing_group_limit_faithful {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E)
    (hFaith : ∀ n, GroupActionFaithful (C.stage (n+1))) :
    ∀ g h, (∀ x, growingActionMap C g x = growingActionMap C h x) → g = h := by
  intro g h hgh
  obtain ⟨n, i, hi⟩ := E.covers g
  obtain ⟨m, j, hj⟩ := E.covers h
  let k := max n m + 1
  have hnk : n ≤ k := Nat.le_trans (Nat.le_max_left n m) (Nat.le_succ (max n m))
  have hmk : m ≤ k := Nat.le_trans (Nat.le_max_right n m) (Nat.le_succ (max n m))
  let i' := exhaustionLift E hnk i
  let j' := exhaustionLift E hmk j
  have hi' : E.embed k i' = g := (exhaustion_lift_embed E hnk i).trans hi
  have hj' : E.embed k j' = h := (exhaustion_lift_embed E hmk j).trans hj
  have hij : i' = j' := by
    apply hFaith (max n m) i' j'
    intro x y
    constructor
    · intro hxy
      obtain ⟨z, hxz, _⟩ := ((C.stage k).iso j').1.2 x
        (coded_function_domain ((C.stage k).iso i').1 hxy)
      have hy := growing_action_map_value C ⟨k, i', hi', hxy⟩
      have hz := growing_action_map_value C ⟨k, j', hj', hxz⟩
      have he : y = z := hy.symm.trans ((hgh x).trans hz)
      exact he.symm ▸ hxz
    · intro hxy
      obtain ⟨z, hxz, _⟩ := ((C.stage k).iso i').1.2 x
        (coded_function_domain ((C.stage k).iso j').1 hxy)
      have hy := growing_action_map_value C ⟨k, j', hj', hxy⟩
      have hz := growing_action_map_value C ⟨k, i', hi', hxz⟩
      have he : y = z := hy.symm.trans ((hgh x).symm.trans hz)
      exact he.symm ▸ hxz
  exact hi'.symm.trans ((congrArg (E.embed k) hij).trans hj')

/-- A faithful action of the entire externally exhausted group. It preserves
    any prescribed initial finite action, even when that initial action is not
    faithful, while acting trivially on the full internal behavior quotient. -/
theorem countable_bafa_faithful_exhausted_group_extension (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (P : TransitiveGroupAction s (E.group 0)) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : K → U → U,
      (∀ g, ElementaryMap s s (J g) ∧ (∀ y, ∃ x, J g x = y) ∧ LocallyInternalTransitiveMap s (J g)) ∧
      (∀ x, J D.one x = x) ∧ (∀ g h x, J (D.mul g h) x = J g (J h x)) ∧
      (∀ i x y, CodedRelation s (P.code i) x y → J (E.embed 0 i) x = y) ∧
      (∀ g h, (∀ x, J g x = J h x) → g = h) ∧
      (∀ g x, internalCode base (J g x) = internalCode base x) ∧
      (∀ g a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ J g x = y) := by
  obtain ⟨C, hC, hFaith⟩ := faithful_growing_group_covering_chain base hB E P enum henum
  refine ⟨growingActionMap C, ?_, growing_action_map_identity C, growing_action_map_multiplication C,
    ?_, growing_group_limit_faithful C hFaith, ?_, ?_⟩
  · intro g
    exact ⟨bijective_membership_elementary _ (growing_action_map_injective C g)
      (growing_action_map_surjective C g) (growing_action_map_members C g),
      growing_action_map_surjective C g, growing_action_map_local C g⟩
  · intro i x y hxy
    apply growing_action_map_value C
    refine ⟨0, i, rfl, ?_⟩
    rw [hC]
    exact hxy
  · intro g x
    exact (internal_code_eq base _ x).mpr (locally_internal_map_behavior base _ (growing_action_map_local C g) x)
  · intro g
    exact locally_internal_map_restriction base (growing_action_map_local C g)

#print axioms countable_bafa_faithful_exhausted_group_extension
end FullBridge
