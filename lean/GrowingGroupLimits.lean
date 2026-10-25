import GrowingGroupChains
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

theorem growing_action_common_stage {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) {g : K} {x y z t : U}
    (hxy : GrowingActionRelation C g x y) (hzt : GrowingActionRelation C g z t) :
    ∃ n i, E.embed n i = g ∧ CodedRelation s ((C.stage n).code i) x y ∧
      CodedRelation s ((C.stage n).code i) z t := by
  obtain ⟨n, i, hi, hxy⟩ := hxy
  obtain ⟨m, j, hj, hzt⟩ := hzt
  have hi' := exhaustion_lift_embed E (Nat.le_max_left n m) i
  have hj' := exhaustion_lift_embed E (Nat.le_max_right n m) j
  have hij := E.injective (max n m) _ _ (hi'.trans (hi.trans (hj.symm.trans hj'.symm)))
  exact ⟨max n m, exhaustionLift E (Nat.le_max_left n m) i, hi'.trans hi,
    growing_group_action_mono C (Nat.le_max_left n m) i hxy,
    hij.symm ▸ growing_group_action_mono C (Nat.le_max_right n m) j hzt⟩

theorem growing_action_map_injective {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) :
    ∀ x y, growingActionMap C g x = growingActionMap C g y → x = y := by
  intro x y hxy
  obtain ⟨n, i, _, hx, hy⟩ := growing_action_common_stage C
    (growing_action_map_relation C g x) (growing_action_map_relation C g y)
  exact ((C.stage n).iso i).2.1 x y _ hx (hxy.symm ▸ hy)

theorem growing_action_map_surjective {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) :
    ∀ y, ∃ x, growingActionMap C g x = y := by
  intro y
  obtain ⟨n, i, hi⟩ := E.covers g
  obtain ⟨m, hy⟩ := C.covers y
  let i' := exhaustionLift E (Nat.le_max_left n m) i
  have hy' := growing_group_domain_mono C (Nat.le_max_right n m) y hy
  obtain ⟨x, _, hxy⟩ := (((C.stage (max n m)).iso i').2.2.1 y).mp hy'
  exact ⟨x, growing_action_map_value C ⟨max n m, i', (exhaustion_lift_embed E _ i).trans hi, hxy⟩⟩

theorem growing_action_map_members {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) (x y : U) :
    s x y ↔ s (growingActionMap C g x) (growingActionMap C g y) := by
  obtain ⟨n, i, _, hx, hy⟩ := growing_action_common_stage C
    (growing_action_map_relation C g x) (growing_action_map_relation C g y)
  exact ((C.stage n).iso i).2.2.2 y x _ _ hy hx

theorem growing_action_map_local {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) :
    LocallyInternalTransitiveMap s (growingActionMap C g) := by
  intro x
  obtain ⟨n, i, hi⟩ := E.covers g
  obtain ⟨m, hx⟩ := C.covers x
  let k := max n m
  let i' := exhaustionLift E (Nat.le_max_left n m) i
  have hi'g : E.embed k i' = g := (exhaustion_lift_embed E _ i).trans hi
  refine ⟨(C.stage k).domain, (C.stage k).domain, (C.stage k).code i',
    (C.stage k).transitive, (C.stage k).transitive,
    growing_group_domain_mono C (Nat.le_max_right n m) x hx, (C.stage k).iso i', ?_⟩
  intro y hy
  obtain ⟨z, hyz, _⟩ := ((C.stage k).iso i').1.2 y hy
  exact (growing_action_map_value C ⟨k, i', hi'g, hyz⟩).symm ▸ hyz

theorem growing_action_map_identity {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (x : U) :
    growingActionMap C D.one x = x := by
  obtain ⟨n, i, hi, hx⟩ := growing_action_map_relation C D.one x
  have hie := E.injective n i (E.group n).one (hi.trans (E.map_one n).symm)
  rw [hie] at hx
  exact ((C.stage n).identity x _ hx).symm

theorem growing_action_map_multiplication {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g h : K) (x : U) :
    growingActionMap C (D.mul g h) x = growingActionMap C g (growingActionMap C h x) := by
  obtain ⟨n, i, hi, hxi⟩ := growing_action_map_relation C h x
  obtain ⟨m, j, hj, hyj⟩ := growing_action_map_relation C g (growingActionMap C h x)
  let i' := exhaustionLift E (Nat.le_max_left n m) i
  let j' := exhaustionLift E (Nat.le_max_right n m) j
  have hi' : E.embed (max n m) i' = h := (exhaustion_lift_embed E _ i).trans hi
  have hj' : E.embed (max n m) j' = g := (exhaustion_lift_embed E _ j).trans hj
  have hprod : E.embed (max n m) ((E.group (max n m)).mul j' i') = D.mul g h := by
    rw [E.map_mul, hi', hj']
  exact growing_action_map_value C ⟨max n m, (E.group (max n m)).mul j' i', hprod,
    ((C.stage (max n m)).multiplication j' i' x _).mpr
      ⟨_, growing_group_action_mono C (Nat.le_max_left n m) i hxi,
        growing_group_action_mono C (Nat.le_max_right n m) j hyj⟩⟩

/-- An actual compatible action of the exhausted group on the whole externally
    countable model, preserving a prescribed action of the first finite stage. -/
theorem countable_bafa_exhausted_group_extension (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (P : TransitiveGroupAction s (E.group 0)) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : K → U → U,
      (∀ g, ElementaryMap s s (J g) ∧ (∀ y, ∃ x, J g x = y) ∧ LocallyInternalTransitiveMap s (J g)) ∧
      (∀ x, J D.one x = x) ∧ (∀ g h x, J (D.mul g h) x = J g (J h x)) ∧
      (∀ i x y, CodedRelation s (P.code i) x y → J (E.embed 0 i) x = y) ∧
      (∀ g x, internalCode base (J g x) = internalCode base x) ∧
      (∀ g a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ J g x = y) := by
  obtain ⟨C, hC⟩ := growing_group_covering_chain base hB E P enum henum
  refine ⟨growingActionMap C, ?_, growing_action_map_identity C, growing_action_map_multiplication C, ?_, ?_, ?_⟩
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

#print axioms countable_bafa_exhausted_group_extension
end FullBridge
