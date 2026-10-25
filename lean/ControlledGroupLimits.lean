import ControlledGroupChains
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

/-- A faithful global action preserving every supplied finite action on the
    same internal core, as well as a separately prescribed initial extension. -/
theorem countable_bafa_controlled_group_extension (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} {E : FiniteGroupExhaustion.{v,w} D}
    (A : FixedCoreActions s E) (P : TransitiveGroupAction s (E.group 0))
    (hAP : GroupActionExtends (A.stage 0) P) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : K → U → U,
      (∀ g, ElementaryMap s s (J g) ∧ (∀ y, ∃ x, J g x = y) ∧ LocallyInternalTransitiveMap s (J g)) ∧
      (∀ x, J D.one x = x) ∧ (∀ g h x, J (D.mul g h) x = J g (J h x)) ∧
      (∀ i x y, CodedRelation s (P.code i) x y → J (E.embed 0 i) x = y) ∧
      (∀ n i x y, CodedRelation s ((A.stage n).code i) x y → J (E.embed n i) x = y) ∧
      (∀ g h, (∀ x, J g x = J h x) → g = h) ∧
      (∀ g x, internalCode base (J g x) = internalCode base x) ∧
      (∀ g a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ J g x = y) := by
  obtain ⟨C, hC, hCore, hFaith⟩ := controlled_growing_group_chain base hB A P hAP enum henum
  refine ⟨growingActionMap C, ?_, growing_action_map_identity C, growing_action_map_multiplication C,
    ?_, ?_, growing_group_limit_faithful C hFaith, ?_, ?_⟩
  · intro g
    exact ⟨bijective_membership_elementary _ (growing_action_map_injective C g)
      (growing_action_map_surjective C g) (growing_action_map_members C g),
      growing_action_map_surjective C g, growing_action_map_local C g⟩
  · intro i x y hxy
    apply growing_action_map_value C
    refine ⟨0, i, rfl, ?_⟩
    rw [hC]
    exact hxy
  · intro n i x y hxy
    exact growing_action_map_value C ⟨n, i, rfl, (hCore n).2 i x y hxy⟩
  · intro g x
    exact (internal_code_eq base _ x).mpr (locally_internal_map_behavior base _ (growing_action_map_local C g) x)
  · intro g
    exact locally_internal_map_restriction base (growing_action_map_local C g)

theorem group_action_preserves_commutation {K : Type v} (D : ExternalGroupData K) (J : K → U → U)
    (hMul : ∀ g h x, J (D.mul g h) x = J g (J h x)) {g h : K}
    (hcomm : D.mul g h = D.mul h g) (x : U) : J g (J h x) = J h (J g x) := by
  rw [← hMul, hcomm, hMul]

#print axioms countable_bafa_controlled_group_extension
end FullBridge
