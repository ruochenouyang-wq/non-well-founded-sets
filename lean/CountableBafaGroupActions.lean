import CountableGroupChains
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- Coherent global extension for one specified finite group and one supplied
    external enumeration of the model; all group laws hold simultaneously. -/
theorem countable_bafa_group_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (P : TransitiveGroupAction s G)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : I → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧
        LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J G.one x = x) ∧ (∀ i j x, J (G.mul i j) x = J i (J j x)) ∧
      (∀ i x y, CodedRelation s (P.code i) x y → J i x = y) ∧
      (∀ i x, internalCode base (J i x) = internalCode base x) ∧
      (∀ i a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ J i x = y) := by
  obtain ⟨C, hC⟩ := enumerated_covering_group_chain base hB G P enum henum
  refine ⟨groupChainMap C, ?_, group_chain_map_identity C, group_chain_map_multiplication C, ?_, ?_, ?_⟩
  · intro i
    exact ⟨bijective_membership_elementary _ (iso_chain_map_injective (C.isoChain i))
      (iso_chain_map_surjective (C.isoChain i)) (iso_chain_map_members (C.isoChain i)),
      iso_chain_map_surjective (C.isoChain i), iso_chain_map_local (C.isoChain i)⟩
  · intro i x y hxy
    apply iso_chain_map_value (C.isoChain i)
    refine ⟨0, ?_⟩
    change CodedRelation s ((C.stage 0).code i) x y
    rw [hC]
    exact hxy
  · intro i x
    exact (internal_code_eq base _ x).mpr
      (locally_internal_map_behavior base _ (iso_chain_map_local (C.isoChain i)) x)
  · intro i
    exact locally_internal_map_restriction base (iso_chain_map_local (C.isoChain i))

theorem extended_group_action_faithful {I : Type v} {G : FiniteGroupData I}
    (P : TransitiveGroupAction s G) (J : I → U → U)
    (hExt : ∀ i x y, CodedRelation s (P.code i) x y → J i x = y)
    (hFaithful : ∀ i j, (∀ x y z, CodedRelation s (P.code i) x y →
      CodedRelation s (P.code j) x z → y = z) → i = j) :
    ∀ i j, (∀ x, J i x = J j x) → i = j := by
  intro i j hij
  apply hFaithful i j
  intro x y z hxy hxz
  exact (hExt i x y hxy).symm.trans ((hij x).trans (hExt j x z hxz))

#print axioms countable_bafa_group_extension
end FullBridge
