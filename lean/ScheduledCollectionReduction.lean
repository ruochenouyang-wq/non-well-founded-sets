import CollectionFullSeparation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The same actual scheduled no-choice BAFA candidate has just one remaining
    full-base obligation: hereditary witness source bounds. Collection alone
    supplies its missing full Separation; neither is asserted unconditionally. -/
theorem countable_bafa_scheduled_collection_reduction (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ d, ∃ t, TransitiveCode s t ∧ Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      Extensional (maskSupportedMember J) ∧ Empty (maskSupportedMember J) ∧
      Pairing (maskSupportedMember J) ∧ Union (maskSupportedMember J) ∧ PowerSet (maskSupportedMember J) ∧
      Infinity (maskSupportedMember J) ∧ BoundedSeparation (maskSupportedMember J) ∧
      PowerBoundedSeparation (maskSupportedMember J) ∧ BAFACode (maskSupportedMember J) ∧
      ¬ ChoiceCode (maskSupportedMember J) ∧
      (BaseCollection (maskSupportedMember J) ↔ MaskHereditaryWitnessBounds s w J) ∧
      (Collection (maskSupportedMember J) ↔ BaseCollection (maskSupportedMember J)) ∧
      (Collection (maskSupportedMember J) → Replacement (maskSupportedMember J)) ∧
      (MaskHereditaryWitnessBounds s w J → MaskSeparationTraces s w J) ∧
      ¬ ElementaryMap (maskSupportedMember J) s (fun X => X.val) := by
  obtain ⟨z, w, hw, P, J, hJ, hOne, hMul, _, _, _, hCover, _, he, hem, hp, hu, hpow, hi,
    hsep, hpsep, hbafa, hnc, htrace, hbound, _, hne⟩ :=
    countable_bafa_scheduled_scheme_criteria base hB enum henum
  have makeBase : Collection (maskSupportedMember J) → BaseCollection (maskSupportedMember J) := by
    intro hcol
    exact ⟨he, hem, hp, hu, hpow, hi, collection_bounded_separation_full_separation hcol hp hu hsep, hcol⟩
  exact ⟨z, w, hw, J, hJ, hOne, hMul, hCover, he, hem, hp, hu, hpow, hi, hsep, hpsep, hbafa, hnc,
    ⟨fun B => hbound.mp B.collection, fun h => makeBase (hbound.mpr h)⟩,
    ⟨makeBase, fun B => B.collection⟩,
    fun h => collection_bounded_separation_replacement h hp hu hsep,
    fun h => htrace.mp (makeBase (hbound.mpr h)).separation, hne⟩

#print axioms countable_bafa_scheduled_collection_reduction
end FullBridge
