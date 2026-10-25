import UniversalBoundedCollection
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Actual bounded finite formulas, rather than arbitrary external predicates. -/
def BoundedCollection (s : U → U → Prop) : Prop :=
  ∀ n (p : BoundedFormula (n+2)) (v : Fin n → U) (a : U),
    (∀ x, s x a → ∃ y, BoundedEval s p (cons y (cons x v))) →
    ∃ b, ∀ x, s x a → ∃ y, s y b ∧ BoundedEval s p (cons y (cons x v))

/-- The same no-choice candidate now also satisfies bounded Collection.
    Full Separation and full Collection are still not asserted. -/
theorem countable_bafa_bounded_collection_candidate (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ J : InternalMask s w → U → U,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) ∧
      CoveredCandidateLaws J ∧ BoundedCollection (coveredMaskMember J) ∧ UniversalMaskRealizations base J ∧
      (BaseCollection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J) := by
  obtain ⟨z, w, hw, P, J, hJ, hOne, hMul, hcore, hCover, hlaws, hUniversal, hcrit⟩ :=
    countable_bafa_universal_covered_candidate base hB enum henum
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  exact ⟨z, w, hw, P, J, hJ, hOne, hMul, hcore, hCover, hlaws,
    universal_Hc_bounded_collection base hB hw (fun i => (hJ i).1) hs hOne hMul hCover hUniversal,
    hUniversal, hcrit⟩

#print axioms countable_bafa_bounded_collection_candidate
end FullBridge
