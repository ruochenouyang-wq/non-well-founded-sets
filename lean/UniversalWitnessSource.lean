import LocalWitnessSourceSyntax
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Actual finite source syntax for one existential quantifier with bounded body.
    This is not a translation of arbitrary formulas or a Collection theorem. -/
theorem universal_Hc_bounded_existential_source_formula (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hUniversal : UniversalMaskRealizations base J)
    (A : CodedMaskAction base w)
    (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    {n} (p : BoundedFormula (n+1)) (v : Fin n → CoveredMaskCarrier s w J)
    (hv : ∀ j, s (v j).val A.domain) :
    (∃ y, BoundedEval (coveredMaskMember J) p (cons y v)) ↔
      Eval s (boundedLocalWitnessFormula p)
        (cons w (cons A.domain (cons A.masks (cons A.family (fun j => (v j).val))))) := by
  exact (universal_Hc_bounded_existential_certificate base hj hs hOne hMul hCover hUniversal A hAJ p v hv).trans
    (bounded_local_source_iff_record base A p (fun j => (v j).val)).symm

#print axioms universal_Hc_bounded_existential_source_formula
end FullBridge
