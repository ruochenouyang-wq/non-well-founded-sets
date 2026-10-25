import MaskOrbitBounds
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def restrictedMaskMap {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) (i : InternalMask s w)
    (X : MaskSupportedCarrier s w J) : MaskSupportedCarrier s w J :=
  ⟨J i X.val, (hereditary_mask_invariant hj hc hs i X.val).mpr X.property⟩

theorem restricted_mask_involutive {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) (i : InternalMask s w) (X : MaskSupportedCarrier s w J) :
    restrictedMaskMap hj hc hs i (restrictedMaskMap hj hc hs i X) = X := Subtype.ext (hs i X.val)

theorem restricted_mask_elementary {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hc : ∀ i j x, J i (J j x) = J j (J i x))
    (hs : ∀ i x, J i (J i x) = x) (i : InternalMask s w) :
    ElementaryMap (maskSupportedMember J) (maskSupportedMember J) (restrictedMaskMap hj hc hs i) := by
  apply bijective_membership_elementary
  · intro X Y h
    have hh := congrArg (restrictedMaskMap hj hc hs i) h
    simpa only [restricted_mask_involutive] using hh
  · intro X
    exact ⟨restrictedMaskMap hj hc hs i X, restricted_mask_involutive hj hc hs i X⟩
  · intro X Y
    exact (hj i) (Formula.member (n := 2) 0 1) (cons X.val (cons Y.val Fin.elim0))

def MaskTrace {w : U} (J : InternalMask s w → U → U)
    (P : MaskSupportedCarrier s w J → Prop) (b : U) : Prop :=
  ∀ x, s x b ↔ ∃ X : MaskSupportedCarrier s w J, X.val = x ∧ P X

theorem mask_trace_member {w : U} {J : InternalMask s w → U → U}
    {P : MaskSupportedCarrier s w J → Prop} {b : U} (hb : MaskTrace J P b)
    (X : MaskSupportedCarrier s w J) : s X.val b ↔ P X := by
  constructor
  · intro h
    obtain ⟨Y, hY, hp⟩ := (hb X.val).mp h
    exact (Subtype.ext hY : Y = X) ▸ hp
  · exact fun h => (hb X.val).mpr ⟨X, rfl, h⟩

theorem mask_trace_hereditary (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    {P : MaskSupportedCarrier s w J → Prop} {b : U} (hb : MaskTrace J P b)
    (hP : ∃ N, s N w ∧ ∀ i, (∀ k, s k i.val → ¬s k N) →
      ∀ X, P X → P (restrictedMaskMap hj hc hs i X)) : HereditarilyMaskSupported s w J b := by
  obtain ⟨N, hN, hP⟩ := hP
  apply hereditary_mask_intro
  · refine ⟨N, hN, fun i hi => elementary_involution_closed_set base (hj i) (hs i) ?_⟩
    intro x hx
    obtain ⟨X, rfl, hp⟩ := (hb x).mp hx
    exact (hb _).mpr ⟨restrictedMaskMap hj hc hs i X, rfl, hP i hi X hp⟩
  · intro x hx
    obtain ⟨X, hX, _⟩ := (hb x).mp hx
    exact hX ▸ X.property

/-- Actual subtype truth, including all unbounded quantifiers. -/
def MaskSeparationTraces (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) : Prop :=
  ∀ n (p : Formula (n+1)) (v : Fin n → MaskSupportedCarrier s w J) (a : MaskSupportedCarrier s w J),
    ∃ b, MaskTrace J (fun X => maskSupportedMember J X a ∧ Eval (maskSupportedMember J) p (cons X v)) b

theorem mask_formula_trace_supported (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    {n} (p : Formula (n+1)) (v : Fin n → MaskSupportedCarrier s w J) (a : MaskSupportedCarrier s w J)
    {b : U} (hb : MaskTrace J (fun X => maskSupportedMember J X a ∧ Eval (maskSupportedMember J) p (cons X v)) b) :
    HereditarilyMaskSupported s w J b := by
  obtain ⟨N, hN, hfix⟩ := mask_fixed_finite_parameters base hw
    (fun j => (cons a v j).val) (fun j => hereditary_mask_root (cons a v j).property)
  apply mask_trace_hereditary base hj hc hs hb
  refine ⟨N, hN, fun i hi X hX => ?_⟩
  have ha : restrictedMaskMap hj hc hs i a = a := Subtype.ext (hfix i hi 0)
  have hv : ∀ j, restrictedMaskMap hj hc hs i (v j) = v j := fun j => Subtype.ext (hfix i hi j.succ)
  have hmem := ((restricted_mask_elementary hj hc hs i)
    (Formula.member (n := 2) 0 1) (cons X (cons a Fin.elim0))).mp hX.1
  change maskSupportedMember J (restrictedMaskMap hj hc hs i X) (restrictedMaskMap hj hc hs i a) at hmem
  rw [ha] at hmem
  have he : (fun j => restrictedMaskMap hj hc hs i (cons X v j)) = cons (restrictedMaskMap hj hc hs i X) v := by
    funext j
    exact Fin.cases rfl (fun j => hv j) j
  have hp := ((restricted_mask_elementary hj hc hs i) p (cons X v)).mp hX.2
  rw [he] at hp
  exact ⟨hmem, hp⟩

theorem mask_separation_iff_traces (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x) :
    Separation (maskSupportedMember J) ↔ MaskSeparationTraces s w J := by
  constructor
  · intro h n p v a
    obtain ⟨b, hb⟩ := h n p v a
    refine ⟨b.val, fun x => ?_⟩
    constructor
    · intro hx
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member b.property hx⟩
      exact ⟨X, rfl, (hb X).mp hx⟩
    · rintro ⟨X, rfl, hX⟩
      exact (hb X).mpr hX
  · intro h n p v a
    obtain ⟨b, hb⟩ := h n p v a
    exact ⟨⟨b, mask_formula_trace_supported base hw hj hc hs p v a hb⟩, fun X => mask_trace_member hb X⟩

#print axioms mask_separation_iff_traces
end FullBridge
