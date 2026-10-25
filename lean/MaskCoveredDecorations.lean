import MaskCoveredCoding
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem transitive_contains_ordered_pair_components {C p x y : U}
    (hC : TransitiveCode s C) (hpC : s p C) (hp : IsOrderedPair s p x y) : s x C ∧ s y C := by
  obtain ⟨a, b, ha, hb, hab⟩ := hp
  exact ⟨hC a (hC p hpC a ((hab a).mpr (Or.inl rfl))) x ((ha x).mpr (Or.inl rfl)),
    hC b (hC p hpC b ((hab b).mpr (Or.inr rfl))) y ((hb y).mpr (Or.inr rfl))⟩

/-- For an already hereditary function, internal transitive covering is
    equivalent to such covering of its domain and its actual range. -/
theorem mask_covered_function_iff (hp : Pairing s) (hu : Union s) {w a f T : U}
    {J : InternalMask s w → U → U} (ha : HereditarilyMaskSupported s w J a)
    (hF : HereditarilyMaskSupported s w J f) (hT : HereditarilyMaskSupported s w J T)
    (hf : FunctionCode s a f) (hr : RangeCode s a f T) :
    InternalMaskCovered s w J f ↔ InternalMaskCovered s w J a ∧ InternalMaskCovered s w J T := by
  constructor
  · rintro ⟨C, hCt, hfC, hroot⟩
    have hend : ∀ x y, CodedRelation s f x y → s x C ∧ s y C := by
      rintro x y ⟨p, hpf, hp⟩
      exact transitive_contains_ordered_pair_components hCt (hCt f hfC p hpf) hp
    constructor
    · apply mask_covered_of_supported_subset hp hu hCt hroot (hereditary_mask_root ha)
      intro x hx
      obtain ⟨y, hxy, _⟩ := hf.2 x hx
      exact (hend x y hxy).1
    · apply mask_covered_of_supported_subset hp hu hCt hroot (hereditary_mask_root hT)
      intro y hy
      obtain ⟨x, _, hxy⟩ := (hr y).mp hy
      exact (hend x y hxy).2
  · rintro ⟨hac, hTc⟩
    obtain ⟨C, hCt, haC, hTC, hroot⟩ := mask_covered_common_transitive_cover hp hu hac hTc
    apply mask_covered_normalized_relation hp hu hCt hroot hF
    intro p hpf
    obtain ⟨x, y, hxa, hp⟩ := hf.1 p hpf
    exact ⟨x, y, hCt a haC x hxa, hCt T hTC y ((hr y).mpr ⟨x, hxa, p, hpf, hp⟩), hp⟩

/-- Every value of a hereditary decoration is internally covered, even
    when its node set is not yet known to have an internal cover. -/
theorem mask_decoration_covered_range (base : BaseCollection s) {w a r f : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x)
    (hf : DecorationCode s a r f) (hF : HereditarilyMaskSupported s w J f) :
    ∃ T, TransitiveCode s T ∧ HereditarilyMaskSupported s w J T ∧
      InternalMaskCovered s w J T ∧ RangeCode s a f T ∧
      ∀ x X, CodedRelation s f x X → InternalMaskCovered s w J X := by
  obtain ⟨T, hT, hr⟩ := decoration_transitive_range base hf
  have hTH := hereditary_mask_function_range base hj hs hf.1 hF hr
  have hTc := hereditary_transitive_internal_mask_covered base.pairing base.union hT hTH
  exact ⟨T, hT, hTH, hTc, hr, fun x X hxX =>
    internal_mask_covered_member hTc ((hr X).mpr ⟨x, coded_function_domain hf.1 hxX, hxX⟩)⟩

theorem mask_decoration_covered_iff_domain (base : BaseCollection s) {w a r f : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x) (ha : HereditarilyMaskSupported s w J a)
    (hf : DecorationCode s a r f) (hF : HereditarilyMaskSupported s w J f) :
    InternalMaskCovered s w J f ↔ InternalMaskCovered s w J a := by
  obtain ⟨T, _, hTH, hTc, hr, _⟩ := mask_decoration_covered_range base hj hs hf hF
  exact (mask_covered_function_iff base.pairing base.union ha hF hTH hf.1 hr).trans
    ⟨fun h => h.1, fun h => ⟨h, hTc⟩⟩

#print axioms mask_decoration_covered_range
#print axioms mask_decoration_covered_iff_domain
end FullBridge
