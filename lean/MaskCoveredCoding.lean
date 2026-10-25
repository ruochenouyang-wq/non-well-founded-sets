import ScheduledInternalCores
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem mask_covered_of_supported_subset (hp : Pairing s) (hu : Union s)
    {w C x : U} {J : InternalMask s w → U → U} (hC : TransitiveCode s C)
    (hroot : ∀ y, s y C → MaskTailSupported s w J y)
    (hx : MaskTailSupported s w J x) (hxC : Subset s x C) : InternalMaskCovered s w J x := by
  obtain ⟨p, hpair⟩ := hp x x
  obtain ⟨d, hd⟩ := binary_union_exists hp hu C p
  have hCd : Subset s C d := fun y hy => (hd y).mpr (Or.inl hy)
  refine ⟨d, ?_, (hd x).mpr (Or.inr ((hpair x).mpr (Or.inl rfl))), ?_⟩
  · intro y hy z hz
    rcases (hd y).mp hy with hyC | hyp
    · exact hCd z (hC y hyC z hz)
    · have hyx : y = x := ((hpair y).mp hyp).elim id id
      exact hCd z (hxC z (hyx ▸ hz))
  · intro y hy
    rcases (hd y).mp hy with hyC | hyp
    · exact hroot y hyC
    · have hyx : y = x := ((hpair y).mp hyp).elim id id
      exact hyx.symm ▸ hx

theorem mask_covered_common_transitive_cover (hp : Pairing s) (hu : Union s)
    {w x y : U} {J : InternalMask s w → U → U}
    (hx : InternalMaskCovered s w J x) (hy : InternalMaskCovered s w J y) :
    ∃ C, TransitiveCode s C ∧ s x C ∧ s y C ∧ ∀ z, s z C → MaskTailSupported s w J z := by
  obtain ⟨a, ha, hxa, hroota⟩ := hx
  obtain ⟨b, hb, hyb, hrootb⟩ := hy
  obtain ⟨C, hC⟩ := binary_union_exists hp hu a b
  refine ⟨C, ?_, (hC x).mpr (Or.inl hxa), (hC y).mpr (Or.inr hyb), ?_⟩
  · intro z hz t ht
    exact ((hC z).mp hz).elim
      (fun hza => (hC t).mpr (Or.inl (ha z hza t ht)))
      (fun hzb => (hC t).mpr (Or.inr (hb z hzb t ht)))
  · intro z hz
    exact ((hC z).mp hz).elim (hroota z) (hrootb z)

theorem mask_covered_pair (base : BaseCollection s) {z w x y p : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hx : InternalMaskCovered s w J x)
    (hy : InternalMaskCovered s w J y) (hp : IsPair s p x y) : InternalMaskCovered s w J p := by
  obtain ⟨C, hC, hxC, hyC, hroot⟩ := mask_covered_common_transitive_cover base.pairing base.union hx hy
  have hH := hereditary_mask_pair base hw hj (internal_mask_covered_hereditary hx)
    (internal_mask_covered_hereditary hy) hp
  exact mask_covered_of_supported_subset base.pairing base.union hC hroot (hereditary_mask_root hH)
    (fun q hq => ((hp q).mp hq).elim (fun he => he ▸ hxC) (fun he => he ▸ hyC))

theorem mask_covered_union (base : BaseCollection s) {w a d : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (ho : ∀ i y, ∃ x, J i x = y) (ha : InternalMaskCovered s w J a)
    (hd : ∀ x, s x d ↔ ∃ y, s y a ∧ s x y) : InternalMaskCovered s w J d := by
  have hH := hereditary_mask_union base hj ho (internal_mask_covered_hereditary ha) hd
  obtain ⟨C, hC, haC, hroot⟩ := ha
  apply mask_covered_of_supported_subset base.pairing base.union hC hroot (hereditary_mask_root hH)
  intro x hx
  obtain ⟨y, hya, hxy⟩ := (hd x).mp hx
  exact hC y (hC a haC y hya) x hxy

/-- Kuratowski pair codes add only two membership layers above their
    endpoints. The transitive cover is constructed from actual source unions. -/
theorem mask_covered_normalized_relation (hp : Pairing s) (hu : Union s)
    {w C f : U} {J : InternalMask s w → U → U} (hC : TransitiveCode s C)
    (hroot : ∀ y, s y C → MaskTailSupported s w J y)
    (hf : HereditarilyMaskSupported s w J f)
    (hnorm : ∀ p, s p f → ∃ x y, s x C ∧ s y C ∧ IsOrderedPair s p x y) :
    InternalMaskCovered s w J f := by
  obtain ⟨u, huCode⟩ := hu f
  have huchild : ∀ q, s q u → Subset s q C := by
    intro q hq z hz
    obtain ⟨p, hpf, hqp⟩ := (huCode q).mp hq
    obtain ⟨x, y, hxC, hyC, a, b, ha, hb, hab⟩ := hnorm p hpf
    rcases (hab q).mp hqp with hqa | hqb
    · have hzx : z = x := ((ha z).mp (hqa ▸ hz)).elim id id
      exact hzx ▸ hxC
    · exact ((hb z).mp (hqb ▸ hz)).elim (fun h => h ▸ hxC) (fun h => h ▸ hyC)
  have huroot : ∀ q, s q u → MaskTailSupported s w J q := by
    intro q hq
    obtain ⟨p, hpf, hqp⟩ := (huCode q).mp hq
    exact hereditary_mask_root (hereditary_mask_member (hereditary_mask_member hf hpf) hqp)
  obtain ⟨E, hE⟩ := binary_union_exists hp hu C u
  obtain ⟨D, hD⟩ := binary_union_exists hp hu E f
  have hCD : Subset s C D := fun x hx => (hD x).mpr (Or.inl ((hE x).mpr (Or.inl hx)))
  have huD : Subset s u D := fun x hx => (hD x).mpr (Or.inl ((hE x).mpr (Or.inr hx)))
  have hfD : Subset s f D := fun x hx => (hD x).mpr (Or.inr hx)
  have hDt : TransitiveCode s D := by
    intro x hx y hy
    rcases (hD x).mp hx with hxE | hxf
    · rcases (hE x).mp hxE with hxC | hxu
      · exact hCD y (hC x hxC y hy)
      · exact hCD y (huchild x hxu y hy)
    · exact huD y ((huCode y).mpr ⟨x, hxf, hy⟩)
  have hDroot : ∀ x, s x D → MaskTailSupported s w J x := by
    intro x hx
    rcases (hD x).mp hx with hxE | hxf
    · exact ((hE x).mp hxE).elim (hroot x) (huroot x)
    · exact hereditary_mask_root (hereditary_mask_member hf hxf)
  exact mask_covered_of_supported_subset hp hu hDt hDroot (hereditary_mask_root hf) hfD

#print axioms mask_covered_normalized_relation
end FullBridge
