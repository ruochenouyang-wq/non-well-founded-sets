import InternalMaskCovers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem hereditary_transitive_internal_mask_covered (hp : Pairing s) (hu : Union s)
    {w t : U} {J : InternalMask s w → U → U} (ht : TransitiveCode s t)
    (hH : HereditarilyMaskSupported s w J t) : InternalMaskCovered s w J t := by
  obtain ⟨p, hpair⟩ := hp t t
  obtain ⟨d, hd⟩ := binary_union_exists hp hu t p
  have htd : Subset s t d := fun x hx => (hd x).mpr (Or.inl hx)
  refine ⟨d, ?_, (hd t).mpr (Or.inr ((hpair t).mpr (Or.inl rfl))), ?_⟩
  · intro x hx y hy
    rcases (hd x).mp hx with hxt | hxp
    · exact htd y (ht x hxt y hy)
    · have he : x = t := ((hpair x).mp hxp).elim id id
      exact htd y (he ▸ hy)
  · intro x hx
    rcases (hd x).mp hx with hxt | hxp
    · exact hereditary_mask_root (hereditary_mask_member hH hxt)
    · have he : x = t := ((hpair x).mp hxp).elim id id
      exact he.symm ▸ hereditary_mask_root hH

/-- A genuine source set, hereditary and transitive, exactly comprising
    internally mask-covered points in the given transitive joint domain. -/
theorem joint_internal_mask_core_exists (base : BaseCollection s) {z w T : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U} (A : JointMaskDomain s w J T)
    (hT : TransitiveCode s T) (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x) :
    ∃ C, (∀ x, s x C ↔ s x T ∧ InternalMaskCovered s w J x) ∧
      TransitiveCode s C ∧ HereditarilyMaskSupported s w J C ∧ InternalMaskCovered s w J C ∧
      (∀ i, J i C = C) ∧ Nonempty (JointMaskDomain s w J C) := by
  have ho : ∀ i y, ∃ x, J i x = y := fun i y => ⟨J i y, hs i y⟩
  obtain ⟨C, hC⟩ := base.separation 4 (internalMaskCoreFormula 1 2 3 4 0)
    (cons w (cons A.masks (cons A.family (cons T Fin.elim0)))) T
  have hm : ∀ x, s x C ↔ s x T ∧ InternalMaskCovered s w J x := by
    intro x
    exact (hC x).trans (and_congr_right (fun hx => joint_internal_mask_core_formula base A hT hj ho hx))
  have hCT : Subset s C T := fun x hx => ((hm x).mp hx).1
  have hstable : ∀ i x, s x C → s (J i x) C := by
    intro i x hx
    obtain ⟨hxT, hxc⟩ := (hm x).mp hx
    exact (hm _).mpr ⟨A.stable i x hxT, (internal_mask_covered_invariant hj hc hs i x).mpr hxc⟩
  have hfixed : ∀ i, J i C = C := fun i =>
    elementary_involution_closed_set base (hj i) (hs i) (hstable i)
  have htr : TransitiveCode s C := by
    intro x hx y hy
    obtain ⟨hxT, hxc⟩ := (hm x).mp hx
    exact (hm y).mpr ⟨hT x hxT y hy, internal_mask_covered_member hxc hy⟩
  have hH : HereditarilyMaskSupported s w J C :=
    hereditary_mask_intro ⟨z, hw.2.1.1, fun i _ => hfixed i⟩
      (fun x hx => internal_mask_covered_hereditary ((hm x).mp hx).2)
  exact ⟨C, hm, htr, hH, hereditary_transitive_internal_mask_covered base.pairing base.union htr hH,
    hfixed, joint_mask_domain_restrict base A hCT hstable⟩

theorem internal_mask_core_maximal {w T C d : U} {J : InternalMask s w → U → U}
    (hC : ∀ x, s x C ↔ s x T ∧ InternalMaskCovered s w J x)
    (hdT : Subset s d T) (hd : TransitiveCode s d)
    (hroot : ∀ x, s x d → MaskTailSupported s w J x) : Subset s d C :=
  fun x hx => (hC x).mpr ⟨hdT x hx, d, hd, hx, hroot⟩

theorem internal_mask_covered_iff_H_transitive_cover (base : BaseCollection s) {z w x : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    InternalMaskCovered s w J x ↔
      ∃ C, TransitiveCode s C ∧ HereditarilyMaskSupported s w J C ∧ s x C := by
  constructor
  · intro hx
    have hxcov := hx
    obtain ⟨d, _, hxd, _⟩ := hx
    obtain ⟨T, hT, ⟨A⟩, hdT⟩ := hCover d
    obtain ⟨C, hm, ht, hH, _⟩ := joint_internal_mask_core_exists base hw A hT hj hc hs
    exact ⟨C, ht, hH, (hm x).mpr ⟨hdT x hxd, hxcov⟩⟩
  · rintro ⟨C, ht, hH, hx⟩
    exact ⟨C, ht, hx, fun y hy => hereditary_mask_root (hereditary_mask_member hH hy)⟩

/-- Internal covered points have exact source traces on every source set.
    No assertion that all externally hereditary points are covered is used. -/
theorem internal_mask_covered_trace_exists (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (a : U) : ∃ b, ∀ x, s x b ↔ s x a ∧ InternalMaskCovered s w J x := by
  obtain ⟨T, hT, ⟨A⟩, haT⟩ := hCover a
  obtain ⟨C, hm, _⟩ := joint_internal_mask_core_exists base hw A hT hj hc hs
  obtain ⟨b, hb⟩ := base.separation 1 (.member 0 1) (cons C Fin.elim0) a
  refine ⟨b, fun x => ?_⟩
  change s x b ↔ s x a ∧ InternalMaskCovered s w J x
  exact (hb x).trans ⟨fun ⟨hx, hxc⟩ => ⟨hx, ((hm x).mp hxc).2⟩,
    fun ⟨hx, hcover⟩ => ⟨hx, (hm x).mpr ⟨haT x hx, hcover⟩⟩⟩

#print axioms joint_internal_mask_core_exists
#print axioms internal_mask_covered_trace_exists
end FullBridge
