import JointDecorationFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Simultaneous extension of the entire source-internal mask group with
    a single source code for the new family. No finite-index restriction. -/
theorem bafa_coded_mask_extension (base : BaseCollection s) (hBafa : BAFACode s)
    {w B : U} (A : CodedMaskAction base w) (hB : TransitiveCode s B) (htB : Subset s A.domain B) :
    ∃ C : CodedMaskAction base w,
      Subset s B C.domain ∧ C.masks = A.masks ∧
      (∀ a x y, CodedRelation s (A.maps a) x y → CodedRelation s (C.maps a) x y) ∧
      (∀ a x y, CodedRelation s (C.maps a) x y → internalCode base x = internalCode base y) := by
  obtain ⟨S, e, K, rho, hG, hEnd, hK, hrho, hAct, hOne, hMul, hExt⟩ :=
    coded_mask_graph_amalgam base A hB htB
  obtain ⟨_, g, T, out, _, hg, hT, _, hBT, _, _, hout, hOutOne, hOutMul, hOld, hQ, _⟩ :=
    bafa_fixed_coherent_realization base hBafa (internalMaskOne base w) (internalMaskMul base) rho
      hB hG hEnd hAct hOne hMul
  obtain ⟨L, hL, hcodes⟩ := joint_decoration_image_family base A.maskMembers hK rho out hrho hout
  let C : CodedMaskAction base w := ⟨T, hT, A.masks, A.maskMembers, L, hL,
    out, hcodes, fun a => (hout a).1, hOutOne, hOutMul⟩
  refine ⟨C, hBT, rfl, ?_, hQ⟩
  intro a x y hxy
  have hx := coded_function_domain (A.iso a).1 hxy
  have hy := ((A.iso a).2.2.1 y).mpr ⟨x, hx, hxy⟩
  exact hOld a x y (htB x hx) (htB y hy) (hExt a x y hxy)

theorem bafa_coded_mask_cover_extension (base : BaseCollection s) (hBafa : BAFACode s)
    {w : U} (A : CodedMaskAction base w) (x : U) :
    ∃ C : CodedMaskAction base w,
      Subset s A.domain C.domain ∧ s x C.domain ∧ C.masks = A.masks ∧
      (∀ a y z, CodedRelation s (A.maps a) y z → CodedRelation s (C.maps a) y z) ∧
      (∀ a y z, CodedRelation s (C.maps a) y z → internalCode base y = internalCode base z) := by
  obtain ⟨b, hb, hxb⟩ := transitive_sets_cover base x
  obtain ⟨B, hB, htB, hbB⟩ := transitive_sets_directed base A.transitive hb
  obtain ⟨C, hBC, hmask, hExt, hQ⟩ := bafa_coded_mask_extension base hBafa A hB htB
  exact ⟨C, fun y hy => hBC y (htB y hy), hBC x (hbB x hxb), hmask, hExt, hQ⟩

/-- The whole internally indexed group-extension theorem has an actual
    label-action instance in any externally enumerated BAFA source. -/
theorem countable_bafa_joint_mask_extensions (base : BaseCollection s) (hBafa : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ z w, OmegaCode s z w ∧ ∃ P : InternalQuinePairs s w, ∃ A : CodedMaskAction base w,
      (∀ y, s y A.domain ↔ ∃ c, s c P.family ∧ s y c) ∧
      (∀ a x y, CodedRelation s (A.maps a) x y ↔
        s x A.domain ∧ y = maskedLabelAction P a.val x) ∧
      ∀ x, ∃ C : CodedMaskAction base w,
        Subset s A.domain C.domain ∧ s x C.domain ∧ C.masks = A.masks ∧
        (∀ a y z, CodedRelation s (A.maps a) y z → CodedRelation s (C.maps a) y z) ∧
        (∀ a y z, CodedRelation s (C.maps a) y z → internalCode base y = internalCode base z) := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  obtain ⟨P⟩ := bafa_internal_quine_pairs base hBafa w
  obtain ⟨J, hJ, hOne, hMul, hcore, _, _, _, hs, _⟩ := countable_bafa_internal_mask_action base hBafa enum henum P
  obtain ⟨d, hd⟩ := base.union P.family
  obtain ⟨D⟩ := joint_mask_label_domain base P J hcore hd
  obtain ⟨A, hAd, _, _, hAr⟩ := joint_mask_coded_action base D (internal_label_domain_transitive P hd)
    (fun a => (hJ a).1) hs hOne hMul
  refine ⟨z, w, hw, P, A, ?_, ?_, bafa_coded_mask_cover_extension base hBafa A⟩
  · exact fun y => hAd.symm ▸ hd y
  · intro a x y
    rw [hAr a x y, hAd]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, hy.symm.trans (hcore a x ((hd x).mp hx))⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, (hcore a x ((hd x).mp hx)).trans hy.symm⟩

#print axioms bafa_coded_mask_extension
#print axioms countable_bafa_joint_mask_extensions
end FullBridge
