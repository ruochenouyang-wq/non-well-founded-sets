import MaskGraphAbsoluteness
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The graph uses the old domain itself as nodes, with its actual old maps.
    The joint graph-action family is constructed from the old family code. -/
theorem countable_bafa_invariant_graph_attachment (base : BaseCollection s) (hB : BAFACode s)
    {w r : U} (P : CodedMaskAction base w) (hG : GraphCode s P.domain r)
    (hExt : GraphExtensionalCode s P.domain r)
    (hInv : ∀ i, GraphIsoCode s P.domain r P.domain r (P.maps i))
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U, ∃ f,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → J i x = y) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      DecorationCode s P.domain r f ∧ InjectiveCode s f ∧
      (∀ i x X, CodedRelation s f x X → CodedRelation s f (J i x) (J i X)) := by
  let Q : CodedMaskGraphAction base P P.domain r :=
    ⟨P.family, P.familyFunction, P.maps, P.mapCodes, hInv, P.one, P.mul⟩
  obtain ⟨t, ht⟩ := base.empty
  obtain ⟨C, f, hPC, _, hf, hfi, _, _, hOld, hEquiv⟩ := bafa_joint_graph_attachment base hB P Q
    (fun x hx => False.elim (ht x hx)) (fun x hx => False.elim (ht x hx)) hG hExt
    ⟨fun x hx => False.elim (ht x hx), fun x hx => False.elim (ht x hx)⟩
    (fun _ x _ hx => False.elim (ht x hx)) (fun _ x _ hx => False.elim (ht x hx))
  obtain ⟨J, hJ, hOne, hMul, hCJ, _, hCover⟩ := countable_bafa_coded_mask_extension base hB C enum henum
  have hPJ : ∀ i x y, CodedRelation s (P.maps i) x y → J i x = y :=
    fun i x y h => hCJ i x y (hOld i x y h)
  refine ⟨J, f, hJ, hOne, hMul, hPJ, hCover, hf, hfi, ?_⟩
  intro i x X hxX
  obtain ⟨y, hxy, _⟩ := (P.iso i).1.2 x (coded_function_domain hf.1 hxX)
  have hy := ((P.iso i).2.2.1 y).mpr ⟨x, coded_function_domain hf.1 hxX, hxy⟩
  obtain ⟨Y, hyY, _⟩ := hf.1.2 y hy
  have hXY := hEquiv i x y X Y hxy hxX hyY
  have hxj := hPJ i x y hxy
  have hXj := hCJ i X Y hXY
  rw [hxj, hXj]
  exact hyY

theorem invariant_core_graph_hereditary_realization (base : BaseCollection s) (hB : BAFACode s)
    {z w r : U} (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (A : CodedMaskAction base w)
    (hd : ∀ x, s x A.domain ↔ ∃ c, s c P.family ∧ s x c)
    (hAr : ∀ i x y, CodedRelation s (A.maps i) x y ↔ s x A.domain ∧ y = maskedLabelAction P i.val x)
    (hG : GraphCode s A.domain r) (hExt : GraphExtensionalCode s A.domain r)
    (hInv : ∀ i, GraphIsoCode s A.domain r A.domain r (A.maps i))
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U, ∃ f,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ i j x, J i (J j x) = J j (J i x)) ∧ (∀ i x, J i (J i x) = x) ∧
      (∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      HereditarilyMaskSupported s w J A.domain ∧ HereditarilyMaskSupported s w J r ∧
      HereditarilyMaskSupported s w J f ∧ DecorationCode s A.domain r f ∧ InjectiveCode s f := by
  obtain ⟨J, f, hJ, hOne, hMul, hOld, hCover, hf, hfi, hEq⟩ :=
    countable_bafa_invariant_graph_attachment base hB A hG hExt hInv enum henum
  have hj : ∀ i, ElementaryMap s s (J i) := fun i => (hJ i).1
  have ho := fun i => (hJ i).2.1
  have hc : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
    group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  have hcore : ∀ i x, (∃ c, s c P.family ∧ s x c) → J i x = maskedLabelAction P i.val x := by
    intro i x hx
    exact hOld i x _ ((hAr i x _).mpr ⟨(hd x).mpr hx, rfl⟩)
  have hnodes : ∀ x, s x A.domain → HereditarilyMaskSupported s w J x :=
    fun x hx => hereditary_mask_label base hw P J hcore ((hd x).mp hx)
  have hA := hereditary_mask_union base hj ho (hereditary_mask_family base hw P J hj ho hcore) hd
  have hrEq : ∀ i x y, CodedRelation s r x y → CodedRelation s r (J i x) (J i y) := by
    intro i x y hxy
    obtain ⟨X, hxX, _⟩ := (A.iso i).1.2 x (graphCode_endpoints hG hxy).1
    obtain ⟨Y, hyY, _⟩ := (A.iso i).1.2 y (graphCode_endpoints hG hxy).2
    rw [hOld i x X hxX, hOld i y Y hyY]
    exact ((hInv i).2.2.2 x y X Y hxX hyY).mp hxy
  have hR : HereditarilyMaskSupported s w J r := by
    apply hereditary_mask_intro
    · refine ⟨z, hw.2.1.1, fun i _ => equivariant_relation_fixed base (hj i) (hs i) ?_ (hrEq i)⟩
      intro p hp
      obtain ⟨x, y, _, _, hxy⟩ := hG p hp
      exact ⟨x, y, hxy⟩
    · intro p hp
      obtain ⟨x, y, hx, hy, hxy⟩ := hG p hp
      exact hereditary_mask_ordered_pair base hw hj (hnodes x hx) (hnodes y hy) hxy
  have hF := (mask_equivariant_decoration_hereditary base hw hj hs hf
    ⟨z, hw.2.1.1, fun i _ => hEq i⟩ hnodes).1
  exact ⟨J, f, hJ, hc, hs, hcore, hCover, hA, hR, hF, hf, hfi⟩

#print axioms countable_bafa_invariant_graph_attachment
#print axioms invariant_core_graph_hereditary_realization
end FullBridge
