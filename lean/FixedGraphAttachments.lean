import JointBafaAttachments
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem trivial_coded_mask_graph_action (base : BaseCollection s) {w a r : U}
    (P : CodedMaskAction base w) : ∃ Q : CodedMaskGraphAction base P a r,
      ∀ i x y, CodedRelation s (Q.maps i) x y ↔ s x a ∧ y = x := by
  obtain ⟨id, hidF, hid⟩ := definable_function_code base (Formula.equal (n := 2) 0 1) Fin.elim0 a (by
    intro x _
    exact ⟨x, rfl, fun y h => h⟩)
  have hid' : ∀ x y, CodedRelation s id x y ↔ s x a ∧ y = x := hid
  have hi : GraphIsoCode s a r a r id := by
    refine ⟨hidF, ?_, ?_, ?_⟩
    · intro x y z hx hy
      exact ((hid' x z).mp hx).2.symm.trans ((hid' y z).mp hy).2
    · intro y
      exact ⟨fun hy => ⟨y, hy, (hid' y y).mpr ⟨hy, rfl⟩⟩,
        fun ⟨x, hx, hxy⟩ => ((hid' x y).mp hxy).2.symm ▸ hx⟩
    · intro x y X Y hx hy
      rcases (hid' x X).mp hx with ⟨_, rfl⟩
      rcases (hid' y Y).mp hy with ⟨_, rfl⟩
      rfl
  obtain ⟨K, hK, hKr⟩ := definable_function_code base (Formula.equal (n := 3) 0 2)
    (cons id Fin.elim0) P.masks (by
      intro i _
      exact ⟨id, rfl, fun f h => h⟩)
  have hKcodes : ∀ i : InternalMask s w, CodedRelation s K i.val id :=
    fun i => (hKr i.val id).mpr ⟨(P.maskMembers i.val).mpr i.property, rfl⟩
  have hOne : ∀ x y, CodedRelation s id x y → x = y := fun x y h => ((hid' x y).mp h).2.symm
  have hMul : ∀ x z, CodedRelation s id x z ↔
      ∃ y, CodedRelation s id x y ∧ CodedRelation s id y z := by
    intro x z
    constructor
    · intro h
      exact ⟨x, (hid' x x).mpr ⟨((hid' x z).mp h).1, rfl⟩, h⟩
    · rintro ⟨y, hxy, hyz⟩
      exact (hOne x y hxy).symm ▸ hyz
  exact ⟨⟨K, hK, fun _ => id, hKcodes, fun _ => hi, hOne, fun _ _ => hMul⟩,
    fun _ => hid'⟩

/-- An actual construction, with no assumed graph-action family: insert an
    injective graph solution whose every value is fixed by every internal mask. -/
theorem bafa_fixed_graph_attachment (base : BaseCollection s) (hBafa : BAFACode s)
    {w a r : U} (P : CodedMaskAction base w) (hG : GraphCode s a r)
    (hExt : GraphExtensionalCode s a r) :
    ∃ C : CodedMaskAction base w, ∃ f,
      CodedMaskExtends base P C ∧ C.masks = P.masks ∧
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ x X, CodedRelation s f x X → s X C.domain) ∧
      (∀ i x X, CodedRelation s f x X → CodedRelation s (C.maps i) X X) := by
  obtain ⟨t, ht⟩ := base.empty
  obtain ⟨Q, hQ⟩ := trivial_coded_mask_graph_action (a := a) (r := r) base P
  obtain ⟨C, f, hPC, hMasks, hf, hfi, _, hRange, hOld, hEquiv⟩ :=
    bafa_joint_graph_attachment base hBafa P Q
      (fun x hx => False.elim (ht x hx)) (fun x hx => False.elim (ht x hx))
      hG hExt ⟨fun x hx => False.elim (ht x hx), fun x hx => False.elim (ht x hx)⟩
      (fun _ x _ hx => False.elim (ht x hx)) (fun _ x _ hx => False.elim (ht x hx))
  refine ⟨C, f, ⟨hPC, hOld⟩, hMasks, hf, hfi, hRange, fun i x X hxX => ?_⟩
  exact hEquiv i x x X X ((hQ i x x).mpr ⟨coded_function_domain hf.1 hxX, rfl⟩) hxX hxX

theorem decoration_descendant_range {a r f X Y : U} (hf : DecorationCode s a r f)
    (hXY : MemberDescendant s X Y) :
    (∃ x, CodedRelation s f x X) → ∃ y, CodedRelation s f y Y := by
  induction hXY with
  | refl => exact fun h => h
  | @step X Z Y hZX _ ih =>
    rintro ⟨x, hxX⟩
    obtain ⟨z, _, _, hzZ⟩ := (hf.2 x (coded_function_domain hf.1 hxX) X hxX Z).mp hZX
    exact ih ⟨z, hzZ⟩

theorem fixed_decoration_values_hereditary {w z a r f : U} (hw : OmegaCode s z w)
    (J : InternalMask s w → U → U) (hf : DecorationCode s a r f)
    (hFix : ∀ i x X, CodedRelation s f x X → J i X = X) :
    ∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J X := by
  intro x X hxX Y hXY
  obtain ⟨y, hyY⟩ := decoration_descendant_range hf hXY ⟨x, hxX⟩
  exact ⟨z, hw.2.1.1, fun i _ => hFix i y Y hyY⟩

/-- The local construction can actually be extended to a global jointly
    coded action. The solution values, not yet its function code, lie in H. -/
theorem countable_bafa_fixed_graph_action (base : BaseCollection s) (hBafa : BAFACode s)
    {z w a r : U} (hw : OmegaCode s z w) (P : CodedMaskAction base w)
    (hG : GraphCode s a r) (hExt : GraphExtensionalCode s a r)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ J : InternalMask s w → U → U, ∃ f,
      (∀ i, ElementaryMap s s (J i) ∧ (∀ y, ∃ x, J i x = y) ∧ LocallyInternalTransitiveMap s (J i)) ∧
      (∀ x, J (internalMaskOne base w) x = x) ∧
      (∀ i j x, J (internalMaskMul base i j) x = J i (J j x)) ∧
      (∀ i x y, CodedRelation s (P.maps i) x y → J i x = y) ∧
      (∀ d, ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d t) ∧
      DecorationCode s a r f ∧ InjectiveCode s f ∧
      (∀ i x X, CodedRelation s f x X → J i X = X) ∧
      (∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J X) := by
  obtain ⟨C, f, hPC, _, hf, hfi, _, hFix⟩ := bafa_fixed_graph_attachment base hBafa P hG hExt
  obtain ⟨J, hJ, hOne, hMul, hOld, _, hCover⟩ := countable_bafa_coded_mask_extension base hBafa C enum henum
  have hFix' : ∀ i x X, CodedRelation s f x X → J i X = X :=
    fun i x X hxX => hOld i X X (hFix i x X hxX)
  exact ⟨J, f, hJ, hOne, hMul, fun i x y h => hOld i x y (hPC.2 i x y h), hCover,
    hf, hfi, hFix', fixed_decoration_values_hereditary hw J hf hFix'⟩

#print axioms bafa_fixed_graph_attachment
#print axioms countable_bafa_fixed_graph_action
end FullBridge
