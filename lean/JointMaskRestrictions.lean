import MaskTwoCycleCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def jointMaskPointFormula {n} (K i x y : Fin n) : Formula n :=
  .ex (.conj (relatedFormula K.succ i.succ 0) (relatedFormula 0 x.succ y.succ))

theorem eval_jointMaskPointFormula {n} (K i x y : Fin n) (v : Fin n → U) :
    Eval s (jointMaskPointFormula K i x y) v ↔
      ∃ f, CodedRelation s (v K) (v i) f ∧ CodedRelation s f (v x) (v y) := by
  simp only [jointMaskPointFormula, Eval, eval_relatedFormula]
  rfl

theorem joint_mask_point_value {w t : U} {J : InternalMask s w → U → U}
    (A : JointMaskDomain s w J t) (i : InternalMask s w) {x : U} (hx : s x t) (y : U) :
    (∃ f, CodedRelation s A.family i.val f ∧ CodedRelation s f x y) ↔ J i x = y := by
  constructor
  · rintro ⟨f, hif, hxy⟩
    exact (((A.graphs i f hif).2 x y).mp hxy).2
  · intro hy
    obtain ⟨f, hif, _, hf⟩ := joint_mask_graph_exists A i
    exact ⟨f, hif, (hf x y).mpr ⟨hx, hy⟩⟩

/-- Restrict a single joint source family to an actual invariant subset. -/
theorem joint_mask_domain_restrict (base : BaseCollection s) {w t d : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hdt : Subset s d t) (hd : ∀ i x, s x d → s (J i x) d) :
    Nonempty (JointMaskDomain s w J d) := by
  let p : Formula 4 := jointMaskPointFormula 3 2 1 0
  have hev : ∀ i x, s x d → ∀ y,
      Eval s p (cons y (cons x (cons i.val (cons A.family Fin.elim0)))) ↔ J i x = y := by
    intro i x hx y
    exact (eval_jointMaskPointFormula 3 2 1 0 _).trans (joint_mask_point_value A i (hdt x hx) y)
  have ht : ∀ i, s i A.masks → ∀ x, s x d → ∃ y,
      Eval s p (cons y (cons x (cons i (cons A.family Fin.elim0)))) ∧
      ∀ z, Eval s p (cons z (cons x (cons i (cons A.family Fin.elim0)))) → z = y := by
    intro i hi x hx
    let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
    exact ⟨J I x, (hev I x hx _).mpr rfl, fun y hy => ((hev I x hx y).mp hy).symm⟩
  obtain ⟨K, hK, hKr⟩ := definable_function_family base p (cons A.family Fin.elim0) A.masks d ht
  refine ⟨⟨A.masks, A.maskMembers, K, hK, ?_, hd⟩⟩
  intro i f hif
  obtain ⟨_, hf, hfr⟩ := (hKr i.val f).mp hif
  refine ⟨hf, fun x y => ?_⟩
  rw [hfr]
  exact and_congr_right (fun hx => hev i x hx y)

theorem joint_mask_orbit_exists (base : BaseCollection s) {w t x : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t) (hx : s x t)
    (hMul : ∀ i j y, J (internalMaskMul base i j) y = J i (J j y)) :
    ∃ F O, FunctionCode s A.masks F ∧
      (∀ i : InternalMask s w, CodedRelation s F i.val (J i x)) ∧
      (∀ y, s y O ↔ ∃ i : InternalMask s w, J i x = y) ∧
      Subset s O t ∧ Nonempty (JointMaskDomain s w J O) := by
  let p : Formula 4 := jointMaskPointFormula 2 1 3 0
  have hev : ∀ i y, Eval s p (cons y (cons i.val (cons A.family (cons x Fin.elim0)))) ↔ J i x = y :=
    fun i y => (eval_jointMaskPointFormula 2 1 3 0 _).trans (joint_mask_point_value A i hx y)
  obtain ⟨F, hF, hFr⟩ := definable_function_code base p (cons A.family (cons x Fin.elim0)) A.masks (by
    intro i hi
    let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
    exact ⟨J I x, (hev I _).mpr rfl, fun y hy => ((hev I y).mp hy).symm⟩)
  have hcodes : ∀ i : InternalMask s w, CodedRelation s F i.val (J i x) :=
    fun i => (hFr i.val _).mpr ⟨(A.maskMembers i.val).mpr i.property, (hev i _).mpr rfl⟩
  obtain ⟨O, hO⟩ := coded_image_set_exists base F A.masks
  have hmem : ∀ y, s y O ↔ ∃ i : InternalMask s w, J i x = y := by
    intro y
    rw [hO]
    constructor
    · rintro ⟨i, hi, hiy⟩
      let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
      exact ⟨I, (hev I y).mp ((hFr i y).mp hiy).2⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, (A.maskMembers i.val).mpr i.property, hcodes i⟩
  have hOt : Subset s O t := by
    intro y hy
    obtain ⟨i, rfl⟩ := (hmem y).mp hy
    exact A.stable i x hx
  have hstable : ∀ i y, s y O → s (J i y) O := by
    intro i y hy
    obtain ⟨j, rfl⟩ := (hmem y).mp hy
    exact (hmem _).mpr ⟨internalMaskMul base i j, hMul i j x⟩
  exact ⟨F, O, hF, hcodes, hmem, hOt, joint_mask_domain_restrict base A hOt hstable⟩

#print axioms joint_mask_domain_restrict
#print axioms joint_mask_orbit_exists
end FullBridge
