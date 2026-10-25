import JointMaskDomains
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem joint_mask_domain_fixed (base : BaseCollection s) {w t : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x) (a : InternalMask s w) : J a t = t :=
  elementary_involution_closed_set base (hj a) (hs a) (A.stable a)

theorem elementary_coded_image (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (ho : ∀ y, ∃ x, j x = y) {t f x y : U}
    (hf : ∀ u v, CodedRelation s f u v ↔ s u t ∧ j u = v) (hx : Subset s x t) :
    CodedImageSet s f x y ↔ y = j x := by
  have himage : CodedImageSet s f x (j x) := by
    intro v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := ho v
      have hu : s u x := (hj (Formula.member (n := 2) 0 1) (cons u (cons x Fin.elim0))).mpr hv
      exact ⟨u, hu, (hf u (j u)).mpr ⟨hx u hu, rfl⟩⟩
    · rintro ⟨u, hu, huv⟩
      have he := ((hf u v).mp huv).2
      exact he ▸ (hj (Formula.member (n := 2) 0 1) (cons u (cons x Fin.elim0))).mp hu
  constructor
  · intro hy
    exact base.extensional y (j x) (fun v => (hy v).trans (himage v).symm)
  · intro hy
    exact hy.symm ▸ himage

/-- Free variables [image,set,family,mask]. -/
def powerMaskValueFormula : Formula 4 :=
  .ex (.conj (relatedFormula 3 4 0) (codedImageSetFormula 0 2 1))

theorem eval_powerMaskValueFormula (y x k a : U) :
    Eval s powerMaskValueFormula (cons y (cons x (cons k (cons a Fin.elim0)))) ↔
      ∃ f, CodedRelation s k a f ∧ CodedImageSet s f x y := by
  simp only [powerMaskValueFormula, Eval, eval_relatedFormula, eval_codedImageSetFormula]
  rfl

theorem joint_mask_power_value (base : BaseCollection s) {w t x : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (a : InternalMask s w) (hx : Subset s x t) (y : U) :
    Eval s powerMaskValueFormula (cons y (cons x (cons A.family (cons a.val Fin.elim0)))) ↔ y = J a x := by
  rw [eval_powerMaskValueFormula]
  constructor
  · rintro ⟨f, haf, hfy⟩
    exact (elementary_coded_image base (hj a) (ho a) (A.graphs a f haf).2 hx).mp hfy
  · intro hy
    obtain ⟨f, haf, _, hf⟩ := joint_mask_graph_exists A a
    exact ⟨f, haf, (elementary_coded_image base (hj a) (ho a) hf hx).mpr hy⟩

/-- Free variables [graph,mask,power-domain,old-family]. -/
def powerMaskGraphFormula : Formula 4 :=
  (definedFunctionGraphFormula powerMaskValueFormula).rename (cons 0 (cons 2 (cons 3 (cons 1 Fin.elim0))))

theorem eval_powerMaskGraphFormula (f a q k : U) :
    Eval s powerMaskGraphFormula (cons f (cons a (cons q (cons k Fin.elim0)))) ↔
      DefinedFunctionGraph s powerMaskValueFormula (cons k (cons a Fin.elim0)) q f := by
  rw [powerMaskGraphFormula, eval_rename]
  have he : (fun i => cons f (cons a (cons q (cons k Fin.elim0)))
      ((cons 0 (cons 2 (cons 3 (cons 1 Fin.elim0)))) i)) =
      cons f (cons q (cons k (cons a Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl
      (fun i => Fin.cases rfl (fun i => Fin.elim0 i) i) i) i) i
  rw [he]
  exact eval_definedFunctionGraphFormula powerMaskValueFormula _ q f

/-- Joint source coding is preserved by the full ambient powerset, not
    merely by the hereditary relative powerset. -/
theorem joint_mask_domain_powerset (base : BaseCollection s) {w t q : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (hs : ∀ a x, J a (J a x) = x)
    (hq : ∀ x, s x q ↔ Subset s x t) : Nonempty (JointMaskDomain s w J q) := by
  have ho : ∀ a y, ∃ x, J a x = y := fun a y => ⟨J a y, hs a y⟩
  have hex : ∀ a, s a A.masks → ∃ f, Eval s powerMaskGraphFormula
      (cons f (cons a (cons q (cons A.family Fin.elim0)))) ∧
      ∀ g, Eval s powerMaskGraphFormula (cons g (cons a (cons q (cons A.family Fin.elim0)))) → g = f := by
    intro a ha
    let M : InternalMask s w := ⟨a, (A.maskMembers a).mp ha⟩
    have ht : ∀ x, s x q → ∃ y, Eval s powerMaskValueFormula
        (cons y (cons x (cons A.family (cons a Fin.elim0)))) ∧
        ∀ z, Eval s powerMaskValueFormula (cons z (cons x (cons A.family (cons a Fin.elim0)))) → z = y := by
      intro x hx
      have hv := joint_mask_power_value base A hj ho M ((hq x).mp hx)
      exact ⟨J M x, (hv _).mpr rfl, fun z hz => (hv z).mp hz⟩
    obtain ⟨f, hf⟩ := definable_function_code base powerMaskValueFormula (cons A.family (cons a Fin.elim0)) q ht
    have hdef : DefinedFunctionGraph s powerMaskValueFormula (cons A.family (cons a Fin.elim0)) q f := hf
    exact ⟨f, (eval_powerMaskGraphFormula f a q A.family).mpr hdef,
      fun g hg => defined_function_graph_unique base ((eval_powerMaskGraphFormula g a q A.family).mp hg) hdef⟩
  obtain ⟨k, hk, hrel⟩ := definable_function_code base powerMaskGraphFormula (cons q (cons A.family Fin.elim0)) A.masks hex
  refine ⟨⟨A.masks, A.maskMembers, k, hk, ?_, ?_⟩⟩
  · intro a f haf
    have hdef := (eval_powerMaskGraphFormula f a.val q A.family).mp ((hrel a.val f).mp haf).2
    refine ⟨hdef.1, fun x y => ?_⟩
    constructor
    · intro h
      obtain ⟨hx, hy⟩ := (hdef.2 x y).mp h
      exact ⟨hx, ((joint_mask_power_value base A hj ho a ((hq x).mp hx) y).mp hy).symm⟩
    · rintro ⟨hx, hy⟩
      exact (hdef.2 x y).mpr ⟨hx, (joint_mask_power_value base A hj ho a ((hq x).mp hx) y).mpr hy.symm⟩
  · intro a x hx
    apply (hq (J a x)).mpr
    have h := (elementary_map_subset (hj a) x t).mp ((hq x).mp hx)
    simpa only [joint_mask_domain_fixed base A hj hs a] using h
end FullBridge
