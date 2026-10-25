import DefinableRetraction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_relation_union (base : BaseCollection s) (p q : U) :
    ∃ k, (∀ z, s z k ↔ s z p ∨ s z q) ∧
      ∀ x y, CodedRelation s k x y ↔ CodedRelation s p x y ∨ CodedRelation s q x y := by
  obtain ⟨k, hk⟩ := binary_union_exists base.pairing base.union p q
  refine ⟨k, hk, fun x y => ?_⟩
  constructor
  · rintro ⟨z, hz, hxy⟩
    exact ((hk z).mp hz).elim (fun h => Or.inl ⟨z, h, hxy⟩) (fun h => Or.inr ⟨z, h, hxy⟩)
  · rintro (⟨z, hz, hxy⟩ | ⟨z, hz, hxy⟩)
    · exact ⟨z, (hk z).mpr (Or.inl hz), hxy⟩
    · exact ⟨z, (hk z).mpr (Or.inr hz), hxy⟩

/-- Extend an actual bijection on a subset using fresh tagged names.
    Neither object Choice nor a choice of one representative per class is used. -/
theorem extend_coded_bijection_domain (base : BaseCollection s) {a b p A : U}
    (hp : FunctionCode s a p) (hi : InjectiveCode s p) (hr : RangeCode s a p b)
    (haA : Subset s a A) :
    ∃ B k, FunctionCode s A k ∧ InjectiveCode s k ∧ RangeCode s A k B ∧
      Subset s b B ∧ (∀ x y, CodedRelation s p x y → CodedRelation s k x y) ∧
      (∀ x y, CodedRelation s k x y → s y b → CodedRelation s p x y) := by
  obtain ⟨c, hc⟩ := base.separation 1 (.impl (.member 0 1) .bottom) (cons a Fin.elim0) A
  have hc' : ∀ x, s x c ↔ s x A ∧ ¬s x a := hc
  obtain ⟨d, g, hg, hgi, hgd, hdis⟩ := fresh_parameter_copy base c b
  obtain ⟨B, hB⟩ := binary_union_exists base.pairing base.union b d
  obtain ⟨k, hkmem, hk⟩ := coded_relation_union base p g
  have hpB : ∀ x y, CodedRelation s p x y → s y b :=
    fun x y h => (hr y).mpr ⟨x, coded_function_domain hp h, h⟩
  have hgD : ∀ x y, CodedRelation s g x y → s y d :=
    fun x y h => (hgd y).mpr ⟨x, coded_function_domain hg h, h⟩
  have hsep : ∀ x y z, CodedRelation s p x z → CodedRelation s g y z → False :=
    fun x y z hpz hgz => hdis z (hgD y z hgz) (hpB x z hpz)
  have hkFun : FunctionCode s A k := by
    constructor
    · intro z hz
      rcases (hkmem z).mp hz with hz | hz
      · obtain ⟨x, y, hx, hxy⟩ := hp.1 z hz
        exact ⟨x, y, haA x hx, hxy⟩
      · obtain ⟨x, y, hx, hxy⟩ := hg.1 z hz
        exact ⟨x, y, ((hc' x).mp hx).1, hxy⟩
    · intro x hx
      by_cases hxa : s x a
      · obtain ⟨y, hxy, hu⟩ := hp.2 x hxa
        refine ⟨y, (hk x y).mpr (Or.inl hxy), ?_⟩
        intro z hxz
        rcases (hk x z).mp hxz with hpz | hgz
        · exact hu z hpz
        · exact False.elim (((hc' x).mp (coded_function_domain hg hgz)).2 hxa)
      · have hxc := (hc' x).mpr ⟨hx, hxa⟩
        obtain ⟨y, hxy, hu⟩ := hg.2 x hxc
        refine ⟨y, (hk x y).mpr (Or.inr hxy), ?_⟩
        intro z hxz
        rcases (hk x z).mp hxz with hpz | hgz
        · exact False.elim (hxa (coded_function_domain hp hpz))
        · exact hu z hgz
  refine ⟨B, k, hkFun, ?_, ?_, (fun x hx => (hB x).mpr (Or.inl hx)),
    (fun x y h => (hk x y).mpr (Or.inl h)), ?_⟩
  · intro x y z hxz hyz
    rcases (hk x z).mp hxz with hx | hx <;> rcases (hk y z).mp hyz with hy | hy
    · exact hi x y z hx hy
    · exact False.elim (hsep x y z hx hy)
    · exact False.elim (hsep y x z hy hx)
    · exact hgi x y z hx hy
  · intro y
    constructor
    · intro hy
      rcases (hB y).mp hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := (hr y).mp hy
        exact ⟨x, haA x hx, (hk x y).mpr (Or.inl hxy)⟩
      · obtain ⟨x, hx, hxy⟩ := (hgd y).mp hy
        exact ⟨x, ((hc' x).mp hx).1, (hk x y).mpr (Or.inr hxy)⟩
    · rintro ⟨x, _, hxy⟩
      exact (hB y).mpr (((hk x y).mp hxy).elim (fun h => Or.inl (hpB x y h))
        (fun h => Or.inr (hgD x y h)))
  · intro x y hxy hyb
    rcases (hk x y).mp hxy with h | h
    · exact h
    · exact False.elim (hdis y (hgD x y h) hyb)

/-- Free variables [second image, first image, bijection]. -/
def transportedMembershipFormula : Formula 3 :=
  .ex (.ex (.conj (relatedFormula 4 1 3) (.conj (relatedFormula 4 0 2) (.member 0 1))))

theorem eval_transportedMembershipFormula (k X Y : U) :
    Eval s transportedMembershipFormula (cons Y (cons X (cons k Fin.elim0))) ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s k y Y ∧ s y x := by
  simp only [transportedMembershipFormula, Eval, eval_relatedFormula]
  rfl

theorem transported_membership_graph (base : BaseCollection s) {A B k : U}
    (hf : FunctionCode s A k) (hr : RangeCode s A k B) :
    ∃ e, GraphCode s B e ∧ ∀ X Y, CodedRelation s e X Y ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s k y Y ∧ s y x := by
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base transportedMembershipFormula
    (cons k Fin.elim0) B
  refine ⟨e, hG, fun X Y => ?_⟩
  rw [he, eval_transportedMembershipFormula]
  constructor
  · exact fun h => h.2.2
  · rintro ⟨x, y, hxX, hyY, hyx⟩
    exact ⟨(hr X).mpr ⟨x, coded_function_domain hf hxX, hxX⟩,
      (hr Y).mpr ⟨y, coded_function_domain hf hyY, hyY⟩, x, y, hxX, hyY, hyx⟩

#print axioms extend_coded_bijection_domain
end FullBridge
