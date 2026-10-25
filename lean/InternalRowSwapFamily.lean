import InternalTailChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def SwapGraphCode (s : U → U → Prop) (d l r f : U) : Prop :=
  FunctionCode s d f ∧ ∀ x y, CodedRelation s f x y ↔ s x d ∧ y = quineSwap l r x

def swapGraphFormula {n} (d l r f : Fin n) : Formula n :=
  .conj (functionCodeFormula d f) (.all (.all
    ((relatedFormula f.succ.succ 1 0).iffF
      (.conj (.member 1 d.succ.succ) (quineSwapFormula l.succ.succ r.succ.succ 1 0)))))

theorem eval_swapGraphFormula {n} (d l r f : Fin n) (v : Fin n → U) (hne : v l ≠ v r) :
    Eval s (swapGraphFormula d l r f) v ↔ SwapGraphCode s (v d) (v l) (v r) (v f) := by
  simp only [swapGraphFormula, Eval, eval_functionCodeFormula, eval_iffF, eval_relatedFormula, cons_succ]
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, fun x y => (h x y).trans (and_congr Iff.rfl
      (eval_quineSwapFormula l.succ.succ r.succ.succ 1 0 (cons y (cons x v)) hne))⟩
  · rintro ⟨hf, h⟩
    exact ⟨hf, fun x y => (h x y).trans (and_congr Iff.rfl
      (eval_quineSwapFormula l.succ.succ r.succ.succ 1 0 (cons y (cons x v)) hne).symm)⟩

def RowSwapCode (s : U → U → Prop) (left right d i f : U) : Prop :=
  ∃ l r, CodedRelation s left i l ∧ CodedRelation s right i r ∧ l ≠ r ∧ SwapGraphCode s d l r f

def rowSwapCodeFormula {n} (left right d i f : Fin n) : Formula n :=
  .ex (.ex (.conj (relatedFormula left.succ.succ i.succ.succ 1)
    (.conj (relatedFormula right.succ.succ i.succ.succ 0)
      (.conj (.impl (.equal 1 0) .bottom) (swapGraphFormula d.succ.succ 1 0 f.succ.succ)))))

theorem eval_rowSwapCodeFormula {n} (left right d i f : Fin n) (v : Fin n → U) :
    Eval s (rowSwapCodeFormula left right d i f) v ↔
      RowSwapCode s (v left) (v right) (v d) (v i) (v f) := by
  simp only [rowSwapCodeFormula, Eval, eval_relatedFormula, cons_succ]
  constructor
  · rintro ⟨l, r, hl, hr, hne, hg⟩
    exact ⟨l, r, hl, hr, hne, (eval_swapGraphFormula d.succ.succ 1 0 f.succ.succ (cons r (cons l v)) hne).mp hg⟩
  · rintro ⟨l, r, hl, hr, hne, hg⟩
    exact ⟨l, r, hl, hr, hne, (eval_swapGraphFormula d.succ.succ 1 0 f.succ.succ (cons r (cons l v)) hne).mpr hg⟩

theorem internal_row_swap_exists (base : BaseCollection s) {w d i : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (hi : s i w) : ∃ f, RowSwapCode s P.leftCode P.rightCode d i f := by
  obtain ⟨l, hl, _⟩ := P.leftFunction.2 i hi
  obtain ⟨r, hr, _⟩ := P.rightFunction.2 i hi
  obtain ⟨c, hc⟩ := base.pairing l r
  have hcf := (P.members c).mpr ⟨i, l, r, hi, hl, hr, hc⟩
  have hld := (hd l).mpr ⟨c, hcf, (hc l).mpr (Or.inl rfl)⟩
  have hrd := (hd r).mpr ⟨c, hcf, (hc r).mpr (Or.inr rfl)⟩
  have hquines : ∀ y, s y d → SelfSingleton s y := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := (hd y).mp hy
    obtain ⟨j, L, R, _, hL, hR, hp⟩ := (P.members b).mp hb
    rcases (hp y).mp hyb with h | h
    · exact h ▸ P.leftQuine j L hL
    · exact h ▸ P.rightQuine j R hR
  obtain ⟨A, hAd, hA⟩ := quine_domain_internal_swap base hquines hld hrd
    (internal_quine_pair_distinct P hl hr)
  exact ⟨A.code, l, r, hl, hr, internal_quine_pair_distinct P hl hr, hAd ▸ A.iso.1, hA⟩

theorem internal_row_swap_unique (base : BaseCollection s) {w d i f g : U}
    (P : InternalQuinePairs s w) (hf : RowSwapCode s P.leftCode P.rightCode d i f)
    (hg : RowSwapCode s P.leftCode P.rightCode d i g) : f = g := by
  obtain ⟨l, r, hl, hr, _, hf⟩ := hf
  obtain ⟨L, R, hL, hR, _, hg⟩ := hg
  have hLl := coded_function_value_unique P.leftFunction hL hl
  have hRr := coded_function_value_unique P.rightFunction hR hr
  subst L
  subst R
  exact function_code_extensional base.extensional hf.1 hg.1
    (fun x u v hxu hxv => ((hf.2 x u).mp hxu).2.trans ((hg.2 x v).mp hxv).2.symm)

/-- One actual source function assigns the local swap graph to every
    internal index, including every nonstandard index. -/
theorem internal_row_swap_family_code (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) :
    ∃ k, FunctionCode s w k ∧ ∀ i f,
      CodedRelation s k i f ↔ s i w ∧ RowSwapCode s P.leftCode P.rightCode d i f := by
  let phi : Formula 6 := .conj (.member 1 2) (rowSwapCodeFormula 3 4 5 1 0)
  let v := cons w (cons P.leftCode (cons P.rightCode (cons d Fin.elim0)))
  have hev : ∀ i f, Eval s phi (cons f (cons i v)) ↔
      s i w ∧ RowSwapCode s P.leftCode P.rightCode d i f := by
    intro i f
    simp only [phi, Eval, eval_rowSwapCodeFormula]
    rfl
  have ht : ∀ i, s i w → ∃ f, Eval s phi (cons f (cons i v)) ∧
      ∀ g, Eval s phi (cons g (cons i v)) → g = f := by
    intro i hi
    obtain ⟨f, hf⟩ := internal_row_swap_exists base P hd hi
    exact ⟨f, (hev i f).mpr ⟨hi, hf⟩,
      fun g hg => internal_row_swap_unique base P ((hev i g).mp hg).2 hf⟩
  obtain ⟨a, ha⟩ := collection_separation_replacement s base.collection base.separation 4 phi v w ht
  obtain ⟨b, hb⟩ := binary_union_exists base.pairing base.union w a
  obtain ⟨k, hG, hK⟩ := normalized_relation_comprehension base phi v b
  have hrel : ∀ i f, CodedRelation s k i f ↔ s i w ∧ RowSwapCode s P.leftCode P.rightCode d i f := by
    intro i f
    constructor
    · intro h
      exact (hev i f).mp ((hK i f).mp h).2.2
    · intro h
      have hp := (hev i f).mpr h
      exact (hK i f).mpr ⟨(hb i).mpr (Or.inl h.1),
        (hb f).mpr (Or.inr ((ha f).mpr ⟨i, h.1, hp⟩)), hp⟩
  refine ⟨k, ⟨?_, ?_⟩, hrel⟩
  · intro p hp
    obtain ⟨i, f, _, _, hpair⟩ := hG p hp
    exact ⟨i, f, ((hrel i f).mp ⟨p, hp, hpair⟩).1, hpair⟩
  · intro i hi
    obtain ⟨f, hf⟩ := internal_row_swap_exists base P hd hi
    exact ⟨f, (hrel i f).mpr ⟨hi, hf⟩,
      fun g hg => internal_row_swap_unique base P ((hrel i g).mp hg).2 hf⟩

#print axioms internal_row_swap_family_code
end FullBridge
