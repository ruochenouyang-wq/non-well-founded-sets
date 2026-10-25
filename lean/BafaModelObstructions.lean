import SupportedChoice
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- Cantor's diagonal argument for actual internal function codes. -/
theorem no_coded_injection_powerset (base : BaseCollection s) {a p f : U}
    (hp : ∀ x, s x p ↔ Subset s x a) (hf : FunctionCode s p f)
    (hi : InjectiveCode s f)
    (hr : ∀ x y, CodedRelation s f x y → s y a) : False := by
  let formula : Formula 3 := .ex (.conj (.member 0 3)
    (.conj (relatedFormula 2 0 1) (.impl (.member 1 0) .bottom)))
  obtain ⟨d, hd⟩ := base.separation 2 formula (cons f (cons p Fin.elim0)) a
  have hd' : ∀ y, s y d ↔ s y a ∧ ∃ x, s x p ∧ CodedRelation s f x y ∧ ¬s y x := by
    intro y
    have h := hd y
    simp only [formula, Eval, eval_relatedFormula] at h
    exact h
  have hdp := (hp d).mpr (fun y hy => ((hd' y).mp hy).1)
  obtain ⟨y, hdy, _⟩ := hf.2 d hdp
  have hnot : ¬s y d := by
    intro hyd
    obtain ⟨_, x, _, hxy, hnot⟩ := (hd' y).mp hyd
    have hxd := hi x d y hxy hdy
    exact hnot (hxd.symm ▸ hyd)
  exact hnot ((hd' y).mpr ⟨hr d y hdy, d, hdp, hdy, hnot⟩)

/-- Internal unboundedness: not a claim that the external model carrier is a proper class. -/
theorem bafa_selfSingleton_outside_set (base : BaseCollection s)
    (hB : BAFACode s) (a : U) : ∃ v, SelfSingleton s v ∧ ¬s v a := by
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ v, SelfSingleton s v → s v a := by
    intro v hv
    apply Classical.byContradiction
    intro hva
    exact h ⟨v, hv, hva⟩
  obtain ⟨p, hp⟩ := base.powerset a
  obtain ⟨f, hf, hi, hs⟩ := bafa_selfSingleton_family base hB p
  exact no_coded_injection_powerset base hp hf hi
    (fun x y hxy => hall y (hs x y (coded_function_domain hf hxy) hxy))

theorem bafa_selfSingleton_fiber_unbounded (base : BaseCollection s)
    (hB : BAFACode s) {v : U} (hv : SelfSingleton s v) (a : U) :
    ∃ w, SelfSingleton s w ∧ internalCode base w = internalCode base v ∧ ¬s w a := by
  obtain ⟨w, hw, hwa⟩ := bafa_selfSingleton_outside_set base hB a
  exact ⟨w, hw, selfSingleton_same_code base hw hv, hwa⟩

theorem bafa_distinct_two_cycle (base : BaseCollection s) (hB : BAFACode s) :
    ∃ V W, V ≠ W ∧ (∀ z, s z V ↔ z = W) ∧ (∀ z, s z W ↔ z = V) := by
  classical
  obtain ⟨v, w, hvw, _, _⟩ := bafa_distinct_selfSingletons base hB
  obtain ⟨a, ha⟩ := base.pairing v w
  have hv := (ha v).mpr (Or.inl rfl)
  have hw := (ha w).mpr (Or.inr rfl)
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base
    (.impl (Formula.equal (n := 2) 0 1) .bottom) Fin.elim0 a
  have hei : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧ y ≠ x := he
  have hE : GraphExtensionalCode s a e := by
    intro x hx y hy hrows
    apply Classical.byContradiction
    intro hxy
    have hyx := (hei y x).mpr ⟨hy, hx, hxy⟩
    exact ((hei x x).mp ((hrows x hx).mpr hyx)).2.2 rfl
  obtain ⟨f, hf, hi⟩ := bafa_extensional_realization base.empty hB a e hG hE
  obtain ⟨V, hvV, _⟩ := hf.1.2 v hv
  obtain ⟨W, hwW, _⟩ := hf.1.2 w hw
  have row : ∀ x y, s x a → s y a → x ≠ y →
      (∀ z, s z a → z = x ∨ z = y) →
      ∀ X Y, CodedRelation s f x X → CodedRelation s f y Y →
      ∀ z, s z X ↔ z = Y := by
    intro x y hx hy hxy hab X Y hxX hyY z
    constructor
    · intro hz
      obtain ⟨t, ht, hxt, htz⟩ := (hf.2 x hx X hxX z).mp hz
      have hty : t = y := (hab t ht).resolve_left ((hei x t).mp hxt).2.2
      subst t
      obtain ⟨Z, _, huniq⟩ := hf.1.2 y hy
      exact (huniq z htz).trans (huniq Y hyY).symm
    · intro hz
      subst z
      exact (hf.2 x hx X hxX Y).mpr
        ⟨y, hy, (hei x y).mpr ⟨hx, hy, Ne.symm hxy⟩, hyY⟩
  refine ⟨V, W, (fun h => hvw (hi v w V hvV (h.symm ▸ hwW))), ?_, ?_⟩
  · exact row v w hv hw hvw (fun z hz => (ha z).mp hz) V W hvV hwW
  · exact row w v hw hv (Ne.symm hvw) (fun z hz => ((ha z).mp hz).symm) W V hwW hvV

/-- A relative-foundation condition on actual internal nonempty sets. No hierarchy
    construction or existence of models satisfying this condition is assumed proved. -/
def QuineRelativeFoundation (s : U → U → Prop) : Prop :=
  ∀ a, (∃ x, s x a) → ∃ x, s x a ∧
    (SelfSingleton s x ∨ ∀ y, s y a → ¬s y x)

def quineRelativeFoundationSentence : Formula 0 :=
  .all (.impl (.ex (.member 0 1))
    (.ex (.conj (.member 0 1)
      ((Formula.all ((Formula.member 0 1).iffF (.equal 0 1))).disj
        (.all (.impl (.member 0 2) (.impl (.member 0 1) .bottom)))))))

theorem eval_quineRelativeFoundationSentence (s : U → U → Prop) :
    Eval s quineRelativeFoundationSentence Fin.elim0 ↔ QuineRelativeFoundation s := by
  simp only [quineRelativeFoundationSentence, Eval, eval_disj, eval_iffF,
    QuineRelativeFoundation, SelfSingleton]
  rfl

/-- An external well-founded rank decreasing below every non-Quine object
    implies the stated internal relative-foundation sentence. This is not a
    construction of ranks for arbitrary internally nonstandard models. -/
theorem rank_over_quines_relative_foundation {I : Type v} (R : I → I → Prop)
    (hWF : WellFounded R) (rank : U → I)
    (hstep : ∀ x, ¬SelfSingleton s x → ∀ y, s y x → R (rank y) (rank x)) :
    QuineRelativeFoundation s := by
  classical
  intro a hne
  have aux : ∀ i, ∀ x, rank x = i → s x a →
      ∃ z, s z a ∧ (SelfSingleton s z ∨ ∀ y, s y a → ¬s y z) := by
    intro i
    apply hWF.induction i
    intro i ih x hxi hxa
    by_cases hq : SelfSingleton s x
    · exact ⟨x, hxa, Or.inl hq⟩
    by_cases hmin : ∀ y, s y a → ¬s y x
    · exact ⟨x, hxa, Or.inr hmin⟩
    have hy : ∃ y, s y a ∧ s y x := by
      apply Classical.byContradiction
      intro hn
      apply hmin
      intro y hya hyx
      exact hn ⟨y, hya, hyx⟩
    obtain ⟨y, hya, hyx⟩ := hy
    exact ih (rank y) (hxi ▸ hstep x hq y hyx) y rfl hya
  obtain ⟨x, hxa⟩ := hne
  exact aux (rank x) x rfl hxa

theorem quine_relative_foundation_not_bafa (base : BaseCollection s)
    (hRF : QuineRelativeFoundation s) : ¬BAFACode s := by
  intro hB
  obtain ⟨V, W, hVW, hV, hW⟩ := bafa_distinct_two_cycle base hB
  obtain ⟨a, ha⟩ := base.pairing V W
  have hv := (ha V).mpr (Or.inl rfl)
  have hw := (ha W).mpr (Or.inr rfl)
  obtain ⟨x, hx, hq | hmin⟩ := hRF a ⟨V, hv⟩
  · rcases (ha x).mp hx with rfl | rfl
    · exact hVW ((hq W).mp ((hV W).mpr rfl)).symm
    · exact hVW ((hq V).mp ((hW V).mpr rfl))
  · rcases (ha x).mp hx with rfl | rfl
    · exact hmin W hw ((hV W).mpr rfl)
    · exact hmin V hv ((hW V).mpr rfl)

#print axioms bafa_selfSingleton_fiber_unbounded
#print axioms quine_relative_foundation_not_bafa
end FullBridge
