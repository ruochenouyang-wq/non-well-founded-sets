import PairTransfer

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem relation_comprehension_members (base : BaseCollection s)
    {n} (p : Formula (n + 2)) (e : Fin n → U) (a : U) :
    ∃ r, ∀ z, s z r ↔ ∃ x y, s x a ∧ s y a ∧ IsOrderedPair s z x y ∧
      Eval s p (cons y (cons x e)) := by
  obtain ⟨pa, hpa⟩ := base.powerset a
  obtain ⟨ppa, hppa⟩ := base.powerset pa
  obtain ⟨r, hr⟩ := base.separation (n + 1) (relationFormula p) (cons a e) ppa
  refine ⟨r, ?_⟩
  intro z
  constructor
  · intro hz
    exact (eval_relationFormula p z a e).mp ((hr z).mp hz).2
  · rintro ⟨x, y, hx, hy, hz, hxy⟩
    exact (hr z).mpr ⟨orderedPair_bound hpa hppa hx hy hz,
      (eval_relationFormula p z a e).mpr ⟨x, y, hx, hy, hz, hxy⟩⟩

theorem internal_graph_lift (base : BaseCollection s)
    (A R : InternalQuotient base) (hG : GraphCode (internalMember base) A R) :
    ∃ a r, internalCode base a = A ∧ internalCode base r = R ∧ GraphCode s a r ∧
      ∀ x y, CodedRelation s r x y ↔ s x a ∧ s y a ∧
        CodedRelation (internalMember base) R (internalCode base x) (internalCode base y) := by
  obtain ⟨a, rfl⟩ := internal_code_onto base A
  obtain ⟨r₀, rfl⟩ := internal_code_onto base R
  let p := Formula.translate (internalInterpretation base).equalFormula
    (internalInterpretation base).memberFormula (relatedFormula (n := 3) 2 1 0)
  have hp : ∀ x y, Eval s p (cons y (cons x (cons r₀ Fin.elim0))) ↔
      CodedRelation (internalMember base) (internalCode base r₀)
        (internalCode base x) (internalCode base y) := by
    intro x y
    have h := internal_formula_translation base (relatedFormula (n := 3) 2 1 0)
      (cons y (cons x (cons r₀ Fin.elim0)))
    rw [eval_relatedFormula] at h
    exact h
  obtain ⟨r, hr⟩ := relation_comprehension_members base p (cons r₀ Fin.elim0) a
  have hg : GraphCode s a r := by
    intro z hz
    obtain ⟨x, y, hx, hy, hzxy, _⟩ := (hr z).mp hz
    exact ⟨x, y, hx, hy, hzxy⟩
  have hq : internalCode base r = internalCode base r₀ := by
    apply internal_extensional base
    intro z
    constructor
    · intro hz
      obtain ⟨v, hv, rfl⟩ := (internal_exact_members base r z).mp hz
      obtain ⟨x, y, _, _, hvxy, hxy⟩ := (hr v).mp hv
      obtain ⟨w, hw, hwxy⟩ := (hp x y).mp hxy
      have heq := orderedPair_unique (internal_extensional base)
        (orderedPair_forward (internal_exact_members base) hvxy) hwxy
      exact heq ▸ hw
    · intro hz
      obtain ⟨X, Y, hXA, hYA, hzXY⟩ := hG z hz
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a X).mp hXA
      obtain ⟨y, hy, rfl⟩ := (internal_exact_members base a Y).mp hYA
      obtain ⟨v, hv⟩ := orderedPair_exists base.pairing x y
      have heq := orderedPair_unique (internal_extensional base)
        (orderedPair_forward (internal_exact_members base) hv) hzXY
      have hvr : s v r := (hr v).mpr ⟨x, y, hx, hy, hv,
        (hp x y).mpr ⟨z, hz, hzXY⟩⟩
      exact (internal_exact_members base r z).mpr ⟨v, hvr, heq⟩
  refine ⟨a, r, rfl, hq, hg, ?_⟩
  intro x y
  constructor
  · rintro ⟨z, hzr, hzxy⟩
    obtain ⟨x', y', hx, hy, hz', hp'⟩ := (hr z).mp hzr
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hzxy hz'
    exact ⟨hx, hy, (hp x y).mp hp'⟩
  · rintro ⟨hx, hy, hxy⟩
    obtain ⟨z, hz⟩ := orderedPair_exists base.pairing x y
    exact ⟨z, (hr z).mpr ⟨x, y, hx, hy, hz, (hp x y).mpr hxy⟩, hz⟩

#print axioms internal_graph_lift
end FullBridge
