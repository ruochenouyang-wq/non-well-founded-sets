import ParameterSemantics
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem decoration_transitive_range (base : BaseCollection s) {a e f : U}
    (hf : DecorationCode s a e f) :
    ∃ T, TransitiveCode s T ∧ RangeCode s a f T := by
  obtain ⟨d, hd⟩ := codedRelation_component_bound base.union f
  obtain ⟨T, hT⟩ := base.separation 1
    (Formula.ex (relatedFormula (n := 3) 2 0 1)) (cons f Fin.elim0) d
  have hi : ∀ y, s y T ↔ ∃ x, CodedRelation s f x y := by
    intro y
    have h := hT y
    simp only [Eval, eval_relatedFormula] at h
    change s y T ↔ s y d ∧ ∃ x, CodedRelation s f x y at h
    constructor
    · exact fun hy => ((h.mp hy).2)
    · rintro ⟨x, hxy⟩
      exact h.mpr ⟨(hd x y hxy).2, x, hxy⟩
  have domain : ∀ x y, CodedRelation s f x y → s x a := by
    rintro x y ⟨p, hp, hpxy⟩
    obtain ⟨x', y', hx', hp'⟩ := hf.1.1 p hp
    exact (orderedPair_injective hpxy hp').1 ▸ hx'
  refine ⟨T, ?_, ?_⟩
  · intro y hy z hz
    obtain ⟨x, hxy⟩ := (hi y).mp hy
    obtain ⟨w, _, _, hwz⟩ := (hf.2 x (domain x y hxy) y hxy z).mp hz
    exact (hi z).mpr ⟨w, hwz⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hxy⟩ := (hi y).mp hy
      exact ⟨x, domain x y hxy, hxy⟩
    · rintro ⟨x, _, hxy⟩
      exact (hi y).mpr ⟨x, hxy⟩

theorem transitive_lift_from_solutions (base : BaseCollection s)
    (hSolve : GraphSolvabilityCode s)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B) :
    ∃ T, TransitiveCode s T ∧ internalCode base T = B ∧ ParameterInjective base T := by
  obtain ⟨a, ha⟩ := internal_code_onto base B
  have hA : TransitiveCode (internalMember base) (internalCode base a) := ha.symm ▸ hB
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base
    (internalInterpretation base).memberFormula Fin.elim0 a
  have hei : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
      internalMember base (internalCode base y) (internalCode base x) := by
    intro x y
    have h := he x y
    change CodedRelation s e x y ↔ s x a ∧ s y a ∧
      Eval s (internalInterpretation base).memberFormula (pairEnv y x) at h
    rw [(internalInterpretation base).member_correct] at h
    exact h
  obtain ⟨f, hf⟩ := hSolve a e heG
  have hq := relative_decoration_code base hA hei hf
  obtain ⟨T, hT, hFT⟩ := decoration_transitive_range base hf
  refine ⟨T, hT, ?_, ?_⟩
  · apply internal_extensional base
    intro X
    constructor
    · intro hX
      obtain ⟨v, hv, hvX⟩ := (internal_exact_members base T X).mp hX
      obtain ⟨x, hx, hxv⟩ := (hFT v).mp hv
      exact ha ▸ (internal_exact_members base a X).mpr ⟨x, hx, (hq x v hxv).trans hvX⟩
    · intro hX
      rw [← ha] at hX
      obtain ⟨x, hx, hxX⟩ := (internal_exact_members base a X).mp hX
      obtain ⟨v, hxv, _⟩ := hf.1.2 x hx
      exact (internal_exact_members base T X).mpr
        ⟨v, (hFT v).mpr ⟨x, hx, hxv⟩, (hq x v hxv).symm.trans hxX⟩
  · intro v w hv hw hvw
    obtain ⟨x, hx, hxv⟩ := (hFT v).mp hv
    obtain ⟨y, hy, hyw⟩ := (hFT w).mp hw
    have hxy := (hq x v hxv).trans (hvw.trans (hq y w hyw).symm)
    apply decoration_equal_rows base.extensional hf hx hy ?_ hxv hyw
    intro z
    rw [hei x z, hei y z, hxy]
    exact and_congr (iff_of_true hx hy) Iff.rfl

theorem transitive_lift_without_choice (base : BaseCollection s) (hBAFA : BAFACode s)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B) :
    ∃ T, TransitiveCode s T ∧ internalCode base T = B ∧ ParameterInjective base T :=
  transitive_lift_from_solutions base (bafa_graph_solvability base hBAFA) B hB

#print axioms transitive_lift_from_solutions
#print axioms transitive_lift_without_choice
end FullBridge
