import RelativeParameterExtension
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def OverQuotientCode (base : BaseCollection s) (a b f : U) : Prop :=
  FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y →
    s y b ∧ internalCode base x = internalCode base y

def liftComparisonFormula : Formula 4 :=
  .conj (.member 1 2) (.conj (.member 0 3) (internalBehaviorFormula 1 0))

theorem eval_liftComparisonFormula (base : BaseCollection s) (y x a b : U) :
    Eval s liftComparisonFormula (cons y (cons x (cons a (cons b Fin.elim0)))) ↔
      s x a ∧ s y b ∧ internalCode base x = internalCode base y := by
  simp only [liftComparisonFormula, Eval, eval_internalBehaviorFormula]
  change (s x a ∧ s y b ∧ InternalBehavior s x y) ↔ _
  rw [← internal_code_eq base x y]

theorem lift_comparison_exists (base : BaseCollection s) {a b : U}
    (hb : ParameterInjective base b) (hab : internalCode base a = internalCode base b) :
    ∃ f, OverQuotientCode base a b f ∧ RangeCode s a f b := by
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a b
  obtain ⟨f, hf⟩ := relation_comprehension_members base liftComparisonFormula
    (cons a (cons b Fin.elim0)) d
  have hi : ∀ x y, CodedRelation s f x y ↔ s x a ∧ s y b ∧ internalCode base x = internalCode base y := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', _, _, hp', hev⟩ := (hf p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact (eval_liftComparisonFormula base _ _ a b).mp hev
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hf p).mpr ⟨x, y, (hd x).mpr (Or.inl hx), (hd y).mpr (Or.inr hy), hp,
        (eval_liftComparisonFormula base y x a b).mpr ⟨hx, hy, hxy⟩⟩, hp⟩
  refine ⟨f, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨x, y, _, _, hpxy, hev⟩ := (hf p).mp hp
    exact ⟨x, y, ((eval_liftComparisonFormula base y x a b).mp hev).1, hpxy⟩
  · intro x hx
    have hqb := hab ▸ (internal_exact_members base a (internalCode base x)).mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (internal_exact_members base b (internalCode base x)).mp hqb
    refine ⟨y, (hi x y).mpr ⟨hx, hy, hyx.symm⟩, ?_⟩
    intro z hxz
    obtain ⟨_, hz, hxzq⟩ := (hi x z).mp hxz
    exact hb z y hz hy (hxzq.symm.trans hyx.symm)
  · intro x y hxy
    exact ((hi x y).mp hxy).2
  · intro y
    constructor
    · intro hy
      have hqa := hab.symm ▸ (internal_exact_members base b (internalCode base y)).mpr ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := (internal_exact_members base a (internalCode base y)).mp hqa
      exact ⟨x, hx, (hi x y).mpr ⟨hx, hy, hxy⟩⟩
    · rintro ⟨x, _, hxy⟩
      exact ((hi x y).mp hxy).2.1

theorem lift_comparison_unique (base : BaseCollection s) {a b f g : U}
    (hb : ParameterInjective base b) (hf : OverQuotientCode base a b f)
    (hg : OverQuotientCode base a b g) : f = g := by
  apply function_code_extensional base.extensional hf.1 hg.1
  intro x u v hxu hxv
  have hu := hf.2 x u hxu
  have hv := hg.2 x v hxv
  exact hb u v hu.1 hv.1 (hu.2.symm.trans hv.2)

theorem lift_comparison_injective (base : BaseCollection s) {a b f : U}
    (ha : ParameterInjective base a) (hf : OverQuotientCode base a b f) : InjectiveCode s f := by
  intro x y z hxz hyz
  have domain : ∀ u v, CodedRelation s f u v → s u a := by
    rintro u v ⟨p, hp, hpuv⟩
    obtain ⟨u', v', hu', hp'⟩ := hf.1.1 p hp
    have hu := (orderedPair_injective hpuv hp').1
    exact hu ▸ hu'
  exact ha x y (domain x z hxz) (domain y z hyz)
    ((hf.2 x z hxz).2.trans (hf.2 y z hyz).2.symm)

theorem lift_comparison_members (base : BaseCollection s) {a b f x y u v : U}
    (haT : TransitiveCode s a) (hbT : TransitiveCode s b)
    (ha : ParameterInjective base a) (hb : ParameterInjective base b)
    (hf : OverQuotientCode base a b f) (hx : s x a) (hy : s y a)
    (hxu : CodedRelation s f x u) (hyv : CodedRelation s f y v) : s x y ↔ s u v := by
  have hu := hf.2 x u hxu
  have hv := hf.2 y v hyv
  rw [← parameter_member_reflection base haT ha hx hy,
    ← parameter_member_reflection base hbT hb hu.1 hv.1, hu.2, hv.2]

theorem lift_comparison_fixes_overlap (base : BaseCollection s) {a b f x : U}
    (hb : ParameterInjective base b) (hf : OverQuotientCode base a b f)
    (hx : s x a) (hxb : s x b) : CodedRelation s f x x := by
  obtain ⟨y, hxy, _⟩ := hf.1.2 x hx
  have hy := hf.2 x y hxy
  have heq := hb x y hxb hy.1 hy.2
  exact heq.symm ▸ hxy

#print axioms lift_comparison_members
#print axioms lift_comparison_unique
end FullBridge
