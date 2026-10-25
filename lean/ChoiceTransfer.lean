import KernelClasses
namespace FullBridge
universe u v
variable {U : Type u} {V : Type v} {s : U → U → Prop} {t : V → V → Prop} {q : U → V}

def coordinatedChoiceFormula (eqF : Formula 2) : Formula 5 :=
  .conj (.member 1 2) (.ex (.ex
    (.conj (kernelClassFormula eqF 1 3 4)
      (.conj (relatedFormula 5 1 0) (relatedFormula 6 0 2)))))

theorem eval_coordinatedChoiceFormula (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y) (y x a k h : U) :
    Eval s (coordinatedChoiceFormula eqF) (cons y (cons x (cons a (cons k (cons h Fin.elim0))))) ↔
      s x a ∧ ∃ c r, KernelClass s q a x c ∧ CodedRelation s k c r ∧ CodedRelation s h r y := by
  simp only [coordinatedChoiceFormula, Eval, eval_kernelClassFormula eqF heq, eval_relatedFormula]
  rfl

theorem coordinated_choice_code (base : BaseCollection s) (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y) (a k h : U) :
    ∃ f, (∀ p, s p f → ∃ x y, s x a ∧ IsOrderedPair s p x y) ∧
      ∀ x y, CodedRelation s f x y ↔ s x a ∧
        ∃ c r, KernelClass s q a x c ∧ CodedRelation s k c r ∧ CodedRelation s h r y := by
  obtain ⟨b, hb⟩ := codedRelation_component_bound base.union h
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a b
  obtain ⟨f, hf⟩ := relation_comprehension_members base (coordinatedChoiceFormula eqF)
    (cons a (cons k (cons h Fin.elim0))) d
  have hi : ∀ p, s p f ↔ ∃ x y, s x a ∧ IsOrderedPair s p x y ∧
      ∃ c r, KernelClass s q a x c ∧ CodedRelation s k c r ∧ CodedRelation s h r y := by
    intro p
    constructor
    · intro hp
      obtain ⟨x, y, _, _, hpxy, hev⟩ := (hf p).mp hp
      obtain ⟨hx, hw⟩ := (eval_coordinatedChoiceFormula eqF heq y x a k h).mp hev
      exact ⟨x, y, hx, hpxy, hw⟩
    · rintro ⟨x, y, hx, hpxy, c, r, hc, hk, hh⟩
      exact (hf p).mpr ⟨x, y, (hd x).mpr (Or.inl hx), (hd y).mpr (Or.inr (hb r y hh).2),
        hpxy, (eval_coordinatedChoiceFormula eqF heq y x a k h).mpr ⟨hx, c, r, hc, hk, hh⟩⟩
  refine ⟨f, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, y, hx, hpxy, _⟩ := (hi p).mp hp
    exact ⟨x, y, hx, hpxy⟩
  · intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨x', y', hx, hp', hw⟩ := (hi p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact ⟨hx, hw⟩
    · rintro ⟨hx, hw⟩
      obtain ⟨p, hp⟩ := orderedPair_exists base.pairing x y
      exact ⟨p, (hi p).mpr ⟨x, y, hx, hp, hw⟩, hp⟩

theorem choice_transfer (base : BaseCollection s) (hAC : ChoiceCode s)
    (I : AtomicInterpretation s t q) (onto : ∀ X, ∃ x, q x = X)
    (hm : ExactMembers s t q) : ChoiceCode t := by
  intro A hA
  obtain ⟨a, rfl⟩ := onto A
  have ha : ∀ x, s x a → ∃ y, s y x := by
    intro x hx
    obtain ⟨Y, hY⟩ := hA (q x) ((hm a (q x)).mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, _⟩ := (hm x Y).mp hY
    exact ⟨y, hy⟩
  obtain ⟨h, hh⟩ := hAC a ha
  obtain ⟨b, hb⟩ := kernel_class_family base I.equalFormula I.equal_correct a
  have hbne : ∀ c, s c b → ∃ x, s x c := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := (hb c).mp hc
    exact ⟨x, (hcx x).mpr ⟨hx, rfl⟩⟩
  obtain ⟨k, hk⟩ := hAC b hbne
  obtain ⟨f, hfmem, hf⟩ := coordinated_choice_code base I.equalFormula I.equal_correct a k h
  have htotal : ∀ x, s x a → ∃ y, CodedRelation s f x y := by
    intro x hx
    obtain ⟨c, hc⟩ := kernel_class_exists base I.equalFormula I.equal_correct a x
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    obtain ⟨r, hkr, _⟩ := hk.1.2 c hcb
    have hra := ((hc r).mp (hk.2 c hcb r hkr)).1
    obtain ⟨y, hry, _⟩ := hh.1.2 r hra
    exact ⟨y, (hf x y).mpr ⟨hx, c, r, hc, hkr, hry⟩⟩
  have hcompatible : ∀ x x' y y', q x = q x' →
      CodedRelation s f x y → CodedRelation s f x' y' → y = y' := by
    intro x x' y y' hxx hxy hx'y'
    obtain ⟨hx, c, r, hc, hkr, hry⟩ := (hf x y).mp hxy
    obtain ⟨_, c', r', hc', hkr', hr'y'⟩ := (hf x' y').mp hx'y'
    have hcc := kernel_class_eq base.extensional hc hc' hxx
    subst c'
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    obtain ⟨r₀, _, hru⟩ := hk.1.2 c hcb
    have hrr : r = r' := (hru r hkr).trans (hru r' hkr').symm
    subst r'
    have hra := ((hc r).mp (hk.2 c hcb r hkr)).1
    obtain ⟨y₀, _, hyu⟩ := hh.1.2 r hra
    exact (hyu y hry).trans (hyu y' hr'y').symm
  have hfunction : FunctionCode s a f := by
    refine ⟨hfmem, ?_⟩
    intro x hx
    obtain ⟨y, hxy⟩ := htotal x hx
    exact ⟨y, hxy, fun z hxz => hcompatible x x z y rfl hxz hxy⟩
  refine ⟨q f, functionCode_forward hm hfunction ?_, ?_⟩
  · intro x x' y y' _ _ heq hxy hx'y'
    exact congrArg q (hcompatible x x' y y' heq hxy hx'y')
  · intro X _ Y hXY
    obtain ⟨x, y, _, hxy, rfl, rfl⟩ := (codedRelation_image hm hfmem X Y).mp hXY
    obtain ⟨hx, c, r, hc, hkr, hry⟩ := (hf x y).mp hxy
    have hcb := (hb c).mpr ⟨x, hx, hc⟩
    have hrc := hk.2 c hcb r hkr
    obtain ⟨hra, hrx⟩ := (hc r).mp hrc
    have hyr := hh.2 r hra y hry
    have hqy := (hm r (q y)).mpr ⟨y, hyr, rfl⟩
    exact hrx ▸ hqy

theorem internal_choice (base : BaseCollection s) (hAC : ChoiceCode s) :
    ChoiceCode (internalMember base) :=
  choice_transfer base hAC (internalInterpretation base) (internal_code_onto base) (internal_exact_members base)

#print axioms internal_choice
end FullBridge
