import FreshParameterLabels
namespace FullBridge
universe u v
variable {U : Type u} {V : Type v} {s : U → U → Prop} {q : U → V}

def relativeRepresentativeFormula (eqF : Formula 2) : Formula 4 :=
  (Formula.member 0 2).disj
    (.conj (.impl (.ex (.conj (.member 0 3) (eqF.rename (atomRename 0 1)))) .bottom)
      (.ex (.conj (kernelClassFormula eqF 0 1 2) (relatedFormula 4 0 1))))

theorem eval_relativeRepresentativeFormula (eqF : Formula 2)
    (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y) (x d t k : U) :
    Eval s (relativeRepresentativeFormula eqF) (cons x (cons d (cons t (cons k Fin.elim0)))) ↔
      s x t ∨ ((¬∃ y, s y t ∧ q y = q x) ∧
        ∃ c, KernelClass s q d x c ∧ CodedRelation s k c x) := by
  simp only [relativeRepresentativeFormula, eval_disj, Eval, eval_rename, atom_env,
    heq, eval_kernelClassFormula eqF heq, eval_relatedFormula]
  rfl

theorem relative_representatives (base : BaseCollection s) (hAC : ChoiceCode s)
    (eqF : Formula 2) (heq : ∀ x y, Eval s eqF (pairEnv x y) ↔ q x = q y)
    {d t : U} (htd : Subset s t d)
    (hti : ∀ x y, s x t → s y t → q x = q y → x = y) :
    ∃ a, Subset s a d ∧ Subset s t a ∧
      (∀ x, s x d → ∃ y, s y a ∧ q y = q x) ∧
      ∀ x y, s x a → s y a → q x = q y → x = y := by
  classical
  obtain ⟨b, hb⟩ := kernel_class_family base eqF heq d
  have hbne : ∀ c, s c b → ∃ x, s x c := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := (hb c).mp hc
    exact ⟨x, (hcx x).mpr ⟨hx, rfl⟩⟩
  obtain ⟨k, hk⟩ := hAC b hbne
  obtain ⟨a, ha⟩ := base.separation 3 (relativeRepresentativeFormula eqF)
    (cons d (cons t (cons k Fin.elim0))) d
  have hai : ∀ x, s x a ↔ s x d ∧ (s x t ∨ ((¬∃ y, s y t ∧ q y = q x) ∧
      ∃ c, KernelClass s q d x c ∧ CodedRelation s k c x)) := by
    intro x
    have h := ha x
    rw [eval_relativeRepresentativeFormula eqF heq] at h
    exact h
  have hta : Subset s t a := by
    intro x hx
    exact (hai x).mpr ⟨htd x hx, Or.inl hx⟩
  refine ⟨a, (fun x hx => ((hai x).mp hx).1), hta, ?_, ?_⟩
  · intro x hx
    by_cases hOld : ∃ y, s y t ∧ q y = q x
    · obtain ⟨y, hy, hyx⟩ := hOld
      exact ⟨y, hta y hy, hyx⟩
    · obtain ⟨c, hc⟩ := kernel_class_exists base eqF heq d x
      have hcb := (hb c).mpr ⟨x, hx, hc⟩
      obtain ⟨y, hky, _⟩ := hk.1.2 c hcb
      obtain ⟨hyd, hyx⟩ := (hc y).mp (hk.2 c hcb y hky)
      have hcy : KernelClass s q d y c := by
        intro z
        rw [hc z, hyx]
      have hNew : ¬∃ z, s z t ∧ q z = q y := by
        rintro ⟨z, hz, hzy⟩
        exact hOld ⟨z, hz, hzy.trans hyx⟩
      exact ⟨y, (hai y).mpr ⟨hyd, Or.inr ⟨hNew, c, hcy, hky⟩⟩, hyx⟩
  · intro x y hxa hya hxy
    obtain ⟨hxd, hx⟩ := (hai x).mp hxa
    obtain ⟨_, hy⟩ := (hai y).mp hya
    rcases hx with hxt | ⟨hxNew, c, hc, hkcx⟩
    · rcases hy with hyt | ⟨hyNew, _⟩
      · exact hti x y hxt hyt hxy
      · exact False.elim (hyNew ⟨x, hxt, hxy⟩)
    · rcases hy with hyt | ⟨_, c', hc', hkc'y⟩
      · exact False.elim (hxNew ⟨y, hyt, hxy.symm⟩)
      · have hcc := kernel_class_eq base.extensional hc hc' hxy
        subst c'
        obtain ⟨z, _, hu⟩ := hk.1.2 c ((hb c).mpr ⟨x, hxd, hc⟩)
        exact (hu x hkcx).trans (hu y hkc'y).symm

theorem relative_internal_representatives (base : BaseCollection s) (hAC : ChoiceCode s)
    {d t : U} (htd : Subset s t d) (hti : ParameterInjective base t) :
    ∃ a, Subset s a d ∧ Subset s t a ∧ internalCode base a = internalCode base d ∧
      ParameterInjective base a := by
  obtain ⟨a, had, hta, hcover, hinj⟩ := relative_representatives base hAC
    (internalInterpretation base).equalFormula (internalInterpretation base).equal_correct htd hti
  refine ⟨a, had, hta, ?_, hinj⟩
  apply internal_extensional base
  intro X
  constructor
  · intro hX
    obtain ⟨x, hx, hqx⟩ := (internal_exact_members base a X).mp hX
    exact (internal_exact_members base d X).mpr ⟨x, had x hx, hqx⟩
  · intro hX
    obtain ⟨x, hx, hqx⟩ := (internal_exact_members base d X).mp hX
    obtain ⟨y, hy, hyx⟩ := hcover x hx
    exact (internal_exact_members base a X).mpr ⟨y, hy, hyx.trans hqx⟩

#print axioms relative_internal_representatives
end FullBridge
