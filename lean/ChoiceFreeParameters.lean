import ChoiceFreeLifting
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Prefer prescribed representatives; retain the old section elsewhere. -/
def unusedParameterFormula : Formula 2 :=
  .impl (.ex (.conj (.member 0 2) (internalBehaviorFormula 0 1))) .bottom

theorem eval_unusedParameterFormula (base : BaseCollection s) (x t : U) :
    Eval s unusedParameterFormula (cons x (cons t Fin.elim0)) ↔
      ¬∃ y, s y t ∧ internalCode base y = internalCode base x := by
  simp only [unusedParameterFormula, Eval, eval_internalBehaviorFormula]
  change (¬∃ y, s y t ∧ InternalBehavior s y x) ↔ _
  simp only [← internal_code_eq base]

theorem replace_section_representatives (base : BaseCollection s) {d t : U}
    (hdi : ParameterInjective base d) (hti : ParameterInjective base t)
    (htd : Subset (internalMember base) (internalCode base t) (internalCode base d)) :
    ∃ a, Subset s t a ∧ internalCode base a = internalCode base d ∧
      ParameterInjective base a := by
  classical
  obtain ⟨c, hc⟩ := base.separation 1 unusedParameterFormula (cons t Fin.elim0) d
  have hci : ∀ x, s x c ↔ s x d ∧
      ¬∃ y, s y t ∧ internalCode base y = internalCode base x := by
    intro x
    exact (hc x).trans (and_congr_right (fun _ => eval_unusedParameterFormula base x t))
  obtain ⟨a, ha⟩ := binary_union_exists base.pairing base.union t c
  have hta : Subset s t a := fun x hx => (ha x).mpr (Or.inl hx)
  refine ⟨a, hta, ?_, ?_⟩
  · apply internal_extensional base
    intro X
    constructor
    · intro hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a X).mp hX
      rcases (ha x).mp hx with hxt | hxc
      · exact htd _ ((internal_exact_members base t _).mpr ⟨x, hxt, rfl⟩)
      · exact (internal_exact_members base d _).mpr ⟨x, ((hci x).mp hxc).1, rfl⟩
    · intro hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hX
      by_cases ho : ∃ y, s y t ∧ internalCode base y = internalCode base x
      · obtain ⟨y, hy, hyx⟩ := ho
        exact (internal_exact_members base a _).mpr ⟨y, hta y hy, hyx⟩
      · exact (internal_exact_members base a _).mpr
          ⟨x, (ha x).mpr (Or.inr ((hci x).mpr ⟨hx, ho⟩)), rfl⟩
  · intro x y hx hy hxy
    rcases (ha x).mp hx with hxt | hxc
    · rcases (ha y).mp hy with hyt | hyc
      · exact hti x y hxt hyt hxy
      · exact False.elim (((hci y).mp hyc).2 ⟨x, hxt, hxy⟩)
    · rcases (ha y).mp hy with hyt | hyc
      · exact False.elim (((hci x).mp hxc).2 ⟨y, hyt, hxy.symm⟩)
      · exact hdi x y ((hci x).mp hxc).1 ((hci y).mp hyc).1 hxy

theorem relative_graph_lift_from_solutions (base : BaseCollection s)
    (hSolve : GraphSolvabilityCode s)
    {t : U} (ht : TransitiveCode s t) (hti : ParameterInjective base t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    ∃ a e, internalCode base a = B ∧ GraphCode s a e ∧ GraphExtensionalCode s a e ∧
      EndExtensionCode s a e t ∧ ParameterInjective base a ∧
      ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
        internalMember base (internalCode base y) (internalCode base x) := by
  obtain ⟨d, _, hdB, hdi⟩ := transitive_lift_from_solutions base hSolve B hB
  obtain ⟨a, hta, had, hai⟩ := replace_section_representatives base hdi hti (hdB.symm ▸ htB)
  have haB := had.trans hdB
  obtain ⟨e, heG, hext, hend, he⟩ := relative_extension_graph base hta ht hai (haB.symm ▸ hB)
  exact ⟨a, e, haB, heG, hext, hend, hai, he⟩

theorem relative_parameter_extension_without_choice (base : BaseCollection s)
    (hBAFA : BAFACode s)
    {t : U} (ht : TransitiveCode s t) (hti : ParameterInjective base t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    ∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧ ParameterInjective base T := by
  obtain ⟨a, e, haB, heG, hext, hend, hai, he⟩ := relative_graph_lift_from_solutions base (bafa_graph_solvability base hBAFA) ht hti B hB htB
  obtain ⟨T, f, hT, hf, _, hrange, hfix⟩ := hBAFA t ht a e heG hext hend
  have hA : TransitiveCode (internalMember base) (internalCode base a) := haB.symm ▸ hB
  have hcode := relative_decoration_code base hA he hf
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · intro x hx
    exact (hrange x).mpr ⟨x, hend.1 x hx, hfix x hx⟩
  · apply internal_extensional base
    intro X
    constructor
    · intro hX
      obtain ⟨v, hv, hvX⟩ := (internal_exact_members base T X).mp hX
      obtain ⟨x, hx, hxv⟩ := (hrange v).mp hv
      have hxX := (hcode x v hxv).trans hvX
      exact haB ▸ (internal_exact_members base a X).mpr ⟨x, hx, hxX⟩
    · intro hX
      rw [← haB] at hX
      obtain ⟨x, hx, hxX⟩ := (internal_exact_members base a X).mp hX
      obtain ⟨v, hxv, _⟩ := hf.1.2 x hx
      exact (internal_exact_members base T X).mpr
        ⟨v, (hrange v).mpr ⟨x, hx, hxv⟩, (hcode x v hxv).symm.trans hxX⟩
  · intro v w hv hw hvw
    obtain ⟨x, hx, hxv⟩ := (hrange v).mp hv
    obtain ⟨y, hy, hyw⟩ := (hrange w).mp hw
    have hxy := hai x y hx hy ((hcode x v hxv).trans (hvw.trans (hcode y w hyw).symm))
    subst y
    obtain ⟨v₀, _, hu⟩ := hf.1.2 x hx
    exact (hu v hxv).trans (hu w hyw).symm

theorem relative_parameter_extension_without_choice_iff (base : BaseCollection s)
    (hBAFA : BAFACode s)
    {t : U} (ht : TransitiveCode s t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    (∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧ ParameterInjective base T) ↔
      InternallyStrongExtensional s t := by
  constructor
  · rintro ⟨T, _, htT, _, hi⟩
    apply (parameter_injective_iff base ht).mp
    intro x y hx hy hxy
    exact hi x y (htT x hx) (htT y hy) hxy
  · intro hi
    exact relative_parameter_extension_without_choice base hBAFA ht
      ((parameter_injective_iff base ht).mpr hi) B hB htB

theorem simultaneous_parameter_extension_without_choice_iff (base : BaseCollection s)
    (hBAFA : BAFACode s) (F : U)
    (hF : ∀ a, s a F → TransitiveCode s a)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (hFB : ∀ a, s a F → Subset (internalMember base) (internalCode base a) B) :
    (∃ T, TransitiveCode s T ∧ (∀ a, s a F → Subset s a T) ∧
      internalCode base T = B ∧ ParameterInjective base T) ↔
      ParameterFamilyCompatible base F := by
  constructor
  · rintro ⟨T, _, hFT, _, hi⟩ a b x y ha hb hx hy hxy
    exact hi x y (hFT a ha x hx) (hFT b hb y hy) hxy
  · intro hc
    obtain ⟨d, hd⟩ := base.union F
    have hdT := transitive_parameter_family_union hd hF
    have hi := (parameter_family_union_criterion base hd).mpr hc
    have hdB : Subset (internalMember base) (internalCode base d) B := by
      intro X hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hX
      obtain ⟨a, ha, hxa⟩ := (hd x).mp hx
      exact hFB a ha _ ((internal_exact_members base a _).mpr ⟨x, hxa, rfl⟩)
    obtain ⟨T, hT, hdT', hTB, hTi⟩ := relative_parameter_extension_without_choice base hBAFA hdT hi B hB hdB
    exact ⟨T, hT, fun a ha x hx => hdT' x ((hd x).mpr ⟨a, ha, hx⟩), hTB, hTi⟩


#print axioms relative_parameter_extension_without_choice
#print axioms simultaneous_parameter_extension_without_choice_iff
end FullBridge
