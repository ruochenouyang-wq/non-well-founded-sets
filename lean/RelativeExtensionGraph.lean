import RelativeRepresentatives
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem relative_extension_graph (base : BaseCollection s) {a t : U}
    (hta : Subset s t a) (ht : TransitiveCode s t) (hi : ParameterInjective base a)
    (hA : TransitiveCode (internalMember base) (internalCode base a)) :
    ∃ e, GraphCode s a e ∧ GraphExtensionalCode s a e ∧ EndExtensionCode s a e t ∧
      ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
        internalMember base (internalCode base y) (internalCode base x) := by
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
  refine ⟨e, heG, ?_, ⟨hta, ?_⟩, hei⟩
  · intro x hx y hy hrows
    apply hi x y hx hy
    apply internal_extensional base
    intro Z
    have hqx := (internal_exact_members base a (internalCode base x)).mpr ⟨x, hx, rfl⟩
    have hqy := (internal_exact_members base a (internalCode base y)).mpr ⟨y, hy, rfl⟩
    constructor
    · intro hZ
      obtain ⟨z, hz, rfl⟩ := (internal_exact_members base a Z).mp (hA _ hqx Z hZ)
      exact ((hei y z).mp ((hrows z hz).mp ((hei x z).mpr ⟨hx, hz, hZ⟩))).2.2
    · intro hZ
      obtain ⟨z, hz, rfl⟩ := (internal_exact_members base a Z).mp (hA _ hqy Z hZ)
      exact ((hei x z).mp ((hrows z hz).mpr ((hei y z).mpr ⟨hy, hz, hZ⟩))).2.2
  · intro x hxt y
    constructor
    · intro hxy
      obtain ⟨_, hya, hqy⟩ := (hei x y).mp hxy
      obtain ⟨z, hzx, hzq⟩ := (internal_exact_members base x (internalCode base y)).mp hqy
      have hzy := hi z y (hta z (ht x hxt z hzx)) hya hzq
      exact hzy ▸ hzx
    · intro hyx
      exact (hei x y).mpr ⟨hta x hxt, hta y (ht x hxt y hyx),
        (internal_exact_members base x (internalCode base y)).mpr ⟨y, hyx, rfl⟩⟩

theorem relative_graph_lift (base : BaseCollection s) (hAC : ChoiceCode s)
    {t : U} (ht : TransitiveCode s t) (hti : ParameterInjective base t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    ∃ a e, internalCode base a = B ∧ GraphCode s a e ∧ GraphExtensionalCode s a e ∧
      EndExtensionCode s a e t ∧ ParameterInjective base a ∧
      ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
        internalMember base (internalCode base y) (internalCode base x) := by
  obtain ⟨d₀, hd₀⟩ := internal_code_onto base B
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union d₀ t
  have htd : Subset s t d := fun x hx => (hd x).mpr (Or.inr hx)
  have hqd : internalCode base d = B := by
    apply internal_extensional base
    intro X
    constructor
    · intro hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hX
      rcases (hd x).mp hx with hx | hx
      · exact hd₀ ▸ (internal_exact_members base d₀ (internalCode base x)).mpr ⟨x, hx, rfl⟩
      · exact htB _ ((internal_exact_members base t (internalCode base x)).mpr ⟨x, hx, rfl⟩)
    · intro hX
      rw [← hd₀] at hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d₀ X).mp hX
      exact (internal_exact_members base d (internalCode base x)).mpr ⟨x, (hd x).mpr (Or.inl hx), rfl⟩
  obtain ⟨a, _, hta, haq, hai⟩ := relative_internal_representatives base hAC htd hti
  have haB := haq.trans hqd
  have hA : TransitiveCode (internalMember base) (internalCode base a) := haB.symm ▸ hB
  obtain ⟨e, heG, hext, hend, he⟩ := relative_extension_graph base hta ht hai hA
  exact ⟨a, e, haB, heG, hext, hend, hai, he⟩

#print axioms relative_graph_lift
#print axioms relative_extension_graph
end FullBridge
