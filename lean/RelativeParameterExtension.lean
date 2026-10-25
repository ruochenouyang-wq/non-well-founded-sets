import RelativeExtensionGraph
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem relative_decoration_code (base : BaseCollection s) {a e f : U}
    (hA : TransitiveCode (internalMember base) (internalCode base a))
    (he : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
      internalMember base (internalCode base y) (internalCode base x))
    (hf : DecorationCode s a e f) :
    ∀ x v, CodedRelation s f x v → internalCode base x = internalCode base v := by
  have hB : Bisimulation (internalMember base)
      (CodedRelation (internalMember base) (internalCode base f)) := by
    intro X V hXV
    obtain ⟨x, v, hx, hxv, rfl, rfl⟩ :=
      (codedRelation_image (internal_exact_members base) hf.1.1 X V).mp hXV
    constructor
    · intro Y hY
      have hYA := hA _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩) Y hY
      obtain ⟨y, hy, rfl⟩ := (internal_exact_members base a Y).mp hYA
      obtain ⟨w, hyw, _⟩ := hf.1.2 y hy
      have hwv := (hf.2 x hx v hxv w).mpr ⟨y, hy, (he x y).mpr ⟨hx, hy, hY⟩, hyw⟩
      exact ⟨internalCode base w, (internal_exact_members base v _).mpr ⟨w, hwv, rfl⟩,
        codedRelation_forward (internal_exact_members base) hyw⟩
    · intro W hW
      obtain ⟨w, hw, rfl⟩ := (internal_exact_members base v W).mp hW
      obtain ⟨y, _, hexy, hyw⟩ := (hf.2 x hx v hxv w).mp hw
      exact ⟨internalCode base y, ((he x y).mp hexy).2.2,
        codedRelation_forward (internal_exact_members base) hyw⟩
  intro x v hxv
  exact internal_coded_coinduction base (internalCode base f) hB _ _
    (codedRelation_forward (internal_exact_members base) hxv)

theorem relative_parameter_extension (base : BaseCollection s)
    (hBAFA : BAFACode s) (hAC : ChoiceCode s)
    {t : U} (ht : TransitiveCode s t) (hti : ParameterInjective base t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    ∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧ ParameterInjective base T := by
  obtain ⟨a, e, haB, heG, hext, hend, hai, he⟩ := relative_graph_lift base hAC ht hti B hB htB
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

theorem relative_parameter_extension_strong (base : BaseCollection s)
    (hBAFA : BAFACode s) (hAC : ChoiceCode s)
    {t : U} (ht : TransitiveCode s t) (hti : InternallyStrongExtensional s t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    ∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧
      InternallyStrongExtensional s T := by
  obtain ⟨T, hT, htT, hTB, hi⟩ := relative_parameter_extension base hBAFA hAC ht
    ((parameter_injective_iff base ht).mpr hti) B hB htB
  exact ⟨T, hT, htT, hTB, (parameter_injective_iff base hT).mp hi⟩

theorem relative_parameter_extension_iff (base : BaseCollection s)
    (hBAFA : BAFACode s) (hAC : ChoiceCode s)
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
    exact relative_parameter_extension base hBAFA hAC ht
      ((parameter_injective_iff base ht).mpr hi) B hB htB

#print axioms relative_parameter_extension_iff
#print axioms relative_parameter_extension
end FullBridge
