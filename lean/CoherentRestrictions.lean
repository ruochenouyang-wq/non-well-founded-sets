import ChoiceFreeParameters
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem subset_image_reflects (base : BaseCollection s) {T a b : U}
    (hi : ParameterInjective base T) (ha : Subset s a T) (hb : Subset s b T) :
    Subset (internalMember base) (internalCode base a) (internalCode base b) ↔
      Subset s a b := by
  constructor
  · intro h x hx
    have hqx := h _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := (internal_exact_members base b _).mp hqx
    exact (hi y x (hb y hy) (ha x hx) hyx) ▸ hy
  · exact subset_forward (internal_exact_members base)

theorem subset_image_injective (base : BaseCollection s) {T a b : U}
    (hi : ParameterInjective base T) (ha : Subset s a T) (hb : Subset s b T)
    (hab : internalCode base a = internalCode base b) : a = b := by
  have hsub : Subset s a b := (subset_image_reflects base hi ha hb).mp
    (fun X hX => hab ▸ hX)
  have hsup : Subset s b a := (subset_image_reflects base hi hb ha).mp
    (fun X hX => hab.symm ▸ hX)
  exact base.extensional a b (fun x => ⟨hsub x, hsup x⟩)

theorem subset_lift_unique (base : BaseCollection s) {T : U}
    (hi : ParameterInjective base T) (B : InternalQuotient base)
    (hB : Subset (internalMember base) B (internalCode base T)) :
    ∃ a, Subset s a T ∧ internalCode base a = B ∧
      ∀ b, Subset s b T → internalCode base b = B → b = a := by
  obtain ⟨a, ha, haq⟩ := subset_representative (internalInterpretation base)
    (internal_code_onto base) (internal_exact_members base) base.separation
    (internal_extensional base) T B hB
  exact ⟨a, ha, haq, fun b hb hbq => subset_image_injective base hi hb ha (hbq.trans haq.symm)⟩

theorem transitivity_reflected_on_subsets (base : BaseCollection s) {T a : U}
    (hT : TransitiveCode s T) (hi : ParameterInjective base T) (ha : Subset s a T) :
    TransitiveCode (internalMember base) (internalCode base a) ↔ TransitiveCode s a := by
  constructor
  · intro h x hx y hy
    have hyT := hT x (ha x hx) y hy
    have hyqa := h _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩) _
      ((internal_exact_members base x _).mpr ⟨y, hy, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := (internal_exact_members base a _).mp hyqa
    exact (hi z y (ha z hz) hyT hzy) ▸ hz
  · exact transitive_parameter_forward base

theorem powerset_parameter_preserved (base : BaseCollection s) {T P : U}
    (hT : TransitiveCode s T) (hi : ParameterInjective base T)
    (hP : ∀ a, s a P ↔ Subset s a T) :
    TransitiveCode s P ∧ ParameterInjective base P ∧
      ∀ B, internalMember base B (internalCode base P) ↔
        Subset (internalMember base) B (internalCode base T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha x hx
    have hxT := (hP a).mp ha x hx
    exact (hP x).mpr (fun y hy => hT x hxT y hy)
  · intro a b ha hb hab
    exact subset_image_injective base hi ((hP a).mp ha) ((hP b).mp hb) hab
  · intro B
    constructor
    · intro hB
      obtain ⟨a, ha, rfl⟩ := (internal_exact_members base P B).mp hB
      exact subset_forward (internal_exact_members base) ((hP a).mp ha)
    · intro hB
      obtain ⟨a, ha, haq, _⟩ := subset_lift_unique base hi B hB
      exact (internal_exact_members base P B).mpr ⟨a, (hP a).mpr ha, haq⟩

theorem transitive_subset_lift_unique (base : BaseCollection s) {T : U}
    (hT : TransitiveCode s T) (hi : ParameterInjective base T)
    (B : InternalQuotient base) (hB : Subset (internalMember base) B (internalCode base T))
    (hBT : TransitiveCode (internalMember base) B) :
    ∃ a, TransitiveCode s a ∧ ParameterInjective base a ∧ Subset s a T ∧
      internalCode base a = B ∧
      ∀ b, Subset s b T → internalCode base b = B → b = a := by
  obtain ⟨a, ha, haq, hu⟩ := subset_lift_unique base hi B hB
  exact ⟨a, (transitivity_reflected_on_subsets base hT hi ha).mp (haq.symm ▸ hBT),
    fun x y hx hy hxy => hi x y (ha x hx) (ha y hy) hxy, ha, haq, hu⟩

/-- The whole internally set-sized family is lifted at once, inside a powerset. -/
theorem subset_family_lift_unique (base : BaseCollection s) {T : U}
    (hT : TransitiveCode s T) (hi : ParameterInjective base T)
    (G : InternalQuotient base)
    (hG : ∀ B, internalMember base B G →
      Subset (internalMember base) B (internalCode base T)) :
    ∃ F, (∀ a, s a F → Subset s a T) ∧ internalCode base F = G ∧
      ParameterFamilyCompatible base F ∧
      (∀ a, s a F → TransitiveCode (internalMember base) (internalCode base a) → TransitiveCode s a) ∧
      ∀ H, (∀ a, s a H → Subset s a T) → internalCode base H = G → H = F := by
  obtain ⟨P, hP⟩ := base.powerset T
  obtain ⟨_, hPi, hPQ⟩ := powerset_parameter_preserved base hT hi hP
  have hGP : Subset (internalMember base) G (internalCode base P) :=
    fun B hB => (hPQ B).mpr (hG B hB)
  obtain ⟨F, hFP, hFq, hu⟩ := subset_lift_unique base hPi G hGP
  have hFT : ∀ a, s a F → Subset s a T := fun a ha => (hP a).mp (hFP a ha)
  refine ⟨F, hFT, hFq, ?_, ?_, ?_⟩
  · intro a b x y ha hb hx hy hxy
    exact hi x y (hFT a ha x hx) (hFT b hb y hy) hxy
  · intro a ha hqa
    exact (transitivity_reflected_on_subsets base hT hi (hFT a ha)).mp hqa
  · intro H hH hHq
    exact hu H (fun a ha => (hP a).mpr (hH a ha)) hHq

theorem simultaneous_exact_restrictions (base : BaseCollection s)
    (hBAFA : BAFACode s) (F : U)
    (hF : ∀ a, s a F → TransitiveCode s a) (hc : ParameterFamilyCompatible base F)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (hFB : ∀ a, s a F → Subset (internalMember base) (internalCode base a) B) :
    ∃ T, TransitiveCode s T ∧ ParameterInjective base T ∧ internalCode base T = B ∧
      (∀ a, s a F → Subset s a T) ∧
      ∀ a, s a F → ∀ b, (Subset s b T ∧ internalCode base b = internalCode base a) ↔ b = a := by
  obtain ⟨T, hT, hFT, hTB, hi⟩ :=
    (simultaneous_parameter_extension_without_choice_iff base hBAFA F hF B hB hFB).mpr hc
  refine ⟨T, hT, hi, hTB, hFT, ?_⟩
  intro a ha b
  constructor
  · rintro ⟨hb, hba⟩
    exact subset_image_injective base hi hb (hFT a ha) hba
  · intro hba
    subst b
    exact ⟨hFT a ha, rfl⟩

#print axioms subset_family_lift_unique
#print axioms simultaneous_exact_restrictions
end FullBridge
