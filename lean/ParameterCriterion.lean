import IdentityLoss
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def InternallyStrongExtensional (s : U → U → Prop) (a : U) : Prop :=
  ∀ r, GraphCode s a r → Bisimulation s (CodedRelation s r) →
    ∀ x y, CodedRelation s r x y → x = y

def ParameterInjective (base : BaseCollection s) (a : U) : Prop :=
  ∀ x y, s x a → s y a → internalCode base x = internalCode base y → x = y

theorem augmented_bisimulation_restrict (base : BaseCollection s) {a k : U}
    (ha : TransitiveCode s a) (hk : Bisimulation s (WithIdentity (CodedRelation s k))) :
    ∃ r, GraphCode s a r ∧ Bisimulation s (CodedRelation s r) ∧
      ∀ x y, CodedRelation s r x y ↔ s x a ∧ s y a ∧ WithIdentity (CodedRelation s k) x y := by
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base
    (augmentedRelatedFormula (n := 3) 2 1 0) (cons k Fin.elim0) a
  have hi : ∀ x y, CodedRelation s r x y ↔ s x a ∧ s y a ∧ WithIdentity (CodedRelation s k) x y := by
    intro x y
    have h := hr x y
    rw [eval_augmentedRelatedFormula] at h
    exact h
  refine ⟨r, hrG, ?_, hi⟩
  intro x y hxy
  obtain ⟨hx, hy, hkxy⟩ := (hi x y).mp hxy
  constructor
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := (hk x y hkxy).1 z hz
    exact ⟨w, hw, (hi z w).mpr ⟨ha x hx z hz, ha y hy w hw, hzw⟩⟩
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := (hk x y hkxy).2 w hw
    exact ⟨z, hz, (hi z w).mpr ⟨ha x hx z hz, ha y hy w hw, hzw⟩⟩

theorem coded_bisimulation_internalBehavior {r x y : U}
    (hr : Bisimulation s (CodedRelation s r)) (hxy : CodedRelation s r x y) :
    InternalBehavior s x y := by
  refine ⟨r, ?_, Or.inr hxy⟩
  intro u v huv
  rcases huv with rfl | huv
  · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
  constructor
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := (hr u v huv).1 z hz
    exact ⟨w, hw, Or.inr hzw⟩
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := (hr u v huv).2 w hw
    exact ⟨z, hz, Or.inr hzw⟩

theorem parameter_injective_iff (base : BaseCollection s) {a : U}
    (ha : TransitiveCode s a) :
    ParameterInjective base a ↔ InternallyStrongExtensional s a := by
  constructor
  · intro hinj r hrG hrB x y hxy
    have hb := graphCode_endpoints hrG hxy
    exact hinj x y hb.1 hb.2 ((internal_code_eq base x y).mpr
      (coded_bisimulation_internalBehavior hrB hxy))
  · intro hstrong x y hx hy heq
    obtain ⟨k, hk, hkxy⟩ := (internal_code_eq base x y).mp heq
    obtain ⟨r, hrG, hrB, hi⟩ := augmented_bisimulation_restrict base ha hk
    exact hstrong r hrG hrB x y ((hi x y).mpr ⟨hx, hy, hkxy⟩)

theorem parameter_member_reflection (base : BaseCollection s) {a x y : U}
    (ha : TransitiveCode s a) (hi : ParameterInjective base a) (hx : s x a) (hy : s y a) :
    internalMember base (internalCode base x) (internalCode base y) ↔ s x y := by
  constructor
  · intro h
    obtain ⟨z, hz, hzx⟩ := (internal_exact_members base y (internalCode base x)).mp h
    have heq := hi z x (ha y hy z hz) hx hzx
    exact heq ▸ hz
  · intro h
    exact (internal_exact_members base y (internalCode base x)).mpr ⟨x, h, rfl⟩

theorem transitive_parameter_forward (base : BaseCollection s) {a : U} (ha : TransitiveCode s a) :
    TransitiveCode (internalMember base) (internalCode base a) := by
  intro X hX Y hY
  obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a X).mp hX
  obtain ⟨y, hy, rfl⟩ := (internal_exact_members base x Y).mp hY
  exact (internal_exact_members base a (internalCode base y)).mpr ⟨y, ha x hx y hy, rfl⟩

theorem parameter_bijection (base : BaseCollection s) {a : U} (hi : ParameterInjective base a) :
    (∀ X, internalMember base X (internalCode base a) →
      ∃ x, s x a ∧ internalCode base x = X ∧
        ∀ y, s y a → internalCode base y = X → y = x) := by
  intro X hX
  obtain ⟨x, hx, hqx⟩ := (internal_exact_members base a X).mp hX
  exact ⟨x, hx, hqx, fun y hy hqy => hi y x hy hx (hqy.trans hqx.symm)⟩

theorem selfSingleton_parameter_preserved (base : BaseCollection s) {v : U}
    (hv : SelfSingleton s v) :
    TransitiveCode s v ∧ ParameterInjective base v ∧ ¬Acc s v := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    have hxv := (hv x).mp hx
    subst x
    exact hy
  · intro x y hx hy _
    exact ((hv x).mp hx).trans ((hv y).mp hy).symm
  · intro hacc
    have hnot : ∀ z, Acc s z → ¬s z z := by
      intro z hz
      induction hz with
      | intro z _ ih =>
        intro hzz
        exact ih z hzz hzz
    exact hnot v hacc ((hv v).mpr rfl)

#print axioms parameter_injective_iff
#print axioms selfSingleton_parameter_preserved
end FullBridge
