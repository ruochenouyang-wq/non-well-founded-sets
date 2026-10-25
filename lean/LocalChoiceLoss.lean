import BafaFiberChoice
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

-- Failure of choice forces a nonempty family, without assuming source AC.
theorem no_choice_family_nonempty (base : BaseCollection s) {a : U}
    (hfail : ¬ ∃ f, ChoiceFunctionCode s a f) : ∃ x, s x a := by
  classical
  by_cases h : ∃ x, s x a
  · exact h
  apply False.elim
  have ha : ∀ x, ¬ s x a := fun x hx => h ⟨x, hx⟩
  obtain ⟨f, hf⟩ := base.empty
  apply hfail
  exact ⟨f, ⟨fun p hp => False.elim (hf p hp), fun x hx => False.elim (ha x hx)⟩,
    fun x hx => False.elim (ha x hx)⟩

theorem selfSingleton_code (base : BaseCollection s) {v : U}
    (hv : SelfSingleton s v) : SelfSingleton (internalMember base) (internalCode base v) := by
  intro X
  rw [internal_exact_members base v X]
  constructor
  · rintro ⟨x, hx, heq⟩
    have h := (hv x).mp hx
    subst x
    exact heq.symm
  · intro h
    exact ⟨v, (hv v).mpr rfl, h.symm⟩

theorem constant_nonempty_family_code (base : BaseCollection s) {a v : U}
    (hne : ∃ x, s x a) (hv : SelfSingleton s v)
    (hc : ∀ x, s x a → internalCode base x = internalCode base v) :
    internalCode base a = internalCode base v := by
  apply internal_extensional base
  intro X
  rw [internal_exact_members base a X, selfSingleton_code base hv X]
  constructor
  · rintro ⟨x, hx, heq⟩
    exact heq.symm.trans (hc x hx)
  · intro h
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, (hc x hx).trans h.symm⟩

theorem selfSingleton_has_choice (base : BaseCollection s) {v : U}
    (hv : SelfSingleton s v) : ∃ f, ChoiceFunctionCode s v f := by
  obtain ⟨p, hp⟩ := orderedPair_exists base.pairing v v
  obtain ⟨f, hf⟩ := base.pairing p p
  have hf' : ∀ z, s z f ↔ z = p := by
    intro z
    exact (hf z).trans ⟨fun h => h.elim id id, fun h => Or.inl h⟩
  have hr : ∀ x y, CodedRelation s f x y ↔ x = v ∧ y = v := by
    intro x y
    constructor
    · rintro ⟨z, hz, hxy⟩
      have hzp := (hf' z).mp hz
      subst z
      exact orderedPair_injective hxy hp
    · rintro ⟨rfl, rfl⟩
      exact ⟨p, (hf' p).mpr rfl, hp⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have hzp := (hf' z).mp hz
    subst z
    exact ⟨v, v, (hv v).mpr rfl, hp⟩
  · intro x hx
    have hxv := (hv x).mp hx
    subst x
    exact ⟨v, (hr v v).mpr ⟨rfl, rfl⟩, fun y hy => ((hr v y).mp hy).2⟩
  · intro x _ y hxy
    obtain ⟨hxv, hyv⟩ := (hr x y).mp hxy
    rw [hxv, hyv]
    exact (hv v).mpr rfl

-- Conditional on a failure witness; this does not construct a model of failure of AC.
theorem bafa_local_choice_failure_collapses (base : BaseCollection s)
    (hBAFA : BAFACode s) {a : U}
    (hne : ∀ x, s x a → ∃ y, s y x)
    (hfail : ¬ ∃ f, ChoiceFunctionCode s a f) :
    ∃ b v, SelfSingleton s v ∧
      (∀ c, s c b → (∃ w, s w c) ∧ ∀ w, s w c → SelfSingleton s w) ∧
      (¬ ∃ f, ChoiceFunctionCode s b f) ∧
      internalCode base b = internalCode base v ∧
      ∃ F, ChoiceFunctionCode (internalMember base) (internalCode base b) F := by
  obtain ⟨d, hd⟩ := base.union a
  obtain ⟨i, hif, hinj, hself⟩ := bafa_selfSingleton_family base hBAFA d
  obtain ⟨b, hb⟩ := coded_image_set_family base a i
  have hbf : ¬ ∃ f, ChoiceFunctionCode s b f := by
    rintro ⟨k, hk⟩
    exact hfail (choice_transports_injection base hinj hb hk)
  have hbc : ∀ c, s c b → (∃ w, s w c) ∧ ∀ w, s w c → SelfSingleton s w := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := (hb c).mp hc
    constructor
    · obtain ⟨y, hy⟩ := hne x hx
      obtain ⟨w, hyw, _⟩ := hif.2 y ((hd y).mpr ⟨x, hx, hy⟩)
      exact ⟨w, (hcx w).mpr ⟨y, hy, hyw⟩⟩
    · intro w hw
      obtain ⟨y, hy, hyw⟩ := (hcx w).mp hw
      exact hself y w ((hd y).mpr ⟨x, hx, hy⟩) hyw
  obtain ⟨c, hc⟩ := no_choice_family_nonempty base hbf
  obtain ⟨v, hvc⟩ := (hbc c hc).1
  have hv := (hbc c hc).2 v hvc
  have hq : internalCode base b = internalCode base v := by
    apply constant_nonempty_family_code base ⟨c, hc⟩ hv
    intro c' hc'
    apply constant_nonempty_family_code base (hbc c' hc').1 hv
    intro w hw
    exact selfSingleton_same_code base ((hbc c' hc').2 w hw) hv
  refine ⟨b, v, hv, hbc, hbf, hq, ?_⟩
  rw [hq]
  exact selfSingleton_has_choice (internal_base_model base) (selfSingleton_code base hv)

#print axioms bafa_local_choice_failure_collapses
end FullBridge
