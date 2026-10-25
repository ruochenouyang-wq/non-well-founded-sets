import BafaFixedSolvability
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

-- Quantification is over subsets coded as sets of the model, not external subsets.
def InternallyWellFounded (s : U → U → Prop) (t : U) : Prop :=
  ∀ b, Subset s b t → (∃ x, s x b) → ∃ x, s x b ∧ ∀ y, s y b → ¬s y x

def internallyWellFoundedFormula {n} (t : Fin n) : Formula n :=
  .all (.impl (.all (.impl (.member 0 1) (.member 0 t.succ.succ)))
    (.impl (.ex (.member 0 1))
      (.ex (.conj (.member 0 1)
        (.all (.impl (.member 0 2) (.impl (.member 0 1) .bottom)))))))

theorem eval_internallyWellFoundedFormula (s : U → U → Prop) {n}
    (t : Fin n) (e : Fin n → U) :
    Eval s (internallyWellFoundedFormula t) e ↔ InternallyWellFounded s (e t) := by
  simp only [internallyWellFoundedFormula, Eval, InternallyWellFounded, Subset, cons_zero, cons_succ]
  rfl

def nontrivialFiberFormula : Formula 1 :=
  .ex (.conj (internalBehaviorFormula 1 0) (.impl (.equal 1 0) .bottom))

theorem eval_nontrivialFiberFormula (base : BaseCollection s) (x : U) :
    Eval s nontrivialFiberFormula (cons x Fin.elim0) ↔
      ∃ y, internalCode base x = internalCode base y ∧ x ≠ y := by
  simp only [nontrivialFiberFormula, Eval, eval_internalBehaviorFormula]
  change (∃ y, InternalBehavior s x y ∧ x ≠ y) ↔ _
  simp only [← internal_code_eq base]

theorem internally_wellFounded_member_fiber (base : BaseCollection s) {t : U}
    (ht : TransitiveCode s t) (hwf : InternallyWellFounded s t)
    {x y : U} (hx : s x t) : internalCode base x = internalCode base y ↔ x = y := by
  classical
  obtain ⟨b, hb⟩ := base.separation 0 nontrivialFiberFormula Fin.elim0 t
  have hbi : ∀ z, s z b ↔ s z t ∧ ∃ w, internalCode base z = internalCode base w ∧ z ≠ w := by
    intro z
    exact (hb z).trans (and_congr_right (fun _ => eval_nontrivialFiberFormula base z))
  have hnone : ¬∃ z, s z b := by
    intro hne
    obtain ⟨z, hz, hmin⟩ := hwf b (fun u hu => ((hbi u).mp hu).1) hne
    obtain ⟨hzt, w, hzw, hnezw⟩ := (hbi z).mp hz
    have hgood : ∀ u, s u z → ∀ v, internalCode base u = internalCode base v → u = v := by
      intro u huz v huv
      by_cases heq : u = v
      · exact heq
      · exact False.elim (hmin u ((hbi u).mpr ⟨ht z hzt u huz, v, huv, heq⟩) huz)
    apply hnezw
    apply base.extensional
    intro u
    constructor
    · intro huz
      have hquw := hzw ▸ (internal_exact_members base z _).mpr ⟨u, huz, rfl⟩
      obtain ⟨v, hvw, hvu⟩ := (internal_exact_members base w _).mp hquw
      have huv := hgood u huz v hvu.symm
      exact huv.symm ▸ hvw
    · intro huw
      have hquz := hzw.symm ▸ (internal_exact_members base w _).mpr ⟨u, huw, rfl⟩
      obtain ⟨v, hvz, hvu⟩ := (internal_exact_members base z _).mp hquz
      exact (hgood v hvz u hvu) ▸ hvz
  constructor
  · intro hxy
    by_cases heq : x = y
    · exact heq
    · exact False.elim (hnone ⟨x, (hbi x).mpr ⟨hx, y, hxy, heq⟩⟩)
  · exact congrArg (internalCode base)

theorem internally_wellFounded_root_fiber (base : BaseCollection s) {t y : U}
    (ht : TransitiveCode s t) (hwf : InternallyWellFounded s t) :
    internalCode base t = internalCode base y ↔ t = y := by
  constructor
  · intro hty
    apply base.extensional
    intro x
    constructor
    · intro hxt
      have hqxy := hty ▸ (internal_exact_members base t _).mpr ⟨x, hxt, rfl⟩
      obtain ⟨z, hzy, hzx⟩ := (internal_exact_members base y _).mp hqxy
      exact ((internally_wellFounded_member_fiber base ht hwf hxt).mp hzx.symm).symm ▸ hzy
    · intro hxy
      have hqxt := hty.symm ▸ (internal_exact_members base y _).mpr ⟨x, hxy, rfl⟩
      obtain ⟨z, hzt, hzx⟩ := (internal_exact_members base t _).mp hqxt
      exact (internally_wellFounded_member_fiber base ht hwf hzt).mp hzx ▸ hzt
  · exact congrArg (internalCode base)

theorem internally_wellFounded_membership (base : BaseCollection s) {t x : U}
    (ht : TransitiveCode s t) (hwf : InternallyWellFounded s t) :
    internalMember base (internalCode base x) (internalCode base t) ↔ s x t := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (internal_exact_members base t _).mp h
    exact (internally_wellFounded_member_fiber base ht hwf hy).mp hyx ▸ hy
  · intro h
    exact (internal_exact_members base t _).mpr ⟨x, h, rfl⟩

theorem internally_wellFounded_reflects (base : BaseCollection s) {t : U}
    (hwf : InternallyWellFounded (internalMember base) (internalCode base t)) :
    InternallyWellFounded s t := by
  intro b hbt hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨X, hXb, hmin⟩ := hwf (internalCode base b)
    (subset_forward (internal_exact_members base) hbt)
    ⟨internalCode base x, (internal_exact_members base b _).mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨z, hzb, hzX⟩ := (internal_exact_members base b X).mp hXb
  refine ⟨z, hzb, ?_⟩
  intro y hy hyz
  apply hmin (internalCode base y) ((internal_exact_members base b _).mpr ⟨y, hy, rfl⟩)
  exact hzX ▸ (internal_exact_members base z _).mpr ⟨y, hyz, rfl⟩

theorem internally_wellFounded_transitive_iff (base : BaseCollection s) {t : U}
    (ht : TransitiveCode s t) :
    InternallyWellFounded s t ↔ InternallyWellFounded (internalMember base) (internalCode base t) := by
  constructor
  · intro hwf B hBt hne
    have hi : ParameterInjective base t := fun x y hx _ hxy =>
      (internally_wellFounded_member_fiber base ht hwf hx).mp hxy
    obtain ⟨b, hbt, rfl, _⟩ := subset_lift_unique base hi B hBt
    obtain ⟨X, hX⟩ := hne
    obtain ⟨x, hx, _⟩ := (internal_exact_members base b X).mp hX
    obtain ⟨z, hz, hmin⟩ := hwf b hbt ⟨x, hx⟩
    refine ⟨internalCode base z, (internal_exact_members base b _).mpr ⟨z, hz, rfl⟩, ?_⟩
    intro Y hY hYz
    obtain ⟨y, hy, rfl⟩ := (internal_exact_members base b Y).mp hY
    exact hmin y hy ((parameter_member_reflection base ht hi (hbt y hy) (hbt z hz)).mp hYz)
  · exact internally_wellFounded_reflects base

-- Work with a minimal bad behavior in the target, so source transitivity is not assumed.
theorem target_wellFounded_member_fiber (base : BaseCollection s) {a : U}
    (hT : TransitiveCode (internalMember base) (internalCode base a))
    (hW : InternallyWellFounded (internalMember base) (internalCode base a))
    {x y : U} (hx : s x a) : internalCode base x = internalCode base y ↔ x = y := by
  classical
  obtain ⟨b, hb⟩ := base.separation 0 nontrivialFiberFormula Fin.elim0 a
  have hbi : ∀ z, s z b ↔ s z a ∧ ∃ w, internalCode base z = internalCode base w ∧ z ≠ w := by
    intro z
    exact (hb z).trans (and_congr_right (fun _ => eval_nontrivialFiberFormula base z))
  have hnone : ¬∃ z, s z b := by
    rintro ⟨z₀, hz₀⟩
    obtain ⟨X, hX, hmin⟩ := hW (internalCode base b)
      (subset_forward (internal_exact_members base) (fun z hz => ((hbi z).mp hz).1))
      ⟨internalCode base z₀, (internal_exact_members base b _).mpr ⟨z₀, hz₀, rfl⟩⟩
    obtain ⟨z, hz, hzX⟩ := (internal_exact_members base b X).mp hX
    obtain ⟨hza, w, hzw, hnezw⟩ := (hbi z).mp hz
    have hgood : ∀ u, s u z → ∀ v, internalCode base u = internalCode base v → u = v := by
      intro u huz v huv
      have huqz := (internal_exact_members base z _).mpr ⟨u, huz, rfl⟩
      have huqa := hT _ ((internal_exact_members base a _).mpr ⟨z, hza, rfl⟩) _ huqz
      obtain ⟨k, hka, hkuq⟩ := (internal_exact_members base a _).mp huqa
      have hku : k = u := by
        by_cases h : k = u
        · exact h
        · exact False.elim (hmin (internalCode base u)
            ((internal_exact_members base b _).mpr ⟨k, (hbi k).mpr ⟨hka, u, hkuq, h⟩, hkuq⟩)
            (hzX ▸ huqz))
      have hkv : k = v := by
        by_cases h : k = v
        · exact h
        · exact False.elim (hmin (internalCode base u)
            ((internal_exact_members base b _).mpr
              ⟨k, (hbi k).mpr ⟨hka, v, hkuq.trans huv, h⟩, hkuq⟩)
            (hzX ▸ huqz))
      exact hku.symm.trans hkv
    apply hnezw
    apply base.extensional
    intro u
    constructor
    · intro huz
      have hquw := hzw ▸ (internal_exact_members base z _).mpr ⟨u, huz, rfl⟩
      obtain ⟨v, hvw, hvu⟩ := (internal_exact_members base w _).mp hquw
      exact (hgood u huz v hvu.symm).symm ▸ hvw
    · intro huw
      have hquz := hzw.symm ▸ (internal_exact_members base w _).mpr ⟨u, huw, rfl⟩
      obtain ⟨v, hvz, hvu⟩ := (internal_exact_members base z _).mp hquz
      exact (hgood v hvz u hvu) ▸ hvz
  constructor
  · intro hxy
    by_cases heq : x = y
    · exact heq
    · exact False.elim (hnone ⟨x, (hbi x).mpr ⟨hx, y, hxy, heq⟩⟩)
  · exact congrArg (internalCode base)

theorem target_wellFounded_transitivity_reflects (base : BaseCollection s) {a : U}
    (hT : TransitiveCode (internalMember base) (internalCode base a))
    (hW : InternallyWellFounded (internalMember base) (internalCode base a)) : TransitiveCode s a := by
  intro x hx y hyx
  have hyqa := hT _ ((internal_exact_members base a _).mpr ⟨x, hx, rfl⟩) _
    ((internal_exact_members base x _).mpr ⟨y, hyx, rfl⟩)
  obtain ⟨z, hz, hzy⟩ := (internal_exact_members base a _).mp hyqa
  exact (target_wellFounded_member_fiber base hT hW hz).mp hzy ▸ hz

theorem wellFounded_target_unique_source (base : BaseCollection s)
    (B : InternalQuotient base) (hBT : TransitiveCode (internalMember base) B)
    (hBW : InternallyWellFounded (internalMember base) B) :
    ∃ t, TransitiveCode s t ∧ InternallyWellFounded s t ∧ internalCode base t = B ∧
      ∀ y, internalCode base y = B → y = t := by
  obtain ⟨t, htB⟩ := internal_code_onto base B
  have hT : TransitiveCode (internalMember base) (internalCode base t) := htB.symm ▸ hBT
  have hW : InternallyWellFounded (internalMember base) (internalCode base t) := htB.symm ▸ hBW
  have ht := target_wellFounded_transitivity_reflects base hT hW
  have hwf := internally_wellFounded_reflects base hW
  refine ⟨t, ht, hwf, htB, ?_⟩
  intro y hyB
  exact ((internally_wellFounded_root_fiber base ht hwf).mp (htB.trans hyB.symm)).symm

#print axioms internally_wellFounded_member_fiber
#print axioms internally_wellFounded_transitive_iff
#print axioms wellFounded_target_unique_source
end FullBridge
