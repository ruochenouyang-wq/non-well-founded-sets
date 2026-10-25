import ModalObservations
import IdentityLoss

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def HasTwoMembers (s : U → U → Prop) (a : U) : Prop :=
  ∃ x y, s x a ∧ s y a ∧ x ≠ y

def twoMembersFormula : Formula 1 :=
  .ex (.ex (.conj (.member 1 2)
    (.conj (.member 0 2) (.impl (.equal 1 0) .bottom))))

theorem eval_two_members_formula (a : U) :
    Eval s twoMembersFormula (fun _ => a) ↔ HasTwoMembers s a := Iff.rfl

theorem self_singleton_not_two_members {a : U} (ha : SelfSingleton s a) :
    ¬HasTwoMembers s a := by
  rintro ⟨x, y, hx, hy, hne⟩
  exact hne (((ha x).mp hx).trans ((ha y).mp hy).symm)

theorem internal_self_singleton (base : BaseCollection s) {a : U}
    (ha : SelfSingleton s a) :
    SelfSingleton (internalMember base) (internalCode base a) := by
  intro X
  constructor
  · intro h
    obtain ⟨x, hx, hxX⟩ := (internal_exact_members base a X).mp h
    exact hxX.symm.trans (congrArg (internalCode base) ((ha x).mp hx))
  · intro h
    exact (internal_exact_members base a X).mpr ⟨a, (ha a).mpr rfl, h.symm⟩

theorem self_singleton_pair_same_code (base : BaseCollection s) {a v w : U}
    (hv : SelfSingleton s v) (hw : SelfSingleton s w)
    (ha : ∀ x, s x a ↔ x = v ∨ x = w) :
    internalCode base a = internalCode base v := by
  apply (internal_code_eq base a v).mpr
  apply internalBehavior_of_children base a v
  · intro x hx
    refine ⟨v, (hv v).mpr rfl, ?_⟩
    rcases (ha x).mp hx with hxv | hxw
    · subst x
      exact internalBehavior_refl base.empty v
    · subst x
      exact (internal_code_eq base w v).mp (selfSingleton_same_code base hw hv)
  · intro y hy
    have hyv := (hv y).mp hy
    subst y
    exact ⟨v, (ha v).mpr (Or.inl rfl), internalBehavior_refl base.empty v⟩

/-- In every full BAFA model, branching cardinality varies inside one quotient
    fiber: a two-element pair and a self-singleton have the same behavior. -/
theorem bafa_counting_fiber (base : BaseCollection s) (hB : BAFACode s) :
    ∃ a b, HasTwoMembers s a ∧ ¬HasTwoMembers s b ∧
      internalCode base a = internalCode base b := by
  obtain ⟨v, w, hne, hv, hw⟩ := bafa_distinct_selfSingletons base hB
  obtain ⟨a, ha⟩ := base.pairing v w
  exact ⟨a, v, ⟨v, w, (ha v).mpr (Or.inl rfl), (ha w).mpr (Or.inr rfl), hne⟩,
    self_singleton_not_two_members hv, self_singleton_pair_same_code base hv hw ha⟩

theorem bafa_modal_counting_counterexample (base : BaseCollection s) (hB : BAFACode s) :
    ∃ a b, HasTwoMembers s a ∧ ¬HasTwoMembers s b ∧
      ∀ p : PureModal, PureModalEval s p a ↔ PureModalEval s p b := by
  obtain ⟨a, b, ha, hb, hab⟩ := bafa_counting_fiber base hB
  exact ⟨a, b, ha, hb, internal_code_same_modal_theory base hab⟩

/-- State definability in the pure ordinary modal language, even within any
    one full BAFA model, fails for 'at least two distinct members'. -/
theorem bafa_two_members_not_pure_modal (base : BaseCollection s) (hB : BAFACode s) :
    ¬∃ p : PureModal, ∀ a, PureModalEval s p a ↔ HasTwoMembers s a := by
  rintro ⟨p, hp⟩
  obtain ⟨a, b, ha, hb, heq⟩ := bafa_modal_counting_counterexample base hB
  exact hb ((hp b).mp ((heq p).mp ((hp a).mpr ha)))

theorem bafa_counting_not_preserved (base : BaseCollection s) (hB : BAFACode s) :
    ∃ a, HasTwoMembers s a ∧
      ¬HasTwoMembers (internalMember base) (internalCode base a) := by
  obtain ⟨v, w, hne, hv, hw⟩ := bafa_distinct_selfSingletons base hB
  obtain ⟨a, ha⟩ := base.pairing v w
  refine ⟨a, ⟨v, w, (ha v).mpr (Or.inl rfl), (ha w).mpr (Or.inr rfl), hne⟩, ?_⟩
  rw [self_singleton_pair_same_code base hv hw ha]
  exact self_singleton_not_two_members (internal_self_singleton base hv)

theorem bafa_first_order_counting_not_preserved (base : BaseCollection s) (hB : BAFACode s) :
    ∃ a, Eval s twoMembersFormula (fun _ => a) ∧
      ¬Eval (internalMember base) twoMembersFormula (fun _ => internalCode base a) :=
  bafa_counting_not_preserved base hB

end FullBridge
