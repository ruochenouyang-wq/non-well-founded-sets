import UnrestrictedNoChoiceTransfer
import ModalCountingBoundary
import ModalPredicateDescent

namespace FullBridge
universe u v

/-- Unlike general first-order formulas, pure modal standard translations
    already have the same meaning before applying the behavior translation. -/
theorem pure_modal_behavior_translation_fixed {U : Type u} {s : U → U → Prop}
    (base : BaseCollection s) (p : PureModal) {n : Nat} (i : Fin n) (e : Fin n → U) :
    Eval s (behaviorTranslation (pureModalTranslate p i)) e ↔
      Eval s (pureModalTranslate p i) e := by
  exact (uniform_behavior_translation base (pureModalTranslate p i) e).trans
    ((pure_modal_standard_translation (internalMember base) p i
      (fun j => internalCode base (e j))).trans
      ((internal_pure_modal_invariance base p (e i)).symm.trans
        (pure_modal_standard_translation s p i e).symm))

theorem elementary_map_pure_modal_invariance {U : Type u} {V : Type v}
    {s : U → U → Prop} {t : V → V → Prop} {j : U → V}
    (hj : ElementaryMap s t j) (p : PureModal) (a : U) :
    PureModalEval s p a ↔ PureModalEval t p (j a) := by
  exact (pure_modal_standard_translation s p (0 : Fin 1) (fun _ => a)).symm.trans
    ((hj (pureModalTranslate p (0 : Fin 1)) (fun _ => a)).trans
      (pure_modal_standard_translation t p (0 : Fin 1) (fun _ => j a)))

/-- A concrete property outside the image of predicate pullback. -/
theorem bafa_counting_predicate_not_descend {U : Type u} {s : U → U → Prop}
    (base : BaseCollection s) (hB : BAFACode s) :
    ¬∃ P : InternalQuotient base → Prop,
      PredicatePullback (internalCode base) P = HasTwoMembers s := by
  intro h
  have hi := (internal_predicate_descent_iff base (HasTwoMembers s)).mp h
  obtain ⟨a, b, ha, hb, hab⟩ := bafa_counting_fiber base hB
  exact hb ((hi a b ((internal_code_eq base a b).mp hab)).mp ha)

/-- Synthesis with stage 9: every AFA model and prescribed countable seed has
    a full no-choice BAFA source carrying a pure-modal-truth-preserving map
    into it. This map covers the seed and erases a branching-count distinction.
    No global surjectivity or exact-member property of this map is asserted. -/
theorem afa_no_choice_modal_cover_with_parameters (M : AfaModel.{u})
    (seed : Nat → M.Carrier) :
    ∃ N : BafaModel.{u}, ¬ChoiceCode N.mem ∧
      ∃ g : N.Carrier → M.Carrier,
        (∀ p : PureModal, ∀ a, PureModalEval N.mem p a ↔ PureModalEval M.mem p (g a)) ∧
        (∀ k, ∃ a, g a = seed k) ∧
        (∃ a b, HasTwoMembers N.mem a ∧ ¬HasTwoMembers N.mem b ∧ g a = g b) := by
  obtain ⟨N, hnc, j, hj, hseed⟩ := afa_no_choice_elementary_lift_with_parameters M seed
  refine ⟨N, hnc, fun a => j (internalCode N.base a), ?_, ?_, ?_⟩
  · intro p a
    exact (internal_pure_modal_invariance N.base p a).trans
      (elementary_map_pure_modal_invariance hj p (internalCode N.base a))
  · intro k
    obtain ⟨X, hX⟩ := hseed k
    obtain ⟨a, rfl⟩ := internal_code_onto N.base X
    exact ⟨a, hX⟩
  · obtain ⟨a, b, ha, hb, hab⟩ := bafa_counting_fiber N.base N.boffa
    exact ⟨a, b, ha, hb, congrArg j hab⟩

end FullBridge
