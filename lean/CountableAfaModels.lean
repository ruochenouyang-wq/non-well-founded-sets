import CountableElementaryHull
import ElementaryModelTransfer

namespace FullBridge
universe u

/-- An actual countable AFA model, elementary in the given model and containing
    any prescribed externally enumerated parameters. The source is arbitrary. -/
theorem countable_afa_elementary_model_with_parameters (M : AfaModel.{u})
    (seed : Nat → M.Carrier) :
    ∃ (C : AfaModel.{u}) (enum : Nat → C.Carrier),
      (∀ x, ∃ k, enum k = x) ∧ ∃ j : C.Carrier → M.Carrier,
        ElementaryMap C.mem M.mem j ∧ (∀ k, ∃ x, j x = seed k) := by
  obtain ⟨D, enum, hseed, honto, helem⟩ := countable_elementary_hull M.mem seed
  let t := fun x y : {x // D x} => M.mem x.val y.val
  let C : AfaModel.{u} := ⟨{x // D x}, t,
    elementary_map_base_reflect helem M.base,
    (elementary_map_afa_iff helem).mpr M.antiFoundation⟩
  refine ⟨C, enum, honto, Subtype.val, helem, ?_⟩
  intro k
  exact ⟨⟨seed k, hseed k⟩, rfl⟩

/-- No external enumeration of the original AFA carrier is an input. -/
theorem countable_afa_elementary_model (M : AfaModel.{u}) :
    ∃ (C : AfaModel.{u}) (enum : Nat → C.Carrier),
      (∀ x, ∃ k, enum k = x) ∧ ∃ j : C.Carrier → M.Carrier,
        ElementaryMap C.mem M.mem j := by
  obtain ⟨z, _⟩ := M.base.empty
  obtain ⟨C, enum, honto, j, helem, _⟩ :=
    countable_afa_elementary_model_with_parameters M (fun _ => z)
  exact ⟨C, enum, honto, j, helem⟩

#print axioms countable_afa_elementary_model_with_parameters
#print axioms countable_afa_elementary_model
end FullBridge
