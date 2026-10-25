import LiftComparison
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def graphSolvabilitySentence : Formula 0 :=
  .all (.all (.impl (graphCodeFormula 1 0) (.ex (decorationCodeFormula 2 1 0))))

theorem eval_graphSolvabilitySentence (s : U → U → Prop) :
    Eval s graphSolvabilitySentence Fin.elim0 ↔ GraphSolvabilityCode s := by
  simp only [graphSolvabilitySentence, Eval, eval_graphCodeFormula,
    eval_decorationCodeFormula, GraphSolvabilityCode]
  rfl

theorem internal_solvability_from_solutions (base : BaseCollection s)
    (hSolve : GraphSolvabilityCode s) : GraphSolvabilityCode (internalMember base) := by
  intro A R hG
  obtain ⟨a, e, rfl, rfl, heG, he⟩ := internal_graph_lift base A R hG
  obtain ⟨f, hf⟩ := hSolve a e heG
  exact ⟨internalCode base f,
    decoration_forward_saturated (internal_exact_members base) base.extensional hf he⟩

theorem internal_afa_from_solutions (base : BaseCollection s)
    (hSolve : GraphSolvabilityCode s) : AFACode (internalMember base) := by
  intro A E hG
  obtain ⟨F, hF⟩ := internal_solvability_from_solutions base hSolve A E hG
  exact ⟨F, hF, fun G hG => internal_decoration_unique base hG hF⟩

structure SolvableChoiceModel where
  Carrier : Type u
  mem : Carrier → Carrier → Prop
  base : BaseCollection mem
  solvability : GraphSolvabilityCode mem
  choice : ChoiceCode mem

def SolvableChoiceModel.behaviorQuotient (M : SolvableChoiceModel.{u}) : AfaChoiceModel.{u} where
  Carrier := InternalQuotient M.base
  mem := internalMember M.base
  base := internal_base_model M.base
  antiFoundation := internal_afa_from_solutions M.base M.solvability
  choice := internal_choice M.base M.choice

theorem solvability_to_afa_model_existence :
    Nonempty SolvableChoiceModel.{u} → Nonempty AfaChoiceModel.{u} := by
  rintro ⟨M⟩
  exact ⟨M.behaviorQuotient⟩

def BafaChoiceModel.toSolvable (M : BafaChoiceModel.{u}) : SolvableChoiceModel.{u} where
  Carrier := M.Carrier
  mem := M.mem
  base := M.base
  solvability := bafa_graph_solvability M.base M.boffa
  choice := M.choice

theorem bafa_quotient_factors_through_solvability (M : BafaChoiceModel.{u}) :
    M.toSolvable.behaviorQuotient = M.behaviorQuotient := by
  rfl

#print axioms internal_afa_from_solutions
#print axioms bafa_quotient_factors_through_solvability
end FullBridge
