import InternalAFA
namespace FullBridge
universe u

structure BafaModel where
  Carrier : Type u
  mem : Carrier → Carrier → Prop
  base : BaseCollection mem
  boffa : BAFACode mem

structure AfaModel where
  Carrier : Type u
  mem : Carrier → Carrier → Prop
  base : BaseCollection mem
  antiFoundation : AFACode mem

def BafaModel.behaviorQuotient (M : BafaModel.{u}) : AfaModel.{u} where
  Carrier := InternalQuotient M.base
  mem := internalMember M.base
  base := internal_base_model M.base
  antiFoundation := internal_afa M.base M.boffa

theorem bafa_to_afa_model_existence : Nonempty BafaModel.{u} → Nonempty AfaModel.{u} := by
  rintro ⟨M⟩
  exact ⟨M.behaviorQuotient⟩

theorem bridge_target_replacement (M : BafaModel.{u}) :
    Replacement M.behaviorQuotient.mem :=
  collection_separation_replacement _ M.behaviorQuotient.base.collection M.behaviorQuotient.base.separation

theorem bridge_sentence_translation (M : BafaModel.{u}) (p : Formula 0) :
    Eval M.mem (Formula.translate (internalInterpretation M.base).equalFormula
      (internalInterpretation M.base).memberFormula p) Fin.elim0 ↔
      Eval M.behaviorQuotient.mem p Fin.elim0 := by
  have h := internal_formula_translation M.base p Fin.elim0
  have he : (fun i : Fin 0 => internalCode M.base (Fin.elim0 i)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he] at h
  exact h

theorem bridge_translated_afa (M : BafaModel.{u}) :
    Eval M.mem (Formula.translate (internalInterpretation M.base).equalFormula
      (internalInterpretation M.base).memberFormula afaSentence) Fin.elim0 :=
  (bridge_sentence_translation M afaSentence).mpr
    ((eval_afaSentence M.behaviorQuotient.mem).mpr M.behaviorQuotient.antiFoundation)

theorem bridge_parameter_semantics (M : BafaModel.{u}) {n} (p : Formula n)
    (v : Fin n → M.Carrier) :
    Eval M.mem (Formula.translate (internalInterpretation M.base).equalFormula
      (internalInterpretation M.base).memberFormula p) v ↔
      Eval M.behaviorQuotient.mem p (fun i => internalCode M.base (v i)) :=
  internal_formula_translation M.base p v

theorem bridge_external_wellFounded_fiber (M : BafaModel.{u}) {a b : M.Carrier}
    (ha : Acc M.mem a) : internalCode M.base a = internalCode M.base b ↔ a = b :=
  internal_wellFounded_fiber M.base ha

#print axioms bafa_to_afa_model_existence
#print axioms bridge_translated_afa
end FullBridge
