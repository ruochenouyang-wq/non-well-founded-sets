import PrunedFixedDecoration
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem solvability_selfSingleton_exists (base : BaseCollection s) (hS : GraphSolvabilityCode s) :
    ∃ b, SelfSingleton s b := by
  obtain ⟨z, _⟩ := base.empty
  obtain ⟨a, ha⟩ := base.pairing z z
  have hz : s z a := (ha z).mpr (Or.inl rfl)
  obtain ⟨e, hG, he⟩ := normalized_relation_comprehension base
    (Formula.equal (n := 2) 0 1) Fin.elim0 a
  have he' : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧ y = x := fun x y => he x y
  obtain ⟨f, hf⟩ := hS a e hG
  obtain ⟨b, hzb, _⟩ := hf.1.2 z hz
  refine ⟨b, ?_⟩
  intro w
  constructor
  · intro hw
    obtain ⟨y, _, hzy, hyw⟩ := (hf.2 z hz b hzb w).mp hw
    have hyz := ((he' z y).mp hzy).2.2
    subst y
    exact coded_function_value_unique hf.1 hyw hzb
  · intro hwb
    subst w
    exact (hf.2 z hz b hzb b).mpr ⟨z, hz, (he' z z).mpr ⟨hz, hz, rfl⟩, hzb⟩

def FixedSolvableModel.prunedBafa (M : FixedSolvableModel.{u}) (b : M.Carrier)
    (hb : SelfSingleton M.mem b) : BafaModel.{u} where
  Carrier := PrunedQuotient M.base b
  mem := prunedMember M.base b
  base := pruned_quotient_base M.base ((hb b).mpr rfl)
  boffa := pruned_quotient_bafa M.base M.fixedSolvability hb

def AfaModel.prunedBafa (M : AfaModel.{u}) (b : M.Carrier)
    (hb : SelfSingleton M.mem b) : BafaModel.{u} where
  Carrier := PrunedQuotient M.base b
  mem := prunedMember M.base b
  base := pruned_quotient_base M.base ((hb b).mpr rfl)
  boffa := afa_source_pruned_bafa M.base M.antiFoundation hb

theorem fixed_solvability_to_bafa_model_existence :
    Nonempty FixedSolvableModel.{u} → Nonempty BafaModel.{u} := by
  rintro ⟨M⟩
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base
    (fixed_solvability_implies_solvability M.base M.fixedSolvability)
  exact ⟨M.prunedBafa b hb⟩

theorem afa_to_bafa_model_existence : Nonempty AfaModel.{u} → Nonempty BafaModel.{u} := by
  rintro ⟨M⟩
  obtain ⟨b, hb⟩ := solvability_selfSingleton_exists M.base
    (fixed_solvability_implies_solvability M.base (afa_fixed_graph_solvability M.base M.antiFoundation))
  exact ⟨M.prunedBafa b hb⟩

theorem bafa_afa_model_existence_iff : Nonempty BafaModel.{u} ↔ Nonempty AfaModel.{u} :=
  ⟨bafa_to_afa_model_existence, afa_to_bafa_model_existence⟩

def prunedTheoryTranslation {n} (p : Formula n) : Formula (n + 1) :=
  Formula.translateParameters (leastGlobalEqualFormula prunedMemberFormula)
    (leastGlobalMemberFormula prunedMemberFormula) (fun _ => 0) Fin.succ p

theorem pruned_theory_formula_translation (base : BaseCollection s) (b : U) {n}
    (p : Formula n) (v : Fin n → U) :
    Eval s (prunedTheoryTranslation p) (cons b v) ↔
      Eval (prunedMember base b) p (fun i => prunedCode base b (v i)) := by
  have hv := least_global_formula_translation base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) p (fun _ => 0) Fin.succ (cons b v)
    (by intro j; exact Fin.cases rfl (fun k => Fin.elim0 k) j)
  exact hv

theorem pruned_bridge_translated_bafa (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b : U} (hb : SelfSingleton s b) :
    Eval s (prunedTheoryTranslation bafaSentence) (cons b Fin.elim0) := by
  apply (pruned_theory_formula_translation base b bafaSentence Fin.elim0).mpr
  have he : (fun i : Fin 0 => prunedCode base b (Fin.elim0 i)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he]
  exact (eval_bafaSentence _).mpr (pruned_quotient_bafa base hF hb)

theorem pruned_bridge_target_replacement (M : AfaModel.{u}) (b : M.Carrier)
    (hb : SelfSingleton M.mem b) : Replacement (M.prunedBafa b hb).mem :=
  collection_separation_replacement _ (M.prunedBafa b hb).base.collection
    (M.prunedBafa b hb).base.separation

theorem pruned_bridge_target_not_afa (M : AfaModel.{u}) (b : M.Carrier)
    (hb : SelfSingleton M.mem b) : ¬AFACode (M.prunedBafa b hb).mem :=
  afa_source_pruned_not_afa M.base M.antiFoundation hb

#print axioms bafa_afa_model_existence_iff
#print axioms pruned_bridge_translated_bafa
end FullBridge
