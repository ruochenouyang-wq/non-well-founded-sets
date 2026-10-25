import PrunedBehaviorEvaluation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

noncomputable def prunedRoundtripMap (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) : InternalQuotient (pruned_quotient_base base hbb) → U :=
  Quotient.lift (prunedEvaluationMap base hA b)
    (fun _ _ h => pruned_internal_behavior_equal_evaluation base hA hbb h)

theorem pruned_roundtrip_code (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) (X : PrunedQuotient base b) :
    prunedRoundtripMap base hA hbb (internalCode (pruned_quotient_base base hbb) X) =
      prunedEvaluationMap base hA b X := rfl

theorem pruned_roundtrip_injective (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) : ∀ X Y,
    prunedRoundtripMap base hA hbb X = prunedRoundtripMap base hA hbb Y → X = Y := by
  intro X Y
  refine Quotient.inductionOn₂ X Y ?_
  intro x y hxy
  apply Quotient.sound
  exact pruned_equal_evaluation_internal_behavior base hA hbb hxy

theorem pruned_roundtrip_surjective (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) : ∀ z,
    ∃ X, prunedRoundtripMap base hA ((hb b).mpr rfl) X = z := by
  intro z
  obtain ⟨X, hX⟩ := pruned_evaluation_surjective base hA hb z
  exact ⟨internalCode (pruned_quotient_base base ((hb b).mpr rfl)) X, hX⟩

theorem pruned_roundtrip_members (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hbb : s b b) (X Y : InternalQuotient (pruned_quotient_base base hbb)) :
    internalMember (pruned_quotient_base base hbb) X Y ↔
      s (prunedRoundtripMap base hA hbb X) (prunedRoundtripMap base hA hbb Y) := by
  refine Quotient.inductionOn₂ X Y ?_
  intro x y
  constructor
  · intro h
    obtain ⟨z, hzy, hzx⟩ := (internal_exact_members (pruned_quotient_base base hbb) y _).mp h
    have heq := congrArg (prunedRoundtripMap base hA hbb) hzx
    exact (pruned_evaluation_exact_members base hA b y _).mpr ⟨z, hzy, heq⟩
  · intro h
    obtain ⟨z, hzy, hzx⟩ := (pruned_evaluation_exact_members base hA b y _).mp h
    exact (internal_exact_members (pruned_quotient_base base hbb) y _).mpr
      ⟨z, hzy, (internal_code_eq _ z x).mpr
        (pruned_equal_evaluation_internal_behavior base hA hbb hzx)⟩

theorem pruned_roundtrip_formula_semantics (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) {n} (p : Formula n)
    (v : Fin n → InternalQuotient (pruned_quotient_base base ((hb b).mpr rfl))) :
    Eval (internalMember (pruned_quotient_base base ((hb b).mpr rfl))) p v ↔
      Eval s p (fun i => prunedRoundtripMap base hA ((hb b).mpr rfl) (v i)) := by
  apply eval_bijective_members
  · exact pruned_roundtrip_injective base hA ((hb b).mpr rfl)
  · exact pruned_roundtrip_surjective base hA hb
  · exact pruned_roundtrip_members base hA ((hb b).mpr rfl)

/-- Reflection concerns this particular reverse construction of an AFA model;
    it is not AC reflection for arbitrary BAFA behavior quotients. -/
theorem pruned_afa_choice_iff (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) :
    ChoiceCode (prunedMember base b) ↔ ChoiceCode s := by
  constructor
  · intro hAC
    have hQ := internal_choice (pruned_quotient_base base ((hb b).mpr rfl)) hAC
    have hv := (pruned_roundtrip_formula_semantics base hA hb choiceSentence Fin.elim0).mp
      ((eval_choiceSentence _).mpr hQ)
    have he : (fun i : Fin 0 => prunedRoundtripMap base hA ((hb b).mpr rfl) (Fin.elim0 i)) =
        (Fin.elim0 : Fin 0 → U) := funext (fun i => Fin.elim0 i)
    rw [he] at hv
    exact (eval_choiceSentence s).mp hv
  · exact fun hAC => pruned_quotient_choice base hAC ((hb b).mpr rfl)

#print axioms pruned_roundtrip_formula_semantics
#print axioms pruned_afa_choice_iff
end FullBridge
