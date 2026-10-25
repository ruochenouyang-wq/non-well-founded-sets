import CoveredBehaviorAbsoluteness
import TrivialActionRepresentatives
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {w : U}
variable {J : InternalMask s w → U → U}

/-- Inclusion of Hc descends to behavior quotients even though inclusion
    itself need not be elementary between the unquotiented models. -/
def coveredQuotientMap (base : BaseCollection s)
    (hbase : BaseCollection (coveredMaskMember J)) :
    InternalQuotient hbase → InternalQuotient base :=
  Quotient.lift (fun x => internalCode base x.val) (by
    intro x y hxy
    exact (internal_code_eq base x.val y.val).mpr (covered_mask_internal_behavior_forward x y hxy))

theorem covered_quotient_map_code (base : BaseCollection s)
    (hbase : BaseCollection (coveredMaskMember J)) (x : CoveredMaskCarrier s w J) :
    coveredQuotientMap base hbase (internalCode hbase x) = internalCode base x.val := rfl

theorem covered_quotient_map_injective (base : BaseCollection s) {z : U}
    (hw : OmegaCode s z w) (ctx : UniversalActionContext base J)
    (hbase : BaseCollection (coveredMaskMember J)) :
    ∀ X Y, coveredQuotientMap base hbase X = coveredQuotientMap base hbase Y → X = Y := by
  have hcomm : ∀ i j x, J i (J j x) = J j (J i x) := by
    intro i j x
    rw [← ctx.mul, internal_mask_mul_comm base i j, ctx.mul]
  intro X Y
  refine Quotient.inductionOn₂ X Y ?_
  intro x y hxy
  apply Quotient.sound
  exact (covered_mask_internal_behavior_iff base hw ctx.elementary hcomm ctx.involutive ctx.cover x y).mpr
    ((internal_code_eq base x.val y.val).mp hxy)

theorem covered_quotient_map_surjective (base : BaseCollection s) {z : U}
    (hw : OmegaCode s z w) (ctx : UniversalActionContext base J)
    (hbase : BaseCollection (coveredMaskMember J)) :
    ∀ Y, ∃ X, coveredQuotientMap base hbase X = Y := by
  intro Y
  obtain ⟨y, rfl⟩ := internal_code_onto base Y
  obtain ⟨x, hxy, _⟩ := universal_covered_behavior_representative base hw ctx y
  exact ⟨internalCode hbase x, ((internal_code_eq base y x.val).mpr hxy).symm⟩

theorem covered_quotient_map_members (base : BaseCollection s) {z : U}
    (hw : OmegaCode s z w) (ctx : UniversalActionContext base J)
    (hbase : BaseCollection (coveredMaskMember J)) (X Y : InternalQuotient hbase) :
    internalMember hbase X Y ↔
      internalMember base (coveredQuotientMap base hbase X) (coveredQuotientMap base hbase Y) := by
  refine Quotient.inductionOn₂ X Y ?_
  intro x y
  constructor
  · intro h
    obtain ⟨z, hzy, hzx⟩ := (internal_exact_members hbase y _).mp h
    exact (internal_exact_members base y.val _).mpr
      ⟨z.val, hzy, congrArg (coveredQuotientMap base hbase) hzx⟩
  · intro h
    obtain ⟨z, hzy, hzx⟩ := (internal_exact_members base y.val _).mp h
    let Z : CoveredMaskCarrier s w J := ⟨z, internal_mask_covered_member y.property hzy⟩
    exact (internal_exact_members hbase y _).mpr ⟨Z, hzy,
      covered_quotient_map_injective base hw ctx hbase (internalCode hbase Z) (internalCode hbase x) hzx⟩

/-- The canonical map is an isomorphism of the two complete behavior
    structures and therefore preserves every finite first-order formula. -/
theorem covered_quotient_map_elementary (base : BaseCollection s) {z : U}
    (hw : OmegaCode s z w) (ctx : UniversalActionContext base J)
    (hbase : BaseCollection (coveredMaskMember J)) :
    ElementaryMap (internalMember hbase) (internalMember base) (coveredQuotientMap base hbase) := by
  intro n p v
  exact eval_bijective_members (coveredQuotientMap base hbase)
    (covered_quotient_map_injective base hw ctx hbase)
    (covered_quotient_map_surjective base hw ctx hbase)
    (covered_quotient_map_members base hw ctx hbase) p v

theorem covered_quotient_choice_iff (base : BaseCollection s) {z : U}
    (hw : OmegaCode s z w) (ctx : UniversalActionContext base J)
    (hbase : BaseCollection (coveredMaskMember J)) :
    ChoiceCode (internalMember hbase) ↔ ChoiceCode (internalMember base) := by
  have h := covered_quotient_map_elementary base hw ctx hbase choiceSentence Fin.elim0
  have he : (fun i : Fin 0 => coveredQuotientMap base hbase (Fin.elim0 i)) =
      (Fin.elim0 : Fin 0 → InternalQuotient base) := funext (fun i => Fin.elim0 i)
  rw [he, eval_choiceSentence, eval_choiceSentence] at h
  exact h

#print axioms covered_quotient_map_elementary
#print axioms covered_quotient_choice_iff
end FullBridge
