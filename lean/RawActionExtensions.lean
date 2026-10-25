import RawMaskActionRepresentation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def RawActionExtends (s : U → U → Prop) (G D K E L : U) : Prop :=
  Subset s D E ∧ ∀ i x y, s i G →
    (∃ f, CodedRelation s K i f ∧ CodedRelation s f x y) →
    ∃ g, CodedRelation s L i g ∧ CodedRelation s g x y

def rawActionExtendsFormula {n} (G D K E L : Fin n) : Formula n :=
  .conj (powerSubsetFormula D E) (.all (.all (.all
    (.impl (.member 2 G.succ.succ.succ)
      (.impl (jointMaskPointFormula K.succ.succ.succ 2 1 0)
        (jointMaskPointFormula L.succ.succ.succ 2 1 0))))))

theorem eval_rawActionExtendsFormula {n} (G D K E L : Fin n) (v : Fin n → U) :
    Eval s (rawActionExtendsFormula G D K E L) v ↔
      RawActionExtends s (v G) (v D) (v K) (v E) (v L) := by
  simp only [rawActionExtendsFormula, Eval, eval_powerSubsetFormula,
    eval_jointMaskPointFormula, RawActionExtends, cons_succ]
  rfl

theorem raw_action_extends_iff (base : BaseCollection s) {w : U}
    (A Q : CodedMaskAction base w) :
    RawActionExtends s A.masks A.domain A.family Q.domain Q.family ↔ CodedMaskExtends base A Q := by
  constructor
  · rintro ⟨hd, h⟩
    refine ⟨hd, fun i x y hxy => ?_⟩
    exact (action_family_point_iff base Q i).mp
      (h i.val x y ((A.maskMembers i.val).mpr i.property)
        ((action_family_point_iff base A i).mpr hxy))
  · rintro ⟨hd, h⟩
    refine ⟨hd, fun i x y hi hxy => ?_⟩
    let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
    exact (action_family_point_iff base Q I).mpr
      (h I x y ((action_family_point_iff base A I).mp hxy))

def RawActionCovered (s : U → U → Prop) (w G K D x : U) : Prop :=
  ∃ c, Subset s c D ∧ TransitiveCode s c ∧ s x c ∧
    ∀ y, s y c → JointPointSupport s w G K y

theorem eval_rawActionCoveredFormula {n} (w G K D x : Fin n) (v : Fin n → U) :
    Eval s (actionCoveredFormula w G K D x) v ↔
      RawActionCovered s (v w) (v G) (v K) (v D) (v x) := by
  simp only [actionCoveredFormula, Eval, eval_powerSubsetFormula, eval_transitiveFormula,
    eval_actionPointSupportFormula, RawActionCovered, cons_succ]
  rfl

theorem raw_action_covered_iff (base : BaseCollection s) {w x : U} (A : CodedMaskAction base w) :
    RawActionCovered s w A.masks A.family A.domain x ↔ ActionCovered base A x := by
  exact exists_congr (fun c => and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' (fun y => imp_congr Iff.rfl (joint_point_support_action base A))))))

#print axioms raw_action_extends_iff
#print axioms raw_action_covered_iff
end FullBridge
