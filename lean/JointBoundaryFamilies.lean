import BoundaryGroupActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem joint_boundary_action_family (base : BaseCollection s) {w D N E b : U}
    (P : CodedMaskAction base w) (Q : CodedMaskGraphAction base P N E)
    {K : BoundaryRenaming s D N b P.domain}
    (F : BoundaryGraphAttachment s D N E b P.domain K) (rho : InternalMask s w → U)
    (hf : ∀ i, FunctionCode s F.domain (rho i))
    (hr : ∀ i X Y, CodedRelation s (rho i) X Y ↔
      AttachmentActionRel s (P.maps i) (Q.maps i) K.code X Y) :
    ∃ K, FunctionCode s P.masks K ∧ ∀ i, CodedRelation s K i.val (rho i) := by
  have hev : ∀ i X Y, Eval s jointAttachmentValueFormula
      (cons Y (cons X (cons i.val (cons P.family (cons Q.family (cons K.code Fin.elim0)))))) ↔
        CodedRelation s (rho i) X Y := by
    intro i X Y
    rw [eval_jointAttachmentValueFormula, hr]
    constructor
    · rintro ⟨p, q, hip, hiq, h⟩
      have hp := coded_function_value_unique P.familyFunction hip (P.mapCodes i)
      have hq := coded_function_value_unique Q.familyFunction hiq (Q.mapCodes i)
      exact hp ▸ hq ▸ h
    · exact fun h => ⟨P.maps i, Q.maps i, P.mapCodes i, Q.mapCodes i, h⟩
  have ht : ∀ i, s i P.masks → ∀ X, s X F.domain → ∃ Y,
      Eval s jointAttachmentValueFormula
        (cons Y (cons X (cons i (cons P.family (cons Q.family (cons K.code Fin.elim0)))))) ∧
      ∀ Z, Eval s jointAttachmentValueFormula
        (cons Z (cons X (cons i (cons P.family (cons Q.family (cons K.code Fin.elim0)))))) → Z = Y := by
    intro i hi X hX
    let j : InternalMask s w := ⟨i, (P.maskMembers i).mp hi⟩
    obtain ⟨Y, hY, hu⟩ := (hf j).2 X hX
    exact ⟨Y, (hev j X Y).mpr hY, fun Z hZ => hu Z ((hev j X Z).mp hZ)⟩
  obtain ⟨K, hK, hKr⟩ := definable_function_family base jointAttachmentValueFormula
    (cons P.family (cons Q.family (cons K.code Fin.elim0))) P.masks F.domain ht
  refine ⟨K, hK, fun i => (hKr i.val (rho i)).mpr ?_⟩
  refine ⟨(P.maskMembers i.val).mpr i.property, hf i, fun X Y => ?_⟩
  exact ⟨fun h => ⟨coded_function_domain (hf i) h, (hev i X Y).mpr h⟩,
    fun h => (hev i X Y).mp h.2⟩


#print axioms joint_boundary_action_family
end FullBridge
