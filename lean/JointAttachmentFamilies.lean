import BafaEquivariantAttachments
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An actual source family codes the graph action of every internal mask. -/
structure CodedMaskGraphAction (base : BaseCollection s) {w : U}
    (P : CodedMaskAction base w) (a r : U) where
  family : U
  familyFunction : FunctionCode s P.masks family
  maps : InternalMask s w → U
  mapCodes : ∀ i, CodedRelation s family i.val (maps i)
  iso : ∀ i, GraphIsoCode s a r a r (maps i)
  one : ∀ x y, CodedRelation s (maps (internalMaskOne base w)) x y → x = y
  mul : ∀ i j x z, CodedRelation s (maps (internalMaskMul base i j)) x z ↔
    ∃ y, CodedRelation s (maps j) x y ∧ CodedRelation s (maps i) y z

def jointAttachmentRename : Fin 5 → Fin 8 :=
  Fin.cases 2 (Fin.cases 3 (Fin.cases 1 (Fin.cases 0 (fun _ => 7))))

theorem joint_attachment_env (q p Y X i K Q k : U) :
    (fun j => cons q (cons p (cons Y (cons X (cons i (cons K (cons Q (cons k Fin.elim0)))))))
      (jointAttachmentRename j)) = cons Y (cons X (cons p (cons q (cons k Fin.elim0)))) := by
  funext j
  refine Fin.cases rfl (fun j => Fin.cases rfl (fun j => Fin.cases rfl
    (fun j => Fin.cases rfl (fun j => ?_) j) j) j) j
  exact Fin.cases rfl (fun j => Fin.elim0 j) j

/-- Free variables [output,input,index,old-family,graph-family,copy]. -/
def jointAttachmentValueFormula : Formula 6 :=
  .ex (.ex (.conj (relatedFormula 5 4 1) (.conj (relatedFormula 6 4 0)
    (attachmentActionFormula.rename jointAttachmentRename))))

theorem eval_jointAttachmentValueFormula (Y X i K Q k : U) :
    Eval s jointAttachmentValueFormula (cons Y (cons X (cons i (cons K (cons Q (cons k Fin.elim0)))))) ↔
      ∃ p q, CodedRelation s K i p ∧ CodedRelation s Q i q ∧ AttachmentActionRel s p q k X Y := by
  simp only [jointAttachmentValueFormula, Eval, eval_relatedFormula, eval_rename,
    joint_attachment_env, eval_attachmentActionFormula]
  rfl

theorem joint_attachment_action_family (base : BaseCollection s) {w t a r : U}
    (P : CodedMaskAction base w) (Q : CodedMaskGraphAction base P a r)
    (D : MemberGraphAttachment s t P.domain a r) (rho : InternalMask s w → U)
    (hf : ∀ i, FunctionCode s D.domain (rho i))
    (hr : ∀ i X Y, CodedRelation s (rho i) X Y ↔
      AttachmentActionRel s (P.maps i) (Q.maps i) D.copy X Y) :
    ∃ K, FunctionCode s P.masks K ∧ ∀ i, CodedRelation s K i.val (rho i) := by
  have hev : ∀ i X Y, Eval s jointAttachmentValueFormula
      (cons Y (cons X (cons i.val (cons P.family (cons Q.family (cons D.copy Fin.elim0)))))) ↔
        CodedRelation s (rho i) X Y := by
    intro i X Y
    rw [eval_jointAttachmentValueFormula, hr]
    constructor
    · rintro ⟨p, q, hip, hiq, h⟩
      have hp := coded_function_value_unique P.familyFunction hip (P.mapCodes i)
      have hq := coded_function_value_unique Q.familyFunction hiq (Q.mapCodes i)
      exact hp ▸ hq ▸ h
    · exact fun h => ⟨P.maps i, Q.maps i, P.mapCodes i, Q.mapCodes i, h⟩
  have ht : ∀ i, s i P.masks → ∀ X, s X D.domain → ∃ Y,
      Eval s jointAttachmentValueFormula
        (cons Y (cons X (cons i (cons P.family (cons Q.family (cons D.copy Fin.elim0)))))) ∧
      ∀ Z, Eval s jointAttachmentValueFormula
        (cons Z (cons X (cons i (cons P.family (cons Q.family (cons D.copy Fin.elim0)))))) → Z = Y := by
    intro i hi X hX
    let j : InternalMask s w := ⟨i, (P.maskMembers i).mp hi⟩
    obtain ⟨Y, hY, hu⟩ := (hf j).2 X hX
    exact ⟨Y, (hev j X Y).mpr hY, fun Z hZ => hu Z ((hev j X Z).mp hZ)⟩
  obtain ⟨K, hK, hKr⟩ := definable_function_family base jointAttachmentValueFormula
    (cons P.family (cons Q.family (cons D.copy Fin.elim0))) P.masks D.domain ht
  refine ⟨K, hK, fun i => (hKr i.val (rho i)).mpr ?_⟩
  refine ⟨(P.maskMembers i.val).mpr i.property, hf i, fun X Y => ?_⟩
  exact ⟨fun h => ⟨coded_function_domain (hf i) h, (hev i X Y).mpr h⟩,
    fun h => (hev i X Y).mp h.2⟩

#print axioms joint_attachment_action_family
end FullBridge
