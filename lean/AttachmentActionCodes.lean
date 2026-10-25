import MemberGraphAttachments
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def AttachmentActionRel (s : U → U → Prop) (p q k X Y : U) : Prop :=
  CodedRelation s p X Y ∨ ∃ x y, CodedRelation s k x X ∧
    CodedRelation s q x y ∧ CodedRelation s k y Y

def attachmentActionFormula : Formula 5 :=
  (relatedFormula 2 1 0).disj (.ex (.ex (.conj (relatedFormula 6 1 3)
    (.conj (relatedFormula 5 1 0) (relatedFormula 6 0 2)))))

theorem eval_attachmentActionFormula (p q k X Y : U) :
    Eval s attachmentActionFormula (cons Y (cons X (cons p (cons q (cons k Fin.elim0))))) ↔
      AttachmentActionRel s p q k X Y := by
  simp only [attachmentActionFormula, eval_disj, Eval, eval_relatedFormula, AttachmentActionRel]
  rfl

theorem attachment_action_old {t A a r p q : U} (D : MemberGraphAttachment s t A a r)
    (hp : MembershipIsoCode s A A p) (hq : GraphIsoCode s a r a r q)
    (hstable : ∀ x y, s x t → CodedRelation s p x y → s y t)
    (hag : ∀ x y, s x t → (CodedRelation s p x y ↔ CodedRelation s q x y))
    {X Y : U} (hX : s X A) :
    AttachmentActionRel s p q D.copy X Y ↔ CodedRelation s p X Y := by
  constructor
  · rintro (h | ⟨x, y, hxX, hxy, hyY⟩)
    · exact h
    · have hXt := (D.overlap X).mp ⟨(D.copyRange X).mpr ⟨x, coded_function_domain D.copyFunction hxX, hxX⟩, hX⟩
      have hx := D.copyInjective x X X hxX (D.fixed X hXt)
      subst x
      have hpy := (hag X y hXt).mpr hxy
      have hyt := hstable X y hXt hpy
      have hy := coded_function_value_unique D.copyFunction hyY (D.fixed y hyt)
      exact hy ▸ hpy
  · exact Or.inl

theorem attachment_action_copy {t A a r p q : U} (D : MemberGraphAttachment s t A a r)
    (hp : MembershipIsoCode s A A p) (hq : GraphIsoCode s a r a r q)
    (hstable : ∀ x y, s x t → CodedRelation s p x y → s y t)
    (hag : ∀ x y, s x t → (CodedRelation s p x y ↔ CodedRelation s q x y))
    {x X Y : U} (hxX : CodedRelation s D.copy x X) :
    AttachmentActionRel s p q D.copy X Y ↔
      ∃ y, CodedRelation s q x y ∧ CodedRelation s D.copy y Y := by
  constructor
  · rintro (h | ⟨x', y, hx'X, hxy, hyY⟩)
    · have hXt := (D.overlap X).mp ⟨(D.copyRange X).mpr ⟨x, coded_function_domain D.copyFunction hxX, hxX⟩,
        coded_function_domain hp.1 h⟩
      have hx := D.copyInjective x X X hxX (D.fixed X hXt)
      subst x
      exact ⟨Y, (hag X Y hXt).mp h, D.fixed Y (hstable X Y hXt h)⟩
    · exact ⟨y, D.copyInjective x' x X hx'X hxX ▸ hxy, hyY⟩
  · exact fun ⟨y, hxy, hyY⟩ => Or.inr ⟨x, y, hxX, hxy, hyY⟩

theorem attachment_action_function (base : BaseCollection s) {t A a r p q : U}
    (D : MemberGraphAttachment s t A a r)
    (hp : MembershipIsoCode s A A p) (hq : GraphIsoCode s a r a r q)
    (hstable : ∀ x y, s x t → CodedRelation s p x y → s y t)
    (hag : ∀ x y, s x t → (CodedRelation s p x y ↔ CodedRelation s q x y)) :
    ∃ f, FunctionCode s D.domain f ∧ ∀ X Y,
      CodedRelation s f X Y ↔ AttachmentActionRel s p q D.copy X Y := by
  have hdom : ∀ X Y, AttachmentActionRel s p q D.copy X Y → s X D.domain := by
    intro X Y h
    apply (D.members X).mpr
    rcases h with h | ⟨x, y, hxX, _, _⟩
    · exact Or.inl (coded_function_domain hp.1 h)
    · exact Or.inr ((D.copyRange X).mpr ⟨x, coded_function_domain D.copyFunction hxX, hxX⟩)
  have htotal : ∀ X, s X D.domain → ∃ Y, AttachmentActionRel s p q D.copy X Y ∧
      ∀ Z, AttachmentActionRel s p q D.copy X Z → Z = Y := by
    intro X hX
    rcases (D.members X).mp hX with hXA | hXB
    · obtain ⟨Y, hXY, _⟩ := hp.1.2 X hXA
      exact ⟨Y, Or.inl hXY, fun Z hXZ => coded_function_value_unique hp.1
        ((attachment_action_old D hp hq hstable hag hXA).mp hXZ) hXY⟩
    · obtain ⟨x, hx, hxX⟩ := (D.copyRange X).mp hXB
      obtain ⟨y, hxy, _⟩ := hq.1.2 x hx
      obtain ⟨Y, hyY, _⟩ := D.copyFunction.2 y (graph_iso_value hq hxy)
      refine ⟨Y, Or.inr ⟨x, y, hxX, hxy, hyY⟩, fun Z hXZ => ?_⟩
      obtain ⟨z, hxz, hzZ⟩ := (attachment_action_copy D hp hq hstable hag hxX).mp hXZ
      have hz := coded_function_value_unique hq.1 hxz hxy
      exact coded_function_value_unique D.copyFunction (hz ▸ hzZ) hyY
  obtain ⟨f, hf, hfr⟩ := definable_function_code base attachmentActionFormula
    (cons p (cons q (cons D.copy Fin.elim0))) D.domain (by
      intro X hX
      obtain ⟨Y, hY, hu⟩ := htotal X hX
      exact ⟨Y, (eval_attachmentActionFormula p q D.copy X Y).mpr hY,
        fun Z hZ => hu Z ((eval_attachmentActionFormula p q D.copy X Z).mp hZ)⟩)
  refine ⟨f, hf, fun X Y => ?_⟩
  rw [hfr, eval_attachmentActionFormula]
  exact ⟨fun h => h.2, fun h => ⟨hdom X Y h, h⟩⟩

#print axioms attachment_action_function
end FullBridge
