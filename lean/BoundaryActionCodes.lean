import FixedOrbitRealizations
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Compatibility of the old and graph actions with the prescribed partial decoration. -/
def BoundaryActionCompatible (s : U → U → Prop) (b p q : U) : Prop :=
  ∀ x y X Y, CodedRelation s q x y → CodedRelation s b x X →
    CodedRelation s p X Y → CodedRelation s b y Y

theorem boundary_action_old {D N b A p q : U} (K : BoundaryRenaming s D N b A)
    (hp : MembershipIsoCode s A A p)
    (hcomp : BoundaryActionCompatible s b p q) {X Y : U} (hX : s X A) :
    AttachmentActionRel s p q K.code X Y ↔ CodedRelation s p X Y := by
  constructor
  · rintro (h | ⟨x, y, hxX, hxy, hyY⟩)
    · exact h
    · obtain ⟨Y', hXY', _⟩ := hp.1.2 X hX
      have hby := hcomp x y X Y' hxy (K.old x X hxX hX) hXY'
      have hYY' := coded_function_value_unique K.function hyY (K.extend y Y' hby)
      exact hYY'.symm ▸ hXY'
  · exact Or.inl

theorem boundary_action_copy {D N E b A p q : U} (K : BoundaryRenaming s D N b A)
    (hp : MembershipIsoCode s A A p) (hq : GraphIsoCode s N E N E q)
    (hOld : ∀ x X, CodedRelation s b x X → s X A)
    (hcomp : BoundaryActionCompatible s b p q) {x X Y : U}
    (hxX : CodedRelation s K.code x X) :
    AttachmentActionRel s p q K.code X Y ↔
      ∃ y, CodedRelation s q x y ∧ CodedRelation s K.code y Y := by
  have oldCase : CodedRelation s p X Y →
      ∃ y, CodedRelation s q x y ∧ CodedRelation s K.code y Y := by
    intro hXY
    have hX := coded_function_domain hp.1 hXY
    obtain ⟨y, hxy, _⟩ := hq.1.2 x (coded_function_domain K.function hxX)
    exact ⟨y, hxy, K.extend y Y (hcomp x y X Y hxy (K.old x X hxX hX) hXY)⟩
  constructor
  · intro h
    rcases h with h | ⟨x', y, hx'X, hxy, hyY⟩
    · exact oldCase h
    · rcases K.collision x' x X hx'X hxX with heq | ⟨_, hbx⟩
      · exact ⟨y, heq ▸ hxy, hyY⟩
      · exact oldCase ((boundary_action_old K hp hcomp (hOld x X hbx)).mp
          (Or.inr ⟨x', y, hx'X, hxy, hyY⟩))
  · exact fun ⟨y, hxy, hyY⟩ => Or.inr ⟨x, y, hxX, hxy, hyY⟩

theorem boundary_action_function (base : BaseCollection s) {D N E b A p q : U}
    {K : BoundaryRenaming s D N b A} (F : BoundaryGraphAttachment s D N E b A K)
    (hp : MembershipIsoCode s A A p) (hq : GraphIsoCode s N E N E q)
    (hOld : ∀ x X, CodedRelation s b x X → s X A)
    (hcomp : BoundaryActionCompatible s b p q) :
    ∃ f, FunctionCode s F.domain f ∧ ∀ X Y,
      CodedRelation s f X Y ↔ AttachmentActionRel s p q K.code X Y := by
  have hdom : ∀ X Y, AttachmentActionRel s p q K.code X Y → s X F.domain := by
    intro X Y h
    apply (F.members X).mpr
    rcases h with h | ⟨x, y, hxX, _, _⟩
    · exact Or.inl (coded_function_domain hp.1 h)
    · exact Or.inr ((K.range X).mpr ⟨x, coded_function_domain K.function hxX, hxX⟩)
  have htotal : ∀ X, s X F.domain → ∃ Y, AttachmentActionRel s p q K.code X Y ∧
      ∀ Z, AttachmentActionRel s p q K.code X Z → Z = Y := by
    intro X hX
    rcases (F.members X).mp hX with hXA | hXB
    · obtain ⟨Y, hXY, _⟩ := hp.1.2 X hXA
      exact ⟨Y, Or.inl hXY, fun Z hXZ => coded_function_value_unique hp.1
        ((boundary_action_old K hp hcomp hXA).mp hXZ) hXY⟩
    · obtain ⟨x, hx, hxX⟩ := (K.range X).mp hXB
      obtain ⟨y, hxy, _⟩ := hq.1.2 x hx
      obtain ⟨Y, hyY, _⟩ := K.function.2 y (graph_iso_value hq hxy)
      refine ⟨Y, Or.inr ⟨x, y, hxX, hxy, hyY⟩, fun Z hXZ => ?_⟩
      obtain ⟨z, hxz, hzZ⟩ := (boundary_action_copy K hp hq hOld hcomp hxX).mp hXZ
      have hz := coded_function_value_unique hq.1 hxz hxy
      exact coded_function_value_unique K.function (hz ▸ hzZ) hyY
  obtain ⟨f, hf, hfr⟩ := definable_function_code base attachmentActionFormula
    (cons p (cons q (cons K.code Fin.elim0))) F.domain (by
      intro X hX
      obtain ⟨Y, hY, hu⟩ := htotal X hX
      exact ⟨Y, (eval_attachmentActionFormula p q K.code X Y).mpr hY,
        fun Z hZ => hu Z ((eval_attachmentActionFormula p q K.code X Z).mp hZ)⟩)
  refine ⟨f, hf, fun X Y => ?_⟩
  rw [hfr, eval_attachmentActionFormula]
  exact ⟨fun h => h.2, fun h => ⟨hdom X Y h, h⟩⟩

#print axioms boundary_action_function
end FullBridge
