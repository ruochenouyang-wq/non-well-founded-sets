import JointMaskGraphActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Free variables [output,input,index,old-action-family,decoration]. -/
def jointDecorationValueFormula : Formula 5 :=
  .ex (.ex (.ex (.conj (relatedFormula 6 5 2) (.conj (relatedFormula 7 1 4)
    (.conj (relatedFormula 2 1 0) (relatedFormula 7 0 3))))))

theorem eval_jointDecorationValueFormula (Y X i K g : U) :
    Eval s jointDecorationValueFormula (cons Y (cons X (cons i (cons K (cons g Fin.elim0))))) ↔
      ∃ p x y, CodedRelation s K i p ∧ CodedRelation s g x X ∧
        CodedRelation s p x y ∧ CodedRelation s g y Y := by
  simp only [jointDecorationValueFormula, Eval, eval_relatedFormula]
  rfl

/-- The jointly coded input action and one common decoration yield one
    actual source function coding every descended action map. -/
theorem joint_decoration_image_family (base : BaseCollection s) {w G K g T : U}
    (hG : ∀ a, s a G ↔ Subset s a w) (hK : FunctionCode s G K)
    (rho out : InternalMask s w → U) (hrho : ∀ a, CodedRelation s K a.val (rho a))
    (hout : ∀ a, MembershipIsoCode s T T (out a) ∧ DecorationImageCode s g (rho a) (out a)) :
    ∃ L, FunctionCode s G L ∧ ∀ a, CodedRelation s L a.val (out a) := by
  have hev : ∀ a X Y, Eval s jointDecorationValueFormula
      (cons Y (cons X (cons a.val (cons K (cons g Fin.elim0))))) ↔ CodedRelation s (out a) X Y := by
    intro a X Y
    rw [eval_jointDecorationValueFormula, (hout a).2 X Y]
    constructor
    · rintro ⟨p, x, y, hap, hxX, hxy, hyY⟩
      have he := coded_function_value_unique hK hap (hrho a)
      exact ⟨x, y, hxX, he ▸ hxy, hyY⟩
    · rintro ⟨x, y, hxX, hxy, hyY⟩
      exact ⟨rho a, x, y, hrho a, hxX, hxy, hyY⟩
  have ht : ∀ i, s i G → ∀ X, s X T → ∃ Y,
      Eval s jointDecorationValueFormula (cons Y (cons X (cons i (cons K (cons g Fin.elim0))))) ∧
      ∀ Z, Eval s jointDecorationValueFormula (cons Z (cons X (cons i (cons K (cons g Fin.elim0))))) → Z = Y := by
    intro i hi X hX
    let a : InternalMask s w := ⟨i, (hG i).mp hi⟩
    obtain ⟨Y, hXY, hu⟩ := (hout a).1.1.2 X hX
    exact ⟨Y, (hev a X Y).mpr hXY, fun Z hZ => hu Z ((hev a X Z).mp hZ)⟩
  obtain ⟨L, hL, hrel⟩ := definable_function_family base jointDecorationValueFormula (cons K (cons g Fin.elim0)) G T ht
  refine ⟨L, hL, fun a => ?_⟩
  apply (hrel a.val (out a)).mpr
  refine ⟨(hG a.val).mpr a.property, (hout a).1.1, fun X Y => ?_⟩
  constructor
  · intro hXY
    exact ⟨coded_function_domain (hout a).1.1 hXY, (hev a X Y).mpr hXY⟩
  · rintro ⟨_, hXY⟩
    exact (hev a X Y).mp hXY
end FullBridge
