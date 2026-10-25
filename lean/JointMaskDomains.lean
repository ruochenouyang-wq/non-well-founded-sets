import JointFunctionCodes
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- One source function, on the actual source powerset of w, codes all
    mask restrictions on t. Stability of t is included explicitly. -/
structure JointMaskDomain (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) (t : U) where
  masks : U
  maskMembers : ∀ a, s a masks ↔ Subset s a w
  family : U
  familyFunction : FunctionCode s masks family
  graphs : ∀ (a : InternalMask s w) f, CodedRelation s family a.val f →
    FunctionCode s t f ∧ ∀ x y, CodedRelation s f x y ↔ s x t ∧ J a x = y
  stable : ∀ (a : InternalMask s w) x, s x t → s (J a x) t

def maskGraphFamilyFormula : Formula 5 :=
  (definedFunctionGraphFormula maskedLabelFormula).rename
    (cons 0 (cons 2 (cons 3 (cons 4 (cons 1 Fin.elim0)))))

theorem eval_maskGraphFamilyFormula (f a d left right : U) :
    Eval s maskGraphFamilyFormula (cons f (cons a (cons d (cons left (cons right Fin.elim0))))) ↔
      DefinedFunctionGraph s maskedLabelFormula (cons left (cons right (cons a Fin.elim0))) d f := by
  rw [maskGraphFamilyFormula, eval_rename]
  have he : (fun i => cons f (cons a (cons d (cons left (cons right Fin.elim0))))
      (cons 0 (cons 2 (cons 3 (cons 4 (cons 1 Fin.elim0)))) i)) =
      cons f (cons d (cons left (cons right (cons a Fin.elim0)))) := by
    funext i
    exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl
      (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.elim0 i) i) i) i) i) i
  rw [he]
  exact eval_definedFunctionGraphFormula maskedLabelFormula _ d f

/-- A single actual source function assigns every internal mask its whole
    label-domain action graph. This is stronger than separate existence. -/
theorem internal_mask_label_family_code (base : BaseCollection s) {w d G : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    :
    ∃ k, FunctionCode s G k ∧ ∀ a f, CodedRelation s k a f ↔
      s a G ∧ DefinedFunctionGraph s maskedLabelFormula (cons P.leftCode (cons P.rightCode (cons a Fin.elim0))) d f := by
  let v := cons d (cons P.leftCode (cons P.rightCode Fin.elim0))
  have ht : ∀ a, s a G → ∃ f, Eval s maskGraphFamilyFormula (cons f (cons a v)) ∧
      ∀ g, Eval s maskGraphFamilyFormula (cons g (cons a v)) → g = f := by
    intro a _
    obtain ⟨f, hf, hrel⟩ := masked_label_action_code base P hd a
    have hdef : DefinedFunctionGraph s maskedLabelFormula (cons P.leftCode (cons P.rightCode (cons a Fin.elim0))) d f := by
      refine ⟨hf, fun x y => ?_⟩
      constructor
      · intro h
        obtain ⟨hx, hy⟩ := (hrel x y).mp h
        exact ⟨hx, (eval_maskedLabelFormula base P hd a hx y).mpr hy⟩
      · rintro ⟨hx, hy⟩
        exact (hrel x y).mpr ⟨hx, (eval_maskedLabelFormula base P hd a hx y).mp hy⟩
    exact ⟨f, (eval_maskGraphFamilyFormula f a d P.leftCode P.rightCode).mpr hdef,
      fun g hg => defined_function_graph_unique base
        ((eval_maskGraphFamilyFormula g a d P.leftCode P.rightCode).mp hg) hdef⟩
  obtain ⟨k, hk, hrel⟩ := definable_function_code base maskGraphFamilyFormula v G ht
  exact ⟨k, hk, fun a f => (hrel a f).trans (and_congr Iff.rfl
    (eval_maskGraphFamilyFormula f a d P.leftCode P.rightCode))⟩

theorem joint_mask_label_domain (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c) : Nonempty (JointMaskDomain s w J d) := by
  obtain ⟨G, hG⟩ := base.powerset w
  obtain ⟨k, hk, hrel⟩ := internal_mask_label_family_code (G := G) base P hd
  refine ⟨⟨G, hG, k, hk, ?_, ?_⟩⟩
  · intro a f haf
    obtain ⟨_, hf, hr⟩ := (hrel a.val f).mp haf
    refine ⟨hf, fun x y => ?_⟩
    constructor
    · intro h
      obtain ⟨hx, hy⟩ := (hr x y).mp h
      have hv := (eval_maskedLabelFormula base P hd a.val hx y).mp hy
      exact ⟨hx, (hcore a x ((hd x).mp hx)).trans hv.symm⟩
    · rintro ⟨hx, hy⟩
      exact (hr x y).mpr ⟨hx, (eval_maskedLabelFormula base P hd a.val hx y).mpr
        (hy.symm.trans (hcore a x ((hd x).mp hx)))⟩
  · intro a x hx
    rw [hcore a x ((hd x).mp hx)]
    exact masked_label_action_mem base P hd a.val hx

theorem joint_mask_graph_exists {w t : U} {J : InternalMask s w → U → U}
    (A : JointMaskDomain s w J t) (a : InternalMask s w) :
    ∃ f, CodedRelation s A.family a.val f ∧ FunctionCode s t f ∧
      ∀ x y, CodedRelation s f x y ↔ s x t ∧ J a x = y := by
  obtain ⟨f, hf, _⟩ := A.familyFunction.2 a.val ((A.maskMembers a.val).mpr a.property)
  exact ⟨f, hf, A.graphs a f hf⟩
end FullBridge
