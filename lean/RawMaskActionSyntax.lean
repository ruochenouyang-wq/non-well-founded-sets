import UniversalLocalWitnesses
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def membershipIsoFormula {n} (a b f : Fin n) : Formula n :=
  .conj (functionCodeFormula a f) (.conj (injectiveFormula f) (.conj (rangeFormula a f b)
    (.all (.all (.all (.all (.impl (relatedFormula f.succ.succ.succ.succ 3 1)
      (.impl (relatedFormula f.succ.succ.succ.succ 2 0)
        ((Formula.member 2 3).iffF (.member 0 1))))))))))

theorem eval_membershipIsoFormula {n} (a b f : Fin n) (v : Fin n → U) :
    Eval s (membershipIsoFormula a b f) v ↔ MembershipIsoCode s (v a) (v b) (v f) := by
  simp only [membershipIsoFormula, Eval, eval_functionCodeFormula, eval_injectiveFormula,
    eval_rangeFormula, eval_relatedFormula, eval_iffF, MembershipIsoCode, cons_succ]
  rfl

def emptyObjectFormula {n} (e : Fin n) : Formula n := .all (.impl (.member 0 e.succ) .bottom)

def RawMaskIdentity (s : U → U → Prop) (K : U) : Prop :=
  ∀ e, (∀ z, ¬s z e) → ∀ f, CodedRelation s K e f → ∀ x y, CodedRelation s f x y → x = y

def rawMaskIdentityFormula {n} (K : Fin n) : Formula n :=
  .all (.impl (emptyObjectFormula 0) (.all (.impl (relatedFormula K.succ.succ 1 0)
    (.all (.all (.impl (relatedFormula 2 1 0) (.equal 1 0)))))))

theorem eval_rawMaskIdentityFormula {n} (K : Fin n) (v : Fin n → U) :
    Eval s (rawMaskIdentityFormula K) v ↔ RawMaskIdentity s (v K) := by
  simp only [rawMaskIdentityFormula, emptyObjectFormula, Eval, eval_relatedFormula,
    RawMaskIdentity, cons_succ]
  rfl

/-- Compose the two action functions with the same orientation as A.mul. -/
def rawFunctionMulFormula {n} (f g h : Fin n) : Formula n :=
  .all (.all ((relatedFormula h.succ.succ 1 0).iffF
    (.ex (.conj (relatedFormula g.succ.succ.succ 2 0) (relatedFormula f.succ.succ.succ 0 1)))))

theorem eval_rawFunctionMulFormula {n} (f g h : Fin n) (v : Fin n → U) :
    Eval s (rawFunctionMulFormula f g h) v ↔
      ∀ x z, CodedRelation s (v h) x z ↔ ∃ y, CodedRelation s (v g) x y ∧ CodedRelation s (v f) y z := by
  simp only [rawFunctionMulFormula, Eval, eval_iffF, eval_relatedFormula, cons_succ]
  rfl

def RawMaskMultiplication (s : U → U → Prop) (G K : U) : Prop :=
  ∀ a b c, s a G → s b G → MaskXor s a b c →
    ∀ f g h, CodedRelation s K a f → CodedRelation s K b g → CodedRelation s K c h →
      ∀ x z, CodedRelation s h x z ↔ ∃ y, CodedRelation s g x y ∧ CodedRelation s f y z

def rawMaskMultiplicationFormula {n} (G K : Fin n) : Formula n :=
  .all (.all (.all (.impl (.member 2 G.succ.succ.succ)
    (.impl (.member 1 G.succ.succ.succ) (.impl (maskXorFormula 2 1 0)
      (.all (.all (.all (.impl (relatedFormula K.succ.succ.succ.succ.succ.succ 5 2)
        (.impl (relatedFormula K.succ.succ.succ.succ.succ.succ 4 1)
          (.impl (relatedFormula K.succ.succ.succ.succ.succ.succ 3 0)
            (rawFunctionMulFormula 2 1 0))))))))))))

theorem eval_rawMaskMultiplicationFormula {n} (G K : Fin n) (v : Fin n → U) :
    Eval s (rawMaskMultiplicationFormula G K) v ↔ RawMaskMultiplication s (v G) (v K) := by
  simp only [rawMaskMultiplicationFormula, Eval, eval_maskXorFormula, eval_relatedFormula,
    eval_rawFunctionMulFormula, RawMaskMultiplication, cons_succ]
  rfl

def RawMaskAction (s : U → U → Prop) (w D G K : U) : Prop :=
  TransitiveCode s D ∧ (∀ a, s a G ↔ Subset s a w) ∧ FunctionCode s G K ∧
  (∀ i f, CodedRelation s K i f → MembershipIsoCode s D D f) ∧
  RawMaskIdentity s K ∧ RawMaskMultiplication s G K

def rawMaskActionFormula {n} (w D G K : Fin n) : Formula n :=
  .conj (transitiveFormula D) (.conj
    (.all ((Formula.member 0 G.succ).iffF (powerSubsetFormula 0 w.succ)))
    (.conj (functionCodeFormula G K) (.conj
      (.all (.all (.impl (relatedFormula K.succ.succ 1 0) (membershipIsoFormula D.succ.succ D.succ.succ 0))))
      (.conj (rawMaskIdentityFormula K) (rawMaskMultiplicationFormula G K)))))

theorem eval_rawMaskActionFormula {n} (w D G K : Fin n) (v : Fin n → U) :
    Eval s (rawMaskActionFormula w D G K) v ↔ RawMaskAction s (v w) (v D) (v G) (v K) := by
  simp only [rawMaskActionFormula, Eval, eval_transitiveFormula, eval_iffF, eval_powerSubsetFormula,
    eval_functionCodeFormula, eval_relatedFormula, eval_membershipIsoFormula,
    eval_rawMaskIdentityFormula, eval_rawMaskMultiplicationFormula, RawMaskAction, cons_succ]
  rfl

#print axioms eval_rawMaskActionFormula
end FullBridge
