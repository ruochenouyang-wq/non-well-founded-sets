import GeneralCopyActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def MaskXor (s : U → U → Prop) (a b c : U) : Prop :=
  ∀ x, s x c ↔ (s x a ∧ ¬s x b) ∨ (s x b ∧ ¬s x a)

def maskXorFormula {n} (a b c : Fin n) : Formula n :=
  .all ((Formula.member 0 c.succ).iffF
    ((Formula.conj (.member 0 a.succ) (.impl (.member 0 b.succ) .bottom)).disj
      (.conj (.member 0 b.succ) (.impl (.member 0 a.succ) .bottom))))

theorem eval_maskXorFormula {n} (a b c : Fin n) (v : Fin n → U) :
    Eval s (maskXorFormula a b c) v ↔ MaskXor s (v a) (v b) (v c) := by
  simp only [maskXorFormula, Eval, eval_iffF, eval_disj, cons_succ, MaskXor]
  rfl

theorem mask_xor_iff_mul (base : BaseCollection s) {w c : U} (a b : InternalMask s w) :
    MaskXor s a.val b.val c ↔ c = (internalMaskMul base a b).val := by
  constructor
  · intro h
    exact base.extensional c _ (fun x => (h x).trans (internal_mask_mul_mem base a b x).symm)
  · rintro rfl
    exact internal_mask_mul_mem base a b

/-- Free variables [output,input,mask,index-domain,copy-family]. -/
def maskCopyTransitionFormula : Formula 5 :=
  .ex (.ex (.ex (.ex (.ex (.conj (.member 4 8) (.conj (maskXorFormula 7 4 3)
    (.conj (relatedFormula 9 4 2) (.conj (relatedFormula 9 3 1)
      (.conj (relatedFormula 2 0 6) (relatedFormula 1 0 5))))))))))

def MaskCopyTransition (s : U → U → Prop) (a G K X Y : U) : Prop :=
  ∃ b c k l x, s b G ∧ MaskXor s a b c ∧ CodedRelation s K b k ∧
    CodedRelation s K c l ∧ CodedRelation s k x X ∧ CodedRelation s l x Y

theorem eval_maskCopyTransitionFormula (a G K X Y : U) :
    Eval s maskCopyTransitionFormula (cons Y (cons X (cons a (cons G (cons K Fin.elim0))))) ↔
      MaskCopyTransition s a G K X Y := by
  simp only [maskCopyTransitionFormula, Eval, eval_maskXorFormula, eval_relatedFormula, MaskCopyTransition]
  rfl

theorem mask_copy_transition_iff (base : BaseCollection s) {w G K : U}
    (hG : ∀ b, s b G ↔ Subset s b w) (hK : FunctionCode s G K)
    (codes : InternalMask s w → U) (hcode : ∀ b, CodedRelation s K b.val (codes b))
    (a : InternalMask s w) (X Y : U) : MaskCopyTransition s a.val G K X Y ↔
      ∃ b x, CodedRelation s (codes b) x X ∧ CodedRelation s (codes (internalMaskMul base a b)) x Y := by
  constructor
  · rintro ⟨b, c, k, l, x, hb, hxor, hbk, hcl, hxX, hxY⟩
    let B : InternalMask s w := ⟨b, (hG b).mp hb⟩
    have hc := (mask_xor_iff_mul base a B).mp hxor
    have hk := coded_function_value_unique hK hbk (hcode B)
    have hl := coded_function_value_unique hK (hc ▸ hcl) (hcode (internalMaskMul base a B))
    exact ⟨B, x, hk ▸ hxX, hl ▸ hxY⟩
  · rintro ⟨b, x, hxX, hxY⟩
    exact ⟨b.val, (internalMaskMul base a b).val, codes b, codes (internalMaskMul base a b), x,
      (hG b.val).mpr b.property, (mask_xor_iff_mul base a b).mpr rfl,
      hcode b, hcode (internalMaskMul base a b), hxX, hxY⟩
end FullBridge
