import FiniteCopyGraph
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

/-- External finite group data, without requiring a group library or an
    internal source set that codes the whole index type. -/
structure FiniteGroupData (I : Type v) where
  one : I
  mul : I → I → I
  inv : I → I
  assoc : ∀ i j k, mul (mul i j) k = mul i (mul j k)
  one_mul : ∀ i, mul one i = i
  mul_one : ∀ i, mul i one = i
  inv_mul : ∀ i, mul (inv i) i = one
  mul_inv : ∀ i, mul i (inv i) = one
  indices : List I
  complete : ∀ i, i ∈ indices

theorem finite_group_left_inverse {I : Type v} (G : FiniteGroupData I) (i k : I) :
    G.mul (G.inv i) (G.mul i k) = k := by
  rw [← G.assoc, G.inv_mul, G.one_mul]

theorem finite_group_right_inverse {I : Type v} (G : FiniteGroupData I) (i k : I) :
    G.mul i (G.mul (G.inv i) k) = k := by
  rw [← G.assoc, G.mul_inv, G.one_mul]

theorem copy_reflects_old_value {t A p B k x y : U}
    (hp : MembershipIsoCode s t t p) (hk : CopyCode s t A p B k)
    (hxy : CodedRelation s k x y) (hy : s y t) : CodedRelation s p x y := by
  obtain ⟨z, _, hzy⟩ := (hp.2.2.1 y).mp hy
  have hzx := hk.2.1 z x y (hk.2.2.2.2 z y hzy) hxy
  exact hzx ▸ hzy

theorem copy_transition_code (base : BaseCollection s) {t A p q B C k l : U}
    (hk : CopyCode s t A p B k) (hl : CopyCode s t A q C l) :
    ∃ r, FunctionCode s B r ∧ ∀ X Y, CodedRelation s r X Y ↔
      ∃ x, CodedRelation s k x X ∧ CodedRelation s l x Y := by
  obtain ⟨inv, hi, _, hir, hinv⟩ := coded_bijection_inverse base hk.1 hk.2.1 hk.2.2.1
  obtain ⟨r, hr, hrr⟩ := coded_functions_compose base hi hl.1
    (fun X x h => (hir x).mpr ⟨X, coded_function_domain hi h, h⟩)
  refine ⟨r, hr, fun X Y => ?_⟩
  rw [hrr]
  exact exists_congr (fun x => and_congr (hinv X x) Iff.rfl)

/-- Compatibility at shared old points uses the supplied multiplication law.
    Away from the old part, distinct copies cannot share an input. -/
theorem finite_copy_action_compatible {I : Type v} (G : FiniteGroupData I)
    {t A : U} (act ranges codes : I → U)
    (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hc : ∀ i, CopyCode s t A (act i) (ranges i) (codes i))
    (hInt : ∀ i j, i ≠ j → ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t)
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z)
    (i k l : I) {x z X Y Z : U}
    (hxX : CodedRelation s (codes k) x X) (hxY : CodedRelation s (codes (G.mul i k)) x Y)
    (hzX : CodedRelation s (codes l) z X) (hzZ : CodedRelation s (codes (G.mul i l)) z Z) : Y = Z := by
  by_cases hkl : k = l
  · subst l
    have hxz := (hc k).2.1 x z X hxX hzX
    exact coded_function_value_unique (hc (G.mul i k)).1 hxY (hxz.symm ▸ hzZ)
  · have hXt := (hInt k l hkl X).mp
      ⟨((hc k).2.2.1 X).mpr ⟨x, coded_function_domain (hc k).1 hxX, hxX⟩,
        ((hc l).2.2.1 X).mpr ⟨z, coded_function_domain (hc l).1 hzX, hzX⟩⟩
    have hpxX := copy_reflects_old_value (hp k) (hc k) hxX hXt
    have hpzX := copy_reflects_old_value (hp l) (hc l) hzX hXt
    obtain ⟨W, hXW, _⟩ := (hp i).1.2 X hXt
    have hxW := (hMul i k x W).mpr ⟨X, hpxX, hXW⟩
    have hzW := (hMul i l z W).mpr ⟨X, hpzX, hXW⟩
    have hYW := coded_function_value_unique (hc (G.mul i k)).1 hxY ((hc (G.mul i k)).2.2.2.2 x W hxW)
    have hZW := coded_function_value_unique (hc (G.mul i l)).1 hzZ ((hc (G.mul i l)).2.2.2.2 z W hzW)
    exact hYW.trans hZW.symm

/-- Build actual internal function codes by finite unions of copy transitions.
    This step constructs the action maps, rather than taking them as inputs. -/
theorem finite_copy_action_functions (base : BaseCollection s) {I : Type v} (G : FiniteGroupData I)
    {t A S : U} (act ranges codes : I → U)
    (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hc : ∀ i, CopyCode s t A (act i) (ranges i) (codes i))
    (hInt : ∀ i j, i ≠ j → ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t)
    (hS : ∀ X, s X S ↔ ∃ i, s X (ranges i))
    (hMul : ∀ i j x z, CodedRelation s (act (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (act j) x y ∧ CodedRelation s (act i) y z) :
    ∃ rho : I → U, ∀ i, FunctionCode s S (rho i) ∧
      ∀ X Y, CodedRelation s (rho i) X Y ↔
        ∃ k x, CodedRelation s (codes k) x X ∧ CodedRelation s (codes (G.mul i k)) x Y := by
  classical
  have htr := fun i k => copy_transition_code base (hc k) (hc (G.mul i k))
  let tr : I → I → U := fun i k => Classical.choose (htr i k)
  have htrSpec := fun i k => Classical.choose_spec (htr i k)
  have hu := fun i => finite_indexed_relation_union base G.indices (tr i)
  let rho : I → U := fun i => Classical.choose (hu i)
  have huSpec := fun i => Classical.choose_spec (hu i)
  have hRel : ∀ i X Y, CodedRelation s (rho i) X Y ↔
      ∃ k x, CodedRelation s (codes k) x X ∧ CodedRelation s (codes (G.mul i k)) x Y := by
    intro i X Y
    constructor
    · intro h
      obtain ⟨k, _, hk⟩ := (huSpec i).2 X Y |>.mp h
      obtain ⟨x, hxX, hxY⟩ := (htrSpec i k).2 X Y |>.mp hk
      exact ⟨k, x, hxX, hxY⟩
    · rintro ⟨k, x, hxX, hxY⟩
      exact ((huSpec i).2 X Y).mpr ⟨k, G.complete k, ((htrSpec i k).2 X Y).mpr ⟨x, hxX, hxY⟩⟩
  refine ⟨rho, fun i => ⟨?_, hRel i⟩⟩
  constructor
  · intro z hz
    obtain ⟨k, _, hzk⟩ := ((huSpec i).1 z).mp hz
    obtain ⟨X, Y, hX, hXY⟩ := (htrSpec i k).1.1 z hzk
    exact ⟨X, Y, (hS X).mpr ⟨k, hX⟩, hXY⟩
  · intro X hX
    obtain ⟨k, hXk⟩ := (hS X).mp hX
    obtain ⟨x, hx, hxX⟩ := ((hc k).2.2.1 X).mp hXk
    obtain ⟨Y, hxY, _⟩ := (hc (G.mul i k)).1.2 x hx
    refine ⟨Y, (hRel i X Y).mpr ⟨k, x, hxX, hxY⟩, ?_⟩
    intro Z hXZ
    obtain ⟨l, z, hzX, hzZ⟩ := (hRel i X Z).mp hXZ
    exact (finite_copy_action_compatible G act ranges codes hp hc hInt hMul i k l hxX hxY hzX hzZ).symm

#print axioms finite_copy_action_functions
end FullBridge
