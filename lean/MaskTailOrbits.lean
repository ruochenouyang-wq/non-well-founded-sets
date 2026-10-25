import CoveredMaskActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def TailMask {w : U} (s : U → U → Prop) (N : U) (i : InternalMask s w) : Prop :=
  ∀ k, s k i.val → ¬ s k N

def TailOrbitCode {w : U} (s : U → U → Prop) (J : InternalMask s w → U → U)
    (N x O : U) : Prop := ∀ y, s y O ↔ ∃ i, TailMask s N i ∧ J i x = y

theorem tail_mask_mul (base : BaseCollection s) {w N : U} {i j : InternalMask s w}
    (hi : TailMask s N i) (hj : TailMask s N j) : TailMask s N (internalMaskMul base i j) := by
  intro k hk
  exact ((internal_mask_mul_mem base i j k).mp hk).elim (fun h => hi k h.1) (fun h => hj k h.1)

def tailOrbitPointFormula {n} (G K N x y : Fin n) : Formula n :=
  .ex (.conj (.member 0 G.succ) (.conj (maskDisjointFormula 0 N.succ)
    (jointMaskPointFormula K.succ 0 x.succ y.succ)))

theorem eval_tailOrbitPointFormula {n} (G K N x y : Fin n) (v : Fin n → U) :
    Eval s (tailOrbitPointFormula G K N x y) v ↔
      ∃ i, s i (v G) ∧ (∀ k, s k i → ¬s k (v N)) ∧
        ∃ f, CodedRelation s (v K) i f ∧ CodedRelation s f (v x) (v y) := by
  simp only [tailOrbitPointFormula, maskDisjointFormula, Eval, eval_jointMaskPointFormula, cons_succ]
  rfl

def tailOrbitSetFormula {n} (G K N x O : Fin n) : Formula n :=
  .all ((Formula.member 0 O.succ).iffF (tailOrbitPointFormula G.succ K.succ N.succ x.succ 0))

theorem joint_tail_orbit_point {w T x y N : U} {J : InternalMask s w → U → U}
    (A : JointMaskDomain s w J T) (hx : s x T) :
    Eval s (tailOrbitPointFormula (n := 5) 2 3 4 1 0)
      (cons y (cons x (cons A.masks (cons A.family (cons N Fin.elim0))))) ↔
      ∃ i, TailMask s N i ∧ J i x = y := by
  rw [eval_tailOrbitPointFormula]
  constructor
  · rintro ⟨i, hi, hd, hr⟩
    let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
    exact ⟨I, hd, (joint_mask_point_value A I hx y).mp hr⟩
  · rintro ⟨i, hd, hy⟩
    exact ⟨i.val, (A.maskMembers i.val).mpr i.property, hd, (joint_mask_point_value A i hx y).mpr hy⟩

theorem joint_tail_orbit_set_formula {w T x O N : U} {J : InternalMask s w → U → U}
    (A : JointMaskDomain s w J T) (hx : s x T) :
    Eval s (tailOrbitSetFormula (n := 5) 2 3 4 1 0)
      (cons O (cons x (cons A.masks (cons A.family (cons N Fin.elim0))))) ↔ TailOrbitCode s J N x O := by
  simp only [tailOrbitSetFormula, Eval, eval_iffF]
  have hh : ∀ y, Eval s (tailOrbitPointFormula (n := 6) 3 4 5 2 0)
      (cons y (cons O (cons x (cons A.masks (cons A.family (cons N Fin.elim0)))))) ↔
      ∃ i, TailMask s N i ∧ J i x = y := by
    intro y
    rw [eval_tailOrbitPointFormula]
    exact (eval_tailOrbitPointFormula (s := s) (n := 5) 2 3 4 1 0 _).symm.trans (joint_tail_orbit_point A hx)
  exact forall_congr' (fun y => iff_congr Iff.rfl (hh y))

theorem joint_tail_orbit_exists (base : BaseCollection s) {w T x N : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J T) (hx : s x T) :
    ∃ O, TailOrbitCode s J N x O := by
  obtain ⟨O, hO⟩ := base.separation 4 (tailOrbitPointFormula 2 3 4 1 0)
    (cons x (cons A.masks (cons A.family (cons N Fin.elim0)))) T
  refine ⟨O, fun y => (hO y).trans ?_⟩
  rw [joint_tail_orbit_point A hx]
  exact ⟨fun h => h.2, fun ⟨i, hd, hy⟩ => ⟨hy ▸ A.stable i x hx, i, hd, hy⟩⟩

theorem tail_orbit_contains_seed (base : BaseCollection s) {w N x O : U}
    {J : InternalMask s w → U → U} (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hO : TailOrbitCode s J N x O) : s x O :=
  (hO x).mpr ⟨internalMaskOne base w, fun k hk => False.elim (internal_mask_one_mem base w k hk), hOne x⟩

theorem tail_orbit_fixed (base : BaseCollection s) {w N x O : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hO : TailOrbitCode s J N x O) (i : InternalMask s w) (hi : TailMask s N i) : J i O = O := by
  apply elementary_involution_closed_set base (hj i) (hs i)
  intro y hy
  obtain ⟨j, hd, rfl⟩ := (hO y).mp hy
  exact (hO _).mpr ⟨internalMaskMul base i j, tail_mask_mul base hi hd, hMul i j x⟩

theorem tail_orbit_subset {w N x O a : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hx : s x a)
    (ha : ∀ i, TailMask s N i → J i a = a) (hO : TailOrbitCode s J N x O) : Subset s O a := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := (hO y).mp hy
  have hm := ((hj i) (Formula.member (n := 2) 0 1) (cons x (cons a Fin.elim0))).mp hx
  change s (J i x) (J i a) at hm
  simpa only [ha i hi] using hm


/-- Any two points of the same tail orbit are connected by another actual
    tail mask. No representative is selected for an entire family. -/
theorem tail_orbit_member_transport (base : BaseCollection s) {w N r O x y : U}
    {J : InternalMask s w → U → U} (hs : ∀ i x, J i (J i x) = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hO : TailOrbitCode s J N r O) (hx : s x O) (hy : s y O) :
    ∃ i, TailMask s N i ∧ J i x = y := by
  obtain ⟨i, hi, rfl⟩ := (hO x).mp hx
  obtain ⟨j, hj, rfl⟩ := (hO y).mp hy
  exact ⟨internalMaskMul base j i, tail_mask_mul base hj hi,
    (hMul j i (J i r)).trans (congrArg (J j) (hs i r))⟩

#print axioms joint_tail_orbit_exists
end FullBridge
