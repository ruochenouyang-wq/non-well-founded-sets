import ScheduledCollectionReduction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Internal transitive containment of all descendants with root support.
    Bounds may differ for different members of the transitive cover. -/
def InternalMaskCovered (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) (x : U) : Prop :=
  ∃ c, TransitiveCode s c ∧ s x c ∧ ∀ y, s y c → MaskTailSupported s w J y

theorem internal_mask_covered_hereditary {w x : U} {J : InternalMask s w → U → U}
    (hx : InternalMaskCovered s w J x) : HereditarilyMaskSupported s w J x := by
  obtain ⟨c, hc, hxc, hroot⟩ := hx
  exact fun y hy => hroot y (descendant_in_transitive hc hxc hy)

theorem internal_mask_covered_member {w x y : U} {J : InternalMask s w → U → U}
    (hx : InternalMaskCovered s w J x) (hy : s y x) : InternalMaskCovered s w J y := by
  obtain ⟨c, hc, hxc, hroot⟩ := hx
  exact ⟨c, hc, hc x hxc y hy, hroot⟩

theorem internal_mask_cover_restrict (base : BaseCollection s) {w T x : U}
    {J : InternalMask s w → U → U} (hT : TransitiveCode s T) (hxT : s x T)
    (hx : InternalMaskCovered s w J x) :
    ∃ c, Subset s c T ∧ TransitiveCode s c ∧ s x c ∧
      ∀ y, s y c → MaskTailSupported s w J y := by
  obtain ⟨d, hd, hxd, hroot⟩ := hx
  obtain ⟨c, hc⟩ := base.separation 1 (.member 0 1) (cons T Fin.elim0) d
  have hmem : ∀ y, s y c ↔ s y d ∧ s y T := hc
  refine ⟨c, fun y hy => ((hmem y).mp hy).2, ?_, (hmem x).mpr ⟨hxd, hxT⟩,
    fun y hy => hroot y ((hmem y).mp hy).1⟩
  intro y hy z hz
  obtain ⟨hyd, hyT⟩ := (hmem y).mp hy
  exact (hmem z).mpr ⟨hd y hyd z hz, hT y hyT z hz⟩

theorem internal_mask_covered_invariant {w : U} {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (i : InternalMask s w) (x : U) : InternalMaskCovered s w J (J i x) ↔ InternalMaskCovered s w J x := by
  have forward : ∀ x, InternalMaskCovered s w J x → InternalMaskCovered s w J (J i x) := by
    rintro x ⟨c, hct, hxc, hroot⟩
    have ht : TransitiveCode s (J i c) :=
      (eval_transitiveFormula s 0 (fun _ => J i c)).mp
        (((hj i) (transitiveFormula (n := 1) 0) (fun _ => c)).mp
          ((eval_transitiveFormula s 0 (fun _ => c)).mpr hct))
    refine ⟨J i c, ht, ((hj i) (Formula.member (n := 2) 0 1) (cons x (cons c Fin.elim0))).mp hxc, ?_⟩
    intro y hy
    have hz := ((hj i) (Formula.member (n := 2) 0 1) (cons y (cons (J i c) Fin.elim0))).mp hy
    change s (J i y) (J i (J i c)) at hz
    rw [hs i c] at hz
    exact (mask_support_invariant hc hs i y).mp (hroot _ hz)
  exact ⟨fun h => hs i x ▸ forward (J i x) h, forward x⟩

/-- Finite external descent is sufficient for hereditary support; no converse
    from it to an internally transitive cover is asserted. -/
def internalMaskCoreFormula {n} (w G K T x : Fin n) : Formula n :=
  .ex (.conj (powerSubsetFormula 0 T.succ) (.conj (transitiveFormula 0)
    (.conj (.member x.succ 0) (.all (.impl (.member 0 1)
      (jointTailSupportFormula w.succ.succ G.succ.succ K.succ.succ 0))))))

theorem eval_internalMaskCoreFormula {n} (w G K T x : Fin n) (v : Fin n → U) :
    Eval s (internalMaskCoreFormula w G K T x) v ↔
      ∃ c, Subset s c (v T) ∧ TransitiveCode s c ∧ s (v x) c ∧
        ∀ y, s y c → JointTailSupport s (v w) (v G) (v K) y := by
  simp only [internalMaskCoreFormula, Eval, eval_powerSubsetFormula, eval_transitiveFormula,
    eval_jointTailSupportFormula, cons_succ]
  rfl

theorem joint_internal_mask_core_formula (base : BaseCollection s) {w T x : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J T)
    (hT : TransitiveCode s T) (hj : ∀ i, ElementaryMap s s (J i))
    (ho : ∀ i y, ∃ x, J i x = y) (hxT : s x T) :
    Eval s (internalMaskCoreFormula (n := 5) 1 2 3 4 0)
      (cons x (cons w (cons A.masks (cons A.family (cons T Fin.elim0))))) ↔
      InternalMaskCovered s w J x := by
  rw [eval_internalMaskCoreFormula]
  constructor
  · rintro ⟨c, hcT, hct, hxc, hroot⟩
    exact ⟨c, hct, hxc, fun y hy =>
      (joint_tail_support_iff base A hj ho (hT y (hcT y hy))).mp (hroot y hy)⟩
  · intro hx
    obtain ⟨c, hcT, hct, hxc, hroot⟩ := internal_mask_cover_restrict base hT hxT hx
    exact ⟨c, hcT, hct, hxc, fun y hy =>
      (joint_tail_support_iff base A hj ho (hT y (hcT y hy))).mpr (hroot y hy)⟩

#print axioms joint_internal_mask_core_formula
end FullBridge
