import CompleteCoveredModel
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The trivial action on a transitive source domain has an actual source
    function family indexed by all internal masks. No object choice is used. -/
theorem trivial_coded_mask_action (base : BaseCollection s) {w T : U}
    (hT : TransitiveCode s T) :
    ∃ A : CodedMaskAction base w, A.domain = T ∧
      ∀ i x y, CodedRelation s (A.maps i) x y ↔ s x T ∧ y = x := by
  obtain ⟨id, hidF, hid⟩ := definable_function_code base (Formula.equal (n := 2) 0 1) Fin.elim0 T (by
    intro x _
    exact ⟨x, rfl, fun y h => h⟩)
  have hid' : ∀ x y, CodedRelation s id x y ↔ s x T ∧ y = x := hid
  have hi : MembershipIsoCode s T T id := by
    refine ⟨hidF, ?_, ?_, ?_⟩
    · intro x y z hx hy
      exact ((hid' x z).mp hx).2.symm.trans ((hid' y z).mp hy).2
    · intro y
      exact ⟨fun hy => ⟨y, hy, (hid' y y).mpr ⟨hy, rfl⟩⟩,
        fun ⟨x, hx, hxy⟩ => ((hid' x y).mp hxy).2.symm ▸ hx⟩
    · intro x y X Y hx hy
      rcases (hid' x X).mp hx with ⟨_, rfl⟩
      rcases (hid' y Y).mp hy with ⟨_, rfl⟩
      rfl
  obtain ⟨G, hG⟩ := base.powerset w
  obtain ⟨K, hK, hKr⟩ := definable_function_code base (Formula.equal (n := 3) 0 2)
    (cons id Fin.elim0) G (by
      intro i _
      exact ⟨id, rfl, fun f h => h⟩)
  have hKcodes : ∀ i : InternalMask s w, CodedRelation s K i.val id :=
    fun i => (hKr i.val id).mpr ⟨(hG i.val).mpr i.property, rfl⟩
  have hOne : ∀ x y, CodedRelation s id x y → x = y := fun x y h => ((hid' x y).mp h).2.symm
  have hMul : ∀ x z, CodedRelation s id x z ↔
      ∃ y, CodedRelation s id x y ∧ CodedRelation s id y z := by
    intro x z
    constructor
    · intro h
      exact ⟨x, (hid' x x).mpr ⟨((hid' x z).mp h).1, rfl⟩, h⟩
    · rintro ⟨y, hxy, hyz⟩
      exact (hOne x y hxy).symm ▸ hyz
  exact ⟨⟨T, hT, G, hG, K, hK, fun _ => id, hKcodes, fun _ => hi, hOne,
    fun _ _ => hMul⟩, rfl, fun _ => hid'⟩

/-- Every ambient transitive set has a coded isomorphic copy whose members
    are fixed by every mask, and hence are internally covered in the same J. -/
theorem universal_fixed_transitive_copy (base : BaseCollection s) {z w T : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (ctx : UniversalActionContext base J) (hT : TransitiveCode s T) :
    ∃ c f, TransitiveCode s c ∧ MembershipIsoCode s T c f ∧
      ∀ Y, s Y c → (∀ i, J i Y = Y) ∧ InternalMaskCovered s w J Y := by
  obtain ⟨A, hAT, hAr⟩ := trivial_coded_mask_action (w := w) base hT
  obtain ⟨B, f, ⟨E⟩, hBJ⟩ := universal_any_action_realized base ctx A
  have hfix : ∀ Y, s Y E.range → ∀ i, J i Y = Y := by
    intro Y hY i
    obtain ⟨x, hx, hxY⟩ := (E.iso.2.2.1 Y).mp hY
    exact hBJ i Y Y (E.intertwines i x x Y Y
      ((hAr i x x).mpr ⟨hAT ▸ hx, rfl⟩) hxY hxY)
  exact ⟨E.range, f, E.transitive, hAT ▸ E.iso, fun Y hY => ⟨hfix Y hY,
    E.range, E.transitive, hY, fun Z hZ => ⟨z, hw.2.1.1, fun i _ => hfix Z hZ i⟩⟩⟩

/-- All ambient behaviors have representatives in Hc. Representatives can
    even be chosen fixed by every internal mask; object AC is not assumed. -/
theorem universal_covered_behavior_representative (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (ctx : UniversalActionContext base J) (x : U) :
    ∃ Y : CoveredMaskCarrier s w J, InternalBehavior s x Y.val ∧ ∀ i, J i Y.val = Y.val := by
  obtain ⟨T, hT, hxT⟩ := transitive_sets_cover base x
  obtain ⟨c, f, hc, hf, hfixed⟩ := universal_fixed_transitive_copy base hw ctx hT
  obtain ⟨Y, hxY, _⟩ := hf.1.2 x hxT
  have hYc := (hf.2.2.1 Y).mpr ⟨x, hxT, hxY⟩
  exact ⟨⟨Y, (hfixed Y hYc).2⟩,
    (internal_code_eq base x Y).mp (((membership_iso_over_quotient base hT hc hf).2 x Y hxY).2),
    (hfixed Y hYc).1⟩

#print axioms trivial_coded_mask_action
#print axioms universal_fixed_transitive_copy
#print axioms universal_covered_behavior_representative
end FullBridge
