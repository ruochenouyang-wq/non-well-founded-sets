import GraphEnrichedMaskCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem elementary_map_ordered_pair {j : U → U} (hj : ElementaryMap s s j)
    {p x y : U} (hp : IsOrderedPair s p x y) : IsOrderedPair s (j p) (j x) (j y) := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  exact ⟨j a, j b, elementary_map_pair hj ha, elementary_map_pair hj hb, elementary_map_pair hj hp⟩

theorem equivariant_relation_fixed (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (hs : ∀ x, j (j x) = x) {f : U}
    (hnorm : ∀ p, s p f → ∃ x y, IsOrderedPair s p x y)
    (heq : ∀ x y, CodedRelation s f x y → CodedRelation s f (j x) (j y)) : j f = f := by
  apply elementary_involution_closed_set base hj hs
  intro p hp
  obtain ⟨x, y, hpxy⟩ := hnorm p hp
  obtain ⟨q, hq, hqxy⟩ := heq x y ⟨p, hp, hpxy⟩
  have h := orderedPair_unique base.extensional (elementary_map_ordered_pair hj hpxy) hqxy
  exact h.symm ▸ hq

theorem equivariant_function_fixed (base : BaseCollection s) {j : U → U}
    (hj : ElementaryMap s s j) (hs : ∀ x, j (j x) = x) {a f : U}
    (hf : FunctionCode s a f)
    (heq : ∀ x y, CodedRelation s f x y → CodedRelation s f (j x) (j y)) : j f = f := by
  apply equivariant_relation_fixed base hj hs (heq := heq)
  intro p hp
  obtain ⟨x, y, _, hxy⟩ := hf.1 p hp
  exact ⟨x, y, hxy⟩

theorem hereditary_mask_ordered_pair (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    {p x y : U} (hx : HereditarilyMaskSupported s w J x) (hy : HereditarilyMaskSupported s w J y)
    (hp : IsOrderedPair s p x y) : HereditarilyMaskSupported s w J p := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  exact hereditary_mask_pair base hw hj
    (hereditary_mask_pair base hw hj hx hx ha) (hereditary_mask_pair base hw hj hx hy hb) hp

/-- This condition is equivariance under actual universe maps on BOTH
    input nodes and values; an unrelated trivial action on nodes is insufficient. -/
def MaskTailEquivariantFunction (s : U → U → Prop) {w : U}
    (J : InternalMask s w → U → U) (f : U) : Prop :=
  ∃ N, s N w ∧ ∀ i, (∀ k, s k i.val → ¬s k N) → ∀ x y,
    CodedRelation s f x y → CodedRelation s f (J i x) (J i y)

theorem mask_equivariant_function_supported (base : BaseCollection s) {w a f : U}
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (hs : ∀ i x, J i (J i x) = x) (hf : FunctionCode s a f)
    (heq : MaskTailEquivariantFunction s J f) : MaskTailSupported s w J f := by
  obtain ⟨N, hN, heq⟩ := heq
  exact ⟨N, hN, fun i hi => equivariant_function_fixed base (hj i) (hs i) hf (heq i hi)⟩

theorem mask_equivariant_value_supported (base : BaseCollection s) {z w a f x X : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hf : FunctionCode s a f) (heq : MaskTailEquivariantFunction s J f)
    (hx : MaskTailSupported s w J x) (hxX : CodedRelation s f x X) : MaskTailSupported s w J X := by
  obtain ⟨N, hN, heq⟩ := heq
  obtain ⟨M, hM, hx⟩ := hx
  obtain ⟨K, hK, hNK, hMK⟩ := internal_omega_common_bound base hw hN hM
  refine ⟨K, hK, fun i hi => ?_⟩
  have h := heq i (fun k hk h => hi k hk (hNK k h)) x X hxX
  rw [hx i (fun k hk h => hi k hk (hMK k h))] at h
  exact coded_function_value_unique hf h hxX

theorem mask_equivariant_decoration_hereditary (base : BaseCollection s) {z w a r f : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (hf : DecorationCode s a r f) (heq : MaskTailEquivariantFunction s J f)
    (hnodes : ∀ x, s x a → HereditarilyMaskSupported s w J x) :
    HereditarilyMaskSupported s w J f ∧
      ∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J X := by
  have hvalues : ∀ x X, CodedRelation s f x X → HereditarilyMaskSupported s w J X := by
    intro x X hxX Y hXY
    obtain ⟨y, hyY⟩ := decoration_descendant_range hf hXY ⟨x, hxX⟩
    exact mask_equivariant_value_supported base hw hf.1 heq
      (hereditary_mask_root (hnodes y (coded_function_domain hf.1 hyY))) hyY
  refine ⟨hereditary_mask_intro (mask_equivariant_function_supported base hj hs hf.1 heq) ?_, hvalues⟩
  intro p hp
  obtain ⟨x, X, hx, hpxX⟩ := hf.1.1 p hp
  exact hereditary_mask_ordered_pair base hw hj (hnodes x hx)
    (hvalues x X ⟨p, hp, hpxX⟩) hpxX

#print axioms mask_equivariant_decoration_hereditary
end FullBridge
