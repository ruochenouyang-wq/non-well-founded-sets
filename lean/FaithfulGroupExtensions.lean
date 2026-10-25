import DisjointGroupActions
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

def GroupActionFaithful {I : Type v} {G : FiniteGroupData I} (P : TransitiveGroupAction s G) : Prop :=
  ∀ i j, (∀ x y, CodedRelation s (P.code i) x y ↔ CodedRelation s (P.code j) x y) → i = j

theorem faithful_action_extension_preserves {I : Type v} {G : FiniteGroupData I}
    {P Q : TransitiveGroupAction s G} (hPQ : GroupActionExtends P Q) (hP : GroupActionFaithful P) :
    GroupActionFaithful Q := by
  intro i j hij
  apply hP i j
  intro x y
  constructor
  · intro hxy
    obtain ⟨z, hxz, _⟩ := (P.iso j).1.2 x (coded_function_domain (P.iso i).1 hxy)
    have hyz := coded_function_value_unique (Q.iso j).1
      ((hij x y).mp (hPQ.2 i x y hxy)) (hPQ.2 j x z hxz)
    exact hyz.symm ▸ hxz
  · intro hxy
    obtain ⟨z, hxz, _⟩ := (P.iso i).1.2 x (coded_function_domain (P.iso j).1 hxy)
    have hyz := coded_function_value_unique (Q.iso i).1
      ((hij x y).mpr (hPQ.2 j x y hxy)) (hPQ.2 i x z hxz)
    exact hyz.symm ▸ hxz

/-- Extend any prescribed finite action to a faithful one by adjoining a fresh
    actual finite regular orbit. The prescribed action need not be faithful. -/
theorem bafa_faithful_group_action_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} {G : FiniteGroupData I} (P : TransitiveGroupAction s G) :
    ∃ Q : TransitiveGroupAction s G, GroupActionExtends P Q ∧ GroupActionFaithful Q := by
  obtain ⟨R, q, _, hqi, _, hreg, hDisj⟩ := finite_quine_regular_action_outside base hB G P.domain
  have hR : GroupActionFaithful R := by
    intro i j hij
    have hi : CodedRelation s (R.code i) (q G.one) (q i) := by
      apply (hreg i _ _).mpr
      exact ⟨G.one, rfl, by rw [G.mul_one]⟩
    have hj : CodedRelation s (R.code j) (q G.one) (q j) := by
      apply (hreg j _ _).mpr
      exact ⟨G.one, rfl, by rw [G.mul_one]⟩
    exact hqi i j (coded_function_value_unique (R.iso j).1 ((hij _ _).mp hi) hj)
  obtain ⟨Q, hPQ, hRQ⟩ := disjoint_group_action_union base P R (fun x hx hR => hDisj x hR hx)
  exact ⟨Q, hPQ, faithful_action_extension_preserves hRQ hR⟩

theorem bafa_subgroup_faithful_cover_extension (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (P : TransitiveGroupAction s G) (x : U) :
    ∃ Q : TransitiveGroupAction s H, Subset s P.domain Q.domain ∧ s x Q.domain ∧
      (∀ g y z, CodedRelation s (P.code g) y z → CodedRelation s (Q.code (f.map g)) y z) ∧
      GroupActionFaithful Q := by
  obtain ⟨R, hPR, hxR, hExt⟩ := bafa_subgroup_cover_extension base hB f P x
  obtain ⟨Q, hRQ, hQ⟩ := bafa_faithful_group_action_extension base hB R
  exact ⟨Q, fun y hy => hRQ.1 y (hPR y hy), hRQ.1 x hxR,
    fun g y z hyz => hRQ.2 (f.map g) y z (hExt g y z hyz), hQ⟩

#print axioms bafa_subgroup_faithful_cover_extension
end FullBridge
