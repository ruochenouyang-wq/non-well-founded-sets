import BafaRelativeGroupExtension
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

/-- Prescribed internally coded finite actions on one fixed transitive set.
    This is input action data, not an assumption that global extensions exist. -/
structure FixedCoreActions (s : U → U → Prop) {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) where
  domain : U
  stage : ∀ n, TransitiveGroupAction s (E.group n)
  domain_eq : ∀ n, (stage n).domain = domain
  step : ∀ n i x y, CodedRelation s ((stage n).code i) x y →
    CodedRelation s ((stage (n+1)).code (exhaustionLift E (Nat.le_succ n) i)) x y

theorem fixed_core_step_compatible {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (A : FixedCoreActions s E) (n : Nat)
    {P : TransitiveGroupAction s (E.group n)} (hAP : GroupActionExtends (A.stage n) P) :
    CoreActionCompatible (exhaustionEmbedding E (Nat.le_succ n)) P (A.stage (n+1)) := by
  constructor
  · intro x hx
    apply hAP.1 x
    rw [A.domain_eq n, ← A.domain_eq (n+1)]
    exact hx
  · intro g x y hxy
    have hx := coded_function_domain ((A.stage (n+1)).iso _).1 hxy
    have hx' : s x (A.stage n).domain := by
      rw [A.domain_eq n, ← A.domain_eq (n+1)]; exact hx
    obtain ⟨z, hxz, _⟩ := ((A.stage n).iso g).1.2 x hx'
    have he := coded_function_value_unique ((A.stage (n+1)).iso _).1 hxy (A.step n g x z hxz)
    exact he.symm ▸ hAP.2 g x z hxz

theorem controlled_group_cover_step (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} {E : FiniteGroupExhaustion.{v,w} D}
    (A : FixedCoreActions s E) (n : Nat) (P : TransitiveGroupAction s (E.group n))
    (hAP : GroupActionExtends (A.stage n) P) (x : U) :
    ∃ R : TransitiveGroupAction s (E.group (n+1)), Subset s P.domain R.domain ∧ s x R.domain ∧
      (∀ i y z, CodedRelation s (P.code i) y z →
        CodedRelation s (R.code (exhaustionLift E (Nat.le_succ n) i)) y z) ∧
      GroupActionExtends (A.stage (n+1)) R ∧ GroupActionFaithful R := by
  obtain ⟨Q, hPQ, hxQ, hExt, hAQ⟩ := bafa_relative_subgroup_cover_extension base hB
    (exhaustionEmbedding E (Nat.le_succ n)) P (A.stage (n+1)) (fixed_core_step_compatible A n hAP) x
  obtain ⟨R, hQR, hFaith⟩ := bafa_faithful_group_action_extension base hB Q
  exact ⟨R, fun y hy => hQR.1 y (hPQ y hy), hQR.1 x hxQ,
    fun i y z hyz => hQR.2 _ y z (hExt i y z hyz),
    ⟨fun y hy => hQR.1 y (hAQ.1 y hy), fun i y z hyz => hQR.2 i y z (hAQ.2 i y z hyz)⟩, hFaith⟩

noncomputable def controlledGroupNext (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} {E : FiniteGroupExhaustion.{v,w} D}
    (A : FixedCoreActions s E) (n : Nat)
    (P : {P : TransitiveGroupAction s (E.group n) // GroupActionExtends (A.stage n) P}) (x : U) :
    {R : TransitiveGroupAction s (E.group (n+1)) // GroupActionExtends (A.stage (n+1)) R} :=
  ⟨Classical.choose (controlled_group_cover_step base hB A n P.val P.property x),
    (Classical.choose_spec (controlled_group_cover_step base hB A n P.val P.property x)).2.2.2.1⟩

noncomputable def controlledGroupSequence (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} {E : FiniteGroupExhaustion.{v,w} D}
    (A : FixedCoreActions s E) (P : TransitiveGroupAction s (E.group 0))
    (hAP : GroupActionExtends (A.stage 0) P) (enum : Nat → U) :
    ∀ n, {R : TransitiveGroupAction s (E.group n) // GroupActionExtends (A.stage n) R}
  | 0 => ⟨P, hAP⟩
  | n+1 => controlledGroupNext base hB A n (controlledGroupSequence base hB A P hAP enum n) (enum n)

theorem controlled_growing_group_chain (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} {E : FiniteGroupExhaustion.{v,w} D}
    (A : FixedCoreActions s E) (P : TransitiveGroupAction s (E.group 0))
    (hAP : GroupActionExtends (A.stage 0) P) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : GrowingGroupChain s E, C.stage 0 = P ∧
      (∀ n, GroupActionExtends (A.stage n) (C.stage n)) ∧
      (∀ n, GroupActionFaithful (C.stage (n+1))) := by
  let seq := controlledGroupSequence base hB A P hAP enum
  have hn := fun n => Classical.choose_spec (controlled_group_cover_step base hB A n (seq n).val (seq n).property (enum n))
  refine ⟨⟨fun n => (seq n).val, fun n => (hn n).1, fun n => (hn n).2.2.1, ?_⟩,
    rfl, fun n => (seq n).property, fun n => (hn n).2.2.2.2⟩
  intro x
  obtain ⟨n, rfl⟩ := henum x
  exact ⟨n+1, (hn n).2.1⟩

#print axioms controlled_growing_group_chain
end FullBridge
