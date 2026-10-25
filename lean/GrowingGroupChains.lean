import FiniteGroupExhaustions
namespace FullBridge
universe u v w
variable {U : Type u} {s : U → U → Prop}

structure GrowingGroupChain (s : U → U → Prop) {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) where
  stage : ∀ n, TransitiveGroupAction s (E.group n)
  domain_step : ∀ n, Subset s (stage n).domain (stage (n+1)).domain
  action_step : ∀ n i x y, CodedRelation s ((stage n).code i) x y →
    CodedRelation s ((stage (n+1)).code (exhaustionLift E (Nat.le_succ n) i)) x y
  covers : ∀ x, ∃ n, s x (stage n).domain

noncomputable def growingGroupNext (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (n : Nat) (P : TransitiveGroupAction s (E.group n)) (x : U) :
    TransitiveGroupAction s (E.group (n+1)) :=
  Classical.choose (bafa_subgroup_cover_extension base hB (exhaustionEmbedding E (Nat.le_succ n)) P x)

noncomputable def growingGroupSequence (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (P : TransitiveGroupAction s (E.group 0)) (enum : Nat → U) :
    ∀ n, TransitiveGroupAction s (E.group n)
  | 0 => P
  | n+1 => growingGroupNext base hB E n (growingGroupSequence base hB E P enum n) (enum n)

theorem growing_group_covering_chain (base : BaseCollection s) (hB : BAFACode s)
    {K : Type v} {D : ExternalGroupData K} (E : FiniteGroupExhaustion.{v,w} D)
    (P : TransitiveGroupAction s (E.group 0)) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : GrowingGroupChain s E, C.stage 0 = P := by
  let seq := growingGroupSequence base hB E P enum
  have hn := fun n => Classical.choose_spec
    (bafa_subgroup_cover_extension base hB (exhaustionEmbedding E (Nat.le_succ n)) (seq n) (enum n))
  refine ⟨⟨seq, fun n => (hn n).1, fun n => (hn n).2.2, ?_⟩, rfl⟩
  intro x
  obtain ⟨n, rfl⟩ := henum x
  exact ⟨n+1, (hn n).2.1⟩

theorem growing_group_domain_mono {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E)
    {n m : Nat} (h : n ≤ m) : Subset s (C.stage n).domain (C.stage m).domain := by
  induction h with
  | refl => exact fun _ hx => hx
  | @step m h ih => exact fun x hx => C.domain_step m x (ih x hx)

theorem growing_group_action_mono {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E)
    {n m : Nat} (h : n ≤ m) (i : E.Stage n) {x y : U}
    (hxy : CodedRelation s ((C.stage n).code i) x y) :
    CodedRelation s ((C.stage m).code (exhaustionLift E h i)) x y := by
  induction h with
  | refl => simpa only [exhaustion_lift_refl] using hxy
  | @step m h ih =>
    have hs := C.action_step m (exhaustionLift E h i) x y ih
    simpa only [exhaustion_lift_comp] using hs

def GrowingActionRelation {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) (x y : U) : Prop :=
  ∃ n i, E.embed n i = g ∧ CodedRelation s ((C.stage n).code i) x y

theorem growing_action_relation_total {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) (x : U) :
    ∃ y, GrowingActionRelation C g x y := by
  obtain ⟨n, i, hi⟩ := E.covers g
  obtain ⟨m, hm⟩ := C.covers x
  have hx := growing_group_domain_mono C (Nat.le_max_right n m) x hm
  let i' := exhaustionLift E (Nat.le_max_left n m) i
  obtain ⟨y, hxy, _⟩ := (C.stage (max n m)).iso i' |>.1.2 x hx
  exact ⟨y, max n m, i', (exhaustion_lift_embed E _ i).trans hi, hxy⟩

theorem growing_action_relation_unique {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) {g : K} {x y z : U}
    (hy : GrowingActionRelation C g x y) (hz : GrowingActionRelation C g x z) : y = z := by
  obtain ⟨n, i, hi, hxy⟩ := hy
  obtain ⟨m, j, hj, hxz⟩ := hz
  have hi' := exhaustion_lift_embed E (Nat.le_max_left n m) i
  have hj' := exhaustion_lift_embed E (Nat.le_max_right n m) j
  have hij := E.injective (max n m) _ _ (hi'.trans (hi.trans (hj.symm.trans hj'.symm)))
  exact coded_function_value_unique ((C.stage (max n m)).iso _).1
    (growing_group_action_mono C (Nat.le_max_left n m) i hxy)
    (hij.symm ▸ growing_group_action_mono C (Nat.le_max_right n m) j hxz)

noncomputable def growingActionMap {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) (x : U) : U :=
  Classical.choose (growing_action_relation_total C g x)

theorem growing_action_map_relation {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) (g : K) (x : U) :
    GrowingActionRelation C g x (growingActionMap C g x) :=
  Classical.choose_spec (growing_action_relation_total C g x)

theorem growing_action_map_value {K : Type v} {D : ExternalGroupData K}
    {E : FiniteGroupExhaustion.{v,w} D} (C : GrowingGroupChain s E) {g : K} {x y : U}
    (h : GrowingActionRelation C g x y) : growingActionMap C g x = y :=
  growing_action_relation_unique C (growing_action_map_relation C g x) h

#print axioms growing_group_covering_chain
#print axioms growing_action_map_value
end FullBridge
