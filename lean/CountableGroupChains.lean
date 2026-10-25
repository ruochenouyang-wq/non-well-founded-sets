import BafaFiniteGroupExtension
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

structure TransitiveGroupAction (s : U → U → Prop) {I : Type v} (G : FiniteGroupData I) where
  domain : U
  code : I → U
  transitive : TransitiveCode s domain
  iso : ∀ i, MembershipIsoCode s domain domain (code i)
  identity : ∀ x y, CodedRelation s (code G.one) x y → x = y
  multiplication : ∀ i j x z, CodedRelation s (code (G.mul i j)) x z ↔
    ∃ y, CodedRelation s (code j) x y ∧ CodedRelation s (code i) y z

def TransitiveGroupAction.partialIso {I : Type v} {G : FiniteGroupData I}
    (P : TransitiveGroupAction s G) (i : I) : TransitivePartialIso s :=
  ⟨P.domain, P.domain, P.code i, P.transitive, P.transitive, P.iso i⟩

def GroupActionExtends {I : Type v} {G : FiniteGroupData I}
    (P Q : TransitiveGroupAction s G) : Prop :=
  Subset s P.domain Q.domain ∧ ∀ i x y,
    CodedRelation s (P.code i) x y → CodedRelation s (Q.code i) x y

theorem internal_group_action_step (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (P : TransitiveGroupAction s G) (x : U) :
    ∃ Q : TransitiveGroupAction s G, GroupActionExtends P Q ∧ s x Q.domain := by
  obtain ⟨C, out, hC, hPC, hxC, ho, hOne, hMul, hExt⟩ :=
    bafa_finite_group_cover_extension base hB G P.transitive P.code P.iso P.identity P.multiplication x
  exact ⟨⟨C, out, hC, ho, hOne, hMul⟩, ⟨hPC, hExt⟩, hxC⟩

noncomputable def groupActionNext (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (P : TransitiveGroupAction s G) (x : U) :
    TransitiveGroupAction s G := Classical.choose (internal_group_action_step base hB G P x)

noncomputable def enumeratedGroupSequence (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (P : TransitiveGroupAction s G) (enum : Nat → U) :
    Nat → TransitiveGroupAction s G
  | 0 => P
  | n+1 => groupActionNext base hB G (enumeratedGroupSequence base hB G P enum n) (enum n)

structure CoveringGroupChain (s : U → U → Prop) {I : Type v} (G : FiniteGroupData I) where
  stage : Nat → TransitiveGroupAction s G
  step_extends : ∀ n, GroupActionExtends (stage n) (stage (n+1))
  covers : ∀ x, ∃ n, s x (stage n).domain

def CoveringGroupChain.isoChain {I : Type v} {G : FiniteGroupData I}
    (C : CoveringGroupChain s G) (i : I) : CoveringIsoChain s where
  stage := fun n => (C.stage n).partialIso i
  step_extends := fun n => ⟨(C.step_extends n).1, (C.step_extends n).1, (C.step_extends n).2 i⟩
  covers_domain := C.covers
  covers_range := C.covers

theorem enumerated_covering_group_chain (base : BaseCollection s) (hB : BAFACode s)
    {I : Type v} (G : FiniteGroupData I) (P : TransitiveGroupAction s G)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : CoveringGroupChain s G, C.stage 0 = P := by
  let seq := enumeratedGroupSequence base hB G P enum
  have hn : ∀ n, GroupActionExtends (seq n) (seq (n+1)) ∧ s (enum n) (seq (n+1)).domain :=
    fun n => Classical.choose_spec (internal_group_action_step base hB G (seq n) (enum n))
  refine ⟨⟨seq, fun n => (hn n).1, ?_⟩, rfl⟩
  intro x
  obtain ⟨n, rfl⟩ := henum x
  exact ⟨n+1, (hn n).2⟩

noncomputable def groupChainMap {I : Type v} {G : FiniteGroupData I}
    (C : CoveringGroupChain s G) (i : I) : U → U := isoChainMap (C.isoChain i)

theorem group_chain_map_identity {I : Type v} {G : FiniteGroupData I}
    (C : CoveringGroupChain s G) (x : U) : groupChainMap C G.one x = x := by
  obtain ⟨n, hn⟩ := iso_chain_map_relation (C.isoChain G.one) x
  exact ((C.stage n).identity x _ hn).symm

/-- Move the two pointwise evaluations into one common stage before using
    its multiplication table; independently chosen chains would not suffice. -/
theorem group_chain_map_multiplication {I : Type v} {G : FiniteGroupData I}
    (C : CoveringGroupChain s G) (i j : I) (x : U) :
    groupChainMap C (G.mul i j) x = groupChainMap C i (groupChainMap C j x) := by
  obtain ⟨n, hn⟩ := iso_chain_map_relation (C.isoChain j) x
  obtain ⟨m, hm⟩ := iso_chain_map_relation (C.isoChain i) (groupChainMap C j x)
  have hn' := (covering_chain_mono (C.isoChain j) (Nat.le_max_left n m)).2.2 x _ hn
  have hm' := (covering_chain_mono (C.isoChain i) (Nat.le_max_right n m)).2.2 _ _ hm
  exact iso_chain_map_value (C.isoChain (G.mul i j))
    ⟨max n m, ((C.stage (max n m)).multiplication i j x _).mpr ⟨_, hn', hm'⟩⟩

#print axioms enumerated_covering_group_chain
#print axioms group_chain_map_multiplication
end FullBridge
