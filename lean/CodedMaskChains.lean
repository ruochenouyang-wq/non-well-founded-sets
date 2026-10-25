import BafaCodedMaskExtension
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def CodedMaskExtends (base : BaseCollection s) {w : U} (A B : CodedMaskAction base w) : Prop :=
  Subset s A.domain B.domain ∧ ∀ a x y, CodedRelation s (A.maps a) x y → CodedRelation s (B.maps a) x y

noncomputable def codedMaskNext (base : BaseCollection s) (hB : BAFACode s) {w : U}
    (A : CodedMaskAction base w) (x : U) : CodedMaskAction base w :=
  Classical.choose (bafa_coded_mask_cover_extension base hB A x)

noncomputable def enumeratedCodedMaskSequence (base : BaseCollection s) (hB : BAFACode s) {w : U}
    (A : CodedMaskAction base w) (enum : Nat → U) : Nat → CodedMaskAction base w
  | 0 => A
  | n+1 => codedMaskNext base hB (enumeratedCodedMaskSequence base hB A enum n) (enum n)

structure CoveringCodedMaskChain (base : BaseCollection s) (w : U) where
  stage : Nat → CodedMaskAction base w
  step : ∀ n, CodedMaskExtends base (stage n) (stage (n+1))
  covers : ∀ x, ∃ n, s x (stage n).domain

def CoveringCodedMaskChain.isoChain (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (a : InternalMask s w) : CoveringIsoChain s where
  stage := fun n => ⟨(C.stage n).domain, (C.stage n).domain, (C.stage n).maps a,
    (C.stage n).transitive, (C.stage n).transitive, (C.stage n).iso a⟩
  step_extends := fun n => ⟨(C.step n).1, (C.step n).1, (C.step n).2 a⟩
  covers_domain := C.covers
  covers_range := C.covers

theorem enumerated_coded_mask_chain (base : BaseCollection s) (hB : BAFACode s) {w : U}
    (A : CodedMaskAction base w) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : CoveringCodedMaskChain base w, C.stage 0 = A := by
  let seq := enumeratedCodedMaskSequence base hB A enum
  have hn := fun n => Classical.choose_spec (bafa_coded_mask_cover_extension base hB (seq n) (enum n))
  refine ⟨⟨seq, fun n => ⟨(hn n).1, (hn n).2.2.2.1⟩, ?_⟩, rfl⟩
  intro x
  obtain ⟨n, rfl⟩ := henum x
  exact ⟨n+1, (hn n).2.1⟩

noncomputable def codedMaskChainMap (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (a : InternalMask s w) : U → U := isoChainMap (C.isoChain base a)

theorem coded_mask_chain_identity (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (x : U) : codedMaskChainMap base C (internalMaskOne base w) x = x := by
  obtain ⟨n, hn⟩ := iso_chain_map_relation (C.isoChain base (internalMaskOne base w)) x
  exact ((C.stage n).one x _ hn).symm

theorem coded_mask_chain_multiplication (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (a b : InternalMask s w) (x : U) :
    codedMaskChainMap base C (internalMaskMul base a b) x =
      codedMaskChainMap base C a (codedMaskChainMap base C b x) := by
  obtain ⟨n, hn⟩ := iso_chain_map_relation (C.isoChain base b) x
  obtain ⟨m, hm⟩ := iso_chain_map_relation (C.isoChain base a) (codedMaskChainMap base C b x)
  have hn' := (covering_chain_mono (C.isoChain base b) (Nat.le_max_left n m)).2.2 x _ hn
  have hm' := (covering_chain_mono (C.isoChain base a) (Nat.le_max_right n m)).2.2 _ _ hm
  exact iso_chain_map_value (C.isoChain base (internalMaskMul base a b))
    ⟨max n m, ((C.stage (max n m)).mul a b x _).mpr ⟨_, hn', hm'⟩⟩

/-- Every stage retains a single source code for all limit-action
    restrictions; the global limit is not built mask by mask. -/
theorem coded_mask_chain_joint_domain (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (n : Nat) :
    Nonempty (JointMaskDomain s w (codedMaskChainMap base C) (C.stage n).domain) := by
  let A := C.stage n
  have hrel : ∀ a x y, CodedRelation s (A.maps a) x y ↔
      s x A.domain ∧ codedMaskChainMap base C a x = y := by
    intro a x y
    constructor
    · intro hxy
      exact ⟨coded_function_domain (A.iso a).1 hxy, iso_chain_map_value (C.isoChain base a) ⟨n, hxy⟩⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨z, hxz, _⟩ := (A.iso a).1.2 x hx
      have he := (iso_chain_map_value (C.isoChain base a) ⟨n, hxz⟩).symm.trans hy
      exact he ▸ hxz
  refine ⟨⟨A.masks, A.maskMembers, A.family, A.familyFunction, ?_, ?_⟩⟩
  · intro a f haf
    have he := coded_function_value_unique A.familyFunction haf (A.mapCodes a)
    exact he.symm ▸ ⟨(A.iso a).1, hrel a⟩
  · intro a x hx
    obtain ⟨y, hxy, _⟩ := (A.iso a).1.2 x hx
    have hy := ((A.iso a).2.2.1 y).mpr ⟨x, hx, hxy⟩
    exact ((hrel a x y).mp hxy).2.symm ▸ hy

theorem coded_mask_chain_joint_covers (base : BaseCollection s) {w : U}
    (C : CoveringCodedMaskChain base w) (d : U) :
    ∃ t, Nonempty (JointMaskDomain s w (codedMaskChainMap base C) t) ∧ Subset s d t := by
  obtain ⟨n, hn⟩ := C.covers d
  exact ⟨(C.stage n).domain, coded_mask_chain_joint_domain base C n,
    fun x hx => (C.stage n).transitive d hn x hx⟩
end FullBridge
