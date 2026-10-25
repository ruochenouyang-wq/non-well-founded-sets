import GlobalOrbitSolutions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure JointUniverseState (base : BaseCollection s) (w : U) where
  maps : InternalMask s w → U → U
  elementary : ∀ i, ElementaryMap s s (maps i) ∧ (∀ y, ∃ x, maps i x = y) ∧ LocallyInternalTransitiveMap s (maps i)
  one : ∀ x, maps (internalMaskOne base w) x = x
  mul : ∀ i j x, maps (internalMaskMul base i j) x = maps i (maps j x)
  covers : ∀ d, ∃ B, TransitiveCode s B ∧ Nonempty (JointMaskDomain s w maps B) ∧ Subset s d B
  retained : CodedMaskAction base w
  agrees : ∀ i x y, CodedRelation s (retained.maps i) x y → maps i x = y

theorem joint_universe_involutive (base : BaseCollection s) {w : U}
    (A : JointUniverseState base w) : ∀ i x, A.maps i (A.maps i x) = x := by
  intro i x
  have h := A.mul i i x
  rw [internal_mask_mul_self] at h
  exact h.symm.trans (A.one x)

theorem joint_universe_state_exists (base : BaseCollection s) (hBAFA : BAFACode s) {w : U}
    (P : CodedMaskAction base w) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ A : JointUniverseState base w, A.retained = P := by
  obtain ⟨J, hJ, hOne, hMul, hP, _, hCover⟩ := countable_bafa_transitive_joint_extension base hBAFA P enum henum
  exact ⟨⟨J, hJ, hOne, hMul, hCover, P, hP⟩, rfl⟩

theorem joint_universe_retained_agreement (base : BaseCollection s) {w : U}
    {A B : JointUniverseState base w} (h : CodedMaskExtends base A.retained B.retained) :
    ∀ i x, s x A.retained.domain → B.maps i x = A.maps i x := by
  intro i x hx
  obtain ⟨y, hxy, _⟩ := (A.retained.iso i).1.2 x hx
  exact (B.agrees i x y (h.2 i x y hxy)).trans (A.agrees i x y hxy).symm

theorem joint_universe_retain (base : BaseCollection s) {w : U}
    (A : JointUniverseState base w) (d : U) :
    ∃ B : JointUniverseState base w, CodedMaskExtends base A.retained B.retained ∧
      Subset s d B.retained.domain ∧ B.maps = A.maps := by
  obtain ⟨S, hS⟩ := binary_union_exists base.pairing base.union A.retained.domain d
  obtain ⟨T, hT, ⟨K⟩, hST⟩ := A.covers S
  obtain ⟨P, hP, _, _, hPr⟩ := joint_mask_coded_action base K hT
    (fun i => (A.elementary i).1) (joint_universe_involutive base A) A.one A.mul
  have hOld : Subset s A.retained.domain P.domain := by
    intro x hx
    rw [hP]
    exact hST x ((hS x).mpr (Or.inl hx))
  have hNew : Subset s d P.domain := by
    intro x hx
    rw [hP]
    exact hST x ((hS x).mpr (Or.inr hx))
  let B : JointUniverseState base w := { A with retained := P, agrees := fun i x y h => ((hPr i x y).mp h).2 }
  refine ⟨B, ⟨hOld, ?_⟩, hNew, rfl⟩
  intro i x y hxy
  exact (hPr i x y).mpr ⟨hP ▸ hOld x (coded_function_domain (A.retained.iso i).1 hxy), A.agrees i x y hxy⟩

theorem hereditary_mask_ordered_pair_components {w p x y : U} {J : InternalMask s w → U → U}
    (hp : IsOrderedPair s p x y) (hH : HereditarilyMaskSupported s w J p) :
    HereditarilyMaskSupported s w J x ∧ HereditarilyMaskSupported s w J y := by
  obtain ⟨a, b, _, hb, hp⟩ := hp
  have hbH := hereditary_mask_member hH ((hp b).mpr (Or.inr rfl))
  exact ⟨hereditary_mask_member hbH ((hb x).mpr (Or.inl rfl)),
    hereditary_mask_member hbH ((hb y).mpr (Or.inr rfl))⟩

theorem hereditary_mask_request_components {w p t a r : U} {J : InternalMask s w → U → U}
    (hp : OrbitGraphParameters s p t a r) (hH : HereditarilyMaskSupported s w J p) :
    HereditarilyMaskSupported s w J t ∧ HereditarilyMaskSupported s w J a ∧ HereditarilyMaskSupported s w J r := by
  obtain ⟨b, hb, hp⟩ := hp
  have h := hereditary_mask_ordered_pair_components hp hH
  exact ⟨h.1, hereditary_mask_ordered_pair_components hb h.2⟩

theorem coded_mask_extends_trans (base : BaseCollection s) {w : U} {A B C : CodedMaskAction base w}
    (hAB : CodedMaskExtends base A B) (hBC : CodedMaskExtends base B C) : CodedMaskExtends base A C :=
  ⟨fun x hx => hBC.1 x (hAB.1 x hx), fun i x y h => hBC.2 i x y (hAB.2 i x y h)⟩

theorem joint_universe_retained_joint (base : BaseCollection s) {w : U}
    (A : JointUniverseState base w) : Nonempty (JointMaskDomain s w A.maps A.retained.domain) := by
  have hrel : ∀ i x y, CodedRelation s (A.retained.maps i) x y ↔
      s x A.retained.domain ∧ A.maps i x = y := by
    intro i x y
    constructor
    · intro h
      exact ⟨coded_function_domain (A.retained.iso i).1 h, A.agrees i x y h⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨z, hxz, _⟩ := (A.retained.iso i).1.2 x hx
      exact ((A.agrees i x z hxz).symm.trans hy) ▸ hxz
  refine ⟨⟨A.retained.masks, A.retained.maskMembers, A.retained.family, A.retained.familyFunction, ?_, ?_⟩⟩
  · intro i f hif
    have he := coded_function_value_unique A.retained.familyFunction hif (A.retained.mapCodes i)
    exact he.symm ▸ ⟨(A.retained.iso i).1, hrel i⟩
  · intro i x hx
    obtain ⟨y, hxy, _⟩ := (A.retained.iso i).1.2 x hx
    exact (A.agrees i x y hxy).symm ▸ ((A.retained.iso i).2.2.1 y).mpr ⟨x, hx, hxy⟩

#print axioms joint_universe_retain
end FullBridge
