import BafaInvolutionExtension
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure TransitiveInvolution (s : U → U → Prop) where
  domain : U
  code : U
  transitive : TransitiveCode s domain
  iso : MembershipIsoCode s domain domain code
  symmetric : ∀ x y, CodedRelation s code x y → CodedRelation s code y x

def TransitiveInvolution.partialIso (P : TransitiveInvolution s) : TransitivePartialIso s :=
  ⟨P.domain, P.domain, P.code, P.transitive, P.transitive, P.iso⟩

theorem internal_involution_step (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitiveInvolution s) (x : U) :
    ∃ Q : TransitiveInvolution s, PartialIsoExtends P.partialIso Q.partialIso ∧ s x Q.domain := by
  obtain ⟨C, q, hC, hPC, hxC, hq, hqs, hPq⟩ :=
    bafa_involution_cover_extension base hB P.transitive P.iso P.symmetric x
  exact ⟨⟨C, q, hC, hq, hqs⟩, ⟨hPC, hPC, hPq⟩, hxC⟩

noncomputable def involutionNext (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitiveInvolution s) (x : U) : TransitiveInvolution s :=
  Classical.choose (internal_involution_step base hB P x)

noncomputable def enumeratedInvolutionSequence (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitiveInvolution s) (enum : Nat → U) : Nat → TransitiveInvolution s
  | 0 => P
  | n + 1 => involutionNext base hB (enumeratedInvolutionSequence base hB P enum n) (enum n)

/-- Each stage is an involution on the same domain and range; the chain is
    constructed externally from a supplied enumeration of the whole carrier. -/
theorem enumerated_covering_involution_chain (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitiveInvolution s) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : CoveringIsoChain s, C.stage 0 = P.partialIso ∧
      ∀ n x y, CodedRelation s (C.stage n).code x y → CodedRelation s (C.stage n).code y x := by
  let seq := enumeratedInvolutionSequence base hB P enum
  have hn : ∀ n, PartialIsoExtends (seq n).partialIso (seq (n+1)).partialIso ∧
      s (enum n) (seq (n+1)).domain :=
    fun n => Classical.choose_spec (internal_involution_step base hB (seq n) (enum n))
  have hcov : ∀ x, ∃ n, s x (seq n).domain := by
    intro x
    obtain ⟨n, rfl⟩ := henum x
    exact ⟨n+1, (hn n).2⟩
  exact ⟨⟨fun n => (seq n).partialIso, fun n => (hn n).1, hcov, hcov⟩,
    rfl, fun n => (seq n).symmetric⟩

theorem iso_chain_map_involution (C : CoveringIsoChain s)
    (hs : ∀ n x y, CodedRelation s (C.stage n).code x y →
      CodedRelation s (C.stage n).code y x) (x : U) :
    isoChainMap C (isoChainMap C x) = x := by
  obtain ⟨n, hn⟩ := iso_chain_map_relation C x
  exact iso_chain_map_value C ⟨n, hs n x (isoChainMap C x) hn⟩

/-- Actual involutive extension, with full formula semantics, internal set
    restrictions, and pointwise identity on the behavior quotient. -/
theorem countable_bafa_involution_extension (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) (P : TransitiveInvolution s) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧
      (∀ x, j (j x) = x) ∧ LocallyInternalTransitiveMap s j ∧
      (∀ x y, CodedRelation s P.code x y → j x = y) ∧
      (∀ x, internalCode base (j x) = internalCode base x) ∧
      ∀ a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ j x = y := by
  obtain ⟨C, hC, hs⟩ := enumerated_covering_involution_chain base hB P enum henum
  have hl := iso_chain_map_local C
  refine ⟨isoChainMap C, bijective_membership_elementary _ (iso_chain_map_injective C)
    (iso_chain_map_surjective C) (iso_chain_map_members C), iso_chain_map_surjective C,
    iso_chain_map_involution C hs, hl, ?_, ?_, locally_internal_map_restriction base hl⟩
  · intro x y hxy
    exact iso_chain_map_value C ⟨0, hC.symm ▸ hxy⟩
  · intro x
    exact (internal_code_eq base _ x).mpr (locally_internal_map_behavior base _ hl x)

/-- Restrict an already constructed two-point swap to the literal pair,
    so that symmetry is explicit in the returned object. -/
theorem distinct_quines_internal_involution (base : BaseCollection s) {u v : U}
    (hu : SelfSingleton s u) (hv : SelfSingleton s v) (hne : u ≠ v) :
    ∃ P : TransitiveInvolution s,
      CodedRelation s P.code u v ∧ CodedRelation s P.code v u := by
  obtain ⟨Q, huv, hvu⟩ := distinct_quines_partial_swap base hu hv hne
  obtain ⟨a, ha⟩ := base.pairing u v
  have hua := (ha u).mpr (Or.inl rfl)
  have hva := (ha v).mpr (Or.inr rfl)
  have had : Subset s a Q.domain := by
    intro x hx
    rcases (ha x).mp hx with rfl | rfl
    · exact coded_function_domain Q.iso.1 huv
    · exact coded_function_domain Q.iso.1 hvu
  obtain ⟨p, hp, hpr⟩ := function_domain_restriction base Q.iso.1 had
  have hpUV := (hpr u v).mpr ⟨hua, huv⟩
  have hpVU := (hpr v u).mpr ⟨hva, hvu⟩
  have hsym : ∀ x y, CodedRelation s p x y → CodedRelation s p y x := by
    intro x y hxy
    rcases (ha x).mp (coded_function_domain hp hxy) with rfl | rfl
    · have hy := coded_function_value_unique hp hxy hpUV
      exact hy.symm ▸ hpVU
    · have hy := coded_function_value_unique hp hxy hpVU
      exact hy.symm ▸ hpUV
  have hTrans : TransitiveCode s a := by
    intro x hx y hyx
    rcases (ha x).mp hx with rfl | rfl
    · exact ((hu y).mp hyx).symm ▸ hua
    · exact ((hv y).mp hyx).symm ▸ hva
  have hi : InjectiveCode s p := by
    intro x y z hxz hyz
    exact Q.iso.2.1 x y z ((hpr x z).mp hxz).2 ((hpr y z).mp hyz).2
  have hr : RangeCode s a p a := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hyx, _⟩ := hp.2 y hy
      exact ⟨x, coded_function_domain hp (hsym y x hyx), hsym y x hyx⟩
    · rintro ⟨x, _, hxy⟩
      exact coded_function_domain hp (hsym x y hxy)
  have hIso : MembershipIsoCode s a a p :=
    ⟨hp, hi, hr, fun x y X Y hxX hyY =>
      Q.iso.2.2.2 x y X Y ((hpr x X).mp hxX).2 ((hpr y Y).mp hyY).2⟩
  exact ⟨⟨a, p, hTrans, hIso, hsym⟩, hpUV, hpVU⟩

theorem countable_bafa_quine_involution (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {u v : U}
    (hu : SelfSingleton s u) (hv : SelfSingleton s v) (hne : u ≠ v) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧
      (∀ x, j (j x) = x) ∧ j u = v ∧ j v = u ∧ LocallyInternalTransitiveMap s j ∧
      ∀ x, internalCode base (j x) = internalCode base x := by
  obtain ⟨P, huv, hvu⟩ := distinct_quines_internal_involution base hu hv hne
  obtain ⟨j, hj, ho, hs, hl, he, hq, _⟩ := countable_bafa_involution_extension base hB enum henum P
  exact ⟨j, hj, ho, hs, he u v huv, he v u hvu, hl, hq⟩

theorem countable_bafa_nontrivial_involution (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧
      (∀ x, j (j x) = x) ∧ (∃ x, j x ≠ x) ∧ LocallyInternalTransitiveMap s j ∧
      ∀ x, internalCode base (j x) = internalCode base x := by
  obtain ⟨u, v, hne, hu, hv⟩ := bafa_distinct_selfSingletons base hB
  obtain ⟨j, hj, ho, hs, huv, _, hl, hq⟩ :=
    countable_bafa_quine_involution base hB enum henum hu hv hne
  exact ⟨j, hj, ho, hs, ⟨u, fun h => hne (h.symm.trans huv)⟩, hl, hq⟩

#print axioms countable_bafa_involution_extension
#print axioms countable_bafa_nontrivial_involution
end FullBridge
