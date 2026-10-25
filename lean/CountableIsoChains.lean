import BafaPartialHomogeneity
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure TransitivePartialIso (s : U → U → Prop) where
  domain : U
  range : U
  code : U
  domain_transitive : TransitiveCode s domain
  range_transitive : TransitiveCode s range
  iso : MembershipIsoCode s domain range code

def PartialIsoExtends (P Q : TransitivePartialIso s) : Prop :=
  Subset s P.domain Q.domain ∧ Subset s P.range Q.range ∧
    ∀ x y, CodedRelation s P.code x y → CodedRelation s Q.code x y

theorem partial_iso_extends_refl (P : TransitivePartialIso s) : PartialIsoExtends P P :=
  ⟨fun _ h => h, fun _ h => h, fun _ _ h => h⟩

theorem partial_iso_extends_trans {P Q R : TransitivePartialIso s}
    (hPQ : PartialIsoExtends P Q) (hQR : PartialIsoExtends Q R) : PartialIsoExtends P R :=
  ⟨fun x hx => hQR.1 x (hPQ.1 x hx), fun x hx => hQR.2.1 x (hPQ.2.1 x hx),
    fun x y h => hQR.2.2 x y (hPQ.2.2 x y h)⟩

theorem partial_iso_cover_extension (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitivePartialIso s) (x y : U) :
    ∃ Q : TransitivePartialIso s, PartialIsoExtends P Q ∧ s x Q.domain ∧ s y Q.range := by
  obtain ⟨A, C, h, hA, hC, hPA, hPC, hxA, hh, hPh⟩ :=
    bafa_transitive_iso_forth base hB P.domain_transitive P.range_transitive P.iso x
  obtain ⟨D, E, k, hD, hE, hAD, hCE, hyE, hk, hhk⟩ :=
    bafa_transitive_iso_back base hB hA hC hh y
  exact ⟨⟨D, E, k, hD, hE, hk⟩,
    ⟨fun z hz => hAD z (hPA z hz), fun z hz => hCE z (hPC z hz),
      fun z w hzw => hhk z w (hPh z w hzw)⟩, hAD x hxA, hyE⟩

noncomputable def partialIsoNext (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitivePartialIso s) (x : U) : TransitivePartialIso s :=
  Classical.choose (partial_iso_cover_extension base hB P x x)

theorem partial_iso_next_spec (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitivePartialIso s) (x : U) :
    PartialIsoExtends P (partialIsoNext base hB P x) ∧
      s x (partialIsoNext base hB P x).domain ∧ s x (partialIsoNext base hB P x).range :=
  Classical.choose_spec (partial_iso_cover_extension base hB P x x)

/-- External recursion along a specified external enumeration. -/
noncomputable def enumeratedIsoSequence (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitivePartialIso s) (enum : Nat → U) : Nat → TransitivePartialIso s
  | 0 => P
  | n + 1 => partialIsoNext base hB (enumeratedIsoSequence base hB P enum n) (enum n)

structure CoveringIsoChain (s : U → U → Prop) where
  stage : Nat → TransitivePartialIso s
  step_extends : ∀ n, PartialIsoExtends (stage n) (stage (n + 1))
  covers_domain : ∀ x, ∃ n, s x (stage n).domain
  covers_range : ∀ x, ∃ n, s x (stage n).range

theorem enumerated_covering_iso_chain (base : BaseCollection s) (hB : BAFACode s)
    (P : TransitivePartialIso s) (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ C : CoveringIsoChain s, C.stage 0 = P := by
  let seq := enumeratedIsoSequence base hB P enum
  have hn : ∀ n, PartialIsoExtends (seq n) (seq (n+1)) ∧
      s (enum n) (seq (n+1)).domain ∧ s (enum n) (seq (n+1)).range :=
    fun n => partial_iso_next_spec base hB (seq n) (enum n)
  refine ⟨⟨seq, fun n => (hn n).1, ?_, ?_⟩, rfl⟩
  · intro x
    obtain ⟨n, rfl⟩ := henum x
    exact ⟨n+1, (hn n).2.1⟩
  · intro x
    obtain ⟨n, rfl⟩ := henum x
    exact ⟨n+1, (hn n).2.2⟩

theorem covering_chain_mono (C : CoveringIsoChain s) {n m : Nat} (h : n ≤ m) :
    PartialIsoExtends (C.stage n) (C.stage m) := by
  induction h with
  | refl => exact partial_iso_extends_refl _
  | @step m h ih => exact partial_iso_extends_trans ih (C.step_extends m)

def IsoChainRelation (C : CoveringIsoChain s) (x y : U) : Prop :=
  ∃ n, CodedRelation s (C.stage n).code x y

theorem iso_chain_relation_total (C : CoveringIsoChain s) (x : U) :
    ∃ y, IsoChainRelation C x y := by
  obtain ⟨n, hn⟩ := C.covers_domain x
  obtain ⟨y, hxy, _⟩ := (C.stage n).iso.1.2 x hn
  exact ⟨y, n, hxy⟩

theorem iso_chain_relation_unique (C : CoveringIsoChain s) {x y z : U}
    (hy : IsoChainRelation C x y) (hz : IsoChainRelation C x z) : y = z := by
  obtain ⟨n, hn⟩ := hy
  obtain ⟨m, hm⟩ := hz
  exact coded_function_value_unique (C.stage (max n m)).iso.1
    ((covering_chain_mono C (Nat.le_max_left n m)).2.2 x y hn)
    ((covering_chain_mono C (Nat.le_max_right n m)).2.2 x z hm)

noncomputable def isoChainMap (C : CoveringIsoChain s) (x : U) : U :=
  Classical.choose (iso_chain_relation_total C x)

theorem iso_chain_map_relation (C : CoveringIsoChain s) (x : U) :
    IsoChainRelation C x (isoChainMap C x) :=
  Classical.choose_spec (iso_chain_relation_total C x)

theorem iso_chain_map_value (C : CoveringIsoChain s) {x y : U}
    (h : IsoChainRelation C x y) : isoChainMap C x = y :=
  iso_chain_relation_unique C (iso_chain_map_relation C x) h

theorem iso_chain_map_injective (C : CoveringIsoChain s) :
    ∀ x y, isoChainMap C x = isoChainMap C y → x = y := by
  intro x y h
  obtain ⟨n, hn⟩ := iso_chain_map_relation C x
  obtain ⟨m, hm⟩ := iso_chain_map_relation C y
  exact (C.stage (max n m)).iso.2.1 x y _
    ((covering_chain_mono C (Nat.le_max_left n m)).2.2 x _ hn)
    (h.symm ▸ (covering_chain_mono C (Nat.le_max_right n m)).2.2 y _ hm)

theorem iso_chain_map_surjective (C : CoveringIsoChain s) :
    ∀ y, ∃ x, isoChainMap C x = y := by
  intro y
  obtain ⟨n, hn⟩ := C.covers_range y
  obtain ⟨x, _, hxy⟩ := ((C.stage n).iso.2.2.1 y).mp hn
  exact ⟨x, iso_chain_map_value C ⟨n, hxy⟩⟩

theorem iso_chain_map_members (C : CoveringIsoChain s) (x y : U) :
    s x y ↔ s (isoChainMap C x) (isoChainMap C y) := by
  obtain ⟨n, hn⟩ := iso_chain_map_relation C x
  obtain ⟨m, hm⟩ := iso_chain_map_relation C y
  exact (C.stage (max n m)).iso.2.2.2 y x _ _
    ((covering_chain_mono C (Nat.le_max_right n m)).2.2 y _ hm)
    ((covering_chain_mono C (Nat.le_max_left n m)).2.2 x _ hn)

theorem iso_chain_map_local (C : CoveringIsoChain s) : LocallyInternalTransitiveMap s (isoChainMap C) := by
  intro x
  obtain ⟨n, hn⟩ := C.covers_domain x
  refine ⟨(C.stage n).domain, (C.stage n).range, (C.stage n).code,
    (C.stage n).domain_transitive, (C.stage n).range_transitive, hn, (C.stage n).iso, ?_⟩
  intro y hy
  obtain ⟨z, hyz, _⟩ := (C.stage n).iso.1.2 y hy
  exact (iso_chain_map_value C ⟨n, hyz⟩).symm ▸ hyz

#print axioms enumerated_covering_iso_chain
#print axioms iso_chain_map_local
end FullBridge
