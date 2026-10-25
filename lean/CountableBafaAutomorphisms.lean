import CountableIsoChains
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The enumeration and recursion are external. No source class recursion or
    object Choice is hidden in this hypothesis. -/
theorem countable_bafa_automorphism_extension (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) (P : TransitivePartialIso s) :
    ∃ j : U → U, (∀ x y, j x = j y → x = y) ∧ (∀ y, ∃ x, j x = y) ∧
      (∀ x y, s x y ↔ s (j x) (j y)) ∧ LocallyInternalTransitiveMap s j ∧
      ∀ x y, CodedRelation s P.code x y → j x = y := by
  obtain ⟨C, hC⟩ := enumerated_covering_iso_chain base hB P enum henum
  refine ⟨isoChainMap C, iso_chain_map_injective C, iso_chain_map_surjective C,
    iso_chain_map_members C, iso_chain_map_local C, ?_⟩
  intro x y hxy
  exact iso_chain_map_value C ⟨0, hC.symm ▸ hxy⟩

theorem locally_internal_map_restriction (base : BaseCollection s) {j : U → U}
    (hj : LocallyInternalTransitiveMap s j) (a : U) :
    ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ j x = y := by
  obtain ⟨A, B, p, hA, _, haA, hp, hpj⟩ := hj a
  have haSub : Subset s a A := fun x hx => hA a haA x hx
  obtain ⟨f, hf, hfr⟩ := function_domain_restriction base hp.1 haSub
  refine ⟨f, hf, fun x y => ?_⟩
  rw [hfr x y]
  apply and_congr_right
  intro hx
  constructor
  · intro hxy
    exact coded_function_value_unique hp.1 (hpj x (haSub x hx)) hxy
  · intro hxy
    exact hxy ▸ hpj x (haSub x hx)

theorem countable_bafa_elementary_extension (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) (P : TransitivePartialIso s) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧
      LocallyInternalTransitiveMap s j ∧
      (∀ x y, CodedRelation s P.code x y → j x = y) ∧
      (∀ x, internalCode base (j x) = internalCode base x) ∧
      ∀ a, ∃ f, FunctionCode s a f ∧ ∀ x y, CodedRelation s f x y ↔ s x a ∧ j x = y := by
  obtain ⟨j, hi, ho, hm, hl, he⟩ := countable_bafa_automorphism_extension base hB enum henum P
  refine ⟨j, bijective_membership_elementary j hi ho hm, ho, hl, he, ?_,
    locally_internal_map_restriction base hl⟩
  intro x
  exact (internal_code_eq base (j x) x).mpr (locally_internal_map_behavior base j hl x)

/-- A literal internal two-point swap, before any global extension. -/
theorem distinct_quines_partial_swap (base : BaseCollection s) {u v : U}
    (hu : SelfSingleton s u) (hv : SelfSingleton s v) (hne : u ≠ v) :
    ∃ P : TransitivePartialIso s,
      CodedRelation s P.code u v ∧ CodedRelation s P.code v u := by
  obtain ⟨a, ha⟩ := base.pairing u v
  have hua := (ha u).mpr (Or.inl rfl)
  have hva := (ha v).mpr (Or.inr rfl)
  have hQuine : ∀ x, s x a → SelfSingleton s x := by
    intro x hx
    rcases (ha x).mp hx with rfl | rfl
    · exact hu
    · exact hv
  have hTrans : TransitiveCode s a := by
    intro x hx y hy
    exact ((hQuine x hx y).mp hy).symm ▸ hx
  obtain ⟨p, hG, hp⟩ := normalized_relation_comprehension base
    (.impl (Formula.equal (n := 2) 0 1) .bottom) Fin.elim0 a
  have hp' : ∀ x y, CodedRelation s p x y ↔ s x a ∧ s y a ∧ y ≠ x := hp
  have hpair : ∀ x, s x a → ∃ y, s y a ∧ y ≠ x ∧ ∀ z, s z a → z ≠ x → z = y := by
    intro x hx
    rcases (ha x).mp hx with rfl | rfl
    · exact ⟨v, hva, Ne.symm hne, fun z hz hz' => ((ha z).mp hz).resolve_left hz'⟩
    · exact ⟨u, hua, hne, fun z hz hz' => ((ha z).mp hz).resolve_right hz'⟩
  have hf : FunctionCode s a p := by
    constructor
    · intro z hz
      obtain ⟨x, y, hx, _, hxy⟩ := hG z hz
      exact ⟨x, y, hx, hxy⟩
    · intro x hx
      obtain ⟨y, hy, hne, huq⟩ := hpair x hx
      exact ⟨y, (hp' x y).mpr ⟨hx, hy, hne⟩,
        fun z hz => huq z ((hp' x z).mp hz).2.1 ((hp' x z).mp hz).2.2⟩
  have hi : InjectiveCode s p := by
    intro x y z hxz hyz
    have hx := (hp' x z).mp hxz
    have hy := (hp' y z).mp hyz
    obtain ⟨w, _, _, huniq⟩ := hpair z hx.2.1
    exact (huniq x hx.1 (Ne.symm hx.2.2)).trans (huniq y hy.1 (Ne.symm hy.2.2)).symm
  have hr : RangeCode s a p a := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy, _⟩ := hpair y hy
      exact ⟨x, hx, (hp' x y).mpr ⟨hx, hy, Ne.symm hxy⟩⟩
    · rintro ⟨x, _, hxy⟩
      exact ((hp' x y).mp hxy).2.1
  have hIso : MembershipIsoCode s a a p := by
    refine ⟨hf, hi, hr, ?_⟩
    intro x y X Y hxX hyY
    have hx := (hp' x X).mp hxX
    have hy := (hp' y Y).mp hyY
    rw [hQuine x hx.1 y, hQuine X hx.2.1 Y]
    constructor
    · intro hyx
      exact coded_function_value_unique hf (hyx ▸ hyY) hxX
    · intro hYX
      exact hi y x X (hYX ▸ hyY) hxX
  exact ⟨⟨a, a, p, hTrans, hTrans, hIso⟩,
    (hp' u v).mpr ⟨hua, hva, Ne.symm hne⟩, (hp' v u).mpr ⟨hva, hua, hne⟩⟩

/-- The constructed global automorphism swaps the specified quines and is
    invisible on the internal behavior quotient. Its order is not asserted. -/
theorem countable_bafa_quine_swap (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) {u v : U}
    (hu : SelfSingleton s u) (hv : SelfSingleton s v) (hne : u ≠ v) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧
      j u = v ∧ j v = u ∧ LocallyInternalTransitiveMap s j ∧
      ∀ x, internalCode base (j x) = internalCode base x := by
  obtain ⟨P, huv, hvu⟩ := distinct_quines_partial_swap base hu hv hne
  obtain ⟨j, hj, ho, hl, he, hq, _⟩ := countable_bafa_elementary_extension base hB enum henum P
  exact ⟨j, hj, ho, he u v huv, he v u hvu, hl, hq⟩

theorem countable_bafa_nontrivial_automorphism (base : BaseCollection s) (hB : BAFACode s)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ j : U → U, ElementaryMap s s j ∧ (∀ y, ∃ x, j x = y) ∧
      (∃ x, j x ≠ x) ∧ LocallyInternalTransitiveMap s j ∧
      ∀ x, internalCode base (j x) = internalCode base x := by
  obtain ⟨u, v, hne, hu, hv⟩ := bafa_distinct_selfSingletons base hB
  obtain ⟨j, hj, ho, huv, _, hl, hq⟩ := countable_bafa_quine_swap base hB enum henum hu hv hne
  exact ⟨j, hj, ho, ⟨u, fun h => hne (h.symm.trans huv)⟩, hl, hq⟩

#print axioms countable_bafa_nontrivial_automorphism
end FullBridge
