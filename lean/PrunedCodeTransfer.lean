import PrunedGraphPresentation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem pruned_pair_forward (base : BaseCollection s) {b p x y : U} (hbb : s b b)
    (hx : ¬s b x) (hy : ¬s b y) (hp : IsPair s p x y) :
    ¬s b p ∧ IsPair (prunedMember base b) (prunedCode base b p) (prunedCode base b x) (prunedCode base b y) := by
  have hg : ∀ z, s z p → ¬s b z := by
    intro z hz
    rcases (hp z).mp hz with hzx | hzy
    · exact hzx ▸ hx
    · exact hzy ▸ hy
  refine ⟨(pruned_good_row base hbb hg).1, ?_⟩
  intro Z
  refine ((pruned_good_row base hbb hg).2 Z).trans ⟨?_, ?_⟩
  · rintro ⟨z, hz, hq⟩
    rcases (hp z).mp hz with hzx | hzy
    · exact Or.inl (hzx ▸ hq.symm)
    · exact Or.inr (hzy ▸ hq.symm)
  · intro h
    rcases h with hzx | hzy
    · exact ⟨x, (hp x).mpr (Or.inl rfl), hzx.symm⟩
    · exact ⟨y, (hp y).mpr (Or.inr rfl), hzy.symm⟩

theorem pruned_orderedPair_forward (base : BaseCollection s) {b p x y : U} (hbb : s b b)
    (hx : ¬s b x) (hy : ¬s b y) (hp : IsOrderedPair s p x y) :
    ¬s b p ∧ IsOrderedPair (prunedMember base b) (prunedCode base b p)
      (prunedCode base b x) (prunedCode base b y) := by
  obtain ⟨a, c, ha, hc, hp⟩ := hp
  obtain ⟨hag, haq⟩ := pruned_pair_forward base hbb hx hx ha
  obtain ⟨hcg, hcq⟩ := pruned_pair_forward base hbb hx hy hc
  obtain ⟨hpg, hpq⟩ := pruned_pair_forward base hbb hag hcg hp
  exact ⟨hpg, prunedCode base b a, prunedCode base b c, haq, hcq, hpq⟩

def RetainedRelationCode (s : U → U → Prop) (b r : U) : Prop :=
  ∀ p, s p r → ∃ x y, ¬s b x ∧ ¬s b y ∧ IsOrderedPair s p x y

theorem retained_relation_members (base : BaseCollection s) {b r : U} (hbb : s b b)
    (hr : RetainedRelationCode s b r) : ∀ p, s p r → ¬s b p := by
  intro p hp
  obtain ⟨x, y, hx, hy, hpair⟩ := hr p hp
  exact (pruned_orderedPair_forward base hbb hx hy hpair).1

theorem pruned_coded_relation_image (base : BaseCollection s) {b r : U} (hbb : s b b)
    (hr : RetainedRelationCode s b r) (X Y : PrunedQuotient base b) :
    CodedRelation (prunedMember base b) (prunedCode base b r) X Y ↔
      ∃ x y, CodedRelation s r x y ∧ prunedCode base b x = X ∧ prunedCode base b y = Y := by
  have hg := retained_relation_members base hbb hr
  constructor
  · rintro ⟨P, hP, hPXY⟩
    obtain ⟨p, hp, rfl⟩ := ((pruned_good_row base hbb hg).2 P).mp hP
    obtain ⟨x, y, hx, hy, hpxy⟩ := hr p hp
    have hxy := orderedPair_injective (pruned_orderedPair_forward base hbb hx hy hpxy).2 hPXY
    exact ⟨x, y, ⟨p, hp, hpxy⟩, hxy⟩
  · rintro ⟨x, y, ⟨p, hp, hpxy⟩, rfl, rfl⟩
    obtain ⟨x', y', hx', hy', hp'⟩ := hr p hp
    obtain ⟨hxx, hyy⟩ := orderedPair_injective hp' hpxy
    subst x'
    subst y'
    exact ⟨prunedCode base b p, ((pruned_good_row base hbb hg).2 _).mpr ⟨p, hp, rfl⟩,
      (pruned_orderedPair_forward base hbb hx' hy' hpxy).2⟩

theorem pruned_function_retained {b a f : U} (hf : FunctionCode s a f)
    (ha : ∀ x, s x a → ¬s b x) (hv : ∀ x v, CodedRelation s f x v → ¬s b v) :
    RetainedRelationCode s b f := by
  intro p hp
  obtain ⟨x, v, hx, hpv⟩ := hf.1 p hp
  exact ⟨x, v, ha x hx, hv x v ⟨p, hp, hpv⟩, hpv⟩

theorem pruned_function_forward (base : BaseCollection s) {b a f : U} (hbb : s b b)
    (hf : FunctionCode s a f) (ha : ∀ x, s x a → ¬s b x)
    (hv : ∀ x v, CodedRelation s f x v → ¬s b v)
    (hcoh : ∀ x y v w, CodedRelation s f x v → CodedRelation s f y w →
      prunedCode base b x = prunedCode base b y → prunedCode base b v = prunedCode base b w) :
    FunctionCode (prunedMember base b) (prunedCode base b a) (prunedCode base b f) := by
  have hr := pruned_function_retained hf ha hv
  have hfg := retained_relation_members base hbb hr
  constructor
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := ((pruned_good_row base hbb hfg).2 P).mp hP
    obtain ⟨x, v, hx, hpv⟩ := hf.1 p hp
    exact ⟨prunedCode base b x, prunedCode base b v,
      ((pruned_good_row base hbb ha).2 _).mpr ⟨x, hx, rfl⟩,
      (pruned_orderedPair_forward base hbb (ha x hx) (hv x v ⟨p, hp, hpv⟩) hpv).2⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb ha).2 X).mp hX
    obtain ⟨v, hxv, _⟩ := hf.2 x hx
    refine ⟨prunedCode base b v, (pruned_coded_relation_image base hbb hr _ _).mpr ⟨x, v, hxv, rfl, rfl⟩, ?_⟩
    intro Y hY
    obtain ⟨y, w, hyw, hqy, hqw⟩ := (pruned_coded_relation_image base hbb hr _ _).mp hY
    exact hqw.symm.trans (hcoh y x w v hyw hxv hqy)

theorem pruned_function_injective (base : BaseCollection s) {b a f : U} (hbb : s b b)
    (hf : FunctionCode s a f) (ha : ∀ x, s x a → ¬s b x)
    (hv : ∀ x v, CodedRelation s f x v → ¬s b v)
    (hrefl : ∀ x y v w, CodedRelation s f x v → CodedRelation s f y w →
      prunedCode base b v = prunedCode base b w → prunedCode base b x = prunedCode base b y) :
    InjectiveCode (prunedMember base b) (prunedCode base b f) := by
  have hr := pruned_function_retained hf ha hv
  intro X Y V hX hY
  obtain ⟨x, v, hxv, hqx, hqv⟩ := (pruned_coded_relation_image base hbb hr _ _).mp hX
  obtain ⟨y, w, hyw, hqy, hqw⟩ := (pruned_coded_relation_image base hbb hr _ _).mp hY
  exact hqx.symm.trans ((hrefl x y v w hxv hyw (hqv.trans hqw.symm)).trans hqy)

#print axioms pruned_function_forward
end FullBridge
