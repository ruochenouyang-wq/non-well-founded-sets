import DecorationPullback
namespace FullBridge
universe u v
variable {U : Type u} {V : Type v}
variable {s : U → U → Prop} {t : V → V → Prop} {q : U → V}

theorem codedRelation_image (hm : ExactMembers s t q) {a f : U}
    (hn : ∀ p, s p f → ∃ x y, s x a ∧ IsOrderedPair s p x y) (X Y : V) :
    CodedRelation t (q f) X Y ↔
      ∃ x y, s x a ∧ CodedRelation s f x y ∧ q x = X ∧ q y = Y := by
  constructor
  · rintro ⟨P, hP, hPXY⟩
    obtain ⟨p, hp, rfl⟩ := (hm f P).mp hP
    obtain ⟨x, y, hx, hpxy⟩ := hn p hp
    have heq := orderedPair_injective (orderedPair_forward hm hpxy) hPXY
    exact ⟨x, y, hx, ⟨p, hp, hpxy⟩, heq⟩
  · rintro ⟨x, y, _, hxy, rfl, rfl⟩
    exact codedRelation_forward hm hxy

theorem functionCode_forward (hm : ExactMembers s t q) {a f : U}
    (hf : FunctionCode s a f)
    (hcompat : ∀ x x' y y', s x a → s x' a → q x = q x' →
      CodedRelation s f x y → CodedRelation s f x' y' → q y = q y') :
    FunctionCode t (q a) (q f) := by
  constructor
  · intro P hP
    obtain ⟨p, hp, rfl⟩ := (hm f P).mp hP
    obtain ⟨x, y, hx, hpxy⟩ := hf.1 p hp
    exact ⟨q x, q y, (hm a (q x)).mpr ⟨x, hx, rfl⟩, orderedPair_forward hm hpxy⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := (hm a X).mp hX
    obtain ⟨y, hxy, _⟩ := hf.2 x hx
    refine ⟨q y, codedRelation_forward hm hxy, ?_⟩
    intro Z hZ
    obtain ⟨x', z, hx', hxz, hxx, rfl⟩ := (codedRelation_image hm hf.1 (q x) Z).mp hZ
    exact hcompat x' x z y hx' hx hxx hxz hxy

theorem decoration_equal_rows (hext : Extensional s) {a e f x x' y y' : U}
    (hf : DecorationCode s a e f) (hx : s x a) (hx' : s x' a)
    (hrows : ∀ z, CodedRelation s e x z ↔ CodedRelation s e x' z)
    (hxy : CodedRelation s f x y) (hxy' : CodedRelation s f x' y') : y = y' := by
  apply hext
  intro w
  rw [hf.2 x hx y hxy w, hf.2 x' hx' y' hxy' w]
  constructor
  · rintro ⟨z, hz, hxz, hzw⟩
    exact ⟨z, hz, (hrows z).mp hxz, hzw⟩
  · rintro ⟨z, hz, hxz, hzw⟩
    exact ⟨z, hz, (hrows z).mpr hxz, hzw⟩

theorem decoration_forward_saturated (hm : ExactMembers s t q) (hext : Extensional s)
    {a e f : U} (hf : DecorationCode s a e f)
    (he : ∀ x y, CodedRelation s e x y ↔ s x a ∧ s y a ∧
      CodedRelation t (q e) (q x) (q y)) :
    DecorationCode t (q a) (q e) (q f) := by
  have hcompat : ∀ x x' y y', s x a → s x' a → q x = q x' →
      CodedRelation s f x y → CodedRelation s f x' y' → q y = q y' := by
    intro x x' y y' hx hx' hq hxy hxy'
    apply congrArg q
    apply decoration_equal_rows hext hf hx hx' ?_ hxy hxy'
    intro z
    rw [he x z, he x' z, hq]
    exact ⟨fun h => ⟨hx', h.2⟩, fun h => ⟨hx, h.2⟩⟩
  refine ⟨functionCode_forward hm hf.1 hcompat, ?_⟩
  intro X _ Y hXY W
  obtain ⟨x, y, hx, hxy, rfl, rfl⟩ := (codedRelation_image hm hf.1.1 X Y).mp hXY
  constructor
  · intro hW
    obtain ⟨w, hwy, rfl⟩ := (hm y W).mp hW
    obtain ⟨z, hz, hxz, hzw⟩ := (hf.2 x hx y hxy w).mp hwy
    exact ⟨q z, (hm a (q z)).mpr ⟨z, hz, rfl⟩,
      (he x z).mp hxz |>.2.2, codedRelation_forward hm hzw⟩
  · rintro ⟨Z, _, hxZ, hZW⟩
    obtain ⟨z, w, hz, hzw, rfl, rfl⟩ := (codedRelation_image hm hf.1.1 Z W).mp hZW
    have hxz := (he x z).mpr ⟨hx, hz, hxZ⟩
    exact (hm y (q w)).mpr ⟨w, (hf.2 x hx y hxy w).mpr ⟨z, hz, hxz, hzw⟩, rfl⟩

theorem internal_graph_solvability (base : BaseCollection s) (hBAFA : BAFACode s) :
    GraphSolvabilityCode (internalMember base) := by
  intro A R hG
  obtain ⟨a, e, rfl, rfl, heG, he⟩ := internal_graph_lift base A R hG
  obtain ⟨f, hf⟩ := bafa_graph_solvability base hBAFA a e heG
  exact ⟨internalCode base f,
    decoration_forward_saturated (internal_exact_members base) base.extensional hf he⟩

#print axioms internal_graph_solvability
end FullBridge
