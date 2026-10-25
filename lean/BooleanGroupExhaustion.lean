import InternalTailLocalSystem
namespace FullBridge
universe v

def booleanSpanList {K : Type v} (D : ExternalGroupData K) (e : Nat → K) : Nat → List K
  | 0 => [D.one]
  | n+1 => booleanSpanList D e n ++ (booleanSpanList D e n).map (D.mul (e n))

theorem boolean_span_one {K : Type v} (D : ExternalGroupData K) (e : Nat → K) (n : Nat) :
    D.one ∈ booleanSpanList D e n := by
  induction n with
  | zero => simp [booleanSpanList]
  | succ n ih => exact List.mem_append_left _ ih

theorem boolean_repeated_factor {K : Type v} (D : ExternalGroupData K)
    (hc : ∀ x y, D.mul x y = D.mul y x) (hs : ∀ x, D.mul x x = D.one) (g x y : K) :
    D.mul (D.mul g x) (D.mul g y) = D.mul x y := by
  rw [D.assoc, ← D.assoc x g y, hc x g, D.assoc g x y,
    ← D.assoc, hs, D.one_mul]

theorem boolean_span_mul {K : Type v} (D : ExternalGroupData K)
    (hc : ∀ x y, D.mul x y = D.mul y x) (hs : ∀ x, D.mul x x = D.one)
    (e : Nat → K) (n : Nat) {x y : K}
    (hx : x ∈ booleanSpanList D e n) (hy : y ∈ booleanSpanList D e n) :
    D.mul x y ∈ booleanSpanList D e n := by
  induction n generalizing x y with
  | zero =>
    have hxx : x = D.one := by simpa [booleanSpanList] using hx
    have hyy : y = D.one := by simpa [booleanSpanList] using hy
    simp [hxx, hyy, D.one_mul, booleanSpanList]
  | succ n ih =>
    rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
    · exact List.mem_append_left _ (ih hx hy)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have he : D.mul x (D.mul (e n) z) = D.mul (e n) (D.mul x z) := by
        rw [← D.assoc, hc x (e n), D.assoc]
      rw [he]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨D.mul x z, ih hx hz, rfl⟩)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      rw [D.assoc]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨D.mul z y, ih hz hy, rfl⟩)
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hx
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hy
      rw [boolean_repeated_factor D hc hs]
      exact List.mem_append_left _ (ih hX hY)

abbrev BooleanSpan {K : Type v} (D : ExternalGroupData K) (e : Nat → K) (n : Nat) :=
  {g : K // g ∈ booleanSpanList D e n}

def booleanSpanGroup {K : Type v} (D : ExternalGroupData K)
    (hc : ∀ x y, D.mul x y = D.mul y x) (hs : ∀ x, D.mul x x = D.one)
    (e : Nat → K) (n : Nat) : FiniteGroupData (BooleanSpan D e n) where
  one := ⟨D.one, boolean_span_one D e n⟩
  mul := fun x y => ⟨D.mul x.val y.val, boolean_span_mul D hc hs e n x.property y.property⟩
  inv := id
  assoc := fun x y z => Subtype.ext (D.assoc x.val y.val z.val)
  one_mul := fun x => Subtype.ext (D.one_mul x.val)
  mul_one := fun x => Subtype.ext (D.mul_one x.val)
  inv_mul := fun x => Subtype.ext (hs x.val)
  mul_inv := fun x => Subtype.ext (hs x.val)
  indices := (booleanSpanList D e n).attach
  complete := fun x => List.mem_attach _ x

/-- Every externally countable Boolean group has an actual exhaustion by
    externally finite subgroups, regardless of how large its elements are. -/
def countableBooleanExhaustion {K : Type v} (D : ExternalGroupData K)
    (hc : ∀ x y, D.mul x y = D.mul y x) (hs : ∀ x, D.mul x x = D.one)
    (e : Nat → K) (he : ∀ g, ∃ n, e n = g) : FiniteGroupExhaustion D where
  Stage := BooleanSpan D e
  group := booleanSpanGroup D hc hs e
  embed := fun _ g => g.val
  injective := fun _ _ _ h => Subtype.ext h
  map_one := fun _ => rfl
  map_mul := fun _ _ _ => rfl
  step := fun _ g => ⟨⟨g.val, List.mem_append_left _ g.property⟩, rfl⟩
  covers := by
    intro g
    obtain ⟨n, rfl⟩ := he g
    have hgen : e n ∈ booleanSpanList D e (n+1) :=
      List.mem_append_right _ (List.mem_map.mpr ⟨D.one, boolean_span_one D e n, D.mul_one (e n)⟩)
    exact ⟨n+1, ⟨e n, hgen⟩, rfl⟩

#print axioms countableBooleanExhaustion
end FullBridge
