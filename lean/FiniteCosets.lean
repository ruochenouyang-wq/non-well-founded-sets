import FiniteRegularActions
namespace FullBridge
universe v w

structure FiniteGroupEmbedding {I : Type v} {J : Type w}
    (G : FiniteGroupData I) (H : FiniteGroupData J) where
  map : I → J
  injective : ∀ i j, map i = map j → i = j
  map_one : map G.one = H.one
  map_mul : ∀ i j, map (G.mul i j) = H.mul (map i) (map j)

def subgroupCosetSetoid {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H) : Setoid J where
  r := fun x y => ∃ g, y = H.mul x (f.map g)
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨G.one, by rw [f.map_one, H.mul_one]⟩
    · intro x y h
      obtain ⟨g, rfl⟩ := h
      exact ⟨G.inv g, by rw [H.assoc, ← f.map_mul, G.mul_inv, f.map_one, H.mul_one]⟩
    · intro x y z hxy hyz
      obtain ⟨g, rfl⟩ := hxy
      obtain ⟨h, rfl⟩ := hyz
      exact ⟨G.mul g h, by rw [H.assoc, f.map_mul]⟩

def SubgroupCoset {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H) :=
  Quotient (subgroupCosetSetoid f)

def cosetBase {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) : SubgroupCoset f := Quotient.mk _ H.one

def cosetAction {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) (h : J) (c : SubgroupCoset f) : SubgroupCoset f :=
  Quotient.lift (fun x => Quotient.mk (subgroupCosetSetoid f) (H.mul h x))
    (by
      intro x y hxy
      obtain ⟨g, rfl⟩ := hxy
      apply Quotient.sound
      exact ⟨g, (H.assoc h x (f.map g)).symm⟩) c

theorem coset_action_identity {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (c : SubgroupCoset f) : cosetAction f H.one c = c := by
  induction c using Quotient.inductionOn with
  | _ x =>
    change Quotient.mk _ (H.mul H.one x) = Quotient.mk _ x
    rw [H.one_mul]

theorem coset_action_multiplication {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (h k : J) (c : SubgroupCoset f) :
    cosetAction f (H.mul h k) c = cosetAction f h (cosetAction f k c) := by
  induction c using Quotient.inductionOn with
  | _ x =>
    change Quotient.mk _ (H.mul (H.mul h k) x) = Quotient.mk _ (H.mul h (H.mul k x))
    rw [H.assoc]

theorem coset_action_subgroup_base {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H) (g : I) :
    cosetAction f (f.map g) (cosetBase f) = cosetBase f := by
  change Quotient.mk _ (H.mul (f.map g) H.one) = Quotient.mk _ H.one
  rw [H.mul_one]
  apply Eq.symm
  exact Quotient.sound ⟨g, (H.one_mul (f.map g)).symm⟩

noncomputable def cosetRepresentative {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (c : SubgroupCoset f) : J := by
  classical
  exact if c = cosetBase f then H.one else Classical.choose (Quotient.exists_rep c)

theorem coset_representative_spec {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (c : SubgroupCoset f) : Quotient.mk (subgroupCosetSetoid f) (cosetRepresentative f c) = c := by
  classical
  by_cases hc : c = cosetBase f
  · subst c
    simp only [cosetRepresentative, ↓reduceIte]
    rfl
  · simpa only [cosetRepresentative, hc, ↓reduceIte] using Classical.choose_spec (Quotient.exists_rep c)

theorem coset_representative_base {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H) :
    cosetRepresentative f (cosetBase f) = H.one := by
  simp only [cosetRepresentative, ↓reduceIte]

theorem coset_factor_exists {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (h : J) (c : SubgroupCoset f) :
    ∃ g, H.mul h (cosetRepresentative f c) =
      H.mul (cosetRepresentative f (cosetAction f h c)) (f.map g) := by
  apply Quotient.exact (s := subgroupCosetSetoid f)
  have he := congrArg (cosetAction f h) (coset_representative_spec f c)
  exact (coset_representative_spec f (cosetAction f h c)).trans he.symm

noncomputable def cosetFactor {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (h : J) (c : SubgroupCoset f) : I := Classical.choose (coset_factor_exists f h c)

theorem coset_factor_spec {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (h : J) (c : SubgroupCoset f) :
    H.mul h (cosetRepresentative f c) =
      H.mul (cosetRepresentative f (cosetAction f h c)) (f.map (cosetFactor f h c)) :=
  Classical.choose_spec (coset_factor_exists f h c)

theorem coset_factor_unique {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (h : J) (c : SubgroupCoset f) (g : I)
    (hg : H.mul h (cosetRepresentative f c) =
      H.mul (cosetRepresentative f (cosetAction f h c)) (f.map g)) : cosetFactor f h c = g := by
  apply f.injective
  exact finite_group_left_cancel H ((coset_factor_spec f h c).symm.trans hg)

theorem coset_factor_identity {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (c : SubgroupCoset f) : cosetFactor f H.one c = G.one := by
  apply coset_factor_unique
  rw [coset_action_identity, f.map_one, H.mul_one, H.one_mul]

/-- The correction factors form the cocycle needed for the induced action. -/
theorem coset_factor_multiplication {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (h k : J) (c : SubgroupCoset f) :
    cosetFactor f (H.mul h k) c =
      G.mul (cosetFactor f h (cosetAction f k c)) (cosetFactor f k c) := by
  apply coset_factor_unique
  calc
    H.mul (H.mul h k) (cosetRepresentative f c) = H.mul h (H.mul k (cosetRepresentative f c)) := H.assoc _ _ _
    _ = H.mul h (H.mul (cosetRepresentative f (cosetAction f k c)) (f.map (cosetFactor f k c))) := by rw [coset_factor_spec f k c]
    _ = H.mul (H.mul h (cosetRepresentative f (cosetAction f k c))) (f.map (cosetFactor f k c)) := (H.assoc _ _ _).symm
    _ = H.mul (H.mul (cosetRepresentative f (cosetAction f h (cosetAction f k c)))
          (f.map (cosetFactor f h (cosetAction f k c)))) (f.map (cosetFactor f k c)) := by rw [coset_factor_spec f h (cosetAction f k c)]
    _ = H.mul (cosetRepresentative f (cosetAction f (H.mul h k) c))
          (f.map (G.mul (cosetFactor f h (cosetAction f k c)) (cosetFactor f k c))) := by
      rw [H.assoc, ← f.map_mul, coset_action_multiplication]

theorem coset_factor_subgroup_base {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H) (g : I) :
    cosetFactor f (f.map g) (cosetBase f) = g := by
  apply coset_factor_unique
  rw [coset_action_subgroup_base, coset_representative_base, H.mul_one, H.one_mul]

def cosetIndices {I : Type v} {J : Type w} {G : FiniteGroupData I} {H : FiniteGroupData J}
    (f : FiniteGroupEmbedding G H) : List (SubgroupCoset f) :=
  H.indices.map (Quotient.mk (subgroupCosetSetoid f))

theorem coset_indices_complete {I : Type v} {J : Type w}
    {G : FiniteGroupData I} {H : FiniteGroupData J} (f : FiniteGroupEmbedding G H)
    (c : SubgroupCoset f) : c ∈ cosetIndices f := by
  obtain ⟨h, rfl⟩ := Quotient.exists_rep c
  exact List.mem_map.mpr ⟨h, H.complete h, rfl⟩

#print axioms coset_factor_multiplication
#print axioms coset_indices_complete
end FullBridge
