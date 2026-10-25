import BafaSubgroupExtension
namespace FullBridge
universe v w

structure ExternalGroupData (K : Type v) where
  one : K
  mul : K → K → K
  inv : K → K
  assoc : ∀ i j k, mul (mul i j) k = mul i (mul j k)
  one_mul : ∀ i, mul one i = i
  mul_one : ∀ i, mul i one = i
  inv_mul : ∀ i, mul (inv i) i = one
  mul_inv : ∀ i, mul i (inv i) = one

/-- A supplied increasing finite-subgroup exhaustion of an external group.
    Coherent transition maps are constructed below from these image inclusions. -/
structure FiniteGroupExhaustion {K : Type v} (D : ExternalGroupData K) where
  Stage : Nat → Type w
  group : ∀ n, FiniteGroupData (Stage n)
  embed : ∀ n, Stage n → K
  injective : ∀ n i j, embed n i = embed n j → i = j
  map_one : ∀ n, embed n (group n).one = D.one
  map_mul : ∀ n i j, embed n ((group n).mul i j) = D.mul (embed n i) (embed n j)
  step : ∀ n i, ∃ j, embed (n+1) j = embed n i
  covers : ∀ g, ∃ n i, embed n i = g

theorem exhaustion_stage_lift_exists {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m : Nat} (h : n ≤ m) (i : E.Stage n) :
    ∃ j, E.embed m j = E.embed n i := by
  induction h with
  | refl => exact ⟨i, rfl⟩
  | @step m h ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, hk⟩ := E.step m j
    exact ⟨k, hk.trans hj⟩

noncomputable def exhaustionLift {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m : Nat} (h : n ≤ m) (i : E.Stage n) : E.Stage m :=
  Classical.choose (exhaustion_stage_lift_exists E h i)

theorem exhaustion_lift_embed {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m : Nat} (h : n ≤ m) (i : E.Stage n) :
    E.embed m (exhaustionLift E h i) = E.embed n i :=
  Classical.choose_spec (exhaustion_stage_lift_exists E h i)

theorem exhaustion_lift_refl {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) (n : Nat) (i : E.Stage n) :
    exhaustionLift E (Nat.le_refl n) i = i := E.injective n _ _ (exhaustion_lift_embed E _ i)

theorem exhaustion_lift_comp {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m k : Nat} (h : n ≤ m) (h' : m ≤ k) (i : E.Stage n) :
    exhaustionLift E h' (exhaustionLift E h i) = exhaustionLift E (Nat.le_trans h h') i := by
  apply E.injective k
  rw [exhaustion_lift_embed, exhaustion_lift_embed, exhaustion_lift_embed]

theorem exhaustion_lift_one {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m : Nat} (h : n ≤ m) :
    exhaustionLift E h (E.group n).one = (E.group m).one := by
  apply E.injective m
  rw [exhaustion_lift_embed, E.map_one, E.map_one]

theorem exhaustion_lift_mul {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m : Nat} (h : n ≤ m) (i j : E.Stage n) :
    exhaustionLift E h ((E.group n).mul i j) =
      (E.group m).mul (exhaustionLift E h i) (exhaustionLift E h j) := by
  apply E.injective m
  rw [exhaustion_lift_embed, E.map_mul, E.map_mul, exhaustion_lift_embed, exhaustion_lift_embed]

noncomputable def exhaustionEmbedding {K : Type v} {D : ExternalGroupData K}
    (E : FiniteGroupExhaustion.{v,w} D) {n m : Nat} (h : n ≤ m) :
    FiniteGroupEmbedding (E.group n) (E.group m) where
  map := exhaustionLift E h
  injective := by
    intro i j hij
    apply E.injective n
    exact (exhaustion_lift_embed E h i).symm.trans
      ((congrArg (E.embed m) hij).trans (exhaustion_lift_embed E h j))
  map_one := exhaustion_lift_one E h
  map_mul := exhaustion_lift_mul E h

#print axioms exhaustion_lift_comp
end FullBridge
