import ControlledGroupLimits
namespace FullBridge

def bitVectors : (n : Nat) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n+1 => (bitVectors n).flatMap (fun v => [cons false v, cons true v])

theorem bit_vectors_complete (n : Nat) (v : Fin n → Bool) : v ∈ bitVectors n := by
  induction n with
  | zero =>
    have he : v = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [bitVectors, he]
  | succ n ih =>
    let tail := fun i : Fin n => v i.succ
    have he : cons (v 0) tail = v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, ih tail, ?_⟩
    rw [← he]
    cases v 0 <;> simp

def finiteBitGroup (n : Nat) : FiniteGroupData (Fin n → Bool) where
  one := fun _ => false
  mul := fun a b i => Bool.xor (a i) (b i)
  inv := id
  assoc := by intro a b c; funext i; change Bool.xor (Bool.xor (a i) (b i)) (c i) = Bool.xor (a i) (Bool.xor (b i) (c i)); cases a i <;> cases b i <;> cases c i <;> rfl
  one_mul := by intro a; funext i; cases a i <;> rfl
  mul_one := by intro a; funext i; cases a i <;> rfl
  inv_mul := by intro a; funext i; change Bool.xor (a i) (a i) = false; cases a i <;> rfl
  mul_inv := by intro a; funext i; change Bool.xor (a i) (a i) = false; cases a i <;> rfl
  indices := bitVectors n
  complete := bit_vectors_complete n

abbrev FiniteBitMask := {v : Nat → Bool // ∃ N, ∀ n, N ≤ n → v n = false}

def bitMaskOne : FiniteBitMask := ⟨fun _ => false, 0, fun _ _ => rfl⟩
def bitMaskMul (a b : FiniteBitMask) : FiniteBitMask := ⟨fun n => Bool.xor (a.val n) (b.val n), by
  obtain ⟨N, hN⟩ := a.property
  obtain ⟨M, hM⟩ := b.property
  exact ⟨max N M, fun n hn => by change Bool.xor (a.val n) (b.val n) = false; rw [hN n (Nat.le_trans (Nat.le_max_left N M) hn),
    hM n (Nat.le_trans (Nat.le_max_right N M) hn)]; rfl⟩⟩

def finiteBitMaskGroup : ExternalGroupData FiniteBitMask where
  one := bitMaskOne
  mul := bitMaskMul
  inv := id
  assoc := by
    intro a b c; apply Subtype.ext; funext n
    change Bool.xor (Bool.xor (a.val n) (b.val n)) (c.val n) = Bool.xor (a.val n) (Bool.xor (b.val n) (c.val n))
    cases a.val n <;> cases b.val n <;> cases c.val n <;> rfl
  one_mul := by intro a; apply Subtype.ext; funext n; change Bool.xor false (a.val n) = _; cases a.val n <;> rfl
  mul_one := by intro a; apply Subtype.ext; funext n; change Bool.xor (a.val n) false = _; cases a.val n <;> rfl
  inv_mul := by intro a; apply Subtype.ext; funext n; change Bool.xor (a.val n) (a.val n) = false; cases a.val n <;> rfl
  mul_inv := by intro a; apply Subtype.ext; funext n; change Bool.xor (a.val n) (a.val n) = false; cases a.val n <;> rfl

def prefixBitMask (n : Nat) (v : Fin n → Bool) : FiniteBitMask :=
  ⟨fun k => if h : k < n then v ⟨k, h⟩ else false,
    n, fun k hk => by simp [Nat.not_lt.mpr hk]⟩

theorem prefix_bit_mask_value (n : Nat) (v : Fin n → Bool) (i : Fin n) :
    (prefixBitMask n v).val i.val = v i := by simp [prefixBitMask, i.isLt]

theorem prefix_bit_mask_restrict (b : FiniteBitMask) {n : Nat}
    (hb : ∀ k, n ≤ k → b.val k = false) : prefixBitMask n (fun i => b.val i.val) = b := by
  apply Subtype.ext
  funext k
  by_cases hk : k < n
  · simp [prefixBitMask, hk]
  · simp [prefixBitMask, hk, hb k (Nat.le_of_not_lt hk)]

def finiteBitExhaustion : FiniteGroupExhaustion finiteBitMaskGroup where
  Stage := fun n => Fin n → Bool
  group := finiteBitGroup
  embed := prefixBitMask
  injective := by
    intro n a b h
    funext i
    have hv := congrArg (fun m : FiniteBitMask => m.val i.val) h
    simpa only [prefix_bit_mask_value] using hv
  map_one := by
    intro n; apply Subtype.ext; funext k
    by_cases hk : k < n <;> simp [prefixBitMask, finiteBitGroup, finiteBitMaskGroup, bitMaskOne]
  map_mul := by
    intro n a b; apply Subtype.ext; funext k
    by_cases hk : k < n <;> simp [prefixBitMask, finiteBitGroup, finiteBitMaskGroup, bitMaskMul, hk]
  step := by
    intro n a
    refine ⟨fun i => (prefixBitMask n a).val i.val, prefix_bit_mask_restrict _ ?_⟩
    intro k hk
    simp [prefixBitMask, Nat.not_lt.mpr (Nat.le_trans (Nat.le_succ n) hk)]
  covers := by
    intro b
    obtain ⟨n, hn⟩ := b.property
    exact ⟨n, fun i => b.val i.val, prefix_bit_mask_restrict b hn⟩

theorem finite_bit_mask_commutative (a b : FiniteBitMask) : bitMaskMul a b = bitMaskMul b a := by
  apply Subtype.ext
  funext n
  change Bool.xor (a.val n) (b.val n) = Bool.xor (b.val n) (a.val n)
  cases a.val n <;> cases b.val n <;> rfl

def singleBitMask (n : Nat) : FiniteBitMask :=
  ⟨fun k => if k = n then true else false, n+1, fun k hk => by
    have hkn : k ≠ n := fun he => Nat.not_succ_le_self n (he ▸ hk)
    simp [hkn]⟩

theorem single_bit_mask_injective (n m : Nat) (h : singleBitMask n = singleBitMask m) : n = m := by
  have he := congrArg (fun b : FiniteBitMask => b.val n) h
  by_cases hnm : n = m
  · exact hnm
  · simp [singleBitMask, hnm] at he

#print axioms finiteBitExhaustion
#print axioms finite_bit_mask_commutative
end FullBridge
