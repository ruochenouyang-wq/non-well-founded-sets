import FiniteBitGroups
namespace FullBridge
universe u
variable {U : Type u}

def finiteInvolutionAction (f : Nat → U → U) : (n : Nat) → (Fin n → Bool) → U → U
  | 0, _, x => x
  | n+1, v, x => if v (Fin.last n) then f n (finiteInvolutionAction f n (fun i => v i.castSucc) x)
    else finiteInvolutionAction f n (fun i => v i.castSucc) x

theorem finite_involution_action_identity (f : Nat → U → U) (n : Nat) (x : U) :
    finiteInvolutionAction f n (fun _ => false) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem finite_involution_action_commutes (f : Nat → U → U)
    (hc : ∀ n m x, f n (f m x) = f m (f n x))
    (n : Nat) (v : Fin n → Bool) (m : Nat) (x : U) :
    finiteInvolutionAction f n v (f m x) = f m (finiteInvolutionAction f n v x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hv : v (Fin.last n) <;> simp only [finiteInvolutionAction, hv, Bool.false_eq_true, ↓reduceIte]
    · exact ih _
    · exact (congrArg (f n) (ih _)).trans (hc n m _)

theorem finite_involution_action_multiplication (f : Nat → U → U)
    (hi : ∀ n x, f n (f n x) = x) (hc : ∀ n m x, f n (f m x) = f m (f n x))
    (n : Nat) (v w : Fin n → Bool) (x : U) :
    finiteInvolutionAction f n (fun i => Bool.xor (v i) (w i)) x =
      finiteInvolutionAction f n v (finiteInvolutionAction f n w x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hv : v (Fin.last n) <;> cases hw : w (Fin.last n) <;>
      simp only [finiteInvolutionAction, hv, hw, Bool.xor, Bool.false_eq_true, ↓reduceIte]
    · exact ih _ _
    · rw [finite_involution_action_commutes f hc]
      exact congrArg (f n) (ih _ _)
    · exact congrArg (f n) (ih _ _)
    · rw [finite_involution_action_commutes f hc, hi]
      exact ih _ _

theorem finite_involution_action_involutive (f : Nat → U → U)
    (hi : ∀ n x, f n (f n x) = x) (hc : ∀ n m x, f n (f m x) = f m (f n x))
    (n : Nat) (v : Fin n → Bool) (x : U) :
    finiteInvolutionAction f n v (finiteInvolutionAction f n v x) = x := by
  rw [← finite_involution_action_multiplication f hi hc]
  have he : (fun i => Bool.xor (v i) (v i)) = (fun _ => false) := by
    funext i; cases v i <;> rfl
  rw [he, finite_involution_action_identity]

theorem finite_involution_action_fixed (f : Nat → U → U) {n : Nat} (v : Fin n → Bool) (x : U)
    (hf : ∀ k, k < n → f k x = x) : finiteInvolutionAction f n v x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev := ih (fun i => v i.castSucc) (fun k hk => hf k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    cases hv : v (Fin.last n) <;> simp only [finiteInvolutionAction, hv, Bool.false_eq_true, ↓reduceIte, hprev]
    exact hf n (Nat.lt_succ_self n)

theorem finite_involution_action_mem {s : U → U → Prop} {d : U} (f : Nat → U → U)
    (hm : ∀ k x, s x d → s (f k x) d) (n : Nat) (v : Fin n → Bool) {x : U} (hx : s x d) :
    s (finiteInvolutionAction f n v x) d := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    cases hv : v (Fin.last n) <;> simp only [finiteInvolutionAction, hv, Bool.false_eq_true, ↓reduceIte]
    · exact ih _
    · exact hm n _ (ih _)

theorem finite_involution_action_last_bit (f : Nat → U → U) (n : Nat) (x : U) :
    finiteInvolutionAction f (n+1) (fun i => if i.val = n then true else false) x = f n x := by
  have he : (fun i : Fin n => if i.castSucc.val = n then true else false) = (fun _ => false) := by
    funext i
    simp [Nat.ne_of_lt i.isLt]
  simp only [finiteInvolutionAction, Fin.val_last, ↓reduceIte, he, finite_involution_action_identity]

theorem prefix_last_bit_mask (n : Nat) :
    prefixBitMask (n+1) (fun i => if i.val = n then true else false) = singleBitMask n := by
  apply Subtype.ext
  funext k
  by_cases hk : k < n+1
  · simp [prefixBitMask, singleBitMask, hk]
  · have hkn : k ≠ n := fun he => hk (he.symm ▸ Nat.lt_succ_self n)
    simp [prefixBitMask, singleBitMask, hk, hkn]

theorem finite_involution_action_prefix_step (f : Nat → U → U) {n : Nat}
    (v : Fin n → Bool) (w : Fin (n+1) → Bool) (he : prefixBitMask (n+1) w = prefixBitMask n v) (x : U) :
    finiteInvolutionAction f (n+1) w x = finiteInvolutionAction f n v x := by
  have hlast : w (Fin.last n) = false := by
    have h := congrArg (fun b : FiniteBitMask => b.val n) he
    simpa [prefixBitMask, Fin.last] using h
  have htail : (fun i : Fin n => w i.castSucc) = v := by
    funext i
    have h := congrArg (fun b : FiniteBitMask => b.val i.val) he
    simpa [prefixBitMask, Fin.castSucc, Fin.castAdd, Fin.castLE, i.isLt, Nat.lt_trans i.isLt (Nat.lt_succ_self n)] using h
  simp only [finiteInvolutionAction, hlast, Bool.false_eq_true, ↓reduceIte, htail]

#print axioms finite_involution_action_multiplication
end FullBridge
