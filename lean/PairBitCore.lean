import CodedBitActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem disjoint_quine_swaps_commute {a b c d : U}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (x : U) :
    quineSwap a b (quineSwap c d x) = quineSwap c d (quineSwap a b x) := by
  classical
  by_cases hxa : x = a
  · subst x
    simp [quineSwap, hac, had, hbc, hbd]
  · by_cases hxb : x = b
    · subst x
      simp [quineSwap, hac, had, hbc, hbd, Ne.symm hab]
    · by_cases hxc : x = c
      · subst x
        simp [quineSwap, Ne.symm hac, Ne.symm hbc, Ne.symm had, Ne.symm hbd]
      · by_cases hxd : x = d
        · subst x
          simp [quineSwap, Ne.symm hac, Ne.symm hbc, Ne.symm had, Ne.symm hbd, Ne.symm hcd]
        · simp [quineSwap, hxa, hxb, hxc, hxd]

noncomputable def pairLocalFlip {F : U} (S : PairSwapSequence s F) (n : Nat) : U → U :=
  quineSwap (S.action n).left (S.action n).right

theorem pair_local_flips_commute {F : U} (S : PairSwapSequence s F) (n m : Nat) (x : U) :
    pairLocalFlip S n (pairLocalFlip S m x) = pairLocalFlip S m (pairLocalFlip S n x) := by
  classical
  by_cases he : n = m
  · subst m; rfl
  · have hdiff : ∀ y, s y (S.row n) → s y (S.row m) → False := by
      intro y hn hm
      exact he (S.row_injective n m (S.disjoint_rows _ _ y (S.row_mem n) (S.row_mem m) hn hm))
    apply disjoint_quine_swaps_commute (S.action n).distinct (S.action m).distinct
    · intro h
      exact hdiff _ (((S.action n).pair _).mpr (Or.inl rfl)) (((S.action m).pair _).mpr (Or.inl h))
    · intro h
      exact hdiff _ (((S.action n).pair _).mpr (Or.inl rfl)) (((S.action m).pair _).mpr (Or.inr h))
    · intro h
      exact hdiff _ (((S.action n).pair _).mpr (Or.inr rfl)) (((S.action m).pair _).mpr (Or.inl h))
    · intro h
      exact hdiff _ (((S.action n).pair _).mpr (Or.inr rfl)) (((S.action m).pair _).mpr (Or.inr h))

theorem pair_local_flip_mem {F d : U} (S : PairSwapSequence s F)
    (hd : ∀ x, s x d ↔ ∃ c, s c F ∧ s x c) (n : Nat) {x : U} (hx : s x d) :
    s (pairLocalFlip S n x) d := by
  classical
  have hl := (hd (S.action n).left).mpr ⟨S.row n, S.row_mem n, ((S.action n).pair _).mpr (Or.inl rfl)⟩
  have hr := (hd (S.action n).right).mpr ⟨S.row n, S.row_mem n, ((S.action n).pair _).mpr (Or.inr rfl)⟩
  by_cases hxl : x = (S.action n).left
  · simpa [pairLocalFlip, quineSwap, hxl] using hr
  · by_cases hxr : x = (S.action n).right
    · simpa [pairLocalFlip, quineSwap, hxr, Ne.symm (S.action n).distinct] using hl
    · simpa [pairLocalFlip, quineSwap, hxl, hxr] using hx

/-- Concrete binary-flip actions on the whole internal union of the pair
    family, including labels outside the selected standard rows. -/
theorem pair_family_bit_core (base : BaseCollection s) {F : U} (S : PairSwapSequence s F) :
    ∃ d, ∃ A : FixedCoreActions s finiteBitExhaustion,
      (∀ x, s x d ↔ ∃ c, s c F ∧ s x c) ∧ A.domain = d ∧
      ∀ n v x y, CodedRelation s ((A.stage n).code v) x y ↔
        s x d ∧ y = finiteInvolutionAction (pairLocalFlip S) n v x := by
  obtain ⟨d, hd⟩ := base.union F
  have hq : ∀ x, s x d → SelfSingleton s x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
    exact S.quines c x hc hxc
  have hc : ∀ n, ∃ c, FunctionCode s d c ∧ ∀ x y,
      CodedRelation s c x y ↔ s x d ∧ y = pairLocalFlip S n x := by
    intro n
    have hl := (hd (S.action n).left).mpr ⟨S.row n, S.row_mem n, ((S.action n).pair _).mpr (Or.inl rfl)⟩
    have hr := (hd (S.action n).right).mpr ⟨S.row n, S.row_mem n, ((S.action n).pair _).mpr (Or.inr rfl)⟩
    obtain ⟨P, hP, hp⟩ := quine_domain_internal_swap base hq hl hr (S.action n).distinct
    exact ⟨P.code, hP ▸ P.iso.1, hp⟩
  obtain ⟨A, ha, hr⟩ := coded_bit_core_actions base hq (pairLocalFlip S)
    (fun n x hx => pair_local_flip_mem S hd n hx)
    (fun n x => quine_swap_involutive (S.action n).distinct x)
    (pair_local_flips_commute S) hc
  exact ⟨d, A, hd, ha, hr⟩

#print axioms pair_family_bit_core
end FullBridge
