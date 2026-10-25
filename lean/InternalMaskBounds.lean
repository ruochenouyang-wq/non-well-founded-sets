import GlobalInternalMaskActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem internal_omega_member_trichotomy (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) : ∀ m, s m w → ∀ n, s n w → s n m ∨ n = m ∨ s m n := by
  let p : Formula 2 := .all (.impl (.member 0 2)
    ((Formula.member 0 1).disj ((Formula.equal 0 1).disj (.member 1 0))))
  have hev : ∀ m, Eval s p (cons m (cons w Fin.elim0)) ↔
      (∀ n, s n w → s n m ∨ n = m ∨ s m n) := by
    intro m
    simp only [p, Eval, eval_disj]
    rfl
  have h := internal_omega_formula_induction base hw p (cons w Fin.elim0)
    ((hev z).mpr (fun n hn => Or.inr (internal_omega_zero_or_contains_zero base hw n hn))) (by
      intro m _ hm M hM
      apply (hev M).mpr
      intro n hn
      rcases (hev m).mp hm n hn with hnm | heq | hmn
      · exact Or.inl ((hM n).mpr (Or.inl hnm))
      · exact Or.inl ((hM n).mpr (Or.inr heq))
      · exact Or.inr (internal_omega_no_successor_gap base hw hM n hn hmn))
  exact fun m hm => (hev m).mp (h m hm)

theorem internal_omega_common_bound (base : BaseCollection s) {z w a b : U}
    (hw : OmegaCode s z w) (ha : s a w) (hb : s b w) :
    ∃ N, s N w ∧ Subset s a N ∧ Subset s b N := by
  rcases internal_omega_member_trichotomy base hw b hb a ha with hab | heq | hba
  · exact ⟨b, hb, fun x hx => (internal_omega_members_transitive_irreflexive base hw b hb).1 a hab x hx,
      fun _ hx => hx⟩
  · exact ⟨b, hb, heq ▸ (fun _ hx => hx), fun _ hx => hx⟩
  · exact ⟨a, ha, fun _ hx => hx,
      fun x hx => (internal_omega_members_transitive_irreflexive base hw a ha).1 b hba x hx⟩

theorem mask_support_common_bound (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U} {x y : U}
    (hx : MaskTailSupported s w J x) (hy : MaskTailSupported s w J y) :
    ∃ N, s N w ∧ ∀ a, (∀ i, s i a.val → ¬s i N) → J a x = x ∧ J a y = y := by
  obtain ⟨M, hM, hMx⟩ := hx
  obtain ⟨K, hK, hKy⟩ := hy
  obtain ⟨N, hN, hMN, hKN⟩ := internal_omega_common_bound base hw hM hK
  exact ⟨N, hN, fun a hdis => ⟨hMx a (fun i hi h => hdis i hi (hMN i h)),
    hKy a (fun i hi h => hdis i hi (hKN i h))⟩⟩
end FullBridge
