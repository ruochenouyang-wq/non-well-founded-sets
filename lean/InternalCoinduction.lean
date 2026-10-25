import RelationSupport
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem internal_coded_coinduction (base : BaseCollection s)
    (R : InternalQuotient base)
    (hR : Bisimulation (internalMember base) (CodedRelation (internalMember base) R)) :
    ∀ X Y, CodedRelation (internalMember base) R X Y → X = Y := by
  let q := internalCode base
  let t := internalMember base
  obtain ⟨B, hB⟩ := relation_support_exists (internal_base_model base) R
  have hBT := bisimulation_support_transitive hR hB
  obtain ⟨d, hdB⟩ := internal_code_onto base B
  have hBd : ∀ X, t X (q d) ↔ ∃ Y, CodedRelation t R X Y ∨ CodedRelation t R Y X := by
    intro X
    change internalMember base X (internalCode base d) ↔ _
    rw [hdB]
    exact hB X
  obtain ⟨ud, hud⟩ := base.union d
  have hchildren : ∀ u, s u ud → ∃ x, s x d ∧ InternalBehavior s u x := by
    intro u hu
    obtain ⟨z, hz, huz⟩ := (hud u).mp hu
    have hqz : internalMember base (q z) B := hdB ▸ (internal_exact_members base d (q z)).mpr ⟨z, hz, rfl⟩
    have hqu := hBT (q z) hqz (q u) ((internal_exact_members base z (q u)).mpr ⟨u, huz, rfl⟩)
    rw [← hdB] at hqu
    obtain ⟨x, hx, hxu⟩ := (internal_exact_members base d (q u)).mp hqu
    exact ⟨x, hx, (internal_code_eq base u x).mp hxu.symm⟩
  obtain ⟨k, hk, hkchild⟩ := collect_forward_witnesses base ud d hchildren
  obtain ⟨D, m, hdD, hm, hkm⟩ := bounded_augmented_extension base d k hk
  obtain ⟨r₀, hr₀⟩ := internal_code_onto base R
  change q r₀ = R at hr₀
  let p := Formula.translate (internalInterpretation base).equalFormula
    (internalInterpretation base).memberFormula (relatedFormula (n := 3) 2 1 0)
  have hp : ∀ x y, Eval s p (cons y (cons x (cons r₀ Fin.elim0))) ↔ CodedRelation t R (q x) (q y) := by
    intro x y
    have h := internal_formula_translation base (relatedFormula (n := 3) 2 1 0)
      (cons y (cons x (cons r₀ Fin.elim0)))
    rw [eval_relatedFormula] at h
    change Eval s p _ ↔ CodedRelation t (q r₀) (q x) (q y) at h
    rw [hr₀] at h
    exact h
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base p (cons r₀ Fin.elim0) d
  have hri : ∀ x y, CodedRelation s r x y ↔ s x d ∧ s y d ∧ CodedRelation t R (q x) (q y) := by
    intro x y
    exact (hr x y).trans (and_congr_right (fun _ => and_congr_right (fun _ => hp x y)))
  have hrGD : GraphCode s D r := by
    intro z hz
    obtain ⟨x, y, hx, hy, hxy⟩ := hrG z hz
    exact ⟨x, y, hdD x hx, hdD y hy, hxy⟩
  have hkeq : ∀ u x, WithIdentity (CodedRelation s k) u x → q u = q x := by
    intro u x hux
    exact (internal_code_eq base u x).mpr ⟨k, hk, hux⟩
  have hstep : ∀ x y, CodedRelation s r x y →
      (∀ u, s u x → ∃ v, s v y ∧ BisimSandwich s m r u v) ∧
      (∀ v, s v y → ∃ u, s u x ∧ BisimSandwich s m r u v) := by
    intro x y hxy
    obtain ⟨hx, hy, hqxy⟩ := (hri x y).mp hxy
    have hmatch := hR (q x) (q y) hqxy
    constructor
    · intro u hu
      obtain ⟨V, hVy, hquV⟩ := hmatch.1 (q u) ((internal_exact_members base x (q u)).mpr ⟨u, hu, rfl⟩)
      obtain ⟨v, hv, hvV⟩ := (internal_exact_members base y V).mp hVy
      obtain ⟨u₀, hu₀, hku⟩ := hkchild u ((hud u).mpr ⟨x, hx, hu⟩)
      obtain ⟨v₀, hv₀, hkv⟩ := hkchild v ((hud v).mpr ⟨y, hy, hv⟩)
      change q v = V at hvV
      have hq : CodedRelation t R (q u₀) (q v₀) := by
        rw [← hkeq u u₀ hku, ← hkeq v v₀ hkv, hvV]
        exact hquV
      exact ⟨v, hv, u₀, v₀, hkm u u₀ hku, (hri u₀ v₀).mpr ⟨hu₀, hv₀, hq⟩,
        maximal_augmented_symm base hm (hkm v v₀ hkv)⟩
    · intro v hv
      obtain ⟨X, hXx, hqXv⟩ := hmatch.2 (q v) ((internal_exact_members base y (q v)).mpr ⟨v, hv, rfl⟩)
      obtain ⟨u, hu, huX⟩ := (internal_exact_members base x X).mp hXx
      obtain ⟨u₀, hu₀, hku⟩ := hkchild u ((hud u).mpr ⟨x, hx, hu⟩)
      obtain ⟨v₀, hv₀, hkv⟩ := hkchild v ((hud v).mpr ⟨y, hy, hv⟩)
      change q u = X at huX
      have hq : CodedRelation t R (q u₀) (q v₀) := by
        rw [← hkeq u u₀ hku, ← hkeq v v₀ hkv, huX]
        exact hqXv
      exact ⟨u, hu, u₀, v₀, hkm u u₀ hku, (hri u₀ v₀).mpr ⟨hu₀, hv₀, hq⟩,
        maximal_augmented_symm base hm (hkm v v₀ hkv)⟩
  have hsub := bounded_bisimulation_up_to base hm hrGD hstep
  intro X Y hXY
  have hXB := (hBd X).mpr ⟨Y, Or.inl hXY⟩
  have hYB := (hBd Y).mpr ⟨X, Or.inr hXY⟩
  obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hXB
  obtain ⟨y, hy, rfl⟩ := (internal_exact_members base d Y).mp hYB
  exact (internal_code_eq base x y).mpr ⟨m, hm.2.1, Or.inr (hsub x y ((hri x y).mpr ⟨hx, hy, hXY⟩))⟩

#print axioms internal_coded_coinduction
end FullBridge
