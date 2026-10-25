import LeastClosedRestriction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def successorFormula {n} (a b : Fin n) : Formula n :=
  .all ((Formula.member 0 b.succ).iffF
    ((Formula.member 0 a.succ).disj (.equal 0 a.succ)))

theorem eval_successorFormula {n} (a b : Fin n) (v : Fin n → U) :
    Eval s (successorFormula a b) v ↔ IsSuccessor s (v a) (v b) := by
  simp only [successorFormula, Eval, eval_iffF, eval_disj, IsSuccessor, cons_succ]
  rfl

def InductiveCode (s : U → U → Prop) (z a : U) : Prop :=
  s z a ∧ ∀ x, s x a → ∀ y, IsSuccessor s x y → s y a

def inductiveFormula {n} (z a : Fin n) : Formula n :=
  .conj (.member z a) (.all (.impl (.member 0 a.succ)
    (.all (.impl (successorFormula 1 0) (.member 0 a.succ.succ)))))

theorem eval_inductiveFormula {n} (z a : Fin n) (v : Fin n → U) :
    Eval s (inductiveFormula z a) v ↔ InductiveCode s (v z) (v a) := by
  simp only [inductiveFormula, Eval, eval_successorFormula, InductiveCode, cons_succ]
  rfl

/-- The least internal inductive set. This does not identify its external
    extension with Lean Nat or assume external well-foundedness. -/
def OmegaCode (s : U → U → Prop) (z w : U) : Prop :=
  IsEmpty s z ∧ InductiveCode s z w ∧
    ∀ a, InductiveCode s z a → Subset s w a

def omegaFormula {n} (z w : Fin n) : Formula n :=
  .conj (.all (.impl (.member 0 z.succ) .bottom))
    (.conj (inductiveFormula z w)
      (.all (.impl (inductiveFormula z.succ 0)
        (.all (.impl (.member 0 w.succ.succ) (.member 0 1))))))

theorem eval_omegaFormula {n} (z w : Fin n) (v : Fin n → U) :
    Eval s (omegaFormula z w) v ↔ OmegaCode s (v z) (v w) := by
  simp only [omegaFormula, Eval, eval_inductiveFormula, OmegaCode, IsEmpty,
    Subset, cons_succ]
  rfl

theorem successor_exists (base : BaseCollection s) (a : U) :
    ∃ b, IsSuccessor s a b := by
  obtain ⟨t, ht⟩ := base.pairing a a
  obtain ⟨b, hb⟩ := binary_union_exists base.pairing base.union a t
  refine ⟨b, fun x => (hb x).trans ?_⟩
  exact or_congr Iff.rfl ((ht x).trans ⟨fun h => h.elim id id, fun h => Or.inl h⟩)

theorem successor_unique (he : Extensional s) {a b c : U}
    (hb : IsSuccessor s a b) (hc : IsSuccessor s a c) : b = c := by
  exact he b c (fun x => (hb x).trans (hc x).symm)

theorem internal_omega_exists (base : BaseCollection s) : ∃ z w, OmegaCode s z w := by
  obtain ⟨i, ⟨z, hzi, hz⟩, hi⟩ := base.infinity
  have hiI : InductiveCode s z i := by
    refine ⟨hzi, ?_⟩
    intro x hx y hxy
    obtain ⟨y', hy'i, hxy'⟩ := hi x hx
    exact successor_unique base.extensional hxy' hxy ▸ hy'i
  obtain ⟨w, hw⟩ := base.separation 1
    (.all (.impl (inductiveFormula 2 0) (.member 1 0))) (cons z Fin.elim0) i
  have hw' : ∀ x, s x w ↔ s x i ∧ ∀ a, InductiveCode s z a → s x a := by
    intro x
    have h := hw x
    simp only [Eval, eval_inductiveFormula] at h
    exact h
  refine ⟨z, w, hz, ?_, fun a ha x hx => ((hw' x).mp hx).2 a ha⟩
  refine ⟨(hw' z).mpr ⟨hzi, fun a ha => ha.1⟩, ?_⟩
  intro x hx y hxy
  have h := (hw' x).mp hx
  exact (hw' y).mpr ⟨hiI.2 x h.1 y hxy, fun a ha => ha.2 x (h.2 a ha) y hxy⟩

theorem internal_omega_unique (base : BaseCollection s) {z w w' : U}
    (hw : OmegaCode s z w) (hw' : OmegaCode s z w') : w = w' := by
  exact base.extensional w w' (fun x => ⟨hw.2.2 w' hw'.2.1 x, hw'.2.2 w hw.2.1 x⟩)

/-- Induction ranges over the actual source syntax, with any finite parameter list. -/
theorem internal_omega_formula_induction (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {n} (p : Formula (n + 1)) (v : Fin n → U)
    (hzero : Eval s p (cons z v))
    (hstep : ∀ x, s x w → Eval s p (cons x v) → ∀ y,
      IsSuccessor s x y → Eval s p (cons y v)) :
    ∀ x, s x w → Eval s p (cons x v) := by
  obtain ⟨d, hd⟩ := base.separation n p v w
  have hdI : InductiveCode s z d := by
    refine ⟨(hd z).mpr ⟨hw.2.1.1, hzero⟩, ?_⟩
    intro x hx y hxy
    obtain ⟨hxw, hpx⟩ := (hd x).mp hx
    exact (hd y).mpr ⟨hw.2.1.2 x hxw y hxy, hstep x hxw hpx y hxy⟩
  exact fun x hx => ((hd x).mp (hw.2.2 d hdI x hx)).2

theorem internal_omega_transitive (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) : TransitiveCode s w := by
  let p : Formula 2 := .all (.impl (.member 0 1) (.member 0 2))
  have hev : ∀ x, Eval s p (cons x (cons w Fin.elim0)) ↔ Subset s x w :=
    fun _ => Iff.rfl
  have h := internal_omega_formula_induction base hw p (cons w Fin.elim0)
    ((hev z).mpr (fun y hy => False.elim (hw.1 y hy))) (by
      intro x hx hpx y hxy
      apply (hev y).mpr
      intro t ht
      exact ((hxy t).mp ht).elim (fun htx => (hev x).mp hpx t htx) (fun htx => htx ▸ hx))
  exact fun x hx => (hev x).mp (h x hx)

theorem internal_omega_members_transitive_irreflexive (base : BaseCollection s)
    {z w : U} (hw : OmegaCode s z w) :
    ∀ x, s x w → TransitiveCode s x ∧ ¬s x x := by
  let p : Formula 1 := .conj (transitiveFormula 0) (.impl (.member 0 0) .bottom)
  have hev : ∀ x, Eval s p (cons x Fin.elim0) ↔ TransitiveCode s x ∧ ¬s x x := by
    intro x
    simp only [p, Eval, eval_transitiveFormula]
    rfl
  have h := internal_omega_formula_induction base hw p Fin.elim0
    ((hev z).mpr ⟨fun x hx => False.elim (hw.1 x hx), hw.1 z⟩) (by
      intro x _ hpx y hxy
      obtain ⟨ht, hn⟩ := (hev x).mp hpx
      apply (hev y).mpr
      constructor
      · intro a ha b hb
        apply (hxy b).mpr
        rcases (hxy a).mp ha with hax | rfl
        · exact Or.inl (ht a hax b hb)
        · exact Or.inl hb
      · intro hyy
        have hxyM := (hxy x).mpr (Or.inr rfl)
        rcases (hxy y).mp hyy with hyx | hyx
        · exact hn (ht y hyx x hxyM)
        · exact hn (hyx ▸ hxyM))
  exact fun x hx => (hev x).mp (h x hx)

theorem internal_omega_zero_or_successor (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) :
    ∀ x, s x w → x = z ∨ ∃ n, s n w ∧ IsSuccessor s n x := by
  let p : Formula 3 := (Formula.equal 0 1).disj
    (.ex (.conj (.member 0 3) (successorFormula 0 1)))
  have hev : ∀ x, Eval s p (cons x (cons z (cons w Fin.elim0))) ↔
      x = z ∨ ∃ n, s n w ∧ IsSuccessor s n x := by
    intro x
    simp only [p, eval_disj, Eval, eval_successorFormula]
    rfl
  have h := internal_omega_formula_induction base hw p (cons z (cons w Fin.elim0))
    ((hev z).mpr (Or.inl rfl)) (by
      intro x hx _ y hxy
      exact (hev y).mpr (Or.inr ⟨x, hx, hxy⟩))
  exact fun x hx => (hev x).mp (h x hx)

theorem internal_omega_successor_injective (base : BaseCollection s) {z w a b c : U}
    (hw : OmegaCode s z w) (ha : s a w)
    (hac : IsSuccessor s a c) (hbc : IsSuccessor s b c) : a = b := by
  obtain ⟨hat, haa⟩ := internal_omega_members_transitive_irreflexive base hw a ha
  have hacM := (hac a).mpr (Or.inr rfl)
  have hbcM := (hbc b).mpr (Or.inr rfl)
  rcases (hbc a).mp hacM with hab | hab
  · rcases (hac b).mp hbcM with hba | hba
    · exact False.elim (haa (hat b hba a hab))
    · exact hba.symm
  · exact hab

theorem internal_omega_members_wellFounded (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) : ∀ x, s x w → InternallyWellFounded s x := by
  have h := internal_omega_formula_induction base hw (internallyWellFoundedFormula 0)
    Fin.elim0 ((eval_internallyWellFoundedFormula s 0 _).mpr (by
      intro b hb hne
      obtain ⟨x, hx⟩ := hne
      exact False.elim (hw.1 x (hb x hx)))) (by
      intro x hx hpx y hxy
      have hWF := (eval_internallyWellFoundedFormula s 0 _).mp hpx
      obtain ⟨hxt, hxx⟩ := internal_omega_members_transitive_irreflexive base hw x hx
      apply (eval_internallyWellFoundedFormula s 0 _).mpr
      intro b hby hne
      obtain ⟨c, hc⟩ := base.separation 1 (.member 0 1) (cons x Fin.elim0) b
      have hc' : ∀ u, s u c ↔ s u b ∧ s u x := hc
      classical
      by_cases hcn : ∃ u, s u c
      · obtain ⟨u, huc, hmin⟩ := hWF c (fun v hv => ((hc' v).mp hv).2) hcn
        obtain ⟨hub, hux⟩ := (hc' u).mp huc
        refine ⟨u, hub, ?_⟩
        intro v hvb hvu
        exact hmin v ((hc' v).mpr ⟨hvb, hxt u hux v hvu⟩) hvu
      · have heq : ∀ u, s u b → u = x := by
          intro u hub
          rcases (hxy u).mp (hby u hub) with hux | hux
          · exact False.elim (hcn ⟨u, (hc' u).mpr ⟨hub, hux⟩⟩)
          · exact hux
        obtain ⟨u, hub⟩ := hne
        have hux := heq u hub
        subst u
        exact ⟨x, hub, fun v hvb hvx => hxx (heq v hvb ▸ hvx)⟩)
  exact fun x hx => (eval_internallyWellFoundedFormula s 0 _).mp (h x hx)

theorem internal_omega_wellFounded (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) : InternallyWellFounded s w := by
  intro b hbw hne
  obtain ⟨x, hxb⟩ := hne
  obtain ⟨y, hxy⟩ := successor_exists base x
  have hyw := hw.2.1.2 x (hbw x hxb) y hxy
  have hyWF := internal_omega_members_wellFounded base hw y hyw
  have hyt := (internal_omega_members_transitive_irreflexive base hw y hyw).1
  obtain ⟨c, hc⟩ := base.separation 1 (.member 0 1) (cons y Fin.elim0) b
  have hc' : ∀ u, s u c ↔ s u b ∧ s u y := hc
  obtain ⟨u, huc, hmin⟩ := hyWF c (fun v hv => ((hc' v).mp hv).2)
    ⟨x, (hc' x).mpr ⟨hxb, (hxy x).mpr (Or.inr rfl)⟩⟩
  obtain ⟨hub, huy⟩ := (hc' u).mp huc
  exact ⟨u, hub, fun v hvb hvu => hmin v
    ((hc' v).mpr ⟨hvb, hyt u huy v hvu⟩) hvu⟩

theorem internal_omega_quotient (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) :
    OmegaCode (internalMember base) (internalCode base z) (internalCode base w) := by
  let q := internalCode base
  let t := internalMember base
  have hm : ExactMembers s t q := internal_exact_members base
  have htbase := internal_base_model base
  refine ⟨isEmpty_forward hm hw.1, ?_, ?_⟩
  · refine ⟨(hm w (q z)).mpr ⟨z, hw.2.1.1, rfl⟩, ?_⟩
    intro X hX Y hXY
    obtain ⟨x, hx, rfl⟩ := (hm w X).mp hX
    obtain ⟨y, hxy⟩ := successor_exists base x
    have heq := successor_unique htbase.extensional (successor_forward hm hxy) hXY
    exact heq ▸ (hm w (q y)).mpr ⟨y, hw.2.1.2 x hx y hxy, rfl⟩
  · intro A hA X hX
    obtain ⟨a, rfl⟩ := internal_code_onto base A
    obtain ⟨x, hx, rfl⟩ := (hm w X).mp hX
    let p : Formula 2 := behaviorTranslation (.member 0 1)
    have hev : ∀ u, Eval s p (cons u (cons a Fin.elim0)) ↔ t (q u) (q a) := by
      intro u
      exact uniform_behavior_translation base (.member 0 1) (cons u (cons a Fin.elim0))
    have h := internal_omega_formula_induction base hw p (cons a Fin.elim0)
      ((hev z).mpr hA.1) (by
        intro u _ hpu v huv
        exact (hev v).mpr (hA.2 (q u) ((hev u).mp hpu) (q v) (successor_forward hm huv)))
    exact (hev x).mp (h x hx)

#print axioms internal_omega_exists
#print axioms internal_omega_formula_induction
#print axioms internal_omega_members_transitive_irreflexive
#print axioms internal_omega_wellFounded
#print axioms internal_omega_quotient
end FullBridge
