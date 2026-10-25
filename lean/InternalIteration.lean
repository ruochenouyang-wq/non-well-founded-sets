import InternalOmega
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def UnionClosureStep (s : U → U → Prop) (a b : U) : Prop :=
  ∀ x, s x b ↔ s x a ∨ ∃ y, s y a ∧ s x y

def unionClosureStepFormula {n} (a b : Fin n) : Formula n :=
  .all ((Formula.member 0 b.succ).iffF ((Formula.member 0 a.succ).disj
    (.ex (.conj (.member 0 a.succ.succ) (.member 1 0)))))

theorem eval_unionClosureStepFormula {n} (a b : Fin n) (v : Fin n → U) :
    Eval s (unionClosureStepFormula a b) v ↔ UnionClosureStep s (v a) (v b) := by
  simp only [unionClosureStepFormula, Eval, eval_iffF, eval_disj,
    UnionClosureStep, cons_succ]
  rfl

theorem union_closure_step_exists (base : BaseCollection s) (a : U) :
    ∃ b, UnionClosureStep s a b := by
  obtain ⟨u, hu⟩ := base.union a
  obtain ⟨b, hb⟩ := binary_union_exists base.pairing base.union a u
  exact ⟨b, fun x => (hb x).trans (or_congr Iff.rfl (hu x))⟩

theorem union_closure_step_unique (he : Extensional s) {a b c : U}
    (hb : UnionClosureStep s a b) (hc : UnionClosureStep s a c) : b = c :=
  he b c (fun x => (hb x).trans (hc x).symm)

theorem coded_function_append (base : BaseCollection s) {d e f v : U}
    (hf : FunctionCode s d f) (hdd : ¬s d d) (hde : IsSuccessor s d e) :
    ∃ g, FunctionCode s e g ∧ ∀ x y, CodedRelation s g x y ↔
      CodedRelation s f x y ∨ (x = d ∧ y = v) := by
  obtain ⟨p, hp⟩ := orderedPair_exists base.pairing d v
  obtain ⟨t, ht⟩ := base.pairing p p
  have ht' : ∀ z, s z t ↔ z = p := fun z =>
    (ht z).trans ⟨fun h => h.elim id id, fun h => Or.inl h⟩
  obtain ⟨g, hg⟩ := binary_union_exists base.pairing base.union f t
  have hrel : ∀ x y, CodedRelation s g x y ↔
      CodedRelation s f x y ∨ (x = d ∧ y = v) := by
    intro x y
    constructor
    · rintro ⟨q, hq, hpair⟩
      rcases (hg q).mp hq with hqf | hqt
      · exact Or.inl ⟨q, hqf, hpair⟩
      · have hqp := (ht' q).mp hqt
        subst q
        exact Or.inr (orderedPair_injective hpair hp)
    · intro h
      rcases h with ⟨q, hq, hpair⟩ | ⟨rfl, rfl⟩
      · exact ⟨q, (hg q).mpr (Or.inl hq), hpair⟩
      · exact ⟨p, (hg p).mpr (Or.inr ((ht' p).mpr rfl)), hp⟩
  refine ⟨g, ⟨?_, ?_⟩, hrel⟩
  · intro q hq
    rcases (hg q).mp hq with hqf | hqt
    · obtain ⟨x, y, hx, hxy⟩ := hf.1 q hqf
      exact ⟨x, y, (hde x).mpr (Or.inl hx), hxy⟩
    · have hqp := (ht' q).mp hqt
      subst q
      exact ⟨d, v, (hde d).mpr (Or.inr rfl), hp⟩
  · intro x hx
    rcases (hde x).mp hx with hxd | hxd
    · obtain ⟨y, hxy, huniq⟩ := hf.2 x hxd
      refine ⟨y, (hrel x y).mpr (Or.inl hxy), ?_⟩
      intro z hxz
      rcases (hrel x z).mp hxz with hxz | ⟨hxd', _⟩
      · exact huniq z hxz
      · exact False.elim (hdd (hxd' ▸ hxd))
    · subst x
      refine ⟨v, (hrel d v).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
      intro y hdy
      rcases (hrel d y).mp hdy with hdy | hdy
      · exact False.elim (hdd (coded_function_domain hf hdy))
      · exact hdy.2

def ClosureIterationCode (s : U → U → Prop) (z a n f : U) : Prop :=
  ∃ d, IsSuccessor s n d ∧ FunctionCode s d f ∧ CodedRelation s f z a ∧
    ∀ i j, s i d → s j d → IsSuccessor s i j → ∀ x y,
      CodedRelation s f i x → CodedRelation s f j y → UnionClosureStep s x y

def iterationRecurrenceFormula {n} (d f : Fin n) : Formula n :=
  .all (.all (.impl (.member 1 d.succ.succ) (.impl (.member 0 d.succ.succ)
    (.impl (successorFormula 1 0) (.all (.all
      (.impl (relatedFormula f.succ.succ.succ.succ 3 1)
        (.impl (relatedFormula f.succ.succ.succ.succ 2 0) (unionClosureStepFormula 1 0)))))))))

def closureIterationFormula {n} (z a i f : Fin n) : Formula n :=
  .ex (.conj (successorFormula i.succ 0)
    (.conj (functionCodeFormula 0 f.succ)
      (.conj (relatedFormula f.succ z.succ a.succ) (iterationRecurrenceFormula 0 f.succ))))

theorem eval_closureIterationFormula {n} (z a i f : Fin n) (v : Fin n → U) :
    Eval s (closureIterationFormula z a i f) v ↔
      ClosureIterationCode s (v z) (v a) (v i) (v f) := by
  simp only [closureIterationFormula, iterationRecurrenceFormula, Eval,
    eval_successorFormula, eval_functionCodeFormula, eval_relatedFormula,
    eval_unionClosureStepFormula, ClosureIterationCode, cons_succ]
  rfl

theorem closure_iteration_zero (base : BaseCollection s) {z : U}
    (hz : IsEmpty s z) (a : U) : ∃ f, ClosureIterationCode s z a z f := by
  obtain ⟨d, hzd⟩ := successor_exists base z
  have hf0 : FunctionCode s z z :=
    ⟨fun p hp => False.elim (hz p hp), fun x hx => False.elim (hz x hx)⟩
  obtain ⟨f, hf, hrel⟩ := coded_function_append (v := a) base hf0 (hz z) hzd
  refine ⟨f, d, hzd, hf, (hrel z a).mpr (Or.inr ⟨rfl, rfl⟩), ?_⟩
  intro i j hi hj hij x y _ _
  have hiz : i = z := ((hzd i).mp hi).resolve_left (hz i)
  have hjz : j = z := ((hzd j).mp hj).resolve_left (hz j)
  subst i
  subst j
  exact False.elim (hz z ((hij z).mpr (Or.inr rfl)))

theorem closure_iteration_extend (base : BaseCollection s) {z w a n m f x y : U}
    (hw : OmegaCode s z w) (hn : s n w) (hnm : IsSuccessor s n m)
    (hf : ClosureIterationCode s z a n f) (hfx : CodedRelation s f n x)
    (hxy : UnionClosureStep s x y) :
    ∃ g, ClosureIterationCode s z a m g ∧
      ∀ i v, CodedRelation s g i v ↔ CodedRelation s f i v ∨ (i = m ∧ v = y) := by
  obtain ⟨d, hnd, hfF, hf0, hfstep⟩ := hf
  have hdm := successor_unique base.extensional hnd hnm
  subst d
  have hm := hw.2.1.2 n hn m hnm
  obtain ⟨hmt, hmm⟩ := internal_omega_members_transitive_irreflexive base hw m hm
  obtain ⟨d, hmd⟩ := successor_exists base m
  obtain ⟨g, hgF, hgr⟩ := coded_function_append (v := y) base hfF hmm hmd
  refine ⟨g, ⟨d, hmd, hgF, (hgr z a).mpr (Or.inl hf0), ?_⟩, hgr⟩
  intro i j hi hj hij u v hiu hjv
  have him : s i m := by
    rcases (hmd i).mp hi with him | him
    · exact him
    · subst i
      have hmj := (hij m).mpr (Or.inr rfl)
      rcases (hmd j).mp hj with hjm | hjm
      · exact False.elim (hmm (hmt j hjm m hmj))
      · exact False.elim (hmm (hjm ▸ hmj))
  have hfi : CodedRelation s f i u := by
    rcases (hgr i u).mp hiu with hfi | ⟨heq, _⟩
    · exact hfi
    · exact False.elim (hmm (heq ▸ him))
  rcases (hmd j).mp hj with hjm | hjm
  · have hfj : CodedRelation s f j v := by
      rcases (hgr j v).mp hjv with hfj | ⟨heq, _⟩
      · exact hfj
      · exact False.elim (hmm (heq ▸ hjm))
    exact hfstep i j him hjm hij u v hfi hfj
  · subst j
    have hni := internal_omega_successor_injective base hw hn hnm hij
    subst i
    have hvy : v = y := by
      rcases (hgr m v).mp hjv with hfv | hmv
      · exact False.elim (hmm (coded_function_domain hfF hfv))
      · exact hmv.2
    obtain ⟨x', _, huniq⟩ := hfF.2 n ((hnm n).mpr (Or.inr rfl))
    have hux := (huniq u hfi).trans (huniq x hfx).symm
    exact hux.symm ▸ hvy.symm ▸ hxy

theorem closure_iteration_exists (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (a : U) : ∀ n, s n w → ∃ f, ClosureIterationCode s z a n f := by
  let p : Formula 3 := .ex (closureIterationFormula 2 3 1 0)
  have hev : ∀ n, Eval s p (cons n (cons z (cons a Fin.elim0))) ↔
      ∃ f, ClosureIterationCode s z a n f := by
    intro n
    simp only [p, Eval, eval_closureIterationFormula]
    rfl
  have h := internal_omega_formula_induction base hw p (cons z (cons a Fin.elim0))
    ((hev z).mpr (closure_iteration_zero base hw.1 a)) (by
      intro n hn hpn m hnm
      obtain ⟨f, hf⟩ := (hev n).mp hpn
      have hfcopy := hf
      obtain ⟨d, hnd, hfF, _, _⟩ := hf
      obtain ⟨x, hfx, _⟩ := hfF.2 n ((hnd n).mpr (Or.inr rfl))
      obtain ⟨y, hxy⟩ := union_closure_step_exists base x
      obtain ⟨g, hg, _⟩ := closure_iteration_extend base hw hn hnm hfcopy hfx hxy
      exact (hev m).mpr ⟨g, hg⟩)
  exact fun n hn => (hev n).mp (h n hn)

def ClosureIterationAgreement (s : U → U → Prop) (z a w i : U) : Prop :=
  ∀ f g m n x y, s m w → s n w → ClosureIterationCode s z a m f →
    ClosureIterationCode s z a n g → CodedRelation s f i x → CodedRelation s g i y → x = y

def iterationAgreementFormula : Formula 4 :=
  .all (.all (.all (.all (.all (.all
    (.impl (.member 3 9) (.impl (.member 2 9)
      (.impl (closureIterationFormula 7 8 3 5) (.impl (closureIterationFormula 7 8 2 4)
        (.impl (relatedFormula 5 6 1) (.impl (relatedFormula 4 6 0) (.equal 1 0))))))))))))

theorem eval_iterationAgreementFormula (i z a w : U) :
    Eval s iterationAgreementFormula (cons i (cons z (cons a (cons w Fin.elim0)))) ↔
      ClosureIterationAgreement s z a w i := by
  simp only [iterationAgreementFormula, Eval, eval_closureIterationFormula,
    eval_relatedFormula, ClosureIterationAgreement]
  rfl

theorem closure_iteration_agree (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (a : U) :
    ∀ i, s i w → ClosureIterationAgreement s z a w i := by
  have h := internal_omega_formula_induction base hw iterationAgreementFormula
    (cons z (cons a (cons w Fin.elim0)))
    ((eval_iterationAgreementFormula z z a w).mpr (by
      intro f g m n x y _ _ hf hg hfx hgy
      obtain ⟨d, _, hfF, hf0, _⟩ := hf
      obtain ⟨e, _, hgF, hg0, _⟩ := hg
      obtain ⟨u, _, hfu⟩ := hfF.2 z (coded_function_domain hfF hf0)
      obtain ⟨v, _, hgv⟩ := hgF.2 z (coded_function_domain hgF hg0)
      exact ((hfu x hfx).trans (hfu a hf0).symm).trans
        ((hgv a hg0).trans (hgv y hgy).symm))) (by
      intro i _ hpi j hij
      have hiA := (eval_iterationAgreementFormula i z a w).mp hpi
      apply (eval_iterationAgreementFormula j z a w).mpr
      intro f g m n x y hm hn hf hg hfx hgy
      have hfcopy := hf
      have hgcopy := hg
      obtain ⟨d, hmd, hfF, _, hfstep⟩ := hf
      obtain ⟨e, hne, hgF, _, hgstep⟩ := hg
      have hdt := (internal_omega_members_transitive_irreflexive base hw d
        (hw.2.1.2 m hm d hmd)).1
      have het := (internal_omega_members_transitive_irreflexive base hw e
        (hw.2.1.2 n hn e hne)).1
      have hjd := coded_function_domain hfF hfx
      have hje := coded_function_domain hgF hgy
      have hijM := (hij i).mpr (Or.inr rfl)
      have hid := hdt j hjd i hijM
      have hie := het j hje i hijM
      obtain ⟨u, hfu, _⟩ := hfF.2 i hid
      obtain ⟨v, hgv, _⟩ := hgF.2 i hie
      have huv := hiA f g m n u v hm hn hfcopy hgcopy hfu hgv
      subst v
      exact union_closure_step_unique base.extensional
        (hfstep i j hid hjd hij u x hfu hfx) (hgstep i j hie hje hij u y hgv hgy))
  exact fun i hi => (eval_iterationAgreementFormula i z a w).mp (h i hi)

def ClosureIterationValue (s : U → U → Prop) (z a n y : U) : Prop :=
  ∃ f, ClosureIterationCode s z a n f ∧ CodedRelation s f n y

def iterationValueFormula {n} (z a i y : Fin n) : Formula n :=
  .ex (.conj (closureIterationFormula z.succ a.succ i.succ 0)
    (relatedFormula 0 i.succ y.succ))

theorem eval_iterationValueFormula {n} (z a i y : Fin n) (v : Fin n → U) :
    Eval s (iterationValueFormula z a i y) v ↔
      ClosureIterationValue s (v z) (v a) (v i) (v y) := by
  simp only [iterationValueFormula, Eval, eval_closureIterationFormula,
    eval_relatedFormula, ClosureIterationValue, cons_succ]
  rfl

theorem closure_iteration_value_exists (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (a : U) {n : U} (hn : s n w) :
    ∃ y, ClosureIterationValue s z a n y := by
  obtain ⟨f, hf⟩ := closure_iteration_exists base hw a n hn
  have hfcopy := hf
  obtain ⟨d, hnd, hfF, _, _⟩ := hf
  obtain ⟨y, hfy, _⟩ := hfF.2 n ((hnd n).mpr (Or.inr rfl))
  exact ⟨y, f, hfcopy, hfy⟩

theorem closure_iteration_value_unique (base : BaseCollection s) {z w a n x y : U}
    (hw : OmegaCode s z w) (hn : s n w)
    (hx : ClosureIterationValue s z a n x) (hy : ClosureIterationValue s z a n y) : x = y := by
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨g, hg, hgy⟩ := hy
  exact closure_iteration_agree base hw a n hn f g n n x y hn hn hf hg hfx hgy

theorem closure_iteration_values_set (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) (a : U) :
    ∃ b, (∀ y, s y b ↔ ∃ n, s n w ∧ ClosureIterationValue s z a n y) ∧
      s a b ∧ ∀ x, s x b → ∃ y, s y b ∧ UnionClosureStep s x y := by
  have hrep := collection_separation_replacement s base.collection base.separation
  obtain ⟨b, hb⟩ := hrep 2 (iterationValueFormula 2 3 1 0)
    (cons z (cons a Fin.elim0)) w (by
      intro n hn
      obtain ⟨y, hy⟩ := closure_iteration_value_exists base hw a hn
      refine ⟨y, (eval_iterationValueFormula 2 3 1 0 _).mpr hy, ?_⟩
      intro v hv
      exact closure_iteration_value_unique base hw hn
        ((eval_iterationValueFormula 2 3 1 0 _).mp hv) hy)
  have hb' : ∀ y, s y b ↔ ∃ n, s n w ∧ ClosureIterationValue s z a n y := by
    intro y
    have h := hb y
    simp only [eval_iterationValueFormula] at h
    exact h
  refine ⟨b, hb', ?_, ?_⟩
  · obtain ⟨f, hf⟩ := closure_iteration_zero base hw.1 a
    have hfcopy := hf
    obtain ⟨_, _, _, hf0, _⟩ := hf
    exact (hb' a).mpr ⟨z, hw.2.1.1, f, hfcopy, hf0⟩
  · intro x hx
    obtain ⟨n, hn, f, hf, hfx⟩ := (hb' x).mp hx
    obtain ⟨m, hnm⟩ := successor_exists base n
    obtain ⟨y, hxy⟩ := union_closure_step_exists base x
    obtain ⟨g, hg, hgr⟩ := closure_iteration_extend base hw hn hnm hf hfx hxy
    exact ⟨y, (hb' y).mpr ⟨m, hw.2.1.2 n hn m hnm, g, hg,
      (hgr m y).mpr (Or.inr ⟨rfl, rfl⟩)⟩, hxy⟩

theorem transitive_cover_exists (base : BaseCollection s) (a : U) :
    ∃ t, TransitiveCode s t ∧ Subset s a t := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  obtain ⟨b, _, hab, hb⟩ := closure_iteration_values_set base hw a
  obtain ⟨t, ht⟩ := base.union b
  refine ⟨t, ?_, fun x hx => (ht x).mpr ⟨a, hab, hx⟩⟩
  intro x hxt y hyx
  obtain ⟨c, hcb, hxc⟩ := (ht x).mp hxt
  obtain ⟨d, hdb, hcd⟩ := hb c hcb
  exact (ht y).mpr ⟨d, hdb, (hcd y).mpr (Or.inr ⟨x, hxc, hyx⟩)⟩

theorem transitive_closure_exists (base : BaseCollection s) (a : U) :
    ∃ t, TransitiveCode s t ∧ Subset s a t ∧
      ∀ b, TransitiveCode s b → Subset s a b → Subset s t b := by
  obtain ⟨T, hT, haT⟩ := transitive_cover_exists base a
  let p : Formula 2 := .all (.impl (transitiveFormula 0)
    (.impl (.all (.impl (.member 0 3) (.member 0 1))) (.member 1 0)))
  obtain ⟨t, ht⟩ := base.separation 1 p (cons a Fin.elim0) T
  have ht' : ∀ x, s x t ↔ s x T ∧ ∀ b, TransitiveCode s b → Subset s a b → s x b := by
    intro x
    have h := ht x
    simp only [p, Eval, eval_transitiveFormula] at h
    exact h
  refine ⟨t, ?_, ?_, fun b hb hab x hx => ((ht' x).mp hx).2 b hb hab⟩
  · intro x hxt y hyx
    have hx := (ht' x).mp hxt
    exact (ht' y).mpr ⟨hT x hx.1 y hyx, fun b hb hab => hb x (hx.2 b hb hab) y hyx⟩
  · intro x hx
    exact (ht' x).mpr ⟨haT x hx, fun b _ hab => hab x hx⟩

#print axioms closure_iteration_exists
#print axioms closure_iteration_agree
#print axioms transitive_closure_exists
end FullBridge
