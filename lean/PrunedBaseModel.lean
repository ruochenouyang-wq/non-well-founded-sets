import PrunedQuotientRows
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Fixed graph parameter b is placed after the one free predicate variable. -/
def prunedUnaryFormula {n} (p : Formula (n + 1)) : Formula (n + 2) :=
  Formula.translateParameters (leastGlobalEqualFormula prunedMemberFormula)
    (leastGlobalMemberFormula prunedMemberFormula) (fun _ => 1)
    (Fin.cases 0 (fun j => j.succ.succ)) p

theorem eval_prunedUnaryFormula (base : BaseCollection s) (b : U) {n}
    (p : Formula (n + 1)) (e : Fin n → U) (x : U) :
    Eval s (prunedUnaryFormula p) (cons x (cons b e)) ↔
      Eval (prunedMember base b) p (cons (prunedCode base b x) (fun j => prunedCode base b (e j))) := by
  have h := least_global_formula_translation base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) p (fun _ => 1) (Fin.cases 0 (fun j => j.succ.succ))
    (cons x (cons b e)) (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j)
  have he : (fun i => prunedCode base b (cons x (cons b e) (Fin.cases 0 (fun j => j.succ.succ) i))) =
      cons (prunedCode base b x) (fun j => prunedCode base b (e j)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact h.trans (by rw [he])

/-- Fixed b follows the two free relation variables [y,x]. -/
def prunedBinaryFormula {n} (p : Formula (n + 2)) : Formula (n + 3) :=
  Formula.translateParameters (leastGlobalEqualFormula prunedMemberFormula)
    (leastGlobalMemberFormula prunedMemberFormula) (fun _ => 2)
    (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ))) p

theorem eval_prunedBinaryFormula (base : BaseCollection s) (b : U) {n}
    (p : Formula (n + 2)) (e : Fin n → U) (x y : U) :
    Eval s (prunedBinaryFormula p) (cons y (cons x (cons b e))) ↔
      Eval (prunedMember base b) p (cons (prunedCode base b y)
        (cons (prunedCode base b x) (fun j => prunedCode base b (e j)))) := by
  have h := least_global_formula_translation base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) p (fun _ => 2)
    (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)))
    (cons y (cons x (cons b e))) (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j)
  have he : (fun i => prunedCode base b (cons y (cons x (cons b e))
      (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)) i))) =
      cons (prunedCode base b y) (cons (prunedCode base b x) (fun j => prunedCode base b (e j))) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  exact h.trans (by rw [he])

/-- Every quotient object is represented by a set whose members are all retained. -/
theorem pruned_clean_representative (base : BaseCollection s) {b : U} (hbb : s b b)
    (X : PrunedQuotient base b) :
    ∃ a, (∀ x, s x a → ¬s b x) ∧ prunedCode base b a = X := by
  obtain ⟨a, hba, rfl⟩ := pruned_good_representative base b X
  obtain ⟨c, hc⟩ := base.separation 1 (.impl (.member 1 0) .bottom) (cons b Fin.elim0) a
  have hc' : ∀ x, s x c ↔ s x a ∧ ¬s b x := hc
  have hgood : ∀ x, s x c → ¬s b x := fun x hx => ((hc' x).mp hx).2
  refine ⟨c, hgood, ?_⟩
  apply least_global_extensional base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
  intro Y
  refine ((pruned_good_row base hbb hgood).2 Y).trans ?_
  refine Iff.trans ?_ (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) a Y).symm
  constructor
  · rintro ⟨x, hx, hq⟩
    obtain ⟨hxa, hbx⟩ := (hc' x).mp hx
    exact ⟨x, ⟨hba, hbx, hxa⟩, hq⟩
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, (hc' x).mpr ⟨hx.2.2, hx.2.1⟩, hq⟩

theorem pruned_quotient_separation (base : BaseCollection s) {b : U} (hbb : s b b) :
    Separation (prunedMember base b) := by
  intro n p e A
  obtain ⟨a, hgood, rfl⟩ := pruned_clean_representative base hbb A
  have onto := least_global_code_onto base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
  obtain ⟨d, hd⟩ := lift_env onto e
  have ht : ∀ x, Eval s (prunedUnaryFormula p) (cons x (cons b d)) ↔
      Eval (prunedMember base b) p (cons (prunedCode base b x) e) := by
    intro x
    simpa only [hd] using eval_prunedUnaryFormula base b p d x
  obtain ⟨c, hc⟩ := base.separation (n + 1) (prunedUnaryFormula p) (cons b d) a
  have hcgood : ∀ x, s x c → ¬s b x := fun x hx => hgood x ((hc x).mp hx).1
  refine ⟨prunedCode base b c, ?_⟩
  intro Y
  constructor
  · intro hY
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hcgood).2 Y).mp hY
    obtain ⟨hxa, hp⟩ := (hc x).mp hx
    exact ⟨((pruned_good_row base hbb hgood).2 _).mpr ⟨x, hxa, rfl⟩, (ht x).mp hp⟩
  · rintro ⟨hY, hp⟩
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hgood).2 Y).mp hY
    exact ((pruned_good_row base hbb hcgood).2 _).mpr ⟨x, (hc x).mpr ⟨hx, (ht x).mpr hp⟩, rfl⟩

theorem pruned_quotient_collection (base : BaseCollection s) {b : U} (hbb : s b b) :
    Collection (prunedMember base b) := by
  intro n p e A htotal
  obtain ⟨a, hgood, rfl⟩ := pruned_clean_representative base hbb A
  have onto := least_global_code_onto base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
  obtain ⟨d, hd⟩ := lift_env onto e
  have ht : ∀ x y, Eval s (prunedBinaryFormula p) (cons y (cons x (cons b d))) ↔
      Eval (prunedMember base b) p (cons (prunedCode base b y) (cons (prunedCode base b x) e)) := by
    intro x y
    simpa only [hd] using eval_prunedBinaryFormula base b p d x y
  have hs : ∀ x, s x a → ∃ y, Eval s (prunedBinaryFormula p) (cons y (cons x (cons b d))) := by
    intro x hx
    obtain ⟨Y, hY⟩ := htotal (prunedCode base b x)
      (((pruned_good_row base hbb hgood).2 _).mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, rfl⟩ := onto Y
    exact ⟨y, (ht x y).mpr hY⟩
  obtain ⟨c, hc⟩ := base.collection (n + 1) (prunedBinaryFormula p) (cons b d) a hs
  obtain ⟨r, _, hr⟩ := pruned_row_realization base hbb c
  refine ⟨prunedCode base b r, ?_⟩
  intro X hX
  obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hgood).2 X).mp hX
  obtain ⟨y, hy, hp⟩ := hc x hx
  exact ⟨prunedCode base b y, (hr _).mpr ⟨y, hy, rfl⟩, (ht x y).mp hp⟩

theorem pruned_quotient_union (base : BaseCollection s) {b : U} (hbb : s b b) :
    Union (prunedMember base b) := by
  intro A
  obtain ⟨a, hgood, rfl⟩ := pruned_clean_representative base hbb A
  obtain ⟨u, hu⟩ := base.union a
  obtain ⟨c, hc⟩ := base.separation 1 (.impl (.member 1 0) .bottom) (cons b Fin.elim0) u
  have hc' : ∀ x, s x c ↔ s x u ∧ ¬s b x := hc
  have hcgood : ∀ x, s x c → ¬s b x := fun x hx => ((hc' x).mp hx).2
  refine ⟨prunedCode base b c, ?_⟩
  intro X
  constructor
  · intro hX
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hcgood).2 X).mp hX
    obtain ⟨hxu, hbx⟩ := (hc' x).mp hx
    obtain ⟨y, hya, hxy⟩ := (hu x).mp hxu
    refine ⟨prunedCode base b y, ((pruned_good_row base hbb hgood).2 _).mpr ⟨y, hya, rfl⟩, ?_⟩
    exact (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) y _).mpr ⟨x, ⟨hgood y hya, hbx, hxy⟩, rfl⟩
  · rintro ⟨Y, hY, hXY⟩
    obtain ⟨y, hya, rfl⟩ := ((pruned_good_row base hbb hgood).2 Y).mp hY
    obtain ⟨x, hx, rfl⟩ := (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) y X).mp hXY
    exact ((pruned_good_row base hbb hcgood).2 _).mpr
      ⟨x, (hc' x).mpr ⟨(hu x).mpr ⟨y, hya, hx.2.2⟩, hx.2.1⟩, rfl⟩

/-- Target subsets lift to actual source subsets of a clean representative. -/
theorem pruned_subset_representative (base : BaseCollection s) {b a : U} (hbb : s b b)
    (ha : ∀ x, s x a → ¬s b x) (Z : PrunedQuotient base b)
    (hZ : Subset (prunedMember base b) Z (prunedCode base b a)) :
    ∃ c, Subset s c a ∧ prunedCode base b c = Z := by
  obtain ⟨z, _, rfl⟩ := pruned_good_representative base b Z
  obtain ⟨c, hc⟩ := base.separation 2 (leastGlobalMemberFormula prunedMemberFormula)
    (cons z (cons b Fin.elim0)) a
  have hc' : ∀ x, s x c ↔ s x a ∧ prunedMember base b (prunedCode base b x) (prunedCode base b z) := by
    intro x
    exact (hc x).trans (and_congr_right (fun _ => eval_leastGlobalMemberFormula base
      prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b) x z))
  have hca : Subset s c a := fun x hx => ((hc' x).mp hx).1
  have hcg : ∀ x, s x c → ¬s b x := fun x hx => ha x (hca x hx)
  refine ⟨c, hca, ?_⟩
  apply least_global_extensional base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
  intro X
  constructor
  · intro hX
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hcg).2 X).mp hX
    exact ((hc' x).mp hx).2
  · intro hX
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb ha).2 X).mp (hZ X hX)
    exact ((pruned_good_row base hbb hcg).2 _).mpr ⟨x, (hc' x).mpr ⟨hx, hX⟩, rfl⟩

theorem pruned_quotient_powerset (base : BaseCollection s) {b : U} (hbb : s b b) :
    PowerSet (prunedMember base b) := by
  intro A
  obtain ⟨a, hag, rfl⟩ := pruned_clean_representative base hbb A
  obtain ⟨p, hp⟩ := base.powerset a
  have hpg : ∀ c, s c p → ¬s b c := by
    intro c hc
    exact (pruned_good_row base hbb (fun x hx => hag x ((hp c).mp hc x hx))).1
  refine ⟨prunedCode base b p, ?_⟩
  intro Z
  constructor
  · intro hZ
    obtain ⟨c, hc, rfl⟩ := ((pruned_good_row base hbb hpg).2 Z).mp hZ
    have hca := (hp c).mp hc
    have hcg : ∀ x, s x c → ¬s b x := fun x hx => hag x (hca x hx)
    intro X hX
    obtain ⟨x, hx, rfl⟩ := ((pruned_good_row base hbb hcg).2 X).mp hX
    exact ((pruned_good_row base hbb hag).2 _).mpr ⟨x, hca x hx, rfl⟩
  · intro hZ
    obtain ⟨c, hca, rfl⟩ := pruned_subset_representative base hbb hag Z hZ
    exact ((pruned_good_row base hbb hpg).2 _).mpr ⟨c, (hp c).mpr hca, rfl⟩

theorem pruned_quotient_infinity (base : BaseCollection s) {b : U} (hbb : s b b) :
    Infinity (prunedMember base b) := by
  obtain ⟨z, w, hw⟩ := internal_omega_exists base
  have hwt := internal_omega_transitive base hw
  have hwg : ∀ x, s x w → ¬s b x := by
    intro x hx hbx
    exact (internal_omega_members_transitive_irreflexive base hw b (hwt x hx b hbx)).2 hbb
  have hng : ∀ x, s x w → ∀ y, s y x → ¬s b y :=
    fun x hx y hy => hwg y (hwt x hx y hy)
  have hrow := (pruned_good_row base hbb hwg).2
  have hzrow := (pruned_good_row base hbb (hng z hw.2.1.1)).2
  refine ⟨prunedCode base b w, ⟨prunedCode base b z, (hrow _).mpr ⟨z, hw.2.1.1, rfl⟩, ?_⟩, ?_⟩
  · intro X hX
    obtain ⟨x, hx, _⟩ := (hzrow X).mp hX
    exact hw.1 x hx
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := (hrow X).mp hX
    obtain ⟨y, hxy⟩ := successor_exists base x
    have hy := hw.2.1.2 x hx y hxy
    refine ⟨prunedCode base b y, (hrow _).mpr ⟨y, hy, rfl⟩, ?_⟩
    intro Z
    constructor
    · intro hZ
      obtain ⟨z', hz', rfl⟩ := ((pruned_good_row base hbb (hng y hy)).2 Z).mp hZ
      rcases (hxy z').mp hz' with hz'x | rfl
      · exact Or.inl (((pruned_good_row base hbb (hng x hx)).2 _).mpr ⟨z', hz'x, rfl⟩)
      · exact Or.inr rfl
    · intro hZ
      rcases hZ with hZ | rfl
      · obtain ⟨z', hz', rfl⟩ := ((pruned_good_row base hbb (hng x hx)).2 Z).mp hZ
        exact ((pruned_good_row base hbb (hng y hy)).2 _).mpr ⟨z', (hxy z').mpr (Or.inl hz'), rfl⟩
      · exact ((pruned_good_row base hbb (hng y hy)).2 _).mpr ⟨x, (hxy x).mpr (Or.inr rfl), rfl⟩

/-- Full base for the actual pruned least quotient. Anti-foundation is not
    included in BaseCollection and is not asserted by this theorem. -/
theorem pruned_quotient_base (base : BaseCollection s) {b : U} (hbb : s b b) :
    BaseCollection (prunedMember base b) where
  extensional := least_global_extensional base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
  empty := pruned_quotient_empty base b
  pairing := pruned_quotient_pairing base hbb
  union := pruned_quotient_union base hbb
  powerset := pruned_quotient_powerset base hbb
  infinity := pruned_quotient_infinity base hbb
  separation := pruned_quotient_separation base hbb
  collection := pruned_quotient_collection base hbb

theorem pruned_quotient_replacement (base : BaseCollection s) {b : U} (hbb : s b b) :
    Replacement (prunedMember base b) :=
  collection_separation_replacement _ (pruned_quotient_collection base hbb)
    (pruned_quotient_separation base hbb)

#print axioms pruned_quotient_base
#print axioms pruned_quotient_replacement
end FullBridge
