import GlobalClosedPreservation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A fresh loop node attached to a fixed parameter object. -/
def taggedLoopEdgeFormula : Formula 5 :=
  (Formula.conj (.member 1 2) (.member 0 1)).disj
    (.conj (.equal 1 3) ((Formula.equal 0 3).disj (.equal 0 4)))

theorem fixed_tagged_loop_exists (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) (l : U) :
    ∃ v, ∀ w, s w v ↔ w = v ∨ w = l := by
  obtain ⟨t, ht, hlt⟩ := transitive_sets_cover base l
  obtain ⟨n, hnt⟩ := object_outside_set base t
  obtain ⟨one, hone⟩ := base.pairing n n
  obtain ⟨a, ha⟩ := binary_union_exists base.pairing base.union t one
  have hat : Subset s t a := fun x hx => (ha x).mpr (Or.inl hx)
  have hna : s n a := (ha n).mpr (Or.inr ((hone n).mpr (Or.inl rfl)))
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base taggedLoopEdgeFormula
    (cons t (cons n (cons l Fin.elim0))) a
  have he' : ∀ x y, CodedRelation s e x y ↔
      (s x t ∧ s y x) ∨ (x = n ∧ (y = n ∨ y = l)) := by
    intro x y
    have h := he x y
    simp only [taggedLoopEdgeFormula, eval_disj, Eval] at h
    refine h.trans ⟨fun h => h.2.2, ?_⟩
    intro hxy
    refine ⟨?_, ?_, hxy⟩
    · rcases hxy with h | ⟨rfl, _⟩
      · exact hat x h.1
      · exact hna
    · rcases hxy with h | ⟨_, h⟩
      · exact hat y (ht x h.1 y h.2)
      · rcases h with hyn | hyl
        · exact hyn.symm ▸ hna
        · exact hyl.symm ▸ hat l hlt
  have hend : EndExtensionCode s a e t := by
    refine ⟨hat, ?_⟩
    intro x hx y
    refine (he' x y).trans ⟨?_, fun h => Or.inl ⟨hx, h⟩⟩
    intro h
    rcases h with h | ⟨rfl, _⟩
    · exact h.2
    · exact False.elim (hnt hx)
  obtain ⟨f, hf, hfix⟩ := hF t ht a e heG hend
  obtain ⟨v, hnv, hv⟩ := hf.1.2 n hna
  have hll := hfix l hlt
  obtain ⟨vl, _, hvl⟩ := hf.1.2 l (hat l hlt)
  have hlUnique : ∀ w, CodedRelation s f l w → w = l :=
    fun w hw => (hvl w hw).trans (hvl l hll).symm
  refine ⟨v, ?_⟩
  intro w
  refine (hf.2 n hna v hnv w).trans ⟨?_, ?_⟩
  · rintro ⟨x, _, hnx, hxw⟩
    rcases (he' n x).mp hnx with h | ⟨_, h⟩
    · exact False.elim (hnt h.1)
    · rcases h with hxn | hxl
      · subst x
        exact Or.inl (hv w hxw)
      · subst x
        exact Or.inr (hlUnique w hxw)
  · intro h
    rcases h with hwv | hwl
    · subst w
      exact ⟨n, hna, (he' n n).mpr (Or.inr ⟨rfl, Or.inl rfl⟩), hnv⟩
    · subst w
      exact ⟨l, hat l hlt, (he' n l).mpr (Or.inr ⟨rfl, Or.inr rfl⟩), hll⟩

/-- Two different excluded labels, both distinct from the self-singleton b. -/
theorem distinct_excluded_labels (base : BaseCollection s) {b : U} (hb : SelfSingleton s b) :
    ∃ l m, s b l ∧ s b m ∧ l ≠ b ∧ m ≠ b ∧ l ≠ m := by
  obtain ⟨z, hz⟩ := base.empty
  have hzb : z ≠ b := by
    intro h
    exact hz b (h ▸ (hb b).mpr rfl)
  obtain ⟨one, hone⟩ := base.pairing z z
  have hzOne : s z one := (hone z).mpr (Or.inl rfl)
  have hzNeOne : z ≠ one := fun h => hz z (h.symm ▸ hzOne)
  have hOneB : one ≠ b := fun h => hzb ((hb z).mp (h ▸ hzOne))
  obtain ⟨l, hl⟩ := base.pairing b z
  obtain ⟨m, hm⟩ := base.pairing b one
  refine ⟨l, m, (hl b).mpr (Or.inl rfl), (hm b).mpr (Or.inl rfl), ?_, ?_, ?_⟩
  · intro h
    exact hzb ((hb z).mp (h ▸ (hl z).mpr (Or.inr rfl)))
  · intro h
    exact hOneB ((hb one).mp (h ▸ (hm one).mpr (Or.inr rfl)))
  · intro h
    have hzm := h ▸ (hl z).mpr (Or.inr rfl)
    exact ((hm z).mp hzm).elim hzb hzNeOne

/-- The label is deleted but the loop remains. -/
theorem pruned_tagged_loop_row {b l x : U} (hb : SelfSingleton s b)
    (hbl : s b l) (hlb : l ≠ b) (hx : ∀ w, s w x ↔ w = x ∨ w = l) :
    ¬s b x ∧ ∀ y, PrunedMember s b x y ↔ y = x := by
  have hxb : x ≠ b := by
    intro h
    exact hlb ((hb l).mp (h ▸ (hx l).mpr (Or.inr rfl)))
  have hbx : ¬s b x := fun h => ((hx b).mp h).elim (fun h => hxb h.symm) (fun h => hlb h.symm)
  refine ⟨hbx, ?_⟩
  intro y
  constructor
  · intro h
    rcases (hx y).mp h.2.2 with hxy | rfl
    · exact hxy
    · exact False.elim (h.2.1 hbl)
  · intro hyx
    subst y
    exact ⟨hbx, hbx, (hx x).mpr (Or.inl rfl)⟩

theorem pruned_loop_selfSingleton (base : BaseCollection s) {b x : U}
    (hx : ∀ y, PrunedMember s b x y ↔ y = x) :
    SelfSingleton (prunedMember base b) (prunedCode base b x) := by
  intro Y
  refine (least_global_exact_members base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) x Y).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy, hq⟩
    have hyx := (hx y).mp hy
    exact hyx ▸ hq.symm
  · rintro rfl
    exact ⟨x, (hx x).mpr rfl, rfl⟩

theorem pruned_distinct_selfSingletons (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b : U} (hb : SelfSingleton s b) :
    ∃ X Y, X ≠ Y ∧ SelfSingleton (prunedMember base b) X ∧ SelfSingleton (prunedMember base b) Y := by
  obtain ⟨l, m, hbl, hbm, hlb, hmb, hlm⟩ := distinct_excluded_labels base hb
  obtain ⟨x, hx⟩ := fixed_tagged_loop_exists base hF l
  obtain ⟨y, hy⟩ := fixed_tagged_loop_exists base hF m
  obtain ⟨hbx, hxrow⟩ := pruned_tagged_loop_row hb hbl hlb hx
  obtain ⟨hby, hyrow⟩ := pruned_tagged_loop_row hb hbm hmb hy
  have hxy : x ≠ y := by
    intro h
    have hly := h ▸ (hx l).mpr (Or.inr rfl)
    rcases (hy l).mp hly with hly | hlm'
    · exact hby (hly ▸ hbl)
    · exact hlm hlm'
  obtain ⟨c, hc⟩ := base.pairing x y
  have hclosed : ∀ u, s u c → ∀ v, FormulaEdges s prunedMemberFormula (cons b Fin.elim0) u v → s v c := by
    intro u hu v huv
    rcases (hc u).mp hu with hux | huy
    · subst u
      exact ((hxrow v).mp huv).symm ▸ (hc x).mpr (Or.inl rfl)
    · subst u
      exact ((hyrow v).mp huv).symm ▸ (hc y).mpr (Or.inr rfl)
  have hext : ∀ u, s u c → ∀ v, s v c →
      (∀ z, s z c → (FormulaEdges s prunedMemberFormula (cons b Fin.elim0) u z ↔
        FormulaEdges s prunedMemberFormula (cons b Fin.elim0) v z)) → u = v := by
    intro u hu v hv hrows
    have hurow : ∀ z, PrunedMember s b u z ↔ z = u := by
      rcases (hc u).mp hu with rfl | rfl
      · exact hxrow
      · exact hyrow
    have hvrow : ∀ z, PrunedMember s b v z ↔ z = v := by
      rcases (hc v).mp hv with rfl | rfl
      · exact hxrow
      · exact hyrow
    exact (hvrow u).mp ((hrows u hu).mp ((hurow u).mpr rfl))
  refine ⟨prunedCode base b x, prunedCode base b y, ?_,
    pruned_loop_selfSingleton base hxrow, pruned_loop_selfSingleton base hyrow⟩
  intro h
  exact hxy ((least_global_injective_on_closed base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) c hclosed hext ((hc x).mpr (Or.inl rfl)) ((hc y).mpr (Or.inr rfl))).mp h)

theorem pruned_quotient_not_afa (base : BaseCollection s)
    (hF : FixedGraphSolvabilityCode s) {b : U} (hb : SelfSingleton s b) :
    ¬AFACode (prunedMember base b) := by
  intro hA
  obtain ⟨X, Y, hne, hX, hY⟩ := pruned_distinct_selfSingletons base hF hb
  exact hne (afa_selfSingleton_unique (pruned_quotient_base base ((hb b).mpr rfl)) hA hX hY)

theorem afa_source_pruned_not_afa (base : BaseCollection s) (hA : AFACode s)
    {b : U} (hb : SelfSingleton s b) : ¬AFACode (prunedMember base b) :=
  pruned_quotient_not_afa base (afa_fixed_graph_solvability base hA) hb

#print axioms pruned_distinct_selfSingletons
#print axioms afa_source_pruned_not_afa
end FullBridge
