import InternalComposition

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def WithIdentity (R : U → U → Prop) (x y : U) : Prop := x = y ∨ R x y

def InternalBehavior (s : U → U → Prop) (a b : U) : Prop :=
  ∃ r, Bisimulation s (WithIdentity (CodedRelation s r)) ∧
    WithIdentity (CodedRelation s r) a b

def augmentedRelatedFormula {n} (r x y : Fin n) : Formula n :=
  (Formula.equal x y).disj (relatedFormula r x y)

theorem eval_augmentedRelatedFormula (s : U → U → Prop) {n}
    (r x y : Fin n) (e : Fin n → U) :
    Eval s (augmentedRelatedFormula r x y) e ↔
      WithIdentity (CodedRelation s (e r)) (e x) (e y) := by
  simp only [augmentedRelatedFormula, eval_disj, Eval, eval_relatedFormula, WithIdentity]

def augmentedBisimFormula {n} (r : Fin n) : Formula n :=
  .all (.all (.impl (augmentedRelatedFormula r.succ.succ 1 0)
    (.conj
      (.all (.impl (.member 0 2) (.ex (.conj (.member 0 2)
        (augmentedRelatedFormula r.succ.succ.succ.succ 1 0)))))
      (.all (.impl (.member 0 1) (.ex (.conj (.member 0 3)
        (augmentedRelatedFormula r.succ.succ.succ.succ 0 1))))))))

theorem eval_augmentedBisimFormula (s : U → U → Prop) {n}
    (r : Fin n) (e : Fin n → U) :
    Eval s (augmentedBisimFormula r) e ↔ Bisimulation s (WithIdentity (CodedRelation s (e r))) := by
  simp only [augmentedBisimFormula, Eval, eval_augmentedRelatedFormula, cons_zero, cons_succ,
    Bisimulation]
  rfl

def internalBehaviorFormula {n} (x y : Fin n) : Formula n :=
  .ex (.conj (augmentedBisimFormula 0) (augmentedRelatedFormula 0 x.succ y.succ))

theorem eval_internalBehaviorFormula (s : U → U → Prop) {n}
    (x y : Fin n) (e : Fin n → U) :
    Eval s (internalBehaviorFormula x y) e ↔ InternalBehavior s (e x) (e y) := by
  simp only [internalBehaviorFormula, Eval, eval_augmentedBisimFormula,
    eval_augmentedRelatedFormula, cons_zero, cons_succ, InternalBehavior]

theorem internalBehavior_refl (hEmpty : Empty s) (a : U) : InternalBehavior s a a := by
  obtain ⟨r, hr⟩ := hEmpty
  refine ⟨r, ?_, Or.inl rfl⟩
  intro x y h
  rcases h with rfl | ⟨p, hpr, _⟩
  · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
  · exact False.elim (hr p hpr)

theorem bisimulation_congr {R T : U → U → Prop}
    (h : ∀ x y, R x y ↔ T x y) (hR : Bisimulation s R) : Bisimulation s T := by
  intro x y hxy
  constructor
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := (hR x y ((h x y).mpr hxy)).1 z hz
    exact ⟨w, hw, (h z w).mp hzw⟩
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := (hR x y ((h x y).mpr hxy)).2 w hw
    exact ⟨z, hz, (h z w).mp hzw⟩

theorem bisimulation_comp {R T : U → U → Prop}
    (hR : Bisimulation s R) (hT : Bisimulation s T) :
    Bisimulation s (fun x z => ∃ y, R x y ∧ T y z) := by
  intro x z hxz
  obtain ⟨y, hxy, hyz⟩ := hxz
  constructor
  · intro x' hx'
    obtain ⟨y', hy', hr⟩ := (hR x y hxy).1 x' hx'
    obtain ⟨z', hz', ht⟩ := (hT y z hyz).1 y' hy'
    exact ⟨z', hz', y', hr, ht⟩
  · intro z' hz'
    obtain ⟨y', hy', ht⟩ := (hT y z hyz).2 z' hz'
    obtain ⟨x', hx', hr⟩ := (hR x y hxy).2 y' hy'
    exact ⟨x', hx', y', hr, ht⟩

theorem internalBehavior_symm (hp : Pairing s) (hu : Union s)
    (hpow : PowerSet s) (hsep : Separation s) {a b : U}
    (h : InternalBehavior s a b) : InternalBehavior s b a := by
  obtain ⟨r, hr, hab⟩ := h
  obtain ⟨v, hv⟩ := codedRelation_inverse hp hu hpow hsep r
  have hi : ∀ x y, WithIdentity (CodedRelation s r) y x ↔ WithIdentity (CodedRelation s v) x y := by
    intro x y
    constructor
    · intro h
      exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((hv x y).mpr h))
    · intro h
      exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((hv x y).mp h))
  refine ⟨v, ?_, (hi b a).mp hab⟩
  apply bisimulation_congr hi
  intro x y hxy
  exact ⟨(hr y x hxy).2, (hr y x hxy).1⟩

theorem internalBehavior_trans (hp : Pairing s) (hu : Union s)
    (hpow : PowerSet s) (hsep : Separation s) {a b c : U}
    (h : InternalBehavior s a b) (k : InternalBehavior s b c) : InternalBehavior s a c := by
  obtain ⟨r, hr, hab⟩ := h
  obtain ⟨t, ht, hbc⟩ := k
  obtain ⟨comp, hc⟩ := codedRelation_composition hp hu hpow hsep r t
  obtain ⟨un, hn⟩ := codedRelation_union hp hu r t
  obtain ⟨v, hv⟩ := codedRelation_union hp hu un comp
  have hi : ∀ x z, (∃ y, WithIdentity (CodedRelation s r) x y ∧
      WithIdentity (CodedRelation s t) y z) ↔ WithIdentity (CodedRelation s v) x z := by
    intro x z
    constructor
    · rintro ⟨y, hxy, hyz⟩
      rcases hxy with rfl | hxy
      · rcases hyz with rfl | hyz
        · exact Or.inl rfl
        · exact Or.inr ((hv x z).mpr (Or.inl ((hn x z).mpr (Or.inr hyz))))
      · rcases hyz with rfl | hyz
        · exact Or.inr ((hv x y).mpr (Or.inl ((hn x y).mpr (Or.inl hxy))))
        · exact Or.inr ((hv x z).mpr (Or.inr ((hc x z).mpr ⟨y, hxy, hyz⟩)))
    · intro h
      rcases h with rfl | hxz
      · exact ⟨x, Or.inl rfl, Or.inl rfl⟩
      · rcases (hv x z).mp hxz with hun | hcomp
        · rcases (hn x z).mp hun with hR | hT
          · exact ⟨z, Or.inr hR, Or.inl rfl⟩
          · exact ⟨x, Or.inl rfl, Or.inr hT⟩
        · obtain ⟨y, hR, hT⟩ := (hc x z).mp hcomp
          exact ⟨y, Or.inr hR, Or.inr hT⟩
  exact ⟨v, bisimulation_congr hi (bisimulation_comp hr ht), (hi a c).mp ⟨b, hab, hbc⟩⟩

theorem internalBehavior_bisimulation (s : U → U → Prop) :
    Bisimulation s (InternalBehavior s) := by
  intro a b h
  obtain ⟨r, hr, hab⟩ := h
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (hr a b hab).1 x hx
    exact ⟨y, hy, r, hr, hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := (hr a b hab).2 y hy
    exact ⟨x, hx, r, hr, hxy⟩

theorem internalBehavior_implies_behavior {a b : U}
    (h : InternalBehavior s a b) : Behavior s a b := by
  obtain ⟨r, hr, hab⟩ := h
  exact ⟨WithIdentity (CodedRelation s r), hr, hab⟩

#print axioms internalBehavior_trans
end FullBridge
