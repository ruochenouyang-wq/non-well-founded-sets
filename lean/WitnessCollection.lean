import InternalQuotient

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem codedRelation_family_union (hu : Union s) (b : U) :
    ∃ r, ∀ x y, CodedRelation s r x y ↔ ∃ t, s t b ∧ CodedRelation s t x y := by
  obtain ⟨r, hr⟩ := hu b
  refine ⟨r, ?_⟩
  intro x y
  constructor
  · rintro ⟨p, hpr, hp⟩
    obtain ⟨t, htb, hpt⟩ := (hr p).mp hpr
    exact ⟨t, htb, p, hpt, hp⟩
  · rintro ⟨t, htb, p, hpt, hp⟩
    exact ⟨p, (hr p).mpr ⟨t, htb, hpt⟩, hp⟩

theorem augmented_family_union (hu : Union s) (b : U)
    (hb : ∀ t, s t b → Bisimulation s (WithIdentity (CodedRelation s t))) :
    ∃ r, Bisimulation s (WithIdentity (CodedRelation s r)) ∧
      ∀ t, s t b → ∀ x y, WithIdentity (CodedRelation s t) x y →
        WithIdentity (CodedRelation s r) x y := by
  obtain ⟨r, hr⟩ := codedRelation_family_union hu b
  have hin : ∀ t, s t b → ∀ x y, WithIdentity (CodedRelation s t) x y →
      WithIdentity (CodedRelation s r) x y := by
    intro t ht x y h
    exact h.elim Or.inl (fun h => Or.inr ((hr x y).mpr ⟨t, ht, h⟩))
  refine ⟨r, ?_, hin⟩
  intro x y h
  rcases h with rfl | h
  · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
  · obtain ⟨t, ht, hxy⟩ := (hr x y).mp h
    have hm := hb t ht x y (Or.inr hxy)
    constructor
    · intro z hz
      obtain ⟨w, hw, hzw⟩ := hm.1 z hz
      exact ⟨w, hw, hin t ht z w hzw⟩
    · intro w hw
      obtain ⟨z, hz, hzw⟩ := hm.2 w hw
      exact ⟨z, hz, hin t ht z w hzw⟩

def forwardWitnessFormula : Formula 3 :=
  .conj (augmentedBisimFormula 0)
    (.ex (.conj (.member 0 3) (augmentedRelatedFormula 1 2 0)))

theorem eval_forwardWitnessFormula (r x b : U) :
    Eval s forwardWitnessFormula (cons r (cons x (cons b Fin.elim0))) ↔
      Bisimulation s (WithIdentity (CodedRelation s r)) ∧
        ∃ y, s y b ∧ WithIdentity (CodedRelation s r) x y := by
  simp only [forwardWitnessFormula, Eval, eval_augmentedBisimFormula,
    eval_augmentedRelatedFormula]
  rfl

theorem collect_forward_witnesses (base : BaseCollection s) (a b : U)
    (h : ∀ x, s x a → ∃ y, s y b ∧ InternalBehavior s x y) :
    ∃ r, Bisimulation s (WithIdentity (CodedRelation s r)) ∧
      ∀ x, s x a → ∃ y, s y b ∧ WithIdentity (CodedRelation s r) x y := by
  have hall : ∀ x, s x a → ∃ r,
      Eval s forwardWitnessFormula (cons r (cons x (cons b Fin.elim0))) := by
    intro x hx
    obtain ⟨y, hy, r, hr, hxy⟩ := h x hx
    exact ⟨r, (eval_forwardWitnessFormula r x b).mpr ⟨hr, y, hy, hxy⟩⟩
  obtain ⟨c, hc⟩ := base.collection 1 forwardWitnessFormula (cons b Fin.elim0) a hall
  obtain ⟨d, hd⟩ := base.separation 0 (augmentedBisimFormula 0) Fin.elim0 c
  have hdgood : ∀ r, s r d → Bisimulation s (WithIdentity (CodedRelation s r)) := by
    intro r hr
    exact (eval_augmentedBisimFormula s 0 (cons r Fin.elim0)).mp ((hd r).mp hr).2
  obtain ⟨r, hr, hin⟩ := augmented_family_union base.union d hdgood
  refine ⟨r, hr, ?_⟩
  intro x hx
  obtain ⟨t, htc, ht⟩ := hc x hx
  obtain ⟨htbis, y, hy, htxy⟩ := (eval_forwardWitnessFormula t x b).mp ht
  have htd : s t d := (hd t).mpr ⟨htc,
    (eval_augmentedBisimFormula s 0 (cons t Fin.elim0)).mpr htbis⟩
  exact ⟨y, hy, hin t htd x y htxy⟩

#print axioms collect_forward_witnesses
end FullBridge
