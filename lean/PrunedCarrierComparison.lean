import PrunedModelBridge
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The original excluded-set notation b subset x agrees with b member x
    when b is a self-singleton. -/
theorem selfSingleton_subset_iff {b x : U} (hb : SelfSingleton s b) :
    Subset s b x ↔ s b x := by
  constructor
  · intro h
    exact h b ((hb b).mpr rfl)
  · intro h y hy
    exact (hb y).mp hy ▸ h

abbrev RetainedCarrier (s : U → U → Prop) (b : U) := {x : U // ¬s b x}

def retainedPrunedSetoid (base : BaseCollection s) (b : U) : Setoid (RetainedCarrier s b) where
  r x y := DefinedLeastRelation s prunedMemberFormula (cons b Fin.elim0) x.val y.val
  iseqv := by
    have h := defined_least_equivalence base prunedMemberFormula (cons b Fin.elim0) (pruned_edges_are_members b)
    exact ⟨fun x => h.refl x.val, fun hxy => h.symm hxy, fun hxy hyz => h.trans hxy hyz⟩

/-- Restriction of the already constructed global equivalence. No independent
    source-class choice or alternative minimality definition is implicit here. -/
abbrev RetainedPrunedQuotient (base : BaseCollection s) (b : U) :=
  Quotient (retainedPrunedSetoid base b)

def retainedPrunedCode (base : BaseCollection s) (b : U) (x : RetainedCarrier s b) :
    RetainedPrunedQuotient base b := Quotient.mk _ x

def retainedPrunedMember (base : BaseCollection s) (b : U)
    (X A : RetainedPrunedQuotient base b) : Prop :=
  ∃ x a : RetainedCarrier s b,
    retainedPrunedCode base b x = X ∧ retainedPrunedCode base b a = A ∧ s x.val a.val

def retainedPrunedToFull (base : BaseCollection s) (b : U) :
    RetainedPrunedQuotient base b → PrunedQuotient base b :=
  Quotient.lift (fun x : RetainedCarrier s b => prunedCode base b x.val)
    (fun x y hxy => (least_global_code_eq base prunedMemberFormula (cons b Fin.elim0)
      (pruned_edges_are_members b) x.val y.val).mpr hxy)

theorem retained_pruned_to_full_code (base : BaseCollection s) (b : U) (x : RetainedCarrier s b) :
    retainedPrunedToFull base b (retainedPrunedCode base b x) = prunedCode base b x.val := rfl

theorem retained_pruned_to_full_injective (base : BaseCollection s) (b : U) :
    ∀ X Y, retainedPrunedToFull base b X = retainedPrunedToFull base b Y → X = Y := by
  intro X Y
  refine Quotient.inductionOn₂ X Y ?_
  intro x y hxy
  apply Quotient.sound
  exact (least_global_code_eq base prunedMemberFormula (cons b Fin.elim0)
    (pruned_edges_are_members b) x.val y.val).mp hxy

theorem retained_pruned_to_full_surjective (base : BaseCollection s) (b : U) :
    ∀ X, ∃ Y, retainedPrunedToFull base b Y = X := by
  intro X
  obtain ⟨x, hx, hq⟩ := pruned_good_representative base b X
  exact ⟨retainedPrunedCode base b ⟨x, hx⟩, hq⟩

theorem retained_pruned_to_full_members (base : BaseCollection s) (b : U)
    (X A : RetainedPrunedQuotient base b) :
    retainedPrunedMember base b X A ↔
      prunedMember base b (retainedPrunedToFull base b X) (retainedPrunedToFull base b A) := by
  refine Quotient.inductionOn A ?_
  intro a
  constructor
  · rintro ⟨x, c, hx, hc, hxc⟩
    have hqx := congrArg (retainedPrunedToFull base b) hx
    have hqc := congrArg (retainedPrunedToFull base b) hc
    exact ⟨x.val, c.val, hqx, hqc, c.property, x.property, hxc⟩
  · intro h
    obtain ⟨x, hax, hqx⟩ := (least_global_exact_members base prunedMemberFormula
      (cons b Fin.elim0) (pruned_edges_are_members b) a.val _).mp h
    let z : RetainedCarrier s b := ⟨x, hax.2.1⟩
    refine ⟨z, a, ?_, rfl, hax.2.2⟩
    apply retained_pruned_to_full_injective base b
    exact hqx

theorem retained_pruned_formula_semantics (base : BaseCollection s) (b : U) {n}
    (p : Formula n) (v : Fin n → RetainedPrunedQuotient base b) :
    Eval (retainedPrunedMember base b) p v ↔
      Eval (prunedMember base b) p (fun i => retainedPrunedToFull base b (v i)) := by
  apply eval_bijective_members
  · exact retained_pruned_to_full_injective base b
  · exact retained_pruned_to_full_surjective base b
  · exact retained_pruned_to_full_members base b

#print axioms retained_pruned_formula_semantics
end FullBridge
