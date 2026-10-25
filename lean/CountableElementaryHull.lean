import ModelMaps
import FormulaEnumeration
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- The ambient first-order existential witnesses needed for an elementary
    substructure. This quantifies over the actual finite external syntax. -/
def ExistentialWitnessClosed (s : U → U → Prop) (D : U → Prop) : Prop :=
  ∀ {n} (p : Formula (n + 1)) (e : Fin n → {x // D x}),
    (∃ x, Eval s p (cons x (fun i => (e i).val))) →
    ∃ y : {x // D x}, Eval s p (cons y.val (fun i => (e i).val))

theorem subtype_cons_environment {D : U → Prop} {n}
    (x : {x // D x}) (e : Fin n → {x // D x}) :
    (fun i => (cons x e i).val) = cons x.val (fun i => (e i).val) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Tarski–Vaught for this project's complete finite first-order syntax,
    including universal quantifiers. -/
theorem existential_witness_closed_elementary {D : U → Prop}
    (hD : ExistentialWitnessClosed s D) :
    ElementaryMap (fun x y : {x // D x} => s x.val y.val) s Subtype.val := by
  classical
  intro n p
  induction p with
  | equal i j =>
      intro e
      constructor
      · exact congrArg Subtype.val
      · exact Subtype.ext
  | member i j => intro e; rfl
  | bottom => intro e; rfl
  | conj p q hp hq =>
      intro e
      exact and_congr (hp e) (hq e)
  | impl p q hp hq =>
      intro e
      exact imp_congr (hp e) (hq e)
  | ex p hp =>
      intro e
      constructor
      · intro ⟨x, hx⟩
        refine ⟨x.val, ?_⟩
        simpa only [subtype_cons_environment] using (hp (cons x e)).mp hx
      · intro h
        obtain ⟨x, hx⟩ := hD p e h
        refine ⟨x, (hp (cons x e)).mpr ?_⟩
        simpa only [subtype_cons_environment] using hx
  | all p hp =>
      intro e
      constructor
      · intro h x
        apply Classical.byContradiction
        intro hx
        obtain ⟨y, hy⟩ := hD (.impl p .bottom) e ⟨x, hx⟩
        apply hy
        simpa only [subtype_cons_environment] using (hp (cons y e)).mp (h y)
      · intro h y
        apply (hp (cons y e)).mpr
        simpa only [subtype_cons_environment] using h y.val

/-- A selected external witness, with a harmless default when none exists. -/
noncomputable def formulaWitness (s : U → U → Prop) (fallback : U) {n}
    (p : Formula (n + 1)) (e : Fin n → U) : U := by
  classical
  exact if h : ∃ x, Eval s p (cons x e) then Classical.choose h else fallback

theorem formulaWitness_spec (s : U → U → Prop) (fallback : U) {n}
    (p : Formula (n + 1)) (e : Fin n → U)
    (h : ∃ x, Eval s p (cons x e)) :
    Eval s p (cons (formulaWitness s fallback p e) e) := by
  classical
  simp only [formulaWitness, dif_pos h]
  exact Classical.choose_spec h

/-- One countable closure step. The zero tag retains the preceding range;
    a successor tag records the arity, formula, and finite tuple of indices. -/
noncomputable def elementaryHullNext (s : U → U → Prop) (fallback : U)
    (e : Nat → U) (k : Nat) : U :=
  match natPairDecode k with
  | (0, j) => e j
  | (n + 1, j) =>
      let z := natPairDecode j
      formulaWitness s fallback (formulaEnumeration (n + 1) z.1)
        (fun i => e (natTupleEnumeration n z.2 i))

theorem elementaryHullNext_retains (s : U → U → Prop) (fallback : U)
    (e : Nat → U) (j : Nat) :
    elementaryHullNext s fallback e (natPairCode 0 j) = e j := by
  simp only [elementaryHullNext, natPairDecode_code]

theorem elementaryHullNext_witness (s : U → U → Prop) (fallback : U)
    (e : Nat → U) {n} (p : Formula (n + 1)) (v : Fin n → Nat)
    (h : ∃ x, Eval s p (cons x (fun i => e (v i)))) :
    ∃ j, Eval s p (cons (elementaryHullNext s fallback e j) (fun i => e (v i))) := by
  obtain ⟨a, ha⟩ := formulaEnumeration_onto (n + 1) p
  obtain ⟨b, hb⟩ := natTupleEnumeration_onto n v
  refine ⟨natPairCode (n + 1) (natPairCode a b), ?_⟩
  simpa only [elementaryHullNext, natPairDecode_code, ha, hb] using
    formulaWitness_spec s fallback p (fun i => e (v i)) h

/-- An external sequence of countable sets, starting with all prescribed seeds. -/
noncomputable def elementaryHullStage (s : U → U → Prop) (seed : Nat → U) :
    Nat → Nat → U
  | 0 => seed
  | k + 1 => elementaryHullNext s (seed 0) (elementaryHullStage s seed k)

/-- The carrier is the external countable union, not a set represented inside U. -/
def ElementaryHullCarrier (s : U → U → Prop) (seed : Nat → U) (x : U) : Prop :=
  ∃ k j, elementaryHullStage s seed k j = x

theorem elementaryHullStage_extends (s : U → U → Prop) (seed : Nat → U)
    (m k i : Nat) :
    ∃ j, elementaryHullStage s seed (m + k) j = elementaryHullStage s seed m i := by
  induction k with
  | zero => exact ⟨i, rfl⟩
  | succ k hk =>
      obtain ⟨j, hj⟩ := hk
      refine ⟨natPairCode 0 j, ?_⟩
      change elementaryHullNext s (seed 0) (elementaryHullStage s seed (m + k))
        (natPairCode 0 j) = elementaryHullStage s seed m i
      rw [elementaryHullNext_retains, hj]

/-- Finitely many members of the union already occur in one common stage. -/
theorem elementaryHull_common_stage (s : U → U → Prop) (seed : Nat → U)
    {n} (e : Fin n → U) (he : ∀ i, ElementaryHullCarrier s seed (e i)) :
    ∃ k, ∀ i, ∃ j, elementaryHullStage s seed k j = e i := by
  induction n with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n hn =>
      obtain ⟨a, ia, ha⟩ := he 0
      obtain ⟨b, hb⟩ := hn (fun i => e i.succ) (fun i => he i.succ)
      refine ⟨a + b, ?_⟩
      intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · obtain ⟨j, hj⟩ := elementaryHullStage_extends s seed a b ia
        exact ⟨j, hj.trans ha⟩
      · obtain ⟨ik, hik⟩ := hb k
        obtain ⟨j, hj⟩ := elementaryHullStage_extends s seed b a ik
        refine ⟨j, ?_⟩
        rw [Nat.add_comm] at hj
        exact hj.trans hik

/-- The closure includes a witness for every existential formula with parameters
    from the eventual union. -/
theorem elementaryHull_witness_closed (s : U → U → Prop) (seed : Nat → U) :
    ExistentialWitnessClosed s (ElementaryHullCarrier s seed) := by
  classical
  intro n p e h
  obtain ⟨k, hk⟩ := elementaryHull_common_stage s seed
    (fun i => (e i).val) (fun i => (e i).property)
  let v : Fin n → Nat := fun i => Classical.choose (hk i)
  have hv : (fun i => elementaryHullStage s seed k (v i)) =
      (fun i => (e i).val) := by
    funext i
    exact Classical.choose_spec (hk i)
  have hw : ∃ x, Eval s p (cons x (fun i => elementaryHullStage s seed k (v i))) := by
    rw [hv]
    exact h
  obtain ⟨j, hj⟩ := elementaryHullNext_witness s (seed 0)
    (elementaryHullStage s seed k) p v hw
  refine ⟨⟨elementaryHullStage s seed (k + 1) j, k + 1, j, rfl⟩, ?_⟩
  change Eval s p (cons (elementaryHullNext s (seed 0)
    (elementaryHullStage s seed k) j) (fun i => (e i).val))
  rw [hv] at hj
  exact hj

/-- An explicit enumeration of the hull's subtype, using the paired stage and
    local index. Neither the ambient relation nor a model axiom is required. -/
noncomputable def elementaryHullEnumeration (s : U → U → Prop) (seed : Nat → U)
    (k : Nat) : {x // ElementaryHullCarrier s seed x} :=
  let z := natPairDecode k
  ⟨elementaryHullStage s seed z.1 z.2, z.1, z.2, rfl⟩

theorem elementaryHullEnumeration_onto (s : U → U → Prop) (seed : Nat → U)
    (x : {x // ElementaryHullCarrier s seed x}) :
    ∃ k, elementaryHullEnumeration s seed k = x := by
  obtain ⟨a, b, h⟩ := x.property
  refine ⟨natPairCode a b, ?_⟩
  apply Subtype.ext
  simpa only [elementaryHullEnumeration, natPairDecode_code] using h

/-- Downward Löwenheim–Skolem for an arbitrary binary relation in the project's
    finite first-order language, with any prescribed external countable seeds. -/
theorem countable_elementary_hull (s : U → U → Prop) (seed : Nat → U) :
    ∃ (D : U → Prop) (enum : Nat → {x // D x}),
      (∀ k, D (seed k)) ∧ (∀ x, ∃ k, enum k = x) ∧
      ElementaryMap (fun x y : {x // D x} => s x.val y.val) s Subtype.val := by
  refine ⟨ElementaryHullCarrier s seed, elementaryHullEnumeration s seed, ?_,
    elementaryHullEnumeration_onto s seed, ?_⟩
  · intro k
    exact ⟨0, k, rfl⟩
  · exact existential_witness_closed_elementary (elementaryHull_witness_closed s seed)

/-- Point-seeded form: the ambient type need only supply one actual element. -/
theorem countable_elementary_hull_of_seed (s : U → U → Prop) (seed : U) :
    ∃ (D : U → Prop) (enum : Nat → {x // D x}),
      D seed ∧ (∀ x, ∃ k, enum k = x) ∧
      ElementaryMap (fun x y : {x // D x} => s x.val y.val) s Subtype.val := by
  obtain ⟨D, enum, hseed, honto, helem⟩ := countable_elementary_hull s (fun _ => seed)
  exact ⟨D, enum, hseed 0, honto, helem⟩

#print axioms countable_elementary_hull
#print axioms countable_elementary_hull_of_seed
end FullBridge
