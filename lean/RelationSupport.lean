import BoundedBisimUpTo
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def relationSupportFormula : Formula 2 :=
  .ex ((relatedFormula 2 1 0).disj (relatedFormula 2 0 1))

theorem eval_relationSupportFormula (x r : U) :
    Eval s relationSupportFormula (cons x (cons r Fin.elim0)) ↔
      ∃ y, CodedRelation s r x y ∨ CodedRelation s r y x := by
  simp only [relationSupportFormula, Eval, eval_disj, eval_relatedFormula]
  rfl

theorem relation_support_exists (base : BaseCollection s) (r : U) :
    ∃ d, ∀ x, s x d ↔ ∃ y, CodedRelation s r x y ∨ CodedRelation s r y x := by
  obtain ⟨b, hb⟩ := codedRelation_component_bound base.union r
  obtain ⟨d, hd⟩ := base.separation 1 relationSupportFormula (cons r Fin.elim0) b
  refine ⟨d, ?_⟩
  intro x
  have h := hd x
  rw [eval_relationSupportFormula] at h
  constructor
  · intro hx
    exact (h.mp hx).2
  · rintro ⟨y, hxy⟩
    have hx := hxy.elim (fun hh => (hb x y hh).1) (fun hh => (hb y x hh).2)
    exact h.mpr ⟨hx, y, hxy⟩

theorem bisimulation_support_transitive {r d : U}
    (hr : Bisimulation s (CodedRelation s r))
    (hd : ∀ x, s x d ↔ ∃ y, CodedRelation s r x y ∨ CodedRelation s r y x) :
    TransitiveCode s d := by
  intro x hx z hz
  obtain ⟨y, hxy⟩ := (hd x).mp hx
  rcases hxy with hxy | hyx
  · obtain ⟨w, _, hzw⟩ := (hr x y hxy).1 z hz
    exact (hd z).mpr ⟨w, Or.inl hzw⟩
  · obtain ⟨w, _, hwz⟩ := (hr y x hyx).2 z hz
    exact (hd z).mpr ⟨w, Or.inr hwz⟩

theorem bounded_augmented_extension (base : BaseCollection s) (d k : U)
    (hk : Bisimulation s (WithIdentity (CodedRelation s k))) :
    ∃ D m, Subset s d D ∧ MaxAugmentedCode s D m ∧
      ∀ x y, WithIdentity (CodedRelation s k) x y → WithIdentity (CodedRelation s m) x y := by
  obtain ⟨b, hb⟩ := codedRelation_component_bound base.union k
  obtain ⟨D, hD⟩ := binary_union_exists base.pairing base.union d b
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base
    (relatedFormula (n := 3) 2 1 0) (cons k Fin.elim0) D
  have hi : ∀ x y, CodedRelation s r x y ↔ CodedRelation s k x y := by
    intro x y
    have h := hr x y
    rw [eval_relatedFormula] at h
    constructor
    · intro hh
      exact (h.mp hh).2.2
    · intro hh
      have hbd := hb x y hh
      exact h.mpr ⟨(hD x).mpr (Or.inr hbd.1), (hD y).mpr (Or.inr hbd.2), hh⟩
  have haug : ∀ x y, WithIdentity (CodedRelation s k) x y ↔ WithIdentity (CodedRelation s r) x y := by
    intro x y
    exact or_congr Iff.rfl (hi x y).symm
  have hrB := bisimulation_congr haug hk
  obtain ⟨m, hm⟩ := maximal_augmented_exists base D
  refine ⟨D, m, (fun x hx => (hD x).mpr (Or.inl hx)), hm, ?_⟩
  intro x y hxy
  exact hxy.elim Or.inl (fun h => Or.inr (hm.2.2 r hrG hrB x y ((hi x y).mpr h)))

#print axioms bounded_augmented_extension
end FullBridge
