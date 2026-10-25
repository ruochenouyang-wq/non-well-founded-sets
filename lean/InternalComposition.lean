import InternalInverse

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem binary_union_exists (hp : Pairing s) (hu : Union s) (a b : U) :
    ∃ d, ∀ x, s x d ↔ s x a ∨ s x b := by
  obtain ⟨p, hp⟩ := hp a b
  obtain ⟨d, hd⟩ := hu p
  refine ⟨d, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (hd x).mp hx
    rcases (hp y).mp hy with rfl | rfl
    · exact Or.inl hxy
    · exact Or.inr hxy
  · intro hx
    rcases hx with ha | hb
    · exact (hd x).mpr ⟨a, (hp a).mpr (Or.inl rfl), ha⟩
    · exact (hd x).mpr ⟨b, (hp b).mpr (Or.inr rfl), hb⟩

theorem codedRelation_union (hp : Pairing s) (hu : Union s) (r t : U) :
    ∃ v, ∀ x y, CodedRelation s v x y ↔ CodedRelation s r x y ∨ CodedRelation s t x y := by
  obtain ⟨v, hv⟩ := binary_union_exists hp hu r t
  refine ⟨v, ?_⟩
  intro x y
  constructor
  · rintro ⟨p, hpv, hpair⟩
    rcases (hv p).mp hpv with hpr | hpt
    · exact Or.inl ⟨p, hpr, hpair⟩
    · exact Or.inr ⟨p, hpt, hpair⟩
  · intro h
    rcases h with ⟨p, hpr, hpair⟩ | ⟨p, hpt, hpair⟩
    · exact ⟨p, (hv p).mpr (Or.inl hpr), hpair⟩
    · exact ⟨p, (hv p).mpr (Or.inr hpt), hpair⟩

def compositionFormula : Formula 4 :=
  .ex (.conj (relatedFormula 3 2 0) (relatedFormula 4 0 1))

theorem eval_compositionFormula (x y r t : U) :
    Eval s compositionFormula (cons y (cons x (cons r (cons t Fin.elim0)))) ↔
      ∃ z, CodedRelation s r x z ∧ CodedRelation s t z y := by
  simp only [compositionFormula, Eval, eval_relatedFormula]
  rfl

theorem codedRelation_composition (hp : Pairing s) (hu : Union s)
    (hpow : PowerSet s) (hsep : Separation s) (r t : U) :
    ∃ v, ∀ x y, CodedRelation s v x y ↔
      ∃ z, CodedRelation s r x z ∧ CodedRelation s t z y := by
  obtain ⟨d₁, h₁⟩ := codedRelation_component_bound hu r
  obtain ⟨d₂, h₂⟩ := codedRelation_component_bound hu t
  obtain ⟨d, hd⟩ := binary_union_exists hp hu d₁ d₂
  obtain ⟨v, hv⟩ := bounded_relation_comprehension hp hpow hsep compositionFormula
    (cons r (cons t Fin.elim0)) d
  refine ⟨v, ?_⟩
  intro x y
  have hh := hv x y
  rw [eval_compositionFormula] at hh
  constructor
  · intro h
    exact ((hh.mp h).2).2
  · rintro ⟨z, hxz, hzy⟩
    exact hh.mpr ⟨(hd x).mpr (Or.inl (h₁ x z hxz).1),
      (hd y).mpr (Or.inr (h₂ z y hzy).2), z, hxz, hzy⟩

theorem codedBehavior_trans (hp : Pairing s) (hu : Union s)
    (hpow : PowerSet s) (hsep : Separation s) {a b c : U}
    (hab : CodedBehavior s a b) (hbc : CodedBehavior s b c) : CodedBehavior s a c := by
  obtain ⟨r, hr, hab⟩ := hab
  obtain ⟨t, ht, hbc⟩ := hbc
  obtain ⟨v, hv⟩ := codedRelation_composition hp hu hpow hsep r t
  refine ⟨v, ?_, (hv a c).mpr ⟨b, hab, hbc⟩⟩
  intro x z hxz
  obtain ⟨y, hxy, hyz⟩ := (hv x z).mp hxz
  constructor
  · intro x' hx'
    obtain ⟨y', hy', hr'⟩ := (hr x y hxy).1 x' hx'
    obtain ⟨z', hz', ht'⟩ := (ht y z hyz).1 y' hy'
    exact ⟨z', hz', (hv x' z').mpr ⟨y', hr', ht'⟩⟩
  · intro z' hz'
    obtain ⟨y', hy', ht'⟩ := (ht y z hyz).2 z' hz'
    obtain ⟨x', hx', hr'⟩ := (hr x y hxy).2 y' hy'
    exact ⟨x', hx', (hv x' z').mpr ⟨y', hr', ht'⟩⟩

#print axioms codedBehavior_trans
end FullBridge
