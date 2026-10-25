import SetOperations

namespace FullBridge
universe u v
variable {U : Type u} {V : Type v}
variable {s : U → U → Prop} {t : V → V → Prop} {q : U → V}

def IsEmpty (s : U → U → Prop) (a : U) : Prop := ∀ x, ¬s x a
def IsSuccessor (s : U → U → Prop) (a b : U) : Prop :=
  ∀ x, s x b ↔ s x a ∨ x = a
def Infinity (s : U → U → Prop) : Prop :=
  ∃ i, (∃ e, s e i ∧ IsEmpty s e) ∧
    ∀ x, s x i → ∃ y, s y i ∧ IsSuccessor s x y

theorem isEmpty_forward (hm : ExactMembers s t q) {a : U}
    (ha : IsEmpty s a) : IsEmpty t (q a) := by
  intro y hy
  obtain ⟨x, hx, _⟩ := (hm a y).mp hy
  exact ha x hx

theorem successor_forward (hm : ExactMembers s t q) {a b : U}
    (hab : IsSuccessor s a b) : IsSuccessor t (q a) (q b) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hm b y).mp hy
    rcases (hab x).mp hx with hxa | rfl
    · exact Or.inl ((hm a (q x)).mpr ⟨x, hxa, rfl⟩)
    · exact Or.inr rfl
  · intro hy
    rcases hy with hya | rfl
    · obtain ⟨x, hx, rfl⟩ := (hm a y).mp hya
      exact (hm b (q x)).mpr ⟨x, (hab x).mpr (Or.inl hx), rfl⟩
    · exact (hm b (q a)).mpr ⟨a, (hab a).mpr (Or.inr rfl), rfl⟩

theorem infinity_transfer (hm : ExactMembers s t q) (hi : Infinity s) : Infinity t := by
  obtain ⟨i, ⟨e, hei, he⟩, hi⟩ := hi
  refine ⟨q i, ⟨q e, (hm i (q e)).mpr ⟨e, hei, rfl⟩, isEmpty_forward hm he⟩, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (hm i x).mp hx
  obtain ⟨b, hbi, hab⟩ := hi a ha
  exact ⟨q b, (hm i (q b)).mpr ⟨b, hbi, rfl⟩, successor_forward hm hab⟩

/- A first-order semantic base. No Choice, Foundation, AFA or BAFA is included. -/
structure BaseCollection (s : U → U → Prop) : Prop where
  extensional : Extensional s
  empty : Empty s
  pairing : Pairing s
  union : Union s
  powerset : PowerSet s
  infinity : Infinity s
  separation : Separation s
  collection : Collection s

theorem base_collection_transfer (I : AtomicInterpretation s t q)
    (onto : ∀ y, ∃ x, q x = y) (hm : ExactMembers s t q)
    (he : Extensional t) (base : BaseCollection s) : BaseCollection t where
  extensional := he
  empty := empty_transfer hm base.empty
  pairing := pairing_transfer onto hm base.pairing
  union := union_transfer onto hm base.union
  powerset := powerset_transfer I onto hm base.separation he base.powerset
  infinity := infinity_transfer hm base.infinity
  separation := separation_transfer I onto hm base.separation
  collection := collection_transfer I onto hm base.collection

#print axioms base_collection_transfer
end FullBridge
