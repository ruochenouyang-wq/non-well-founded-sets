import SchemeTransfer

namespace FullBridge
universe u v
variable {U : Type u} {V : Type v}
variable {s : U → U → Prop} {t : V → V → Prop} {q : U → V}

def Extensional (s : U → U → Prop) : Prop :=
  ∀ a b, (∀ x, s x a ↔ s x b) → a = b
def Empty (s : U → U → Prop) : Prop := ∃ a, ∀ x, ¬s x a
def Pairing (s : U → U → Prop) : Prop :=
  ∀ a b, ∃ c, ∀ x, s x c ↔ x = a ∨ x = b
def Union (s : U → U → Prop) : Prop :=
  ∀ a, ∃ b, ∀ x, s x b ↔ ∃ y, s y a ∧ s x y
def Subset (s : U → U → Prop) (a b : U) : Prop := ∀ x, s x a → s x b
def PowerSet (s : U → U → Prop) : Prop :=
  ∀ a, ∃ b, ∀ x, s x b ↔ Subset s x a

theorem empty_transfer (hm : ExactMembers s t q) (h : Empty s) : Empty t := by
  obtain ⟨a, ha⟩ := h
  refine ⟨q a, ?_⟩
  intro y hy
  obtain ⟨x, hx, _⟩ := (hm a y).mp hy
  exact ha x hx

theorem pairing_transfer (onto : ∀ y, ∃ x, q x = y)
    (hm : ExactMembers s t q) (h : Pairing s) : Pairing t := by
  intro a b
  obtain ⟨a₀, rfl⟩ := onto a
  obtain ⟨b₀, rfl⟩ := onto b
  obtain ⟨c, hc⟩ := h a₀ b₀
  refine ⟨q c, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hm c y).mp hy
    rcases (hc x).mp hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hy
    rcases hy with rfl | rfl
    · exact (hm c (q a₀)).mpr ⟨a₀, (hc a₀).mpr (Or.inl rfl), rfl⟩
    · exact (hm c (q b₀)).mpr ⟨b₀, (hc b₀).mpr (Or.inr rfl), rfl⟩

theorem union_transfer (onto : ∀ y, ∃ x, q x = y)
    (hm : ExactMembers s t q) (h : Union s) : Union t := by
  intro a
  obtain ⟨a₀, rfl⟩ := onto a
  obtain ⟨b, hb⟩ := h a₀
  refine ⟨q b, ?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := (hm b x).mp hx
    obtain ⟨y, hya, hzy⟩ := (hb z).mp hz
    exact ⟨q y, (hm a₀ (q y)).mpr ⟨y, hya, rfl⟩,
      (hm y (q z)).mpr ⟨z, hzy, rfl⟩⟩
  · rintro ⟨y, hya, hxy⟩
    obtain ⟨z, hza, rfl⟩ := (hm a₀ y).mp hya
    obtain ⟨w, hwz, rfl⟩ := (hm z x).mp hxy
    exact (hm b (q w)).mpr ⟨w, (hb w).mpr ⟨z, hza, hwz⟩, rfl⟩

theorem subset_forward (hm : ExactMembers s t q) {a b : U}
    (h : Subset s a b) : Subset t (q a) (q b) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (hm a y).mp hy
  exact (hm b (q x)).mpr ⟨x, h x hx, rfl⟩

/- A target subset is represented by a source subset of the specified source set,
   using definability and Separation; no powerset preservation is assumed. -/
theorem subset_representative (I : AtomicInterpretation s t q)
    (onto : ∀ y, ∃ x, q x = y) (hm : ExactMembers s t q)
    (hs : Separation s) (he : Extensional t) (a : U) (z : V)
    (hz : Subset t z (q a)) : ∃ b, Subset s b a ∧ q b = z := by
  obtain ⟨z₀, rfl⟩ := onto z
  obtain ⟨b, hb⟩ := hs 1 I.memberFormula (cons z₀ Fin.elim0) a
  have row : ∀ x, s x b ↔ s x a ∧ t (q x) (q z₀) := by
    intro x
    have hh : s x b ↔ s x a ∧ Eval s I.memberFormula (pairEnv x z₀) := hb x
    rw [I.member_correct] at hh
    exact hh
  refine ⟨b, fun x hx => ((row x).mp hx).1, he (q b) (q z₀) ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hm b y).mp hy
    exact ((row x).mp hx).2
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hm a y).mp (hz y hy)
    exact (hm b (q x)).mpr ⟨x, (row x).mpr ⟨hx, hy⟩, rfl⟩

theorem powerset_transfer (I : AtomicInterpretation s t q)
    (onto : ∀ y, ∃ x, q x = y) (hm : ExactMembers s t q)
    (hs : Separation s) (he : Extensional t) (hp : PowerSet s) : PowerSet t := by
  intro a
  obtain ⟨a₀, rfl⟩ := onto a
  obtain ⟨p, hpa⟩ := hp a₀
  refine ⟨q p, ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨b, hb, rfl⟩ := (hm p z).mp hz
    exact subset_forward hm ((hpa b).mp hb)
  · intro hz
    obtain ⟨b, hb, rfl⟩ := subset_representative I onto hm hs he a₀ z hz
    exact (hm p (q b)).mpr ⟨b, (hpa b).mpr hb, rfl⟩

#print axioms powerset_transfer
end FullBridge
