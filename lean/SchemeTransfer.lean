import Translation

namespace FullBridge
universe u v
variable {U : Type u} {V : Type v}
variable {s : U → U → Prop} {t : V → V → Prop} {q : U → V}

def ExactMembers (s : U → U → Prop) (t : V → V → Prop) (q : U → V) : Prop :=
  ∀ a y, t y (q a) ↔ ∃ x, s x a ∧ q x = y

theorem lift_env (onto : ∀ y, ∃ x, q x = y) {n} (e : Fin n → V) :
    ∃ d : Fin n → U, (fun i => q (d i)) = e := by
  classical
  refine ⟨fun i => Classical.choose (onto (e i)), ?_⟩
  funext i
  exact Classical.choose_spec (onto (e i))

theorem separation_transfer (I : AtomicInterpretation s t q)
    (onto : ∀ y, ∃ x, q x = y) (hm : ExactMembers s t q)
    (hs : Separation s) : Separation t := by
  intro n p e a
  obtain ⟨a₀, rfl⟩ := onto a
  obtain ⟨d, hd⟩ := lift_env onto e
  let p₀ := Formula.translate I.equalFormula I.memberFormula p
  have ht : ∀ x, Eval s p₀ (cons x d) ↔ Eval t p (cons (q x) e) := by
    intro x
    simpa only [cons_map, hd] using eval_translate I onto p (cons x d)
  obtain ⟨b, hb⟩ := hs n p₀ d a₀
  refine ⟨q b, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (hm b y).mp hy
    obtain ⟨hxa, hxp⟩ := (hb x).mp hx
    exact ⟨(hm a₀ (q x)).mpr ⟨x, hxa, rfl⟩, (ht x).mp hxp⟩
  · rintro ⟨hya, hyp⟩
    obtain ⟨x, hxa, rfl⟩ := (hm a₀ y).mp hya
    exact (hm b (q x)).mpr ⟨x, (hb x).mpr ⟨hxa, (ht x).mpr hyp⟩, rfl⟩

theorem collection_transfer (I : AtomicInterpretation s t q)
    (onto : ∀ y, ∃ x, q x = y) (hm : ExactMembers s t q)
    (hc : Collection s) : Collection t := by
  intro n p e a htotal
  obtain ⟨a₀, rfl⟩ := onto a
  obtain ⟨d, hd⟩ := lift_env onto e
  let p₀ := Formula.translate I.equalFormula I.memberFormula p
  have ht : ∀ x y, Eval s p₀ (cons y (cons x d)) ↔
      Eval t p (cons (q y) (cons (q x) e)) := by
    intro x y
    simpa only [cons_map, hd] using eval_translate I onto p (cons y (cons x d))
  have hsTotal : ∀ x, s x a₀ → ∃ y, Eval s p₀ (cons y (cons x d)) := by
    intro x hx
    obtain ⟨y, hy⟩ := htotal (q x) ((hm a₀ (q x)).mpr ⟨x, hx, rfl⟩)
    obtain ⟨z, rfl⟩ := onto y
    exact ⟨z, (ht x z).mpr hy⟩
  obtain ⟨b, hb⟩ := hc n p₀ d a₀ hsTotal
  refine ⟨q b, ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := (hm a₀ x).mp hx
  obtain ⟨w, hw, hp⟩ := hb z hz
  exact ⟨q w, (hm b (q w)).mpr ⟨w, hw, rfl⟩, (ht z w).mp hp⟩

theorem replacement_transfer (I : AtomicInterpretation s t q)
    (onto : ∀ y, ∃ x, q x = y) (hm : ExactMembers s t q)
    (hc : Collection s) (hs : Separation s) : Replacement t :=
  collection_separation_replacement t
    (collection_transfer I onto hm hc) (separation_transfer I onto hm hs)

#print axioms separation_transfer
#print axioms collection_transfer
#print axioms replacement_transfer
end FullBridge
