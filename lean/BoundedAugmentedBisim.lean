import DecorationTransfer
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def MaxAugmentedCode (s : U → U → Prop) (d m : U) : Prop :=
  GraphCode s d m ∧ Bisimulation s (WithIdentity (CodedRelation s m)) ∧
  ∀ r, GraphCode s d r → Bisimulation s (WithIdentity (CodedRelation s r)) →
    ∀ x y, CodedRelation s r x y → CodedRelation s m x y

def boundedAugmentedFormula : Formula 2 :=
  .conj (graphCodeFormula 1 0) (augmentedBisimFormula 0)

theorem eval_boundedAugmentedFormula (r d : U) :
    Eval s boundedAugmentedFormula (cons r (cons d Fin.elim0)) ↔
      GraphCode s d r ∧ Bisimulation s (WithIdentity (CodedRelation s r)) := by
  simp only [boundedAugmentedFormula, Eval, eval_graphCodeFormula, eval_augmentedBisimFormula]
  rfl

theorem maximal_augmented_exists (base : BaseCollection s) (d : U) :
    ∃ m, MaxAugmentedCode s d m := by
  obtain ⟨pd, hpd⟩ := base.powerset d
  obtain ⟨ppd, hppd⟩ := base.powerset pd
  obtain ⟨pppd, hpppd⟩ := base.powerset ppd
  obtain ⟨b, hb⟩ := base.separation 1 boundedAugmentedFormula (cons d Fin.elim0) pppd
  have hbiff : ∀ r, s r b ↔ Subset s r ppd ∧
      GraphCode s d r ∧ Bisimulation s (WithIdentity (CodedRelation s r)) := by
    intro r
    have h := hb r
    rw [hpppd, eval_boundedAugmentedFormula] at h
    exact h
  obtain ⟨m, hm⟩ := base.union b
  have hrel : ∀ x y, CodedRelation s m x y ↔ ∃ r, s r b ∧ CodedRelation s r x y := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨r, hr, hpr⟩ := (hm p).mp hp
      exact ⟨r, hr, p, hpr, hpxy⟩
    · rintro ⟨r, hr, p, hpr, hpxy⟩
      exact ⟨p, (hm p).mpr ⟨r, hr, hpr⟩, hpxy⟩
  have hin : ∀ r, s r b → ∀ x y, WithIdentity (CodedRelation s r) x y →
      WithIdentity (CodedRelation s m) x y := by
    intro r hr x y h
    exact h.elim Or.inl (fun hh => Or.inr ((hrel x y).mpr ⟨r, hr, hh⟩))
  refine ⟨m, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨r, hr, hpr⟩ := (hm p).mp hp
    exact ((hbiff r).mp hr).2.1 p hpr
  · intro x y hxy
    rcases hxy with rfl | hxy
    · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
    · obtain ⟨r, hr, hrxy⟩ := (hrel x y).mp hxy
      have hmatch := ((hbiff r).mp hr).2.2 x y (Or.inr hrxy)
      constructor
      · intro z hz
        obtain ⟨w, hw, hzw⟩ := hmatch.1 z hz
        exact ⟨w, hw, hin r hr z w hzw⟩
      · intro w hw
        obtain ⟨z, hz, hzw⟩ := hmatch.2 w hw
        exact ⟨z, hz, hin r hr z w hzw⟩
  · intro r hrG hrB x y hrxy
    have hbound : Subset s r ppd := by
      intro p hp
      obtain ⟨u, v, hu, hv, hpuv⟩ := hrG p hp
      exact orderedPair_bound hpd hppd hu hv hpuv
    exact (hrel x y).mpr ⟨r, (hbiff r).mpr ⟨hbound, hrG, hrB⟩, hrxy⟩

theorem maximal_augmented_symm (base : BaseCollection s) {d m x y : U}
    (hm : MaxAugmentedCode s d m) (hxy : WithIdentity (CodedRelation s m) x y) :
    WithIdentity (CodedRelation s m) y x := by
  rcases hxy with rfl | hxy
  · exact Or.inl rfl
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base
    (relatedFormula (n := 3) 2 0 1) (cons m Fin.elim0) d
  have hi : ∀ u v, CodedRelation s r u v ↔ CodedRelation s m v u := by
    intro u v
    have h := hr u v
    rw [eval_relatedFormula] at h
    constructor
    · intro h'
      exact (h.mp h').2.2
    · intro h'
      have hb := graphCode_endpoints hm.1 h'
      exact h.mpr ⟨hb.2, hb.1, h'⟩
  have hB : Bisimulation s (WithIdentity (CodedRelation s r)) := by
    intro u v huv
    have hrev : WithIdentity (CodedRelation s m) v u :=
      huv.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((hi u v).mp h))
    have hh := hm.2.1 v u hrev
    constructor
    · intro z hz
      obtain ⟨w, hw, hwz⟩ := hh.2 z hz
      exact ⟨w, hw, hwz.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((hi z w).mpr h))⟩
    · intro w hw
      obtain ⟨z, hz, hwz⟩ := hh.1 w hw
      exact ⟨z, hz, hwz.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((hi z w).mpr h))⟩
  exact Or.inr (hm.2.2 r hrG hB y x ((hi y x).mpr hxy))

theorem maximal_augmented_trans (base : BaseCollection s) {d m x y z : U}
    (hm : MaxAugmentedCode s d m)
    (hxy : WithIdentity (CodedRelation s m) x y)
    (hyz : WithIdentity (CodedRelation s m) y z) :
    WithIdentity (CodedRelation s m) x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base compositionFormula
    (cons m (cons m Fin.elim0)) d
  have hi : ∀ u v, CodedRelation s r u v ↔ ∃ w, CodedRelation s m u w ∧ CodedRelation s m w v := by
    intro u v
    have h := hr u v
    rw [eval_compositionFormula] at h
    constructor
    · intro hh
      exact (h.mp hh).2.2
    · rintro ⟨w, huw, hwv⟩
      exact h.mpr ⟨(graphCode_endpoints hm.1 huw).1, (graphCode_endpoints hm.1 hwv).2, w, huw, hwv⟩
  obtain ⟨v, hvG, hv⟩ := normalized_relation_comprehension base
    ((relatedFormula (n := 4) 2 1 0).disj (relatedFormula 3 1 0))
    (cons m (cons r Fin.elim0)) d
  have hviff : ∀ u w, CodedRelation s v u w ↔ CodedRelation s m u w ∨ CodedRelation s r u w := by
    intro u w
    have h := hv u w
    rw [eval_disj, eval_relatedFormula, eval_relatedFormula] at h
    constructor
    · intro hh
      exact (h.mp hh).2.2
    · intro hh
      have hb : s u d ∧ s w d := hh.elim (graphCode_endpoints hm.1) (graphCode_endpoints hrG)
      exact h.mpr ⟨hb.1, hb.2, hh⟩
  have hcomp : ∀ u w, WithIdentity (CodedRelation s v) u w ↔
      ∃ k, WithIdentity (CodedRelation s m) u k ∧ WithIdentity (CodedRelation s m) k w := by
    intro u w
    constructor
    · intro h
      rcases h with rfl | h
      · exact ⟨u, Or.inl rfl, Or.inl rfl⟩
      rcases (hviff u w).mp h with h | h
      · exact ⟨w, Or.inr h, Or.inl rfl⟩
      obtain ⟨k, huk, hkw⟩ := (hi u w).mp h
      exact ⟨k, Or.inr huk, Or.inr hkw⟩
    · rintro ⟨k, huk, hkw⟩
      rcases huk with rfl | huk
      · exact hkw.elim Or.inl (fun h => Or.inr ((hviff u w).mpr (Or.inl h)))
      rcases hkw with rfl | hkw
      · exact Or.inr ((hviff u k).mpr (Or.inl huk))
      exact Or.inr ((hviff u w).mpr (Or.inr ((hi u w).mpr ⟨k, huk, hkw⟩)))
  have hvB := bisimulation_congr (fun u w => (hcomp u w).symm) (bisimulation_comp hm.2.1 hm.2.1)
  exact Or.inr (hm.2.2 v hvG hvB x z ((hviff x z).mpr (Or.inr ((hi x z).mpr ⟨y, hxy, hyz⟩))))

#print axioms maximal_augmented_trans
end FullBridge
