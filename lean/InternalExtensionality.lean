import WitnessCollection

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem augmented_inverse (base : BaseCollection s) (r : U)
    (hr : Bisimulation s (WithIdentity (CodedRelation s r))) :
    ∃ t, Bisimulation s (WithIdentity (CodedRelation s t)) ∧
      ∀ x y, WithIdentity (CodedRelation s t) x y ↔ WithIdentity (CodedRelation s r) y x := by
  obtain ⟨t, ht⟩ := codedRelation_inverse base.pairing base.union base.powerset base.separation r
  have he : ∀ x y, WithIdentity (CodedRelation s t) x y ↔ WithIdentity (CodedRelation s r) y x := by
    intro x y
    constructor
    · intro h
      exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((ht x y).mp h))
    · intro h
      exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((ht x y).mpr h))
  refine ⟨t, ?_, he⟩
  apply bisimulation_congr (fun x y => (he x y).symm)
  intro x y hxy
  exact ⟨(hr y x hxy).2, (hr y x hxy).1⟩

theorem augmented_merge (base : BaseCollection s) (r t : U)
    (hr : Bisimulation s (WithIdentity (CodedRelation s r)))
    (ht : Bisimulation s (WithIdentity (CodedRelation s t))) :
    ∃ v, Bisimulation s (WithIdentity (CodedRelation s v)) ∧
      (∀ x y, WithIdentity (CodedRelation s r) x y → WithIdentity (CodedRelation s v) x y) ∧
      (∀ x y, WithIdentity (CodedRelation s t) x y → WithIdentity (CodedRelation s v) x y) := by
  obtain ⟨p, hp⟩ := base.pairing r t
  have hall : ∀ w, s w p → Bisimulation s (WithIdentity (CodedRelation s w)) := by
    intro w hw
    rcases (hp w).mp hw with rfl | rfl
    · exact hr
    · exact ht
  obtain ⟨v, hv, hi⟩ := augmented_family_union base.union p hall
  exact ⟨v, hv, hi r ((hp r).mpr (Or.inl rfl)), hi t ((hp t).mpr (Or.inr rfl))⟩

theorem codedRelation_singleton (hp : Pairing s) (a b : U) :
    ∃ r, ∀ x y, CodedRelation s r x y ↔ x = a ∧ y = b := by
  obtain ⟨p, hpab⟩ := orderedPair_exists hp a b
  obtain ⟨r, hr⟩ := hp p p
  refine ⟨r, ?_⟩
  intro x y
  constructor
  · rintro ⟨q, hqr, hqxy⟩
    have hqp : q = p := ((hr q).mp hqr).elim id id
    subst q
    exact orderedPair_injective hqxy hpab
  · rintro ⟨rfl, rfl⟩
    exact ⟨p, (hr p).mpr (Or.inl rfl), hpab⟩

theorem internalBehavior_add_root (base : BaseCollection s) (r a b : U)
    (hr : Bisimulation s (WithIdentity (CodedRelation s r)))
    (hf : ∀ x, s x a → ∃ y, s y b ∧ WithIdentity (CodedRelation s r) x y)
    (hb : ∀ y, s y b → ∃ x, s x a ∧ WithIdentity (CodedRelation s r) x y) :
    InternalBehavior s a b := by
  obtain ⟨root, hroot⟩ := codedRelation_singleton base.pairing a b
  obtain ⟨v, hv⟩ := codedRelation_union base.pairing base.union r root
  have hin : ∀ x y, WithIdentity (CodedRelation s r) x y → WithIdentity (CodedRelation s v) x y := by
    intro x y h
    exact h.elim Or.inl (fun h => Or.inr ((hv x y).mpr (Or.inl h)))
  refine ⟨v, ?_, Or.inr ((hv a b).mpr (Or.inr ((hroot a b).mpr ⟨rfl, rfl⟩)))⟩
  intro x y hxy
  have hmatching :
      (∀ z, s z x → ∃ w, s w y ∧ WithIdentity (CodedRelation s r) z w) ∧
      (∀ w, s w y → ∃ z, s z x ∧ WithIdentity (CodedRelation s r) z w) := by
    rcases hxy with rfl | hxy
    · exact hr x x (Or.inl rfl)
    · rcases (hv x y).mp hxy with hR | hrootxy
      · exact hr x y (Or.inr hR)
      · obtain ⟨rfl, rfl⟩ := (hroot x y).mp hrootxy
        exact ⟨hf, hb⟩
  constructor
  · intro z hz
    obtain ⟨w, hw, hzw⟩ := hmatching.1 z hz
    exact ⟨w, hw, hin z w hzw⟩
  · intro w hw
    obtain ⟨z, hz, hzw⟩ := hmatching.2 w hw
    exact ⟨z, hz, hin z w hzw⟩

theorem internalBehavior_of_children (base : BaseCollection s) (a b : U)
    (hf : ∀ x, s x a → ∃ y, s y b ∧ InternalBehavior s x y)
    (hb : ∀ y, s y b → ∃ x, s x a ∧ InternalBehavior s x y) : InternalBehavior s a b := by
  obtain ⟨r, hr, hrf⟩ := collect_forward_witnesses base a b hf
  have hback : ∀ y, s y b → ∃ x, s x a ∧ InternalBehavior s y x := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hb y hy
    exact ⟨x, hx, internalBehavior_symm base.pairing base.union base.powerset base.separation hxy⟩
  obtain ⟨t, ht, htb⟩ := collect_forward_witnesses base b a hback
  obtain ⟨ti, hti, hi⟩ := augmented_inverse base t ht
  obtain ⟨v, hv, hir, hit⟩ := augmented_merge base r ti hr hti
  apply internalBehavior_add_root base v a b hv
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hrf x hx
    exact ⟨y, hy, hir x y hxy⟩
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := htb y hy
    exact ⟨x, hx, hit x y ((hi x y).mpr hyx)⟩

theorem internal_extensional (base : BaseCollection s) : Extensional (internalMember base) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  apply (internal_code_eq base x y).mpr
  apply internalBehavior_of_children base x y
  · intro z hz
    have hqz := (internal_exact_members base x (internalCode base z)).mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (internal_exact_members base y (internalCode base z)).mp ((h _).mp hqz)
    exact ⟨w, hw, (internal_code_eq base z w).mp hwz.symm⟩
  · intro w hw
    have hqw := (internal_exact_members base y (internalCode base w)).mpr ⟨w, hw, rfl⟩
    obtain ⟨z, hz, hzw⟩ := (internal_exact_members base x (internalCode base w)).mp ((h _).mpr hqw)
    exact ⟨z, hz, (internal_code_eq base z w).mp hzw⟩

theorem internal_base_model (base : BaseCollection s) : BaseCollection (internalMember base) :=
  base_collection_transfer (internalInterpretation base) (internal_code_onto base)
    (internal_exact_members base) (internal_extensional base) base

#print axioms internal_base_model
end FullBridge
