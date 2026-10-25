import InfinityTransfer

namespace FullBridge
universe u
variable {U : Type u}

def Bisimulation (s : U → U → Prop) (R : U → U → Prop) : Prop :=
  ∀ a b, R a b →
    (∀ x, s x a → ∃ y, s y b ∧ R x y) ∧
    (∀ y, s y b → ∃ x, s x a ∧ R x y)

def Behavior (s : U → U → Prop) (a b : U) : Prop :=
  ∃ R, Bisimulation s R ∧ R a b

theorem behavior_refl (s : U → U → Prop) (a : U) : Behavior s a a := by
  refine ⟨Eq, ?_, rfl⟩
  intro x y h
  subst y
  exact ⟨fun z hz => ⟨z, hz, rfl⟩, fun z hz => ⟨z, hz, rfl⟩⟩

theorem behavior_symm {s : U → U → Prop} {a b : U}
    (h : Behavior s a b) : Behavior s b a := by
  obtain ⟨R, hR, hab⟩ := h
  exact ⟨fun x y => R y x, fun x y h => ⟨(hR y x h).2, (hR y x h).1⟩, hab⟩

theorem behavior_trans {s : U → U → Prop} {a b c : U}
    (h : Behavior s a b) (k : Behavior s b c) : Behavior s a c := by
  obtain ⟨R, hR, hab⟩ := h
  obtain ⟨S, hS, hbc⟩ := k
  refine ⟨fun x z => ∃ y, R x y ∧ S y z, ?_, ⟨b, hab, hbc⟩⟩
  intro x z hxz
  obtain ⟨y, hxy, hyz⟩ := hxz
  constructor
  · intro x' hx'
    obtain ⟨y', hy', hr⟩ := (hR x y hxy).1 x' hx'
    obtain ⟨z', hz', hs⟩ := (hS y z hyz).1 y' hy'
    exact ⟨z', hz', y', hr, hs⟩
  · intro z' hz'
    obtain ⟨y', hy', hs⟩ := (hS y z hyz).2 z' hz'
    obtain ⟨x', hx', hr⟩ := (hR x y hxy).2 y' hy'
    exact ⟨x', hx', y', hr, hs⟩

theorem behavior_bisimulation (s : U → U → Prop) : Bisimulation s (Behavior s) := by
  intro a b h
  obtain ⟨R, hR, hab⟩ := h
  constructor
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (hR a b hab).1 x hx
    exact ⟨y, hy, R, hR, hxy⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := (hR a b hab).2 y hy
    exact ⟨x, hx, R, hR, hxy⟩

theorem behavior_of_children {s : U → U → Prop} {a b : U}
    (hf : ∀ x, s x a → ∃ y, s y b ∧ Behavior s x y)
    (hb : ∀ y, s y b → ∃ x, s x a ∧ Behavior s x y) : Behavior s a b := by
  refine ⟨fun x y => Behavior s x y ∨ (x = a ∧ y = b), ?_, Or.inr ⟨rfl, rfl⟩⟩
  intro x y h
  rcases h with h | ⟨rfl, rfl⟩
  · constructor
    · intro z hz
      obtain ⟨w, hw, hzw⟩ := (behavior_bisimulation s x y h).1 z hz
      exact ⟨w, hw, Or.inl hzw⟩
    · intro w hw
      obtain ⟨z, hz, hzw⟩ := (behavior_bisimulation s x y h).2 w hw
      exact ⟨z, hz, Or.inl hzw⟩
  · constructor
    · intro z hz
      obtain ⟨w, hw, hzw⟩ := hf z hz
      exact ⟨w, hw, Or.inl hzw⟩
    · intro w hw
      obtain ⟨z, hz, hzw⟩ := hb w hw
      exact ⟨z, hz, Or.inl hzw⟩

def behaviorSetoid (s : U → U → Prop) : Setoid U where
  r := Behavior s
  iseqv := ⟨behavior_refl s, behavior_symm, behavior_trans⟩
abbrev BehaviorQuotient (s : U → U → Prop) := Quotient (behaviorSetoid s)
def behaviorCode (s : U → U → Prop) (a : U) : BehaviorQuotient s := Quotient.mk _ a

def behaviorMember (s : U → U → Prop) (x a : BehaviorQuotient s) : Prop :=
  ∃ y b, behaviorCode s y = x ∧ behaviorCode s b = a ∧ s y b

theorem behavior_code_eq {s : U → U → Prop} (a b : U) :
    behaviorCode s a = behaviorCode s b ↔ Behavior s a b :=
  ⟨fun h => Quotient.exact h, fun h => @Quotient.sound U (behaviorSetoid s) a b h⟩

theorem behavior_code_onto (s : U → U → Prop) :
    ∀ y, ∃ x, behaviorCode s x = y := by
  intro y
  exact Quotient.inductionOn y (fun x => ⟨x, rfl⟩)

theorem behavior_exact_members (s : U → U → Prop) :
    ExactMembers s (behaviorMember s) (behaviorCode s) := by
  intro a y
  constructor
  · rintro ⟨x, b, hxy, hba, hxb⟩
    have hsim := (behavior_code_eq b a).mp hba
    obtain ⟨z, hza, hxz⟩ := (behavior_bisimulation s b a hsim).1 x hxb
    exact ⟨z, hza, ((behavior_code_eq x z).mpr hxz).symm.trans hxy⟩
  · rintro ⟨x, hxa, hxy⟩
    exact ⟨x, a, hxy, rfl, hxa⟩

theorem behavior_quotient_extensional (s : U → U → Prop) :
    Extensional (behaviorMember s) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  apply (behavior_code_eq x y).mpr
  apply behavior_of_children
  · intro z hz
    have hzq := (behavior_exact_members s x (behaviorCode s z)).mpr ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := (behavior_exact_members s y (behaviorCode s z)).mp ((h _).mp hzq)
    exact ⟨w, hw, (behavior_code_eq z w).mp hwz.symm⟩
  · intro w hw
    have hwq := (behavior_exact_members s y (behaviorCode s w)).mpr ⟨w, hw, rfl⟩
    obtain ⟨z, hz, hzw⟩ := (behavior_exact_members s x (behaviorCode s w)).mp ((h _).mpr hwq)
    exact ⟨z, hz, (behavior_code_eq z w).mp hzw⟩

/- The remaining definability obligation is explicit. This theorem does not
   assert that external Behavior is first-order definable in every model. -/
theorem behavior_base_transfer (s : U → U → Prop)
    (I : AtomicInterpretation s (behaviorMember s) (behaviorCode s))
    (base : BaseCollection s) : BaseCollection (behaviorMember s) :=
  base_collection_transfer I (behavior_code_onto s) (behavior_exact_members s)
    (behavior_quotient_extensional s) base

#print axioms behavior_base_transfer
end FullBridge
