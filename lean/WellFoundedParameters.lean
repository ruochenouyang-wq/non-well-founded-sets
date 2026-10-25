import BehaviorQuotient

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem behavior_acc {a : U} (ha : Acc s a) :
    ∀ b, Behavior s a b → Acc s b := by
  induction ha with
  | intro a ha ih =>
    intro b hab
    apply Acc.intro b
    intro y hy
    obtain ⟨x, hx, hxy⟩ := (behavior_bisimulation s a b hab).2 y hy
    exact ih x hx y hxy

theorem behavior_eq_of_acc (he : Extensional s) {a : U} (ha : Acc s a) :
    ∀ b, Acc s b → Behavior s a b → a = b := by
  induction ha with
  | intro a ha ih =>
    intro b hb hab
    apply he a b
    intro z
    constructor
    · intro hz
      obtain ⟨w, hw, hzw⟩ := (behavior_bisimulation s a b hab).1 z hz
      have hEq := ih z hz w (Acc.inv hb hw) hzw
      exact hEq ▸ hw
    · intro hz
      obtain ⟨w, hw, hwz⟩ := (behavior_bisimulation s a b hab).2 z hz
      have hEq := ih w hw z (Acc.inv hb hz) hwz
      exact hEq ▸ hw

theorem wellFounded_fiber_singleton (he : Extensional s) {a b : U} (ha : Acc s a) :
    behaviorCode s a = behaviorCode s b ↔ a = b := by
  constructor
  · intro h
    have hab := (behavior_code_eq a b).mp h
    exact behavior_eq_of_acc he ha b (behavior_acc ha b hab) hab
  · intro h
    exact congrArg (behaviorCode s) h

theorem wellFounded_member_reflection (he : Extensional s) {a b : U} (hb : Acc s b) :
    behaviorMember s (behaviorCode s a) (behaviorCode s b) ↔ s a b := by
  constructor
  · intro h
    obtain ⟨x, hxb, hxa⟩ := (behavior_exact_members s b (behaviorCode s a)).mp h
    have hEq := (wellFounded_fiber_singleton he (Acc.inv hb hxb)).mp hxa
    exact hEq ▸ hxb
  · intro h
    exact (behavior_exact_members s b (behaviorCode s a)).mpr ⟨a, h, rfl⟩

#print axioms wellFounded_fiber_singleton
#print axioms wellFounded_member_reflection
end FullBridge
