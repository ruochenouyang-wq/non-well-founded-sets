import InternalBehavior

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def internalSetoid (base : BaseCollection s) : Setoid U where
  r := InternalBehavior s
  iseqv := ⟨internalBehavior_refl base.empty,
    internalBehavior_symm base.pairing base.union base.powerset base.separation,
    internalBehavior_trans base.pairing base.union base.powerset base.separation⟩

abbrev InternalQuotient (base : BaseCollection s) := Quotient (internalSetoid base)
def internalCode (base : BaseCollection s) (a : U) : InternalQuotient base := Quotient.mk _ a

def internalMember (base : BaseCollection s) (x a : InternalQuotient base) : Prop :=
  ∃ y b, internalCode base y = x ∧ internalCode base b = a ∧ s y b

theorem internal_code_eq (base : BaseCollection s) (a b : U) :
    internalCode base a = internalCode base b ↔ InternalBehavior s a b :=
  ⟨fun h => Quotient.exact h, fun h => @Quotient.sound U (internalSetoid base) a b h⟩

theorem internal_code_onto (base : BaseCollection s) :
    ∀ y, ∃ x, internalCode base x = y := by
  intro y
  exact Quotient.inductionOn y (fun x => ⟨x, rfl⟩)

theorem internal_exact_members (base : BaseCollection s) :
    ExactMembers s (internalMember base) (internalCode base) := by
  intro a y
  constructor
  · rintro ⟨x, b, hxy, hba, hxb⟩
    have hsim := (internal_code_eq base b a).mp hba
    obtain ⟨z, hza, hxz⟩ := (internalBehavior_bisimulation s b a hsim).1 x hxb
    exact ⟨z, hza, ((internal_code_eq base x z).mpr hxz).symm.trans hxy⟩
  · rintro ⟨x, hxa, hxy⟩
    exact ⟨x, a, hxy, rfl, hxa⟩

def internalInterpretation (base : BaseCollection s) :
    AtomicInterpretation s (internalMember base) (internalCode base) :=
  interpretationFromKernel (internalBehaviorFormula 0 1) (by
    intro a b
    exact (eval_internalBehaviorFormula s 0 1 (pairEnv a b)).trans
      (internal_code_eq base a b).symm) (internal_exact_members base)

theorem internal_formula_translation (base : BaseCollection s) {n}
    (p : Formula n) (e : Fin n → U) :
    Eval s (Formula.translate (internalInterpretation base).equalFormula
      (internalInterpretation base).memberFormula p) e ↔
    Eval (internalMember base) p (fun i => internalCode base (e i)) :=
  eval_translate (internalInterpretation base) (internal_code_onto base) p e

theorem internal_separation (base : BaseCollection s) : Separation (internalMember base) :=
  separation_transfer (internalInterpretation base) (internal_code_onto base)
    (internal_exact_members base) base.separation

theorem internal_collection (base : BaseCollection s) : Collection (internalMember base) :=
  collection_transfer (internalInterpretation base) (internal_code_onto base)
    (internal_exact_members base) base.collection

theorem internal_wellFounded_fiber (base : BaseCollection s) {a b : U} (ha : Acc s a) :
    internalCode base a = internalCode base b ↔ a = b := by
  constructor
  · intro h
    have hab := internalBehavior_implies_behavior ((internal_code_eq base a b).mp h)
    exact behavior_eq_of_acc base.extensional ha b (behavior_acc ha b hab) hab
  · intro h
    exact congrArg (internalCode base) h

theorem internal_wellFounded_member (base : BaseCollection s) {a b : U} (hb : Acc s b) :
    internalMember base (internalCode base a) (internalCode base b) ↔ s a b := by
  constructor
  · intro h
    obtain ⟨x, hxb, hxa⟩ := (internal_exact_members base b (internalCode base a)).mp h
    have heq := (internal_wellFounded_fiber base (Acc.inv hb hxb)).mp hxa
    exact heq ▸ hxb
  · intro h
    exact (internal_exact_members base b (internalCode base a)).mpr ⟨a, h, rfl⟩

#print axioms internal_formula_translation
#print axioms internal_collection
#print axioms internal_wellFounded_member
end FullBridge
