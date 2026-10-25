import ModalObservations

namespace FullBridge
universe u v
variable {U : Type u} {V : Type v} {s : U → U → Prop} {t : V → V → Prop}

def PredicatePullback (f : U → V) (P : V → Prop) : U → Prop := fun x => P (f x)
def MemberDiamond (s : U → U → Prop) (P : U → Prop) : U → Prop :=
  fun a => ∃ x, s x a ∧ P x
def MemberBox (s : U → U → Prop) (P : U → Prop) : U → Prop :=
  fun a => ∀ x, s x a → P x
def InternalInvariant (s : U → U → Prop) (P : U → Prop) : Prop :=
  ∀ x y, InternalBehavior s x y → (P x ↔ P y)

theorem predicate_pullback_neg (f : U → V) (P : V → Prop) :
    PredicatePullback f (fun y => ¬P y) = (fun x => ¬PredicatePullback f P x) := rfl

theorem predicate_pullback_conj (f : U → V) (P Q : V → Prop) :
    PredicatePullback f (fun y => P y ∧ Q y) =
      (fun x => PredicatePullback f P x ∧ PredicatePullback f Q x) := rfl

theorem exact_members_pullback_diamond {f : U → V} (hf : ExactMembers s t f)
    (P : V → Prop) :
    PredicatePullback f (MemberDiamond t P) = MemberDiamond s (PredicatePullback f P) := by
  funext a
  apply propext
  constructor
  · rintro ⟨y, hy, hp⟩
    obtain ⟨x, hx, rfl⟩ := (hf a y).mp hy
    exact ⟨x, hx, hp⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨f x, (hf a (f x)).mpr ⟨x, hx, rfl⟩, hp⟩

theorem exact_members_pullback_box {f : U → V} (hf : ExactMembers s t f)
    (P : V → Prop) :
    PredicatePullback f (MemberBox t P) = MemberBox s (PredicatePullback f P) := by
  funext a
  apply propext
  constructor
  · intro h x hx
    exact h (f x) ((hf a (f x)).mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := (hf a y).mp hy
    exact h x hx

def internalPredicateDescend (base : BaseCollection s) (P : U → Prop)
    (hP : InternalInvariant s P) : InternalQuotient base → Prop :=
  Quotient.lift P (fun x y hxy => propext (hP x y hxy))

theorem internal_predicate_pullback_invariant (base : BaseCollection s)
    (Q : InternalQuotient base → Prop) : InternalInvariant s (PredicatePullback (internalCode base) Q) := by
  intro x y hxy
  exact Iff.of_eq (congrArg Q ((internal_code_eq base x y).mpr hxy))

theorem internal_predicate_pullback_injective (base : BaseCollection s)
    (P Q : InternalQuotient base → Prop)
    (h : PredicatePullback (internalCode base) P = PredicatePullback (internalCode base) Q) :
    P = Q := by
  funext X
  obtain ⟨x, rfl⟩ := internal_code_onto base X
  exact congrFun h x

theorem internal_predicate_descent_iff (base : BaseCollection s) (P : U → Prop) :
    (∃ Q : InternalQuotient base → Prop, PredicatePullback (internalCode base) Q = P) ↔
      InternalInvariant s P := by
  constructor
  · rintro ⟨Q, rfl⟩
    exact internal_predicate_pullback_invariant base Q
  · intro hP
    exact ⟨internalPredicateDescend base P hP, rfl⟩

theorem internal_invariant_diamond (base : BaseCollection s) (P : U → Prop)
    (hP : InternalInvariant s P) : InternalInvariant s (MemberDiamond s P) := by
  obtain ⟨Q, rfl⟩ := (internal_predicate_descent_iff base P).mpr hP
  rw [←exact_members_pullback_diamond (internal_exact_members base)]
  exact internal_predicate_pullback_invariant base _

theorem internal_invariant_box (base : BaseCollection s) (P : U → Prop)
    (hP : InternalInvariant s P) : InternalInvariant s (MemberBox s P) := by
  obtain ⟨Q, rfl⟩ := (internal_predicate_descent_iff base P).mpr hP
  rw [←exact_members_pullback_box (internal_exact_members base)]
  exact internal_predicate_pullback_invariant base _

theorem internal_invariant_neg (P : U → Prop) (hP : InternalInvariant s P) :
    InternalInvariant s (fun x => ¬P x) := by
  intro x y hxy
  exact not_congr (hP x y hxy)

theorem internal_invariant_conj (P Q : U → Prop)
    (hP : InternalInvariant s P) (hQ : InternalInvariant s Q) :
    InternalInvariant s (fun x => P x ∧ Q x) := by
  intro x y hxy
  exact and_congr (hP x y hxy) (hQ x y hxy)

end FullBridge
