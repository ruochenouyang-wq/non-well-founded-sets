import InternalQuotient

namespace FullBridge
universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable {s : U → U → Prop} {t : V → V → Prop} {r : W → W → Prop}

/-- The external successor predicate of a membership transition system. -/
def memberSuccessors (s : U → U → Prop) (a : U) : U → Prop := fun x => s x a

def predicateImage (f : U → V) (P : U → Prop) : V → Prop :=
  fun y => ∃ x, P x ∧ f x = y

/-- Powerset coalgebra morphisms are exactly the existing exact-member maps. -/
theorem exact_members_coalgebra_iff (f : U → V) :
    ExactMembers s t f ↔ ∀ a,
      memberSuccessors t (f a) = predicateImage f (memberSuccessors s a) := by
  constructor
  · intro h a
    funext y
    exact propext (h a y)
  · intro h a y
    exact Iff.of_eq (congrFun (h a) y)

theorem exact_members_identity : ExactMembers s s (fun x => x) := by
  intro a y
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

theorem exact_members_comp {f : U → V} {g : V → W}
    (hf : ExactMembers s t f) (hg : ExactMembers t r g) :
    ExactMembers s r (fun x => g (f x)) := by
  intro a z
  constructor
  · intro h
    obtain ⟨y, hy, hgz⟩ := (hg (f a) z).mp h
    obtain ⟨x, hx, hfx⟩ := (hf a y).mp hy
    exact ⟨x, hx, (congrArg g hfx).trans hgz⟩
  · rintro ⟨x, hx, hgz⟩
    exact (hg (f a) z).mpr ⟨f x, (hf a (f x)).mpr ⟨x, hx, rfl⟩, hgz⟩

/-- Kernel pairs carry the componentwise transition relation. -/
abbrev InternalKernel (s : U → U → Prop) :=
  {p : U × U // InternalBehavior s p.1 p.2}

def internalKernelMember (s : U → U → Prop)
    (x a : InternalKernel s) : Prop := s x.val.1 a.val.1 ∧ s x.val.2 a.val.2

theorem internal_kernel_left_exact :
    ExactMembers (internalKernelMember s) s (fun p => p.val.1) := by
  intro a x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := (internalBehavior_bisimulation s _ _ a.property).1 x hx
    exact ⟨⟨(x, y), hxy⟩, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact hp.1

theorem internal_kernel_right_exact :
    ExactMembers (internalKernelMember s) s (fun p => p.val.2) := by
  intro a y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := (internalBehavior_bisimulation s _ _ a.property).2 y hy
    exact ⟨⟨(x, y), hxy⟩, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact hp.2

theorem internal_kernel_equalized (base : BaseCollection s) (p : InternalKernel s) :
    internalCode base p.val.1 = internalCode base p.val.2 :=
  (internal_code_eq base _ _).mpr p.property

theorem internal_equalizes_iff (f : U → V) :
    (∀ p : InternalKernel s, f p.val.1 = f p.val.2) ↔
      (∀ x y, InternalBehavior s x y → f x = f y) := by
  constructor
  · intro h x y hxy
    exact h ⟨(x, y), hxy⟩
  · intro h p
    exact h _ _ p.property

def internalCoalgebraFactor (base : BaseCollection s) (f : U → V)
    (h : ∀ x y, InternalBehavior s x y → f x = f y) : InternalQuotient base → V :=
  Quotient.lift f h

theorem internal_coalgebra_factor_code (base : BaseCollection s) (f : U → V)
    (h : ∀ x y, InternalBehavior s x y → f x = f y) (x : U) :
    internalCoalgebraFactor base f h (internalCode base x) = f x := rfl

theorem internal_coalgebra_factor_exact (base : BaseCollection s) (f : U → V)
    (h : ∀ x y, InternalBehavior s x y → f x = f y)
    (hf : ExactMembers s t f) :
    ExactMembers (internalMember base) t (internalCoalgebraFactor base f h) := by
  intro A y
  obtain ⟨a, rfl⟩ := internal_code_onto base A
  constructor
  · intro hy
    obtain ⟨x, hx, hfx⟩ := (hf a y).mp hy
    exact ⟨internalCode base x,
      (internal_exact_members base a _).mpr ⟨x, hx, rfl⟩, hfx⟩
  · rintro ⟨X, hXA, hXy⟩
    obtain ⟨x, hx, rfl⟩ := (internal_exact_members base a X).mp hXA
    exact (hf a y).mpr ⟨x, hx, hXy⟩

theorem internal_coalgebra_factor_unique (base : BaseCollection s) (f : U → V)
    (h : ∀ x y, InternalBehavior s x y → f x = f y)
    (F : InternalQuotient base → V) (hF : ∀ x, F (internalCode base x) = f x) :
    F = internalCoalgebraFactor base f h := by
  funext A
  obtain ⟨a, rfl⟩ := internal_code_onto base A
  exact hF a

/-- Explicit coequalizer property among external relational systems and
    exact-member maps, for the internally coded behavior kernel only. -/
theorem internal_quotient_coequalizer (base : BaseCollection s) (f : U → V)
    (hf : ExactMembers s t f)
    (heq : ∀ p : InternalKernel s, f p.val.1 = f p.val.2) :
    ∃ F : InternalQuotient base → V,
      ExactMembers (internalMember base) t F ∧
      (∀ x, F (internalCode base x) = f x) ∧
      ∀ G : InternalQuotient base → V,
        (∀ x, G (internalCode base x) = f x) → G = F := by
  let h := (internal_equalizes_iff f).mp heq
  exact ⟨internalCoalgebraFactor base f h,
    internal_coalgebra_factor_exact base f h hf,
    internal_coalgebra_factor_code base f h,
    fun G hG => internal_coalgebra_factor_unique base f h G hG⟩

end FullBridge
