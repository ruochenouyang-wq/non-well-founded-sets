import ParameterFamilies
namespace FullBridge
universe u v

theorem eval_bijective_members {U : Type u} {V : Type v}
    {s : U → U → Prop} {t : V → V → Prop} (q : U → V)
    (hi : ∀ x y, q x = q y → x = y) (ho : ∀ y, ∃ x, q x = y)
    (hm : ∀ x y, s x y ↔ t (q x) (q y))
    {n} (p : Formula n) (e : Fin n → U) :
    Eval s p e ↔ Eval t p (fun i => q (e i)) := by
  induction p with
  | equal i j => exact ⟨congrArg q, hi _ _⟩
  | member i j => exact hm _ _
  | bottom => rfl
  | conj p r hp hr => exact and_congr (hp e) (hr e)
  | impl p r hp hr => exact imp_congr (hp e) (hr e)
  | ex p hp =>
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨q x, ?_⟩
      simpa only [cons_map] using (hp (cons x e)).mp hx
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := ho y
      refine ⟨x, (hp (cons x e)).mpr ?_⟩
      simpa only [cons_map] using hy
  | all p hp =>
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := ho y
      simpa only [cons_map] using (hp (cons x e)).mp (h x)
    · intro h x
      apply (hp (cons x e)).mpr
      simpa only [cons_map] using h (q x)

variable {U : Type u} {s : U → U → Prop}

def ParameterCarrier (s : U → U → Prop) (a : U) := {x : U // s x a}

def parameterCode (base : BaseCollection s) (a : U) :
    ParameterCarrier s a → ParameterCarrier (internalMember base) (internalCode base a) :=
  fun x => ⟨internalCode base x.val, (internal_exact_members base a _).mpr ⟨x.val, x.property, rfl⟩⟩

theorem parameter_code_bijective (base : BaseCollection s) {a : U}
    (hi : ParameterInjective base a) :
    (∀ x y, parameterCode base a x = parameterCode base a y → x = y) ∧
    (∀ Y, ∃ x, parameterCode base a x = Y) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact hi x.val y.val x.property y.property (congrArg Subtype.val h)
  · intro Y
    obtain ⟨x, hx, hq⟩ := (internal_exact_members base a Y.val).mp Y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hq⟩

theorem parameter_original_formula_semantics (base : BaseCollection s) {a : U}
    (ha : TransitiveCode s a) (hi : ParameterInjective base a)
    {n} (p : Formula n) (e : Fin n → ParameterCarrier s a) :
    Eval (fun x y : ParameterCarrier s a => s x.val y.val) p e ↔
    Eval (fun X Y : ParameterCarrier (internalMember base) (internalCode base a) =>
      internalMember base X.val Y.val) p (fun i => parameterCode base a (e i)) := by
  obtain ⟨hinj, honto⟩ := parameter_code_bijective base hi
  apply eval_bijective_members (parameterCode base a) hinj honto
  intro x y
  exact (parameter_member_reflection base ha hi x.property y.property).symm

#print axioms parameter_original_formula_semantics
end FullBridge
