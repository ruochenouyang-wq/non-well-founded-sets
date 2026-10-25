import MembershipSymmetry
namespace FullBridge
universe u v w
variable {U : Type u} {V : Type v} {W : Type w}
variable {s : U → U → Prop} {t : V → V → Prop} {r : W → W → Prop}

/-- An external map preserving all formulas of the actual finite first-order syntax.
    This is not an internally coded function or an object-language truth predicate. -/
def ElementaryMap (s : U → U → Prop) (t : V → V → Prop) (j : U → V) : Prop :=
  ∀ {n} (p : Formula n) (e : Fin n → U),
    Eval s p e ↔ Eval t p (fun i => j (e i))

theorem elementary_map_identity : ElementaryMap s s (fun x => x) := by
  intro n p e
  rfl

theorem elementary_map_comp {j : U → V} {k : V → W}
    (hj : ElementaryMap s t j) (hk : ElementaryMap t r k) :
    ElementaryMap s r (fun x => k (j x)) := by
  intro n p e
  exact (hj p e).trans (hk p (fun i => j (e i)))

theorem elementary_map_injective {j : U → V} (hj : ElementaryMap s t j) :
    ∀ x y, j x = j y → x = y := by
  intro x y h
  exact (hj (Formula.equal (n := 2) 0 1) (pairEnv x y)).mpr h

theorem elementary_map_internal_behavior {j : U → V} (hj : ElementaryMap s t j)
    (x y : U) : InternalBehavior s x y ↔ InternalBehavior t (j x) (j y) := by
  have h := hj (internalBehaviorFormula 0 1) (pairEnv x y)
  rw [eval_internalBehaviorFormula, eval_internalBehaviorFormula] at h
  exact h

/-- The same syntactic translation is used in every source model. -/
def behaviorTranslation {n} (p : Formula n) : Formula n :=
  Formula.translate (internalBehaviorFormula 0 1)
    (memberFromKernel (internalBehaviorFormula 0 1)) p

theorem uniform_behavior_translation (base : BaseCollection s) {n}
    (p : Formula n) (e : Fin n → U) :
    Eval s (behaviorTranslation p) e ↔
      Eval (internalMember base) p (fun i => internalCode base (e i)) :=
  internal_formula_translation base p e

/-- The induced map is external, on the actual semantic quotient types. -/
def behaviorMap (bs : BaseCollection s) (bt : BaseCollection t)
    (j : U → V) (hj : ElementaryMap s t j) : InternalQuotient bs → InternalQuotient bt :=
  Quotient.lift (fun x => internalCode bt (j x)) (by
    intro x y hxy
    exact (internal_code_eq bt (j x) (j y)).mpr
      ((elementary_map_internal_behavior hj x y).mp hxy))

theorem behavior_map_code (bs : BaseCollection s) (bt : BaseCollection t)
    (j : U → V) (hj : ElementaryMap s t j) (x : U) :
    behaviorMap bs bt j hj (internalCode bs x) = internalCode bt (j x) := rfl

theorem behavior_map_elementary (bs : BaseCollection s) (bt : BaseCollection t)
    (j : U → V) (hj : ElementaryMap s t j) :
    ElementaryMap (internalMember bs) (internalMember bt) (behaviorMap bs bt j hj) := by
  classical
  intro n p e
  let a : Fin n → U := fun i => Classical.choose (internal_code_onto bs (e i))
  have ha : ∀ i, internalCode bs (a i) = e i :=
    fun i => Classical.choose_spec (internal_code_onto bs (e i))
  have h := (uniform_behavior_translation bs p a).symm.trans
    ((hj (behaviorTranslation p) a).trans
      (uniform_behavior_translation bt p (fun i => j (a i))))
  have he : (fun i => internalCode bs (a i)) = e := funext ha
  have hf : (fun i => internalCode bt (j (a i))) =
      (fun i => behaviorMap bs bt j hj (e i)) := by
    funext i
    rw [← ha i]
    rfl
  rw [he, hf] at h
  exact h

theorem behavior_map_unique (bs : BaseCollection s) (bt : BaseCollection t)
    (j : U → V) (hj : ElementaryMap s t j)
    (F : InternalQuotient bs → InternalQuotient bt)
    (hF : ∀ x, F (internalCode bs x) = internalCode bt (j x)) :
    F = behaviorMap bs bt j hj := by
  funext X
  obtain ⟨x, rfl⟩ := internal_code_onto bs X
  exact hF x

theorem behavior_map_identity (bs : BaseCollection s) :
    behaviorMap bs bs (fun x => x) elementary_map_identity = (fun X => X) := by
  funext X
  obtain ⟨x, rfl⟩ := internal_code_onto bs X
  rfl

theorem behavior_map_comp (bs : BaseCollection s) (bt : BaseCollection t)
    (br : BaseCollection r) (j : U → V) (k : V → W)
    (hj : ElementaryMap s t j) (hk : ElementaryMap t r k) :
    behaviorMap bs br (fun x => k (j x)) (elementary_map_comp hj hk) =
      (fun X => behaviorMap bt br k hk (behaviorMap bs bt j hj X)) := by
  funext X
  obtain ⟨x, rfl⟩ := internal_code_onto bs X
  rfl

theorem behavior_map_surjective (bs : BaseCollection s) (bt : BaseCollection t)
    (j : U → V) (hj : ElementaryMap s t j) (honto : ∀ y, ∃ x, j x = y) :
    ∀ Y, ∃ X, behaviorMap bs bt j hj X = Y := by
  intro Y
  obtain ⟨y, rfl⟩ := internal_code_onto bt Y
  obtain ⟨x, rfl⟩ := honto y
  exact ⟨internalCode bs x, rfl⟩

theorem behavior_map_identity_iff (bs : BaseCollection s) (j : U → U)
    (hj : ElementaryMap s s j) :
    behaviorMap bs bs j hj = (fun X => X) ↔
      ∀ x, InternalBehavior s (j x) x := by
  constructor
  · intro h x
    exact (internal_code_eq bs (j x) x).mp (congrFun h (internalCode bs x))
  · intro h
    funext X
    obtain ⟨x, rfl⟩ := internal_code_onto bs X
    exact (internal_code_eq bs (j x) x).mpr (h x)

/-- An explicit sufficient condition; neither internal covers nor internal restrictions
    of arbitrary external maps are assumed to exist automatically. -/
def LocallyInternalTransitiveMap (s : U → U → Prop) (j : U → U) : Prop :=
  ∀ x, ∃ a b p, TransitiveCode s a ∧ TransitiveCode s b ∧ s x a ∧
    MembershipIsoCode s a b p ∧ ∀ y, s y a → CodedRelation s p y (j y)

theorem locally_internal_map_behavior (bs : BaseCollection s) (j : U → U)
    (hlocal : LocallyInternalTransitiveMap s j) :
    ∀ x, InternalBehavior s (j x) x := by
  intro x
  obtain ⟨a, b, p, ha, hb, hx, hp, hj⟩ := hlocal x
  have heq := ((membership_iso_over_quotient bs ha hb hp).2 x (j x) (hj x hx)).2
  exact (internal_code_eq bs (j x) x).mp heq.symm

theorem locally_internal_elementary_map_trivial_quotient (bs : BaseCollection s)
    (j : U → U) (hj : ElementaryMap s s j) (hlocal : LocallyInternalTransitiveMap s j) :
    behaviorMap bs bs j hj = (fun X => X) :=
  (behavior_map_identity_iff bs j hj).mpr (locally_internal_map_behavior bs j hlocal)

theorem bafa_bridge_elementary_map (M : BafaModel.{u}) (N : BafaModel.{v})
    (j : M.Carrier → N.Carrier) (hj : ElementaryMap M.mem N.mem j) :
    ∃ F : M.behaviorQuotient.Carrier → N.behaviorQuotient.Carrier,
      ElementaryMap M.behaviorQuotient.mem N.behaviorQuotient.mem F ∧
      (∀ x, F (internalCode M.base x) = internalCode N.base (j x)) ∧
      ∀ G : M.behaviorQuotient.Carrier → N.behaviorQuotient.Carrier,
        (∀ x, G (internalCode M.base x) = internalCode N.base (j x)) → G = F := by
  exact ⟨behaviorMap M.base N.base j hj, behavior_map_elementary M.base N.base j hj,
    behavior_map_code M.base N.base j hj, fun G hG => behavior_map_unique M.base N.base j hj G hG⟩

#print axioms behavior_map_elementary
#print axioms bafa_bridge_elementary_map
#print axioms locally_internal_elementary_map_trivial_quotient
end FullBridge
