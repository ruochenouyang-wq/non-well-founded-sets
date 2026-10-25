import ModelMaps
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem bounded_augmented_up_to (base : BaseCollection s) {d m r : U}
    (hm : MaxAugmentedCode s d m) (hrG : GraphCode s d r)
    (hstep : ∀ x y, CodedRelation s r x y →
      (∀ u, s u x → ∃ v, s v y ∧
        (WithIdentity (CodedRelation s m) u v ∨ BisimSandwich s m r u v)) ∧
      (∀ v, s v y → ∃ u, s u x ∧
        (WithIdentity (CodedRelation s m) u v ∨ BisimSandwich s m r u v))) :
    ∀ x y, CodedRelation s r x y → CodedRelation s m x y := by
  obtain ⟨w, hwG, hw⟩ := normalized_relation_comprehension base
    ((relatedFormula (n := 4) 2 1 0).disj bisimSandwichFormula)
    (cons m (cons r Fin.elim0)) d
  have hi : ∀ u v, CodedRelation s w u v ↔
      CodedRelation s m u v ∨ BisimSandwich s m r u v := by
    intro u v
    have h := hw u v
    rw [eval_disj, eval_relatedFormula, eval_bisimSandwichFormula] at h
    refine h.trans ⟨fun h => h.2.2, ?_⟩
    intro huv
    have hb : s u d ∧ s v d := by
      rcases huv with huv | ⟨x, y, hux, hxy, hyv⟩
      · exact graphCode_endpoints hm.1 huv
      · have hb := graphCode_endpoints hrG hxy
        exact ⟨hux.elim (fun h => h ▸ hb.1) (fun h => (graphCode_endpoints hm.1 h).1),
          hyv.elim (fun h => h ▸ hb.2) (fun h => (graphCode_endpoints hm.1 h).2)⟩
    exact ⟨hb.1, hb.2, huv⟩
  have hin : ∀ u v, WithIdentity (CodedRelation s m) u v → WithIdentity (CodedRelation s w) u v := by
    intro u v huv
    exact huv.elim Or.inl (fun h => Or.inr ((hi u v).mpr (Or.inl h)))
  have absorb : ∀ u x y v, WithIdentity (CodedRelation s m) u x →
      (WithIdentity (CodedRelation s m) x y ∨ BisimSandwich s m r x y) →
      WithIdentity (CodedRelation s m) y v → WithIdentity (CodedRelation s w) u v := by
    intro u x y v hux hxy hyv
    rcases hxy with hxy | hxy
    · exact hin u v (maximal_augmented_trans base hm
        (maximal_augmented_trans base hm hux hxy) hyv)
    · exact Or.inr ((hi u v).mpr (Or.inr (bisim_sandwich_absorb base hm hux hxy hyv)))
  have hwB : Bisimulation s (WithIdentity (CodedRelation s w)) := by
    intro u v huv
    rcases huv with rfl | huv
    · exact ⟨fun z hz => ⟨z, hz, Or.inl rfl⟩, fun z hz => ⟨z, hz, Or.inl rfl⟩⟩
    rcases (hi u v).mp huv with hmuv | ⟨x, y, hux, hrxy, hyv⟩
    · constructor
      · intro z hz
        obtain ⟨z', hz', hzz'⟩ := (hm.2.1 u v (Or.inr hmuv)).1 z hz
        exact ⟨z', hz', hin z z' hzz'⟩
      · intro z' hz'
        obtain ⟨z, hz, hzz'⟩ := (hm.2.1 u v (Or.inr hmuv)).2 z' hz'
        exact ⟨z, hz, hin z z' hzz'⟩
    · constructor
      · intro u' hu'
        obtain ⟨x', hx', hux'⟩ := (hm.2.1 u x hux).1 u' hu'
        obtain ⟨y', hy', hxy'⟩ := (hstep x y hrxy).1 x' hx'
        obtain ⟨v', hv', hyv'⟩ := (hm.2.1 y v hyv).1 y' hy'
        exact ⟨v', hv', absorb u' x' y' v' hux' hxy' hyv'⟩
      · intro v' hv'
        obtain ⟨y', hy', hyv'⟩ := (hm.2.1 y v hyv).2 v' hv'
        obtain ⟨x', hx', hxy'⟩ := (hstep x y hrxy).2 y' hy'
        obtain ⟨u', hu', hux'⟩ := (hm.2.1 u x hux).2 x' hx'
        exact ⟨u', hu', absorb u' x' y' v' hux' hxy' hyv'⟩
  intro x y hxy
  exact hm.2.2 w hwG hwB x y ((hi x y).mpr (Or.inr ⟨x, y, Or.inl rfl, hxy, Or.inl rfl⟩))

def pairBehaviorWitnessFormula : Formula 2 :=
  .ex (.ex (.conj (orderedPairFormula 3 1 0)
    (.conj (augmentedBisimFormula 2) (augmentedRelatedFormula 2 1 0))))

theorem eval_pairBehaviorWitnessFormula (k z : U) :
    Eval s pairBehaviorWitnessFormula (cons k (cons z Fin.elim0)) ↔
      ∃ x y, IsOrderedPair s z x y ∧ Bisimulation s (WithIdentity (CodedRelation s k)) ∧
        WithIdentity (CodedRelation s k) x y := by
  simp only [pairBehaviorWitnessFormula, Eval, eval_orderedPairFormula,
    eval_augmentedBisimFormula, eval_augmentedRelatedFormula]
  rfl

theorem collect_bounded_behavior_witnesses (base : BaseCollection s) (a : U) :
    ∃ k, Bisimulation s (WithIdentity (CodedRelation s k)) ∧
      ∀ x y, s x a → s y a → InternalBehavior s x y →
        WithIdentity (CodedRelation s k) x y := by
  obtain ⟨r, hr⟩ := relation_comprehension_members base
    (internalBehaviorFormula (n := 2) 1 0) Fin.elim0 a
  have hall : ∀ z, s z r → ∃ k, Eval s pairBehaviorWitnessFormula (cons k (cons z Fin.elim0)) := by
    intro z hz
    obtain ⟨x, y, _, _, hpair, hev⟩ := (hr z).mp hz
    obtain ⟨k, hk, hkxy⟩ := (eval_internalBehaviorFormula s 1 0 _).mp hev
    exact ⟨k, (eval_pairBehaviorWitnessFormula k z).mpr ⟨x, y, hpair, hk, hkxy⟩⟩
  obtain ⟨c, hc⟩ := base.collection 0 pairBehaviorWitnessFormula Fin.elim0 r hall
  obtain ⟨d, hd⟩ := base.separation 0 (augmentedBisimFormula 0) Fin.elim0 c
  have hdgood : ∀ k, s k d → Bisimulation s (WithIdentity (CodedRelation s k)) := by
    intro k hk
    exact (eval_augmentedBisimFormula s 0 _).mp ((hd k).mp hk).2
  obtain ⟨k, hk, hin⟩ := augmented_family_union base.union d hdgood
  refine ⟨k, hk, ?_⟩
  intro x y hx hy hxy
  obtain ⟨z, hz⟩ := orderedPair_exists base.pairing x y
  have hzr := (hr z).mpr ⟨x, y, hx, hy, hz, (eval_internalBehaviorFormula s 1 0 _).mpr hxy⟩
  obtain ⟨l, hlc, hl⟩ := hc z hzr
  obtain ⟨x', y', hz', hlB, hlxy⟩ := (eval_pairBehaviorWitnessFormula l z).mp hl
  obtain ⟨rfl, rfl⟩ := orderedPair_injective hz hz'
  exact hin l ((hd l).mpr ⟨hlc, (eval_augmentedBisimFormula s 0 _).mpr hlB⟩) x y hlxy

theorem internal_augmented_coinduction (base : BaseCollection s)
    (R : InternalQuotient base)
    (hR : Bisimulation (internalMember base) (WithIdentity (CodedRelation (internalMember base) R))) :
    ∀ X Y, WithIdentity (CodedRelation (internalMember base) R) X Y → X = Y := by
  let q := internalCode base
  let t := internalMember base
  obtain ⟨B, hB⟩ := relation_support_exists (internal_base_model base) R
  obtain ⟨d, hd⟩ := internal_code_onto base B
  obtain ⟨ud, hud⟩ := base.union d
  obtain ⟨a, ha⟩ := binary_union_exists base.pairing base.union d ud
  obtain ⟨k, hk, hke⟩ := collect_bounded_behavior_witnesses base a
  obtain ⟨D, m, hdD, hm, hkm⟩ := bounded_augmented_extension base d k hk
  have match_eq : ∀ u v, s u a → s v a → q u = q v → WithIdentity (CodedRelation s m) u v := by
    intro u v hu hv huv
    exact hkm u v (hke u v hu hv ((internal_code_eq base u v).mp huv))
  obtain ⟨r₀, hr₀⟩ := internal_code_onto base R
  change q r₀ = R at hr₀
  let p := behaviorTranslation (relatedFormula (n := 3) 2 1 0)
  obtain ⟨r, hrG, hr⟩ := normalized_relation_comprehension base p (cons r₀ Fin.elim0) d
  have hri : ∀ x y, CodedRelation s r x y ↔ s x d ∧ s y d ∧ CodedRelation t R (q x) (q y) := by
    intro x y
    have hev := uniform_behavior_translation base (relatedFormula (n := 3) 2 1 0)
      (cons y (cons x (cons r₀ Fin.elim0)))
    rw [eval_relatedFormula] at hev
    change Eval s p _ ↔ CodedRelation t (q r₀) (q x) (q y) at hev
    rw [hr₀] at hev
    exact (hr x y).trans (and_congr_right (fun _ => and_congr_right (fun _ => hev)))
  have hrd : GraphCode s D r := by
    intro z hz
    obtain ⟨x, y, hx, hy, hp⟩ := hrG z hz
    exact ⟨x, y, hdD x hx, hdD y hy, hp⟩
  have hmatch : ∀ u v, s u ud → s v ud →
      WithIdentity (CodedRelation t R) (q u) (q v) →
      (WithIdentity (CodedRelation s m) u v ∨ BisimSandwich s m r u v) := by
    intro u v hu hv huv
    rcases huv with heq | huv
    · exact Or.inl (match_eq u v ((ha u).mpr (Or.inr hu)) ((ha v).mpr (Or.inr hv)) heq)
    · have huB := (hB (q u)).mpr ⟨q v, Or.inl huv⟩
      have hvB := (hB (q v)).mpr ⟨q u, Or.inr huv⟩
      rw [← hd] at huB hvB
      obtain ⟨x, hx, hxu⟩ := (internal_exact_members base d (q u)).mp huB
      obtain ⟨y, hy, hyv⟩ := (internal_exact_members base d (q v)).mp hvB
      change q x = q u at hxu
      change q y = q v at hyv
      have hxy : CodedRelation t R (q x) (q y) := by rw [hxu, hyv]; exact huv
      exact Or.inr ⟨x, y,
        match_eq u x ((ha u).mpr (Or.inr hu)) ((ha x).mpr (Or.inl hx)) hxu.symm,
        (hri x y).mpr ⟨hx, hy, hxy⟩,
        match_eq y v ((ha y).mpr (Or.inl hy)) ((ha v).mpr (Or.inr hv)) hyv⟩
  have hstep : ∀ x y, CodedRelation s r x y →
      (∀ u, s u x → ∃ v, s v y ∧ (WithIdentity (CodedRelation s m) u v ∨ BisimSandwich s m r u v)) ∧
      (∀ v, s v y → ∃ u, s u x ∧ (WithIdentity (CodedRelation s m) u v ∨ BisimSandwich s m r u v)) := by
    intro x y hxy
    obtain ⟨hx, hy, hqxy⟩ := (hri x y).mp hxy
    constructor
    · intro u hu
      obtain ⟨V, hV, hUV⟩ := (hR (q x) (q y) (Or.inr hqxy)).1 (q u)
        ((internal_exact_members base x (q u)).mpr ⟨u, hu, rfl⟩)
      obtain ⟨v, hv, hvV⟩ := (internal_exact_members base y V).mp hV
      change q v = V at hvV
      rw [← hvV] at hUV
      exact ⟨v, hv, hmatch u v ((hud u).mpr ⟨x, hx, hu⟩) ((hud v).mpr ⟨y, hy, hv⟩) hUV⟩
    · intro v hv
      obtain ⟨X, hX, hXV⟩ := (hR (q x) (q y) (Or.inr hqxy)).2 (q v)
        ((internal_exact_members base y (q v)).mpr ⟨v, hv, rfl⟩)
      obtain ⟨u, hu, huX⟩ := (internal_exact_members base x X).mp hX
      change q u = X at huX
      rw [← huX] at hXV
      exact ⟨u, hu, hmatch u v ((hud u).mpr ⟨x, hx, hu⟩) ((hud v).mpr ⟨y, hy, hv⟩) hXV⟩
  have hsub := bounded_augmented_up_to base hm hrd hstep
  intro X Y hXY
  rcases hXY with hXY | hXY
  · exact hXY
  · have hXB := (hB X).mpr ⟨Y, Or.inl hXY⟩
    have hYB := (hB Y).mpr ⟨X, Or.inr hXY⟩
    rw [← hd] at hXB hYB
    obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hXB
    obtain ⟨y, hy, rfl⟩ := (internal_exact_members base d Y).mp hYB
    exact (internal_code_eq base x y).mpr ⟨m, hm.2.1,
      Or.inr (hsub x y ((hri x y).mpr ⟨hx, hy, hXY⟩))⟩

theorem quotient_internal_behavior_eq (base : BaseCollection s)
    (X Y : InternalQuotient base) : InternalBehavior (internalMember base) X Y ↔ X = Y := by
  constructor
  · rintro ⟨R, hR, hXY⟩
    exact internal_augmented_coinduction base R hR X Y hXY
  · rintro rfl
    exact internalBehavior_refl (internal_base_model base).empty X



theorem second_code_injective (base : BaseCollection s) {X Y : InternalQuotient base}
    (h : internalCode (internal_base_model base) X = internalCode (internal_base_model base) Y) : X = Y :=
  (quotient_internal_behavior_eq base X Y).mp
    ((internal_code_eq (internal_base_model base) X Y).mp h)

theorem second_code_membership (base : BaseCollection s) (X Y : InternalQuotient base) :
    internalMember (internal_base_model base)
      (internalCode (internal_base_model base) X) (internalCode (internal_base_model base) Y) ↔
        internalMember base X Y := by
  constructor
  · intro h
    obtain ⟨Z, hZ, heq⟩ := (internal_exact_members (internal_base_model base) Y _).mp h
    exact second_code_injective base heq ▸ hZ
  · intro h
    exact (internal_exact_members (internal_base_model base) Y _).mpr ⟨X, h, rfl⟩

/-- A semantic isomorphism preserves the actual syntax, without a truth predicate. -/
theorem bijective_membership_elementary {V : Type v} {t : V → V → Prop}
    (f : U → V) (hinj : ∀ x y, f x = f y → x = y) (honto : ∀ y, ∃ x, f x = y)
    (hmem : ∀ x y, s x y ↔ t (f x) (f y)) : ElementaryMap s t f := by
  intro n p e
  induction p with
  | equal i j => exact ⟨congrArg f, hinj (e i) (e j)⟩
  | member i j => exact hmem (e i) (e j)
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp e) (hq e)
  | impl p q hp hq => exact imp_congr (hp e) (hq e)
  | ex p hp =>
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨f x, ?_⟩
      simpa only [cons_map] using (hp (cons x e)).mp hx
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := honto y
      refine ⟨x, (hp (cons x e)).mpr ?_⟩
      simpa only [cons_map] using hy
  | all p hp =>
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := honto y
      simpa only [cons_map] using (hp (cons x e)).mp (h x)
    · intro h x
      apply (hp (cons x e)).mpr
      simpa only [cons_map] using h (f x)

theorem second_code_elementary (base : BaseCollection s) :
    ElementaryMap (internalMember base) (internalMember (internal_base_model base))
      (internalCode (internal_base_model base)) :=
  bijective_membership_elementary _ (fun _ _ h => second_code_injective base h)
    (internal_code_onto (internal_base_model base)) (fun X Y => (second_code_membership base X Y).symm)

/-- Canonical flattening Q(Q(M)) -> Q(M); no representatives are chosen. -/
def quotientFlatten (base : BaseCollection s) :
    InternalQuotient (internal_base_model base) → InternalQuotient base :=
  Quotient.lift (fun X => X) (fun X Y h => (quotient_internal_behavior_eq base X Y).mp h)

theorem quotient_flatten_code (base : BaseCollection s) (X : InternalQuotient base) :
    quotientFlatten base (internalCode (internal_base_model base) X) = X := rfl

theorem quotient_code_flatten (base : BaseCollection s) (Z : InternalQuotient (internal_base_model base)) :
    internalCode (internal_base_model base) (quotientFlatten base Z) = Z := by
  obtain ⟨X, rfl⟩ := internal_code_onto (internal_base_model base) Z
  rfl

theorem quotient_flatten_membership (base : BaseCollection s)
    (X Y : InternalQuotient (internal_base_model base)) :
    internalMember (internal_base_model base) X Y ↔
      internalMember base (quotientFlatten base X) (quotientFlatten base Y) := by
  obtain ⟨x, rfl⟩ := internal_code_onto (internal_base_model base) X
  obtain ⟨y, rfl⟩ := internal_code_onto (internal_base_model base) Y
  exact second_code_membership base x y

theorem quotient_flatten_elementary (base : BaseCollection s) :
    ElementaryMap (internalMember (internal_base_model base)) (internalMember base) (quotientFlatten base) := by
  apply bijective_membership_elementary
  · intro X Y h
    have h' := congrArg (internalCode (internal_base_model base)) h
    simpa only [quotient_code_flatten] using h'
  · intro X
    exact ⟨internalCode (internal_base_model base) X, rfl⟩
  · exact quotient_flatten_membership base

theorem behavior_translation_idempotent (base : BaseCollection s) {n} (p : Formula n) (e : Fin n → U) :
    Eval s (behaviorTranslation (behaviorTranslation p)) e ↔ Eval s (behaviorTranslation p) e := by
  exact (uniform_behavior_translation base (behaviorTranslation p) e).trans
    ((uniform_behavior_translation (internal_base_model base) p (fun i => internalCode base (e i))).trans
      (((second_code_elementary base) p (fun i => internalCode base (e i))).symm.trans
        (uniform_behavior_translation base p e).symm))

theorem quotient_flatten_natural {V : Type v} {t : V → V → Prop}
    (bs : BaseCollection s) (bt : BaseCollection t) (j : U → V) (hj : ElementaryMap s t j) :
    (fun Z => quotientFlatten bt
      (behaviorMap (internal_base_model bs) (internal_base_model bt)
        (behaviorMap bs bt j hj) (behavior_map_elementary bs bt j hj) Z)) =
    (fun Z => behaviorMap bs bt j hj (quotientFlatten bs Z)) := by
  funext Z
  obtain ⟨X, rfl⟩ := internal_code_onto (internal_base_model bs) Z
  rfl

#print axioms internal_augmented_coinduction
#print axioms behavior_translation_idempotent
#print axioms quotient_flatten_elementary
end FullBridge
