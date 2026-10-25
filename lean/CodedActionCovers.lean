import CodedMaskEmbeddings
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def ActionPointSupported (base : BaseCollection s) {w : U} (A : CodedMaskAction base w) (x : U) : Prop :=
  ∃ N, s N w ∧ ∀ i, TailMask s N i → CodedRelation s (A.maps i) x x

def ActionCovered (base : BaseCollection s) {w : U} (A : CodedMaskAction base w) (x : U) : Prop :=
  ∃ c, Subset s c A.domain ∧ TransitiveCode s c ∧ s x c ∧
    ∀ y, s y c → ActionPointSupported base A y

def JointPointSupport (s : U → U → Prop) (w G K x : U) : Prop :=
  ∃ N, s N w ∧ ∀ i, s i G → (∀ k, s k i → ¬s k N) →
    ∃ f, CodedRelation s K i f ∧ CodedRelation s f x x

def actionPointSupportFormula {n} (w G K x : Fin n) : Formula n :=
  .ex (.conj (.member 0 w.succ) (.all (.impl (.member 0 G.succ.succ)
    (.impl (maskDisjointFormula 0 1) (jointMaskPointFormula K.succ.succ 0 x.succ.succ x.succ.succ)))))

theorem eval_actionPointSupportFormula {n} (w G K x : Fin n) (v : Fin n → U) :
    Eval s (actionPointSupportFormula w G K x) v ↔ JointPointSupport s (v w) (v G) (v K) (v x) := by
  simp only [actionPointSupportFormula, maskDisjointFormula, Eval, eval_jointMaskPointFormula, JointPointSupport, cons_succ]
  rfl

theorem joint_point_support_action (base : BaseCollection s) {w x : U} (A : CodedMaskAction base w) :
    JointPointSupport s w A.masks A.family x ↔ ActionPointSupported base A x := by
  constructor
  · rintro ⟨N, hN, h⟩
    refine ⟨N, hN, fun i hi => ?_⟩
    obtain ⟨f, hif, hxx⟩ := h i.val ((A.maskMembers i.val).mpr i.property) hi
    exact (coded_function_value_unique A.familyFunction hif (A.mapCodes i)) ▸ hxx
  · rintro ⟨N, hN, h⟩
    refine ⟨N, hN, fun i hi hd => ?_⟩
    let I : InternalMask s w := ⟨i, (A.maskMembers i).mp hi⟩
    exact ⟨A.maps I, A.mapCodes I, h I hd⟩

def actionCoveredFormula {n} (w G K D x : Fin n) : Formula n :=
  .ex (.conj (powerSubsetFormula 0 D.succ) (.conj (transitiveFormula 0)
    (.conj (.member x.succ 0) (.all (.impl (.member 0 1)
      (actionPointSupportFormula w.succ.succ G.succ.succ K.succ.succ 0))))))

theorem eval_actionCoveredFormula (base : BaseCollection s) {w x : U} (A : CodedMaskAction base w) :
    Eval s (actionCoveredFormula (n := 5) 1 2 3 4 0)
      (cons x (cons w (cons A.masks (cons A.family (cons A.domain Fin.elim0))))) ↔
      ActionCovered base A x := by
  simp only [actionCoveredFormula, Eval, eval_powerSubsetFormula, eval_transitiveFormula,
    eval_actionPointSupportFormula]
  change (∃ c, Subset s c A.domain ∧ TransitiveCode s c ∧ s x c ∧
    ∀ y, s y c → JointPointSupport s w A.masks A.family y) ↔ ActionCovered base A x
  exact exists_congr (fun c => and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' (fun y => imp_congr Iff.rfl (joint_point_support_action base A))))))

/-- The actual source formula describes global internal coverage on any
    transitive domain whose complete action is coded by A. -/
theorem action_covered_iff_global (base : BaseCollection s) {w x : U}
    (A : CodedMaskAction base w) {J : InternalMask s w → U → U}
    (hJ : ∀ i y Y, CodedRelation s (A.maps i) y Y ↔ s y A.domain ∧ J i y = Y)
    (hx : s x A.domain) : ActionCovered base A x ↔ InternalMaskCovered s w J x := by
  constructor
  · rintro ⟨c, _, hct, hxc, hr⟩
    refine ⟨c, hct, hxc, fun y hy => ?_⟩
    obtain ⟨N, hN, hfix⟩ := hr y hy
    exact ⟨N, hN, fun i hi => ((hJ i y y).mp (hfix i hi)).2⟩
  · intro h
    obtain ⟨c, hcA, hct, hxc, hr⟩ := internal_mask_cover_restrict base A.transitive hx h
    refine ⟨c, hcA, hct, hxc, fun y hy => ?_⟩
    obtain ⟨N, hN, hfix⟩ := hr y hy
    exact ⟨N, hN, fun i hi => (hJ i y y).mpr ⟨hcA y hy, hfix i hi⟩⟩

theorem coded_mask_embedding_support_iff (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hx : CodedRelation s f x X) : ActionPointSupported base A x ↔ ActionPointSupported base B X := by
  exact exists_congr (fun N => and_congr Iff.rfl (forall_congr' (fun i => imp_congr Iff.rfl
    (coded_mask_embedding_action_iff base E i hx hx))))

theorem coded_mask_embedding_cover_forward (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hx : CodedRelation s f x X) (h : ActionCovered base A x) : ActionCovered base B X := by
  obtain ⟨c, hcA, hct, hxc, hr⟩ := h
  obtain ⟨d, hd⟩ := coded_image_set_exists base f c
  have hdB : Subset s d B.domain := by
    intro Y hY
    obtain ⟨y, _, hyY⟩ := (hd Y).mp hY
    exact coded_mask_embedding_value base E hyY
  refine ⟨d, hdB, ?_, (hd X).mpr ⟨x, hxc, hx⟩, ?_⟩
  · intro Y hY Z hZY
    obtain ⟨y, hyc, hyY⟩ := (hd Y).mp hY
    have hYr := (E.iso.2.2.1 Y).mpr ⟨y, hcA y hyc, hyY⟩
    obtain ⟨z, _, hzZ⟩ := (E.iso.2.2.1 Z).mp (E.transitive Y hYr Z hZY)
    exact (hd Z).mpr ⟨z, hct y hyc z ((E.iso.2.2.2 y z Y Z hyY hzZ).mpr hZY), hzZ⟩
  · intro Y hY
    obtain ⟨y, hyc, hyY⟩ := (hd Y).mp hY
    exact (coded_mask_embedding_support_iff base E hyY).mp (hr y hyc)

theorem coded_mask_embedding_cover_reflects (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hx : CodedRelation s f x X) (h : ActionCovered base B X) : ActionCovered base A x := by
  obtain ⟨d, _, hdt, hXd, hr⟩ := h
  obtain ⟨c, hc⟩ := base.separation 2
    (.ex (.conj (.member 0 2) (relatedFormula (n := 4) 3 1 0)))
    (cons d (cons f Fin.elim0)) A.domain
  have hmem : ∀ y, s y c ↔ s y A.domain ∧ ∃ Y, s Y d ∧ CodedRelation s f y Y := by
    intro y
    have hh := hc y
    simp only [Eval, eval_relatedFormula] at hh
    exact hh
  refine ⟨c, fun y hy => ((hmem y).mp hy).1, ?_,
    (hmem x).mpr ⟨coded_function_domain E.iso.1 hx, X, hXd, hx⟩, ?_⟩
  · intro y hy z hzy
    obtain ⟨hyA, Y, hYd, hyY⟩ := (hmem y).mp hy
    have hzA := A.transitive y hyA z hzy
    obtain ⟨Z, hzZ, _⟩ := E.iso.1.2 z hzA
    exact (hmem z).mpr ⟨hzA, Z, hdt Y hYd Z ((E.iso.2.2.2 y z Y Z hyY hzZ).mp hzy), hzZ⟩
  · intro y hy
    obtain ⟨_, Y, hYd, hyY⟩ := (hmem y).mp hy
    exact (coded_mask_embedding_support_iff base E hyY).mpr (hr Y hYd)

theorem coded_mask_embedding_cover_iff (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (hx : CodedRelation s f x X) : ActionCovered base A x ↔ ActionCovered base B X :=
  ⟨coded_mask_embedding_cover_forward base E hx, coded_mask_embedding_cover_reflects base E hx⟩

#print axioms coded_mask_embedding_cover_iff
#print axioms action_covered_iff_global
end FullBridge
