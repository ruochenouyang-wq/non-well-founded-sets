import JointMaskPowers
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def maskDisjointFormula {n} (a N : Fin n) : Formula n :=
  .all (.impl (.member 0 a.succ) (.impl (.member 0 N.succ) .bottom))

def maskFixesSubsetFormula {n} (k a L : Fin n) : Formula n :=
  .all (.impl (relatedFormula k.succ a.succ 0) (codedImageSetFormula 0 L.succ L.succ))

def jointTailSupportFormula {n} (w G k L : Fin n) : Formula n :=
  .ex (.conj (.member 0 w.succ) (.all (.impl (.member 0 G.succ.succ)
    (.impl (maskDisjointFormula 0 1) (maskFixesSubsetFormula k.succ.succ 0 L.succ.succ)))))

def JointTailSupport (s : U → U → Prop) (w G k L : U) : Prop :=
  ∃ N, s N w ∧ ∀ a, s a G → (∀ i, s i a → ¬s i N) →
    ∀ f, CodedRelation s k a f → CodedImageSet s f L L

theorem eval_jointTailSupportFormula {n} (w G k L : Fin n) (v : Fin n → U) :
    Eval s (jointTailSupportFormula w G k L) v ↔ JointTailSupport s (v w) (v G) (v k) (v L) := by
  simp only [jointTailSupportFormula, maskDisjointFormula, maskFixesSubsetFormula, Eval,
    eval_relatedFormula, eval_codedImageSetFormula, cons_succ, JointTailSupport]
  rfl

theorem joint_tail_support_iff (base : BaseCollection s) {w t L : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hL : Subset s L t) : JointTailSupport s w A.masks A.family L ↔ MaskTailSupported s w J L := by
  constructor
  · rintro ⟨N, hN, hfix⟩
    refine ⟨N, hN, fun a hdis => ?_⟩
    obtain ⟨f, haf, _, hf⟩ := joint_mask_graph_exists A a
    exact ((elementary_coded_image base (hj a) (ho a) hf hL).mp
      (hfix a.val ((A.maskMembers a.val).mpr a.property) hdis f haf)).symm
  · rintro ⟨N, hN, hfix⟩
    refine ⟨N, hN, fun a ha hdis f haf => ?_⟩
    let M : InternalMask s w := ⟨a, (A.maskMembers a).mp ha⟩
    exact (elementary_coded_image base (hj M) (ho M) (A.graphs M f haf).2 hL).mpr
      (hfix M hdis).symm

/-- Exact hereditary powerset traces exist for every hereditary object
    whose members lie in a jointly coded domain. -/
theorem joint_mask_power_trace_exists (base : BaseCollection s) {w t d : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hD : HereditarilyMaskSupported s w J d) (hdt : Subset s d t) :
    ∃ p, ∀ L, s L p ↔ HereditarilyMaskSupported s w J L ∧ Subset s L d := by
  obtain ⟨q, hq⟩ := base.powerset d
  obtain ⟨p, hp⟩ := base.separation 3 (jointTailSupportFormula 1 2 3 0)
    (cons w (cons A.masks (cons A.family Fin.elim0))) q
  have hp' : ∀ L, s L p ↔ Subset s L d ∧ JointTailSupport s w A.masks A.family L := fun L =>
    (hp L).trans (and_congr (hq L) (eval_jointTailSupportFormula 1 2 3 0 _))
  refine ⟨p, fun L => ?_⟩
  constructor
  · intro h
    obtain ⟨hLd, hroot⟩ := (hp' L).mp h
    have hLt : Subset s L t := fun x hx => hdt x (hLd x hx)
    exact ⟨hereditary_mask_intro ((joint_tail_support_iff base A hj ho hLt).mp hroot)
      (fun x hx => hereditary_mask_member hD (hLd x hx)), hLd⟩
  · rintro ⟨hH, hLd⟩
    exact (hp' L).mpr ⟨hLd, (joint_tail_support_iff base A hj ho
      (fun x hx => hdt x (hLd x hx))).mpr (hereditary_mask_root hH)⟩

theorem joint_mask_relative_power (base : BaseCollection s) {w t : U}
    {J : InternalMask s w → U → U} (A : JointMaskDomain s w J t)
    (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    (d : MaskSupportedCarrier s w J) (hdt : Subset s d.val t) :
    ∃ p : MaskSupportedCarrier s w J,
      (∀ L, s L p.val ↔ HereditarilyMaskSupported s w J L ∧ Subset s L d.val) ∧
      (∀ x, maskSupportedMember J x p ↔ Subset (maskSupportedMember J) x d) := by
  obtain ⟨p, hp⟩ := joint_mask_power_trace_exists base A hj (fun a y => ⟨J a y, hs a y⟩) d.property hdt
  refine ⟨⟨p, mask_power_trace_hereditary base hj hc hs d.property hp⟩, hp, fun x => ?_⟩
  exact (hp x.val).trans ⟨fun h => (mask_carrier_subset_iff x d).mpr h.2,
    fun h => ⟨x.property, (mask_carrier_subset_iff x d).mp h⟩⟩

/-- A sufficient global cover condition. This theorem does not assert that
    arbitrary globally constructed actions have these joint codes. -/
theorem mask_carrier_power_of_joint_covers (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    (hcover : ∀ d : MaskSupportedCarrier s w J,
      ∃ t, Nonempty (JointMaskDomain s w J t) ∧ Subset s d.val t) :
    PowerSet (maskSupportedMember J) := by
  intro d
  obtain ⟨t, ⟨A⟩, hdt⟩ := hcover d
  obtain ⟨p, _, hp⟩ := joint_mask_relative_power base A hj hc hs d hdt
  exact ⟨p, hp⟩
end FullBridge
