import MaskSupportedLabels
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem elementary_map_subset {j : U → U} (hj : ElementaryMap s s j) (x d : U) :
    Subset s x d ↔ Subset s (j x) (j d) :=
  hj (.all (.impl (.member (n := 3) 0 1) (.member 0 2))) (cons x (cons d Fin.elim0))

def MaskSupportedPowerTraces (s : U → U → Prop) (w : U) (J : InternalMask s w → U → U) : Prop :=
  ∀ a : MaskSupportedCarrier s w J, ∃ p, ∀ x,
    s x p ↔ HereditarilyMaskSupported s w J x ∧ Subset s x a.val

theorem mask_power_trace_hereditary (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    {d p : U} (hd : HereditarilyMaskSupported s w J d)
    (hp : ∀ x, s x p ↔ HereditarilyMaskSupported s w J x ∧ Subset s x d) :
    HereditarilyMaskSupported s w J p := by
  apply hereditary_mask_intro
  · obtain ⟨N, hN, hfix⟩ := hereditary_mask_root hd
    refine ⟨N, hN, fun a ha => ?_⟩
    apply elementary_involution_closed_set base (hj a) (hs a)
    intro x hx
    obtain ⟨hH, hsub⟩ := (hp x).mp hx
    apply (hp (J a x)).mpr
    refine ⟨(hereditary_mask_invariant hj hc hs a x).mpr hH, ?_⟩
    have h := (elementary_map_subset (hj a) x d).mp hsub
    simpa only [hfix a ha] using h
  · exact fun x hx => ((hp x).mp hx).1

theorem mask_carrier_power_iff_traces (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (hj : ∀ a, ElementaryMap s s (J a))
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x) :
    PowerSet (maskSupportedMember J) ↔ MaskSupportedPowerTraces s w J := by
  constructor
  · intro h a
    obtain ⟨p, hp⟩ := h a
    refine ⟨p.val, fun x => ?_⟩
    constructor
    · intro hx
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member p.property hx⟩
      exact ⟨X.property, (mask_carrier_subset_iff X a).mp ((hp X).mp hx)⟩
    · rintro ⟨hH, hsub⟩
      exact (hp ⟨x, hH⟩).mpr ((mask_carrier_subset_iff _ a).mpr hsub)
  · intro h a
    obtain ⟨p, hp⟩ := h a
    refine ⟨⟨p, mask_power_trace_hereditary base hj hc hs a.property hp⟩, fun X => ?_⟩
    exact (hp X.val).trans ⟨fun h => (mask_carrier_subset_iff X a).mpr h.2,
      fun h => ⟨X.property, (mask_carrier_subset_iff X a).mp h⟩⟩

/-- The previously collected internal formula trace is the actual relative
    powerset of the whole label domain in the new hereditary carrier. -/
theorem mask_label_domain_relative_power (base : BaseCollection s) {z w d : U}
    (hw : OmegaCode s z w) (P : InternalQuinePairs s w) (J : InternalMask s w → U → U)
    (hj : ∀ a, ElementaryMap s s (J a)) (ho : ∀ a y, ∃ x, J a x = y)
    (hc : ∀ a b x, J a (J b x) = J b (J a x)) (hs : ∀ a x, J a (J a x) = x)
    (hcore : ∀ a x, (∃ c, s c P.family ∧ s x c) → J a x = maskedLabelAction P a.val x)
    (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c) :
    ∃ hD : HereditarilyMaskSupported s w J d, ∃ p : MaskSupportedCarrier s w J,
      (∀ x : MaskSupportedCarrier s w J, maskSupportedMember J x p ↔
        Subset (maskSupportedMember J) x ⟨d, hD⟩) ∧
      (∀ L, s L p.val ↔ Subset s L d ∧ InternallyBoundedRowSupport s w P.leftCode P.rightCode L) := by
  have hD := hereditary_mask_union base hj ho (hereditary_mask_family base hw P J hj ho hcore) hd
  obtain ⟨p, hp⟩ := internally_supported_subsets_exist base w P.leftCode P.rightCode d
  have htrace : ∀ L, s L p ↔ HereditarilyMaskSupported s w J L ∧ Subset s L d := by
    intro L
    constructor
    · intro h
      obtain ⟨hsub, hbal⟩ := (hp L).mp h
      exact ⟨(mask_label_subset_exact_formula base hw P J hj hs hcore hd hsub).mpr hbal, hsub⟩
    · rintro ⟨hH, hsub⟩
      exact (hp L).mpr ⟨hsub, (mask_label_subset_exact_formula base hw P J hj hs hcore hd hsub).mp hH⟩
  have hP := mask_power_trace_hereditary base hj hc hs hD htrace
  refine ⟨hD, ⟨p, hP⟩, ?_, hp⟩
  intro X
  exact (htrace X.val).trans ⟨fun h => (mask_carrier_subset_iff X ⟨d, hD⟩).mpr h.2,
    fun h => ⟨X.property, (mask_carrier_subset_iff X ⟨d, hD⟩).mp h⟩⟩
end FullBridge
