import MaskEquivariantFunctions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {w : U} {J : InternalMask s w → U → U}

theorem mask_function_iff (a f : MaskSupportedCarrier s w J) :
    FunctionCode (maskSupportedMember J) a f ↔ FunctionCode s a.val f.val := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro p hp
      let P : MaskSupportedCarrier s w J := ⟨p, hereditary_mask_member f.property hp⟩
      obtain ⟨x, y, hx, hpxy⟩ := hf.1 P hp
      exact ⟨x.val, y.val, hx, (mask_ordered_pair_iff P x y).mp hpxy⟩
    · intro x hx
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
      obtain ⟨Y, hXY, hu⟩ := hf.2 X hx
      refine ⟨Y.val, (mask_coded_relation_iff f X Y).mp hXY, fun y hxy => ?_⟩
      let Y' : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components f.property hxy).2⟩
      exact congrArg Subtype.val (hu Y' ((mask_coded_relation_iff f X Y').mpr hxy))
  · intro hf
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨x, y, hx, hpxy⟩ := hf.1 p.val hp
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
      let Y : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components f.property ⟨p.val, hp, hpxy⟩).2⟩
      exact ⟨X, Y, hx, (mask_ordered_pair_iff p X Y).mpr hpxy⟩
    · intro x hx
      obtain ⟨y, hxy, hu⟩ := hf.2 x.val hx
      let Y : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components f.property hxy).2⟩
      exact ⟨Y, (mask_coded_relation_iff f x Y).mpr hxy,
        fun Z hZ => Subtype.ext (hu Z.val ((mask_coded_relation_iff f x Z).mp hZ))⟩

theorem mask_graph_iff (a r : MaskSupportedCarrier s w J) :
    GraphCode (maskSupportedMember J) a r ↔ GraphCode s a.val r.val := by
  constructor
  · intro h p hp
    let P : MaskSupportedCarrier s w J := ⟨p, hereditary_mask_member r.property hp⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := h P hp
    exact ⟨x.val, y.val, hx, hy, (mask_ordered_pair_iff P x y).mp hxy⟩
  · intro h p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := h p.val hp
    let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
    let Y : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member a.property hy⟩
    exact ⟨X, Y, hx, hy, (mask_ordered_pair_iff p X Y).mpr hxy⟩

theorem mask_graph_extensional_iff (a r : MaskSupportedCarrier s w J) :
    GraphExtensionalCode (maskSupportedMember J) a r ↔ GraphExtensionalCode s a.val r.val := by
  constructor
  · intro h x hx y hy hrows
    let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
    let Y : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member a.property hy⟩
    apply congrArg Subtype.val (h X hx Y hy ?_)
    intro Z hZ
    exact (mask_coded_relation_iff r X Z).trans ((hrows Z.val hZ).trans (mask_coded_relation_iff r Y Z).symm)
  · intro h x hx y hy hrows
    apply Subtype.ext (h x.val hx y.val hy ?_)
    intro z hz
    let Z : MaskSupportedCarrier s w J := ⟨z, hereditary_mask_member a.property hz⟩
    exact (mask_coded_relation_iff r x Z).symm.trans ((hrows Z hz).trans (mask_coded_relation_iff r y Z))

theorem mask_injective_iff (f : MaskSupportedCarrier s w J) :
    InjectiveCode (maskSupportedMember J) f ↔ InjectiveCode s f.val := by
  constructor
  · intro h x y z hx hy
    let X : MaskSupportedCarrier s w J := ⟨x, (mask_relation_components f.property hx).1⟩
    let Y : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components f.property hy).1⟩
    let Z : MaskSupportedCarrier s w J := ⟨z, (mask_relation_components f.property hx).2⟩
    exact congrArg Subtype.val (h X Y Z ((mask_coded_relation_iff f X Z).mpr hx)
      ((mask_coded_relation_iff f Y Z).mpr hy))
  · intro h x y z hx hy
    exact Subtype.ext (h x.val y.val z.val ((mask_coded_relation_iff f x z).mp hx)
      ((mask_coded_relation_iff f y z).mp hy))

theorem mask_decoration_iff (a r f : MaskSupportedCarrier s w J) :
    DecorationCode (maskSupportedMember J) a r f ↔ DecorationCode s a.val r.val f.val := by
  constructor
  · intro hf
    refine ⟨(mask_function_iff a f).mp hf.1, ?_⟩
    intro x hx X hxX Y
    let xH : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
    let XH : MaskSupportedCarrier s w J := ⟨X, (mask_relation_components f.property hxX).2⟩
    constructor
    · intro hYX
      let YH : MaskSupportedCarrier s w J := ⟨Y, hereditary_mask_member XH.property hYX⟩
      obtain ⟨y, hy, hxy, hyY⟩ := (hf.2 xH hx XH ((mask_coded_relation_iff f xH XH).mpr hxX) YH).mp hYX
      exact ⟨y.val, hy, (mask_coded_relation_iff r xH y).mp hxy, (mask_coded_relation_iff f y YH).mp hyY⟩
    · rintro ⟨y, hy, hxy, hyY⟩
      let yH : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member a.property hy⟩
      let YH : MaskSupportedCarrier s w J := ⟨Y, (mask_relation_components f.property hyY).2⟩
      exact (hf.2 xH hx XH ((mask_coded_relation_iff f xH XH).mpr hxX) YH).mpr
        ⟨yH, hy, (mask_coded_relation_iff r xH yH).mpr hxy, (mask_coded_relation_iff f yH YH).mpr hyY⟩
  · intro hf
    refine ⟨(mask_function_iff a f).mpr hf.1, ?_⟩
    intro x hx X hxX Y
    rw [mask_coded_relation_iff] at hxX
    constructor
    · intro hYX
      obtain ⟨y, hy, hxy, hyY⟩ := (hf.2 x.val hx X.val hxX Y.val).mp hYX
      let yH : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member a.property hy⟩
      exact ⟨yH, hy, (mask_coded_relation_iff r x yH).mpr hxy, (mask_coded_relation_iff f yH Y).mpr hyY⟩
    · rintro ⟨y, hy, hxy, hyY⟩
      exact (hf.2 x.val hx X.val hxX Y.val).mpr
        ⟨y.val, hy, (mask_coded_relation_iff r x y).mp hxy, (mask_coded_relation_iff f y Y).mp hyY⟩

theorem mask_transitive_iff (t : MaskSupportedCarrier s w J) :
    TransitiveCode (maskSupportedMember J) t ↔ TransitiveCode s t.val := by
  constructor
  · intro h x hx y hy
    let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member t.property hx⟩
    exact h X hx ⟨y, hereditary_mask_member X.property hy⟩ hy
  · exact fun h x hx y hy => h x.val hx y.val hy

theorem mask_range_iff (a f t : MaskSupportedCarrier s w J) :
    RangeCode (maskSupportedMember J) a f t ↔ RangeCode s a.val f.val t.val := by
  constructor
  · intro h y
    constructor
    · intro hy
      let Y : MaskSupportedCarrier s w J := ⟨y, hereditary_mask_member t.property hy⟩
      obtain ⟨x, hx, hxy⟩ := (h Y).mp hy
      exact ⟨x.val, hx, (mask_coded_relation_iff f x Y).mp hxy⟩
    · rintro ⟨x, hx, hxy⟩
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
      let Y : MaskSupportedCarrier s w J := ⟨y, (mask_relation_components f.property hxy).2⟩
      exact (h Y).mpr ⟨X, hx, (mask_coded_relation_iff f X Y).mpr hxy⟩
  · intro h y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := (h y.val).mp hy
      let X : MaskSupportedCarrier s w J := ⟨x, hereditary_mask_member a.property hx⟩
      exact ⟨X, hx, (mask_coded_relation_iff f X y).mpr hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact (h y.val).mpr ⟨x.val, hx, (mask_coded_relation_iff f x y).mp hxy⟩

theorem hereditary_mask_function_range (base : BaseCollection s)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    {a f t : U} (hf : FunctionCode s a f) (hF : HereditarilyMaskSupported s w J f)
    (hr : RangeCode s a f t) : HereditarilyMaskSupported s w J t := by
  apply hereditary_mask_intro
  · obtain ⟨N, hN, hfix⟩ := hereditary_mask_root hF
    refine ⟨N, hN, fun i hi => elementary_involution_closed_set base (hj i) (hs i) ?_⟩
    intro y hy
    obtain ⟨x, _, hxy⟩ := (hr y).mp hy
    have h := (elementary_map_coded_relation (hj i) f x y).mp hxy
    rw [hfix i hi] at h
    exact (hr (J i y)).mpr ⟨J i x, coded_function_domain hf h, h⟩
  · intro y hy
    obtain ⟨x, _, hxy⟩ := (hr y).mp hy
    exact (mask_relation_components hF hxy).2

theorem mask_realization_transitive_range (base : BaseCollection s)
    (hj : ∀ i, ElementaryMap s s (J i)) (hs : ∀ i x, J i (J i x) = x)
    (a r f : MaskSupportedCarrier s w J) (hf : DecorationCode s a.val r.val f.val)
    (hi : InjectiveCode s f.val) :
    ∃ t : MaskSupportedCarrier s w J, TransitiveCode (maskSupportedMember J) t ∧
      DecorationCode (maskSupportedMember J) a r f ∧ InjectiveCode (maskSupportedMember J) f ∧
      RangeCode (maskSupportedMember J) a f t := by
  obtain ⟨t, ht, hr⟩ := decoration_transitive_range base hf
  let T : MaskSupportedCarrier s w J := ⟨t, hereditary_mask_function_range base hj hs hf.1 f.property hr⟩
  exact ⟨T, (mask_transitive_iff T).mpr ht, (mask_decoration_iff a r f).mpr hf,
    (mask_injective_iff f).mpr hi, (mask_range_iff a f T).mpr hr⟩

#print axioms mask_decoration_iff
#print axioms mask_realization_transitive_range
end FullBridge
