import CoveredMaskCoding
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop} {w : U} {J : InternalMask s w → U → U}

theorem covered_mask_function_iff (a f : CoveredMaskCarrier s w J) :
    FunctionCode (coveredMaskMember J) a f ↔ FunctionCode s a.val f.val := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro p hp
      let P : CoveredMaskCarrier s w J := ⟨p, internal_mask_covered_member f.property hp⟩
      obtain ⟨x, y, hx, hpxy⟩ := hf.1 P hp
      exact ⟨x.val, y.val, hx, (covered_mask_ordered_pair_iff P x y).mp hpxy⟩
    · intro x hx
      let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
      obtain ⟨Y, hXY, hu⟩ := hf.2 X hx
      refine ⟨Y.val, (covered_mask_coded_relation_iff f X Y).mp hXY, fun y hxy => ?_⟩
      let Y' : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components f.property hxy).2⟩
      exact congrArg Subtype.val (hu Y' ((covered_mask_coded_relation_iff f X Y').mpr hxy))
  · intro hf
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨x, y, hx, hpxy⟩ := hf.1 p.val hp
      let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
      let Y : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components f.property ⟨p.val, hp, hpxy⟩).2⟩
      exact ⟨X, Y, hx, (covered_mask_ordered_pair_iff p X Y).mpr hpxy⟩
    · intro x hx
      obtain ⟨y, hxy, hu⟩ := hf.2 x.val hx
      let Y : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components f.property hxy).2⟩
      exact ⟨Y, (covered_mask_coded_relation_iff f x Y).mpr hxy,
        fun Z hZ => Subtype.ext (hu Z.val ((covered_mask_coded_relation_iff f x Z).mp hZ))⟩

theorem covered_mask_graph_iff (a r : CoveredMaskCarrier s w J) :
    GraphCode (coveredMaskMember J) a r ↔ GraphCode s a.val r.val := by
  constructor
  · intro h p hp
    let P : CoveredMaskCarrier s w J := ⟨p, internal_mask_covered_member r.property hp⟩
    obtain ⟨x, y, hx, hy, hxy⟩ := h P hp
    exact ⟨x.val, y.val, hx, hy, (covered_mask_ordered_pair_iff P x y).mp hxy⟩
  · intro h p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := h p.val hp
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    let Y : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member a.property hy⟩
    exact ⟨X, Y, hx, hy, (covered_mask_ordered_pair_iff p X Y).mpr hxy⟩

theorem covered_mask_graph_extensional_iff (a r : CoveredMaskCarrier s w J) :
    GraphExtensionalCode (coveredMaskMember J) a r ↔ GraphExtensionalCode s a.val r.val := by
  constructor
  · intro h x hx y hy hrows
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    let Y : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member a.property hy⟩
    apply congrArg Subtype.val (h X hx Y hy ?_)
    intro Z hZ
    exact (covered_mask_coded_relation_iff r X Z).trans ((hrows Z.val hZ).trans (covered_mask_coded_relation_iff r Y Z).symm)
  · intro h x hx y hy hrows
    apply Subtype.ext (h x.val hx y.val hy ?_)
    intro z hz
    let Z : CoveredMaskCarrier s w J := ⟨z, internal_mask_covered_member a.property hz⟩
    exact (covered_mask_coded_relation_iff r x Z).symm.trans ((hrows Z hz).trans (covered_mask_coded_relation_iff r y Z))

theorem covered_mask_injective_iff (f : CoveredMaskCarrier s w J) :
    InjectiveCode (coveredMaskMember J) f ↔ InjectiveCode s f.val := by
  constructor
  · intro h x y z hx hy
    let X : CoveredMaskCarrier s w J := ⟨x, (covered_mask_relation_components f.property hx).1⟩
    let Y : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components f.property hy).1⟩
    let Z : CoveredMaskCarrier s w J := ⟨z, (covered_mask_relation_components f.property hx).2⟩
    exact congrArg Subtype.val (h X Y Z ((covered_mask_coded_relation_iff f X Z).mpr hx)
      ((covered_mask_coded_relation_iff f Y Z).mpr hy))
  · intro h x y z hx hy
    exact Subtype.ext (h x.val y.val z.val ((covered_mask_coded_relation_iff f x z).mp hx)
      ((covered_mask_coded_relation_iff f y z).mp hy))

theorem covered_mask_decoration_iff (a r f : CoveredMaskCarrier s w J) :
    DecorationCode (coveredMaskMember J) a r f ↔ DecorationCode s a.val r.val f.val := by
  constructor
  · intro hf
    refine ⟨(covered_mask_function_iff a f).mp hf.1, ?_⟩
    intro x hx X hxX Y
    let xH : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
    let XH : CoveredMaskCarrier s w J := ⟨X, (covered_mask_relation_components f.property hxX).2⟩
    constructor
    · intro hYX
      let YH : CoveredMaskCarrier s w J := ⟨Y, internal_mask_covered_member XH.property hYX⟩
      obtain ⟨y, hy, hxy, hyY⟩ := (hf.2 xH hx XH ((covered_mask_coded_relation_iff f xH XH).mpr hxX) YH).mp hYX
      exact ⟨y.val, hy, (covered_mask_coded_relation_iff r xH y).mp hxy, (covered_mask_coded_relation_iff f y YH).mp hyY⟩
    · rintro ⟨y, hy, hxy, hyY⟩
      let yH : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member a.property hy⟩
      let YH : CoveredMaskCarrier s w J := ⟨Y, (covered_mask_relation_components f.property hyY).2⟩
      exact (hf.2 xH hx XH ((covered_mask_coded_relation_iff f xH XH).mpr hxX) YH).mpr
        ⟨yH, hy, (covered_mask_coded_relation_iff r xH yH).mpr hxy, (covered_mask_coded_relation_iff f yH YH).mpr hyY⟩
  · intro hf
    refine ⟨(covered_mask_function_iff a f).mpr hf.1, ?_⟩
    intro x hx X hxX Y
    rw [covered_mask_coded_relation_iff] at hxX
    constructor
    · intro hYX
      obtain ⟨y, hy, hxy, hyY⟩ := (hf.2 x.val hx X.val hxX Y.val).mp hYX
      let yH : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member a.property hy⟩
      exact ⟨yH, hy, (covered_mask_coded_relation_iff r x yH).mpr hxy, (covered_mask_coded_relation_iff f yH Y).mpr hyY⟩
    · rintro ⟨y, hy, hxy, hyY⟩
      exact (hf.2 x.val hx X.val hxX Y.val).mpr
        ⟨y.val, hy, (covered_mask_coded_relation_iff r x y).mp hxy, (covered_mask_coded_relation_iff f y Y).mp hyY⟩

theorem covered_mask_transitive_iff (t : CoveredMaskCarrier s w J) :
    TransitiveCode (coveredMaskMember J) t ↔ TransitiveCode s t.val := by
  constructor
  · intro h x hx y hy
    let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member t.property hx⟩
    exact h X hx ⟨y, internal_mask_covered_member X.property hy⟩ hy
  · exact fun h x hx y hy => h x.val hx y.val hy

theorem covered_mask_range_iff (a f t : CoveredMaskCarrier s w J) :
    RangeCode (coveredMaskMember J) a f t ↔ RangeCode s a.val f.val t.val := by
  constructor
  · intro h y
    constructor
    · intro hy
      let Y : CoveredMaskCarrier s w J := ⟨y, internal_mask_covered_member t.property hy⟩
      obtain ⟨x, hx, hxy⟩ := (h Y).mp hy
      exact ⟨x.val, hx, (covered_mask_coded_relation_iff f x Y).mp hxy⟩
    · rintro ⟨x, hx, hxy⟩
      let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
      let Y : CoveredMaskCarrier s w J := ⟨y, (covered_mask_relation_components f.property hxy).2⟩
      exact (h Y).mpr ⟨X, hx, (covered_mask_coded_relation_iff f X Y).mpr hxy⟩
  · intro h y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := (h y.val).mp hy
      let X : CoveredMaskCarrier s w J := ⟨x, internal_mask_covered_member a.property hx⟩
      exact ⟨X, hx, (covered_mask_coded_relation_iff f X y).mpr hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact (h y.val).mpr ⟨x.val, hx, (covered_mask_coded_relation_iff f x y).mp hxy⟩


#print axioms covered_mask_decoration_iff
end FullBridge
