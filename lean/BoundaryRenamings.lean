import OrbitBoundaryCodes
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Retain a possibly noninjective boundary map and give fresh names elsewhere. -/
structure BoundaryRenaming (s : U → U → Prop) (D N b A : U) where
  domain : U
  code : U
  function : FunctionCode s N code
  range : RangeCode s N code domain
  extend : ∀ X x, CodedRelation s b X x → CodedRelation s code X x
  old : ∀ X x, CodedRelation s code X x → s x A → CodedRelation s b X x
  collision : ∀ X Y x, CodedRelation s code X x → CodedRelation s code Y x →
    X = Y ∨ (CodedRelation s b X x ∧ CodedRelation s b Y x)

theorem boundary_renaming_exists (base : BaseCollection s) {D N b A : U}
    (hb : FunctionCode s D b) (hDN : Subset s D N)
    (hOld : ∀ X x, CodedRelation s b X x → s x A) : Nonempty (BoundaryRenaming s D N b A) := by
  obtain ⟨c, hc⟩ := base.separation 1 (.impl (.member 0 1) .bottom) (cons D Fin.elim0) N
  have hc' : ∀ X, s X c ↔ s X N ∧ ¬s X D := hc
  obtain ⟨fresh, f, hf, hfi, hfr, hdis⟩ := fresh_parameter_copy base c A
  obtain ⟨k, hkm, hkr⟩ := coded_relation_union base b f
  have hk : FunctionCode s N k := by
    constructor
    · intro q hq
      rcases (hkm q).mp hq with hq | hq
      · obtain ⟨X, x, hX, hpair⟩ := hb.1 q hq
        exact ⟨X, x, hDN X hX, hpair⟩
      · obtain ⟨X, x, hX, hpair⟩ := hf.1 q hq
        exact ⟨X, x, ((hc' X).mp hX).1, hpair⟩
    · intro X hX
      by_cases hXD : s X D
      · obtain ⟨x, hXx, hu⟩ := hb.2 X hXD
        refine ⟨x, (hkr X x).mpr (Or.inl hXx), ?_⟩
        intro y hXy
        rcases (hkr X y).mp hXy with h | h
        · exact hu y h
        · exact False.elim (((hc' X).mp (coded_function_domain hf h)).2 hXD)
      · obtain ⟨x, hXx, hu⟩ := hf.2 X ((hc' X).mpr ⟨hX, hXD⟩)
        refine ⟨x, (hkr X x).mpr (Or.inr hXx), ?_⟩
        intro y hXy
        rcases (hkr X y).mp hXy with h | h
        · exact False.elim (hXD (coded_function_domain hb h))
        · exact hu y h
  obtain ⟨B, hB⟩ := coded_image_set_exists base k N
  have hsep : ∀ X Y x, CodedRelation s b X x → CodedRelation s f Y x → False := by
    intro X Y x hX hY
    exact hdis x ((hfr x).mpr ⟨Y, coded_function_domain hf hY, hY⟩) (hOld X x hX)
  refine ⟨⟨B, k, hk, hB, fun X x h => (hkr X x).mpr (Or.inl h), ?_, ?_⟩⟩
  · intro X x hXx hxA
    rcases (hkr X x).mp hXx with h | h
    · exact h
    · exact False.elim (hdis x ((hfr x).mpr ⟨X, coded_function_domain hf h, h⟩) hxA)
  · intro X Y x hXx hYx
    rcases (hkr X x).mp hXx with hX | hX <;> rcases (hkr Y x).mp hYx with hY | hY
    · exact Or.inr ⟨hX, hY⟩
    · exact False.elim (hsep X Y x hX hY)
    · exact False.elim (hsep Y X x hY hX)
    · exact Or.inl (hfi X Y x hX hY)

theorem boundary_renaming_on_boundary {D N b A : U} (K : BoundaryRenaming s D N b A)
    (hb : FunctionCode s D b) {X x : U} (hX : s X D)
    (hXx : CodedRelation s K.code X x) : CodedRelation s b X x := by
  obtain ⟨y, hXy, _⟩ := hb.2 X hX
  have hxy := coded_function_value_unique K.function hXx (K.extend X y hXy)
  exact hxy.symm ▸ hXy

theorem orbit_boundary_renaming_component_injective (base : BaseCollection s) {O N E p a r A : U}
    (B : OrbitBoundary s O N E) (C : OrbitDiagramComponent s N E p a r)
    (K : BoundaryRenaming s B.domain N B.code A) :
    ∀ X Y x, s X C.domain → s Y C.domain → CodedRelation s K.code X x →
      CodedRelation s K.code Y x → X = Y := by
  intro X Y x hX hY hXx hYx
  rcases K.collision X Y x hXx hYx with h | ⟨hXb, hYb⟩
  · exact h
  · obtain ⟨u, _, huX⟩ := (C.range X).mp hX
    obtain ⟨v, _, hvY⟩ := (C.range Y).mp hY
    obtain ⟨_, _, _, _, _, _, _, hpairX⟩ := (B.values X x).mp hXb
    obtain ⟨_, _, _, _, _, _, _, hpairY⟩ := (B.values Y x).mp hYb
    have hux := (orderedPair_injective ((C.values u X).mp huX).2 hpairX).2
    have hvx := (orderedPair_injective ((C.values v Y).mp hvY).2 hpairY).2
    apply orderedPair_unique base.extensional
      ((C.values u X).mp huX).2
    rw [hux.trans hvx.symm]
    exact ((C.values v Y).mp hvY).2

#print axioms boundary_renaming_exists
end FullBridge
