import LocalChoiceLoss
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

-- The set-sized fixed-part graph-solvability condition; no injectivity is required.
def FixedGraphSolvabilityCode (s : U → U → Prop) : Prop :=
  ∀ t, TransitiveCode s t → ∀ a e, GraphCode s a e → EndExtensionCode s a e t →
    ∃ f, DecorationCode s a e f ∧ ∀ x, s x t → CodedRelation s f x x

def fixedGraphSolvabilitySentence : Formula 0 :=
  .all (.impl (transitiveFormula 0)
    (.all (.all (.impl (graphCodeFormula 1 0)
      (.impl (endExtensionFormula 1 0 2)
        (.ex (.conj (decorationCodeFormula 2 1 0)
          (.all (.impl (.member 0 4) (relatedFormula 1 0 0))))))))))

theorem eval_fixedGraphSolvabilitySentence (s : U → U → Prop) :
    Eval s fixedGraphSolvabilitySentence Fin.elim0 ↔ FixedGraphSolvabilityCode s := by
  simp only [fixedGraphSolvabilitySentence, Eval, eval_transitiveFormula,
    eval_graphCodeFormula, eval_endExtensionFormula, eval_decorationCodeFormula,
    eval_relatedFormula, FixedGraphSolvabilityCode]
  rfl

theorem fixed_solvability_implies_solvability (base : BaseCollection s)
    (hFixed : FixedGraphSolvabilityCode s) : GraphSolvabilityCode s := by
  obtain ⟨t, ht⟩ := base.empty
  intro a e hG
  have hT : TransitiveCode s t := fun x hx => False.elim (ht x hx)
  obtain ⟨f, hf, _⟩ := hFixed t hT a e hG
    ⟨fun x hx => False.elim (ht x hx), fun x hx => False.elim (ht x hx)⟩
  exact ⟨f, hf⟩

-- Restrict an actual encoded function by separating its ordered pairs.
theorem function_domain_restriction (base : BaseCollection s) {a f t : U}
    (hf : FunctionCode s a f) (hta : Subset s t a) :
    ∃ g, FunctionCode s t g ∧
      ∀ x y, CodedRelation s g x y ↔ s x t ∧ CodedRelation s f x y := by
  obtain ⟨g, hg⟩ := base.separation 1
    (Formula.ex (.ex (.conj (.member 1 3) (orderedPairFormula 2 1 0))))
    (cons t Fin.elim0) f
  have hm : ∀ p, s p g ↔ s p f ∧ ∃ x y, s x t ∧ IsOrderedPair s p x y := by
    intro p
    have h := hg p
    simp only [Eval, eval_orderedPairFormula] at h
    exact h
  have hr : ∀ x y, CodedRelation s g x y ↔ s x t ∧ CodedRelation s f x y := by
    intro x y
    constructor
    · rintro ⟨p, hp, hpxy⟩
      obtain ⟨hpf, x', y', hx', hp'⟩ := (hm p).mp hp
      obtain ⟨rfl, rfl⟩ := orderedPair_injective hpxy hp'
      exact ⟨hx', p, hpf, hp'⟩
    · rintro ⟨hx, p, hp, hpxy⟩
      exact ⟨p, (hm p).mpr ⟨hp, x, y, hx, hpxy⟩, hpxy⟩
  refine ⟨g, ⟨?_, ?_⟩, hr⟩
  · intro p hp
    exact ((hm p).mp hp).2
  · intro x hx
    obtain ⟨y, hxy, hu⟩ := hf.2 x (hta x hx)
    exact ⟨y, (hr x y).mpr ⟨hx, hxy⟩, fun z hz => hu z ((hr x z).mp hz).2⟩

theorem membership_graph_identity_decoration (base : BaseCollection s) {t : U}
    (ht : TransitiveCode s t) :
    ∃ e i, GraphCode s t e ∧ DecorationCode s t e i ∧
      (∀ x y, CodedRelation s e x y ↔ s x t ∧ s y x) ∧
      (∀ x y, CodedRelation s i x y ↔ s x t ∧ y = x) := by
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base
    (Formula.member (n := 2) 0 1) Fin.elim0 t
  have her : ∀ x y, CodedRelation s e x y ↔ s x t ∧ s y x := by
    intro x y
    have h := he x y
    change CodedRelation s e x y ↔ s x t ∧ s y t ∧ s y x at h
    exact h.trans ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ht x h.1 y h.2, h.2⟩⟩
  obtain ⟨i, hiG, hi⟩ := normalized_relation_comprehension base
    (Formula.equal (n := 2) 0 1) Fin.elim0 t
  have hir : ∀ x y, CodedRelation s i x y ↔ s x t ∧ y = x := by
    intro x y
    have h := hi x y
    change CodedRelation s i x y ↔ s x t ∧ s y t ∧ y = x at h
    refine h.trans ⟨fun h => ⟨h.1, h.2.2⟩, ?_⟩
    rintro ⟨hx, rfl⟩
    exact ⟨hx, hx, rfl⟩
  refine ⟨e, i, heG, ⟨⟨?_, ?_⟩, ?_⟩, her, hir⟩
  · intro p hp
    obtain ⟨x, y, hx, _, hxy⟩ := hiG p hp
    exact ⟨x, y, hx, hxy⟩
  · intro x hx
    exact ⟨x, (hir x x).mpr ⟨hx, rfl⟩, fun y hy => ((hir x y).mp hy).2⟩
  · intro x hx v hxv w
    have hv := ((hir x v).mp hxv).2
    subst v
    constructor
    · intro hw
      have hwt := ht x hx w hw
      exact ⟨w, hwt, (her x w).mpr ⟨hx, hw⟩, (hir w w).mpr ⟨hwt, rfl⟩⟩
    · rintro ⟨y, _, hxy, hyw⟩
      have hwy := ((hir y w).mp hyw).2
      exact hwy.symm ▸ ((her x y).mp hxy).2

theorem afa_fixed_graph_solvability (base : BaseCollection s)
    (hAFA : AFACode s) : FixedGraphSolvabilityCode s := by
  intro t ht a e hG hend
  obtain ⟨f, hf, _⟩ := hAFA a e hG
  obtain ⟨g, hg, hgr⟩ := function_domain_restriction base hf.1 hend.1
  obtain ⟨et, i, hetG, hi, hetr, hir⟩ := membership_graph_identity_decoration base ht
  have hgd : DecorationCode s t et g := by
    refine ⟨hg, ?_⟩
    intro x hx v hxv w
    have hfxv := ((hgr x v).mp hxv).2
    rw [hf.2 x (hend.1 x hx) v hfxv w]
    constructor
    · rintro ⟨y, _, hexy, hfyw⟩
      have hyx := (hend.2 x hx y).mp hexy
      have hyt := ht x hx y hyx
      exact ⟨y, hyt, (hetr x y).mpr ⟨hx, hyx⟩, (hgr y w).mpr ⟨hyt, hfyw⟩⟩
    · rintro ⟨y, hy, hetxy, hgyw⟩
      exact ⟨y, hend.1 y hy, (hend.2 x hx y).mpr ((hetr x y).mp hetxy).2,
        ((hgr y w).mp hgyw).2⟩
  obtain ⟨k, _, hu⟩ := hAFA t et hetG
  have hgi : g = i := (hu g hgd).trans (hu i hi).symm
  refine ⟨f, hf, ?_⟩
  intro x hx
  have hix := (hir x x).mpr ⟨hx, rfl⟩
  rw [← hgi] at hix
  exact ((hgr x x).mp hix).2

theorem fixed_solutions_parameter_extension (base : BaseCollection s)
    (hFixed : FixedGraphSolvabilityCode s)
    {t : U} (ht : TransitiveCode s t) (hti : ParameterInjective base t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    ∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧ ParameterInjective base T := by
  obtain ⟨a, e, haB, heG, hext, hend, hai, he⟩ := relative_graph_lift_from_solutions base (fixed_solvability_implies_solvability base hFixed) ht hti B hB htB
  obtain ⟨f, hf, hfix⟩ := hFixed t ht a e heG hend
  obtain ⟨T, hT, hrange⟩ := decoration_transitive_range base hf
  have hA : TransitiveCode (internalMember base) (internalCode base a) := haB.symm ▸ hB
  have hcode := relative_decoration_code base hA he hf
  refine ⟨T, hT, ?_, ?_, ?_⟩
  · intro x hx
    exact (hrange x).mpr ⟨x, hend.1 x hx, hfix x hx⟩
  · apply internal_extensional base
    intro X
    constructor
    · intro hX
      obtain ⟨v, hv, hvX⟩ := (internal_exact_members base T X).mp hX
      obtain ⟨x, hx, hxv⟩ := (hrange v).mp hv
      have hxX := (hcode x v hxv).trans hvX
      exact haB ▸ (internal_exact_members base a X).mpr ⟨x, hx, hxX⟩
    · intro hX
      rw [← haB] at hX
      obtain ⟨x, hx, hxX⟩ := (internal_exact_members base a X).mp hX
      obtain ⟨v, hxv, _⟩ := hf.1.2 x hx
      exact (internal_exact_members base T X).mpr
        ⟨v, (hrange v).mpr ⟨x, hx, hxv⟩, (hcode x v hxv).symm.trans hxX⟩
  · intro v w hv hw hvw
    obtain ⟨x, hx, hxv⟩ := (hrange v).mp hv
    obtain ⟨y, hy, hyw⟩ := (hrange w).mp hw
    have hxy := hai x y hx hy ((hcode x v hxv).trans (hvw.trans (hcode y w hyw).symm))
    subst y
    obtain ⟨v₀, _, hu⟩ := hf.1.2 x hx
    exact (hu v hxv).trans (hu w hyw).symm

theorem fixed_solutions_parameter_extension_iff (base : BaseCollection s)
    (hFixed : FixedGraphSolvabilityCode s)
    {t : U} (ht : TransitiveCode s t)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (htB : Subset (internalMember base) (internalCode base t) B) :
    (∃ T, TransitiveCode s T ∧ Subset s t T ∧ internalCode base T = B ∧ ParameterInjective base T) ↔
      InternallyStrongExtensional s t := by
  constructor
  · rintro ⟨T, _, htT, _, hi⟩
    apply (parameter_injective_iff base ht).mp
    intro x y hx hy hxy
    exact hi x y (htT x hx) (htT y hy) hxy
  · intro hi
    exact fixed_solutions_parameter_extension base hFixed ht
      ((parameter_injective_iff base ht).mpr hi) B hB htB

theorem fixed_solutions_parameter_family_iff (base : BaseCollection s)
    (hFixed : FixedGraphSolvabilityCode s) (F : U)
    (hF : ∀ a, s a F → TransitiveCode s a)
    (B : InternalQuotient base) (hB : TransitiveCode (internalMember base) B)
    (hFB : ∀ a, s a F → Subset (internalMember base) (internalCode base a) B) :
    (∃ T, TransitiveCode s T ∧ (∀ a, s a F → Subset s a T) ∧
      internalCode base T = B ∧ ParameterInjective base T) ↔
      ParameterFamilyCompatible base F := by
  constructor
  · rintro ⟨T, _, hFT, _, hi⟩ a b x y ha hb hx hy hxy
    exact hi x y (hFT a ha x hx) (hFT b hb y hy) hxy
  · intro hc
    obtain ⟨d, hd⟩ := base.union F
    have hdT := transitive_parameter_family_union hd hF
    have hi := (parameter_family_union_criterion base hd).mpr hc
    have hdB : Subset (internalMember base) (internalCode base d) B := by
      intro X hX
      obtain ⟨x, hx, rfl⟩ := (internal_exact_members base d X).mp hX
      obtain ⟨a, ha, hxa⟩ := (hd x).mp hx
      exact hFB a ha _ ((internal_exact_members base a _).mpr ⟨x, hxa, rfl⟩)
    obtain ⟨T, hT, hdT', hTB, hTi⟩ := fixed_solutions_parameter_extension base hFixed hdT hi B hB hdB
    exact ⟨T, hT, fun a ha x hx => hdT' x ((hd x).mpr ⟨a, ha, hx⟩), hTB, hTi⟩


structure FixedSolvableModel where
  Carrier : Type u
  mem : Carrier → Carrier → Prop
  base : BaseCollection mem
  fixedSolvability : FixedGraphSolvabilityCode mem

def FixedSolvableModel.behaviorQuotient (M : FixedSolvableModel.{u}) : AfaModel.{u} where
  Carrier := InternalQuotient M.base
  mem := internalMember M.base
  base := internal_base_model M.base
  antiFoundation := internal_afa_from_solutions M.base
    (fixed_solvability_implies_solvability M.base M.fixedSolvability)

theorem fixed_solvability_to_afa_model_existence :
    Nonempty FixedSolvableModel.{u} → Nonempty AfaModel.{u} := by
  rintro ⟨M⟩
  exact ⟨M.behaviorQuotient⟩

theorem fixed_solvable_non_bafa_model_existence :
    Nonempty BafaModel.{u} → ∃ M : FixedSolvableModel.{u}, ¬BAFACode M.mem := by
  rintro ⟨M⟩
  let N := M.behaviorQuotient
  refine ⟨⟨N.Carrier, N.mem, N.base, afa_fixed_graph_solvability N.base N.antiFoundation⟩, ?_⟩
  exact afa_not_bafa N.base N.antiFoundation

#print axioms fixed_solutions_parameter_extension
#print axioms fixed_solvable_non_bafa_model_existence
#print axioms afa_fixed_graph_solvability
end FullBridge
