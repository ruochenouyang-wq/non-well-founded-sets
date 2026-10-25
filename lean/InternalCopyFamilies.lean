import InternalCopyValues
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

structure InternalCopyFamily (s : U → U → Prop) (G t A : U) (F : InternalIsoFamily s G t) where
  codes : U
  codesFunction : FunctionCode s G codes
  ranges : U
  rangesFunction : FunctionCode s G ranges
  copy : ∀ i, s i G → ∀ b k, CodedRelation s ranges i b → CodedRelation s codes i k →
    ∀ f, CodedRelation s F.code i f → CopyCode s t A f b k
  identityMap : ∀ k, CodedRelation s codes F.one k → ∀ x y,
    CodedRelation s k x y ↔ s x A ∧ y = x
  identityRange : ∀ b, CodedRelation s ranges F.one b → b = A
  overlaps : ∀ i j b c, i ≠ j → CodedRelation s ranges i b → CodedRelation s ranges j c →
    ∀ y, s y b ∧ s y c ↔ s y t

def copyRangeFamilyFormula : Formula 4 :=
  .ex (.conj (relatedFormula 4 2 0) (codedImageSetFormula 0 3 1))

theorem eval_copyRangeFamilyFormula (b i A K : U) :
    Eval s copyRangeFamilyFormula (cons b (cons i (cons A (cons K Fin.elim0)))) ↔
      ∃ k, CodedRelation s K i k ∧ CodedImageSet s k A b := by
  simp only [copyRangeFamilyFormula, Eval, eval_relatedFormula, eval_codedImageSetFormula]
  rfl

/-- A jointly coded family of exact ranges for any jointly coded family of
    maps with the same source domain. -/
theorem coded_family_ranges (base : BaseCollection s) {G K : U}
    (hK : FunctionCode s G K) (A : U) :
    ∃ R, FunctionCode s G R ∧ ∀ i b, CodedRelation s R i b ↔
      s i G ∧ ∃ k, CodedRelation s K i k ∧ CodedImageSet s k A b := by
  have ht : ∀ i, s i G → ∃ b, Eval s copyRangeFamilyFormula (cons b (cons i (cons A (cons K Fin.elim0)))) ∧
      ∀ c, Eval s copyRangeFamilyFormula (cons c (cons i (cons A (cons K Fin.elim0)))) → c = b := by
    intro i hi
    obtain ⟨k, hik, _⟩ := hK.2 i hi
    obtain ⟨b, hb⟩ := coded_image_set_exists base k A
    refine ⟨b, (eval_copyRangeFamilyFormula b i A K).mpr ⟨k, hik, hb⟩, ?_⟩
    intro c hc
    obtain ⟨l, hil, hcl⟩ := (eval_copyRangeFamilyFormula c i A K).mp hc
    have hlk := coded_function_value_unique hK hil hik
    subst l
    exact base.extensional c b (fun x => (hcl x).trans (hb x).symm)
  obtain ⟨R, hR, hrel⟩ := definable_function_code base copyRangeFamilyFormula (cons A (cons K Fin.elim0)) G ht
  exact ⟨R, hR, fun i b => (hrel i b).trans (and_congr Iff.rfl (eval_copyRangeFamilyFormula b i A K))⟩

/-- Arbitrarily internally large copy families, constructed with one common
    fresh tag and actual source family codes; no internal enumeration or
    object-level choice is required. -/
theorem internal_copy_family_exists (base : BaseCollection s) {G t A : U}
    (F : InternalIsoFamily s G t) (htA : Subset s t A) : Nonempty (InternalCopyFamily s G t A F) := by
  obtain ⟨tag, hfresh⟩ := fresh_orderedPair_tag base A
  let v := cons F.one (cons t (cons F.code (cons tag Fin.elim0)))
  have ht : ∀ i, s i G → ∀ x, s x A → ∃ y,
      Eval s internalCopyValueFormula (cons y (cons x (cons i v))) ∧
      ∀ z, Eval s internalCopyValueFormula (cons z (cons x (cons i v))) → z = y := by
    intro i hi x _
    obtain ⟨y, hy, hu⟩ := internal_copy_value_total_unique base (tag := tag) F hi x
    exact ⟨y, (eval_internalCopyValueFormula F.one t F.code tag i x y).mpr hy,
      fun z hz => hu z ((eval_internalCopyValueFormula F.one t F.code tag i x z).mp hz)⟩
  obtain ⟨K, hK, hgraphs⟩ := definable_function_family base internalCopyValueFormula v G A ht
  have hval : ∀ i k, CodedRelation s K i k → FunctionCode s A k ∧ ∀ x y,
      CodedRelation s k x y ↔ s x A ∧ InternalCopyValue s F.one t F.code tag i x y := by
    intro i k hik
    obtain ⟨_, hk, hrel⟩ := (hgraphs i k).mp hik
    exact ⟨hk, fun x y => (hrel x y).trans (and_congr Iff.rfl
      (eval_internalCopyValueFormula F.one t F.code tag i x y))⟩
  obtain ⟨R, hR, hr⟩ := coded_family_ranges base hK A
  have hRange : ∀ i b k, CodedRelation s R i b → CodedRelation s K i k → RangeCode s A k b := by
    intro i b k hib hik
    obtain ⟨_, l, hil, hb⟩ := (hr i b).mp hib
    have he := coded_function_value_unique hK hil hik
    exact he ▸ hb
  have hCopy : ∀ i, s i G → ∀ b k, CodedRelation s R i b → CodedRelation s K i k →
      ∀ f, CodedRelation s F.code i f → CopyCode s t A f b k := by
    intro i hi b k hib hik f hif
    have hk := hval i k hik
    have hb := hRange i b k hib hik
    have hext : ∀ x y, CodedRelation s f x y → CodedRelation s k x y := by
      intro x y hxy
      have hxt := coded_function_domain (F.iso i f hif).1 hxy
      exact (hk.2 x y).mpr ⟨htA x hxt, (internal_copy_value_old F hi hxt).mpr ⟨f, hif, hxy⟩⟩
    refine ⟨hk.1, ?_, hb, ?_, hext⟩
    · intro x z y hxy hzy
      exact internal_copy_value_injective F htA hfresh hi ((hk.2 x y).mp hxy).2 ((hk.2 z y).mp hzy).2
    · intro y hyt
      obtain ⟨x, hx, hxy⟩ := ((F.iso i f hif).2.2.1 y).mp hyt
      exact (hb y).mpr ⟨x, htA x hx, hext x y hxy⟩
  have hId : ∀ k, CodedRelation s K F.one k → ∀ x y,
      CodedRelation s k x y ↔ s x A ∧ y = x := by
    intro k hk x y
    exact ((hval F.one k hk).2 x y).trans (and_congr Iff.rfl internal_copy_value_identity)
  refine ⟨⟨K, hK, R, hR, hCopy, hId, ?_, ?_⟩⟩
  · intro b hb
    obtain ⟨k, hk, _⟩ := hK.2 F.one F.one_mem
    apply base.extensional
    intro y
    rw [hRange F.one b k hb hk y]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ((hId k hk x y).mp hxy).2.symm ▸ hx
    · intro hy
      exact ⟨y, hy, (hId k hk y y).mpr ⟨hy, rfl⟩⟩
  · intro i j b c hij hib hjc y
    have hi := coded_function_domain hR hib
    have hj := coded_function_domain hR hjc
    obtain ⟨k, hik, _⟩ := hK.2 i hi
    obtain ⟨l, hjl, _⟩ := hK.2 j hj
    constructor
    · rintro ⟨hyb, hyc⟩
      obtain ⟨x, hx, hxy⟩ := (hRange i b k hib hik y).mp hyb
      obtain ⟨z, hz, hzy⟩ := (hRange j c l hjc hjl y).mp hyc
      exact internal_copy_distinct_overlap F hfresh hi hj hij hx hz
        (((hval i k hik).2 x y).mp hxy).2 (((hval j l hjl).2 z y).mp hzy).2
    · intro hyt
      obtain ⟨f, hif, _⟩ := F.function.2 i hi
      obtain ⟨g, hjg, _⟩ := F.function.2 j hj
      exact ⟨(hCopy i hi b k hib hik f hif).2.2.2.1 y hyt,
        (hCopy j hj c l hjc hjl g hjg).2.2.2.1 y hyt⟩
end FullBridge
