import FaithfulGrowingGroupLimits
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Both label maps and the whole pair family are actual source sets. -/
structure InternalQuinePairs (s : U → U → Prop) (a : U) where
  leftCode : U
  rightCode : U
  family : U
  leftFunction : FunctionCode s a leftCode
  rightFunction : FunctionCode s a rightCode
  leftInjective : InjectiveCode s leftCode
  rightInjective : InjectiveCode s rightCode
  disjoint : ∀ x y v, CodedRelation s leftCode x v → CodedRelation s rightCode y v → False
  leftQuine : ∀ x v, CodedRelation s leftCode x v → SelfSingleton s v
  rightQuine : ∀ x v, CodedRelation s rightCode x v → SelfSingleton s v
  members : ∀ c, s c family ↔ ∃ x l r, s x a ∧ CodedRelation s leftCode x l ∧
    CodedRelation s rightCode x r ∧ IsPair s c l r

def pairImagesFormula {n} (l r x c : Fin n) : Formula n :=
  .ex (.ex (.conj (relatedFormula l.succ.succ x.succ.succ 1)
    (.conj (relatedFormula r.succ.succ x.succ.succ 0) (pairFormula c.succ.succ 1 0))))

theorem eval_pairImagesFormula {n} (l r x c : Fin n) (v : Fin n → U) :
    Eval s (pairImagesFormula l r x c) v ↔
      ∃ y z, CodedRelation s (v l) (v x) y ∧ CodedRelation s (v r) (v x) z ∧ IsPair s (v c) y z := by
  simp only [pairImagesFormula, Eval, eval_relatedFormula, eval_pairFormula, cons_succ, cons_zero]
  rfl

theorem coded_pair_image_family (base : BaseCollection s) {a l r : U}
    (hl : FunctionCode s a l) (hr : FunctionCode s a r) :
    ∃ b, ∀ c, s c b ↔ ∃ x y z, s x a ∧ CodedRelation s l x y ∧
      CodedRelation s r x z ∧ IsPair s c y z := by
  have rep := collection_separation_replacement s base.collection base.separation
  have ht : ∀ x, s x a → ∃ c,
      Eval s (pairImagesFormula (n := 4) 2 3 1 0) (cons c (cons x (cons l (cons r Fin.elim0)))) ∧
      ∀ d, Eval s (pairImagesFormula (n := 4) 2 3 1 0) (cons d (cons x (cons l (cons r Fin.elim0)))) → d = c := by
    intro x hx
    obtain ⟨y, hxy, _⟩ := hl.2 x hx
    obtain ⟨z, hxz, _⟩ := hr.2 x hx
    obtain ⟨c, hc⟩ := base.pairing y z
    refine ⟨c, (eval_pairImagesFormula 2 3 1 0 _).mpr ⟨y, z, hxy, hxz, hc⟩, ?_⟩
    intro d hd
    obtain ⟨y', z', hy', hz', hd⟩ := (eval_pairImagesFormula 2 3 1 0 _).mp hd
    have hy := coded_function_value_unique hl hy' hxy
    have hz := coded_function_value_unique hr hz' hxz
    subst y'; subst z'
    exact pair_unique base.extensional hd hc
  obtain ⟨b, hb⟩ := rep 2 (pairImagesFormula 2 3 1 0) (cons l (cons r Fin.elim0)) a ht
  refine ⟨b, fun c => ?_⟩
  have h := hb c
  simp only [eval_pairImagesFormula] at h
  exact h.trans ⟨fun ⟨x, hx, y, z, hyl, hzr, hp⟩ => ⟨x, y, z, hx, hyl, hzr, hp⟩,
    fun ⟨x, y, z, hx, hyl, hzr, hp⟩ => ⟨x, hx, y, z, hyl, hzr, hp⟩⟩

/-- Arbitrary internal index sets, not merely finite or externally coded lists. -/
theorem bafa_internal_quine_pairs (base : BaseCollection s) (hB : BAFACode s) (a : U) :
    Nonempty (InternalQuinePairs s a) := by
  obtain ⟨b, t, ht, hti, htb, hba⟩ := fresh_parameter_copy base a a
  obtain ⟨d, hd⟩ := binary_union_exists base.pairing base.union a b
  have had : Subset s a d := fun x hx => (hd x).mpr (Or.inl hx)
  obtain ⟨f, hf, hfi, hq⟩ := bafa_selfSingleton_family base hB d
  obtain ⟨l, hl, hlrel⟩ := function_domain_restriction base hf had
  have htd : ∀ x y, CodedRelation s t x y → s y d := by
    intro x y hxy
    exact (hd y).mpr (Or.inr ((htb y).mpr ⟨x, coded_function_domain ht hxy, hxy⟩))
  obtain ⟨r, hr, hrrel⟩ := coded_functions_compose base ht hf htd
  have hli : InjectiveCode s l := fun x y z hx hy => hfi x y z ((hlrel x z).mp hx).2 ((hlrel y z).mp hy).2
  have hri : InjectiveCode s r := by
    intro x y z hx hy
    obtain ⟨X, hxX, hXz⟩ := (hrrel x z).mp hx
    obtain ⟨Y, hyY, hYz⟩ := (hrrel y z).mp hy
    have he := hfi X Y z hXz hYz
    exact hti x y X hxX (he.symm ▸ hyY)
  have hdis : ∀ x y v, CodedRelation s l x v → CodedRelation s r y v → False := by
    intro x y v hx hy
    obtain ⟨Y, hyY, hYv⟩ := (hrrel y v).mp hy
    obtain ⟨hxa, hxv⟩ := (hlrel x v).mp hx
    have he := hfi x Y v hxv hYv
    exact hba Y ((htb Y).mpr ⟨y, coded_function_domain ht hyY, hyY⟩) (he ▸ hxa)
  obtain ⟨F, hF⟩ := coded_pair_image_family base hl hr
  refine ⟨⟨l, r, F, hl, hr, hli, hri, hdis, ?_, ?_, hF⟩⟩
  · intro x v hx
    exact hq x v (had x ((hlrel x v).mp hx).1) ((hlrel x v).mp hx).2
  · intro x v hx
    obtain ⟨y, hxy, hyv⟩ := (hrrel x v).mp hx
    exact hq y v (htd x y hxy) hyv

theorem internal_quine_pair_distinct {a : U} (P : InternalQuinePairs s a)
    {x l r : U} (hl : CodedRelation s P.leftCode x l) (hr : CodedRelation s P.rightCode x r) : l ≠ r := by
  intro he
  exact P.disjoint x x r (he ▸ hl) hr

/-- Any shared element forces equal indices, hence the rows are disjoint. -/
theorem internal_quine_pair_rows_disjoint {a : U} (P : InternalQuinePairs s a)
    {x y l r L R c d v : U}
    (hl : CodedRelation s P.leftCode x l) (hr : CodedRelation s P.rightCode x r)
    (hL : CodedRelation s P.leftCode y L) (hR : CodedRelation s P.rightCode y R)
    (hc : IsPair s c l r) (hd : IsPair s d L R) (hv : s v c) (hw : s v d) : x = y := by
  rcases (hc v).mp hv with hv | hv <;> rcases (hd v).mp hw with hw | hw
  · exact P.leftInjective x y v (hv.symm ▸ hl) (hw.symm ▸ hL)
  · exact False.elim (P.disjoint x y v (hv.symm ▸ hl) (hw.symm ▸ hR))
  · exact False.elim (P.disjoint y x v (hw.symm ▸ hL) (hv.symm ▸ hr))
  · exact P.rightInjective x y v (hv.symm ▸ hr) (hw.symm ▸ hR)

#print axioms bafa_internal_quine_pairs
#print axioms internal_quine_pair_rows_disjoint
end FullBridge
