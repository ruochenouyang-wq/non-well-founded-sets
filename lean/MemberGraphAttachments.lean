import MaskPowerBoundedCandidate
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A graph is attached over its fixed transitive part, while the whole
    previously constructed transitive domain remains literal membership. -/
structure MemberGraphAttachment (s : U → U → Prop) (t A a r : U) where
  copyDomain : U
  copy : U
  domain : U
  edge : U
  copyFunction : FunctionCode s a copy
  copyInjective : InjectiveCode s copy
  copyRange : RangeCode s a copy copyDomain
  fixed : ∀ x, s x t → CodedRelation s copy x x
  overlap : ∀ x, s x copyDomain ∧ s x A ↔ s x t
  members : ∀ x, s x domain ↔ s x A ∨ s x copyDomain
  graph : GraphCode s domain edge
  old : EndExtensionCode s domain edge A
  closed : GraphClosedCode s domain edge copyDomain
  transported : ∀ x y X Y, CodedRelation s copy x X → CodedRelation s copy y Y →
    (CodedRelation s edge X Y ↔ CodedRelation s r x y)

def transportedRelationFormula : Formula 4 :=
  .ex (.ex (.conj (relatedFormula 4 1 3)
    (.conj (relatedFormula 4 0 2) (relatedFormula 5 1 0))))

theorem eval_transportedRelationFormula (k r X Y : U) :
    Eval s transportedRelationFormula (cons Y (cons X (cons k (cons r Fin.elim0)))) ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s k y Y ∧ CodedRelation s r x y := by
  simp only [transportedRelationFormula, Eval, eval_relatedFormula]
  rfl

theorem transported_relation_graph (base : BaseCollection s) {a B k r : U}
    (hk : FunctionCode s a k) (hB : RangeCode s a k B) :
    ∃ e, GraphCode s B e ∧ ∀ X Y, CodedRelation s e X Y ↔
      ∃ x y, CodedRelation s k x X ∧ CodedRelation s k y Y ∧ CodedRelation s r x y := by
  obtain ⟨e, heG, he⟩ := normalized_relation_comprehension base transportedRelationFormula
    (cons k (cons r Fin.elim0)) B
  refine ⟨e, heG, fun X Y => ?_⟩
  rw [he, eval_transportedRelationFormula]
  exact ⟨fun h => h.2.2, fun ⟨x, y, hx, hy, hxy⟩ =>
    ⟨(hB X).mpr ⟨x, coded_function_domain hk hx, hx⟩,
      (hB Y).mpr ⟨y, coded_function_domain hk hy, hy⟩, x, y, hx, hy, hxy⟩⟩

theorem member_graph_attachment_exists (base : BaseCollection s) {t A a r : U}
    (ht : TransitiveCode s t) (hA : TransitiveCode s A) (htA : Subset s t A)
    (hG : GraphCode s a r) (hEnd : EndExtensionCode s a r t) :
    Nonempty (MemberGraphAttachment s t A a r) := by
  obtain ⟨_, id, _, hidF, _, hid⟩ := membership_graph_identity_decoration base ht
  have hidIso : MembershipIsoCode s t t id := by
    refine ⟨hidF.1, ?_, ?_, ?_⟩
    · intro x y z hx hy
      exact ((hid x z).mp hx).2.symm.trans ((hid y z).mp hy).2
    · intro y
      exact ⟨fun hy => ⟨y, hy, (hid y y).mpr ⟨hy, rfl⟩⟩,
        fun ⟨x, hx, hxy⟩ => ((hid x y).mp hxy).2.symm ▸ hx⟩
    · intro x y X Y hx hy
      rcases (hid x X).mp hx with ⟨_, rfl⟩
      rcases (hid y Y).mp hy with ⟨_, rfl⟩
      rfl
  obtain ⟨B, k, hk, hOverlap⟩ := copy_with_exact_overlap base hidIso hEnd.1 htA
  have hfix : ∀ x, s x t → CodedRelation s k x x :=
    fun x hx => hk.2.2.2.2 x x ((hid x x).mpr ⟨hx, rfl⟩)
  obtain ⟨eB, heBG, heB⟩ := transported_relation_graph base hk.1 hk.2.2.1 (r := r)
  have hBrow : ∀ X, s X t → ∀ Y, CodedRelation s eB X Y ↔ s Y X := by
    intro X hX Y
    constructor
    · intro hXY
      obtain ⟨x, y, hxX, hyY, hxy⟩ := (heB X Y).mp hXY
      have hx := hk.2.1 x X X hxX (hfix X hX)
      subst x
      have hyX := (hEnd.2 X hX y).mp hxy
      have hyt := ht X hX y hyX
      have hYy := coded_function_value_unique hk.1 hyY (hfix y hyt)
      exact hYy ▸ hyX
    · intro hyX
      exact (heB X Y).mpr ⟨X, Y, hfix X hX, hfix Y (ht X hX Y hyX),
        (hEnd.2 X hX Y).mpr hyX⟩
  obtain ⟨eA, _, heAG, _, heA, _⟩ := membership_graph_identity_decoration base hA
  obtain ⟨S, hS⟩ := binary_union_exists base.pairing base.union A B
  obtain ⟨e, hem, her⟩ := coded_relation_union base eA eB
  have heG : GraphCode s S e := by
    intro z hz
    rcases (hem z).mp hz with hza | hzb
    · obtain ⟨X, Y, hX, hY, hxy⟩ := heAG z hza
      exact ⟨X, Y, (hS X).mpr (Or.inl hX), (hS Y).mpr (Or.inl hY), hxy⟩
    · obtain ⟨X, Y, hX, hY, hxy⟩ := heBG z hzb
      exact ⟨X, Y, (hS X).mpr (Or.inr hX), (hS Y).mpr (Or.inr hY), hxy⟩
  have hOld : EndExtensionCode s S e A := by
    refine ⟨fun X hX => (hS X).mpr (Or.inl hX), fun X hX Y => ?_⟩
    rw [her]
    constructor
    · rintro (h | h)
      · exact ((heA X Y).mp h).2
      · exact (hBrow X ((hOverlap X).mp ⟨(graphCode_endpoints heBG h).1, hX⟩) Y).mp h
    · exact fun h => Or.inl ((heA X Y).mpr ⟨hX, h⟩)
  have hRow : ∀ X, s X B → ∀ Y, CodedRelation s e X Y ↔ CodedRelation s eB X Y := by
    intro X hX Y
    rw [her]
    constructor
    · rintro (h | h)
      · have hXt := (hOverlap X).mp ⟨hX, ((heA X Y).mp h).1⟩
        exact (hBrow X hXt Y).mpr ((heA X Y).mp h).2
      · exact h
    · exact Or.inr
  refine ⟨⟨B, k, S, e, hk.1, hk.2.1, hk.2.2.1, hfix, hOverlap, hS, heG, hOld,
    ⟨fun X hX => (hS X).mpr (Or.inr hX), fun X hX Y hXY =>
      (graphCode_endpoints heBG ((hRow X hX Y).mp hXY)).2⟩, ?_⟩⟩
  intro x y X Y hxX hyY
  rw [hRow X ((hk.2.2.1 X).mpr ⟨x, coded_function_domain hk.1 hxX, hxX⟩) Y, heB]
  constructor
  · rintro ⟨x', y', hx'X, hy'Y, hxy⟩
    exact hk.2.1 x' x X hx'X hxX ▸ hk.2.1 y' y Y hy'Y hyY ▸ hxy
  · exact fun h => ⟨x, y, hxX, hyY, h⟩

theorem attachment_closed_extensional {t A a r : U} (D : MemberGraphAttachment s t A a r)
    (hExt : GraphExtensionalCode s a r) : GraphExtensionalCode s D.copyDomain D.edge := by
  intro X hX Y hY hrows
  obtain ⟨x, hx, hxX⟩ := (D.copyRange X).mp hX
  obtain ⟨y, hy, hyY⟩ := (D.copyRange Y).mp hY
  have hxy : x = y := by
    apply hExt x hx y hy
    intro z hz
    obtain ⟨Z, hzZ, _⟩ := D.copyFunction.2 z hz
    exact (D.transported x z X Z hxX hzZ).symm.trans
      ((hrows Z ((D.copyRange Z).mpr ⟨z, hz, hzZ⟩)).trans (D.transported y z Y Z hyY hzZ))
  subst y
  exact coded_function_value_unique D.copyFunction hxX hyY

#print axioms member_graph_attachment_exists
#print axioms attachment_closed_extensional
end FullBridge
