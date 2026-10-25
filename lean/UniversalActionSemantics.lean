import UniversalActionBackAndForth
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem universal_action_extend_covered_environment (base : BaseCollection s) {w f : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {A B : CodedMaskAction base w} (I : CodedMaskIsomorphism base A B f)
    (hAJ : ∀ i y Y, CodedRelation s (A.maps i) y Y → J i y = Y)
    (hBJ : ∀ i y Y, CodedRelation s (B.maps i) y Y → J i y = Y)
    {n} (v V : Fin n → CoveredMaskCarrier s w J)
    (hv : ∀ j, CodedRelation s f (v j).val (V j).val) (x : CoveredMaskCarrier s w J) :
    ∃ A' B' : CodedMaskAction base w, ∃ g, ∃ _I' : CodedMaskIsomorphism base A' B' g,
      (∀ i y Y, CodedRelation s (A'.maps i) y Y → J i y = Y) ∧
      (∀ i y Y, CodedRelation s (B'.maps i) y Y → J i y = Y) ∧
      ∃ X : CoveredMaskCarrier s w J, ∀ j,
        CodedRelation s g (cons x v j).val (cons X V j).val := by
  obtain ⟨A', B', g, _, hxA, hA'J, ⟨I'⟩, hB'J, hfg⟩ := universal_action_iso_forth base ctx I hAJ hBJ x.val
  obtain ⟨X, hxX, _⟩ := I'.iso.1.2 x.val hxA
  have hXc := (global_action_iso_covered_iff base I' hA'J hB'J hxX).mp x.property
  exact ⟨A', B', g, I', hA'J, hB'J, ⟨X, hXc⟩,
    fun j => Fin.cases hxX (fun j => hfg (v j).val (V j).val (hv j)) j⟩

/-- Every finite first-order formula of the covered carrier is invariant
    under actual equivariant isomorphisms between global-coded action domains.
    Quantifiers use back-and-forth; this is not ambient source elementarity. -/
theorem universal_action_iso_semantics (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {n} (p : Formula n) :
    ∀ {A B : CodedMaskAction base w} {f}, (I : CodedMaskIsomorphism base A B f) →
      (∀ i y Y, CodedRelation s (A.maps i) y Y → J i y = Y) →
      (∀ i y Y, CodedRelation s (B.maps i) y Y → J i y = Y) →
      ∀ v V : Fin n → CoveredMaskCarrier s w J,
      (∀ j, CodedRelation s f (v j).val (V j).val) →
      (Eval (coveredMaskMember J) p v ↔ Eval (coveredMaskMember J) p V) := by
  induction p with
  | equal i j =>
    intro A B f I hAJ hBJ v V hv
    constructor
    · intro h
      have hij : (v i).val = (v j).val := congrArg Subtype.val h
      exact Subtype.ext (coded_function_value_unique I.iso.1 (hij ▸ hv i) (hv j))
    · intro h
      have hij : (V i).val = (V j).val := congrArg Subtype.val h
      exact Subtype.ext (I.iso.2.1 (v i).val (v j).val (V j).val (hij ▸ hv i) (hv j))
  | member i j =>
    intro A B f I hAJ hBJ v V hv
    exact (I.iso.2.2.2 (v j).val (v i).val (V j).val (V i).val (hv j) (hv i))
  | bottom =>
    intro A B f I hAJ hBJ v V hv
    exact Iff.rfl
  | conj p q hp hq =>
    intro A B f I hAJ hBJ v V hv
    exact and_congr (hp I hAJ hBJ v V hv) (hq I hAJ hBJ v V hv)
  | impl p q hp hq =>
    intro A B f I hAJ hBJ v V hv
    exact imp_congr (hp I hAJ hBJ v V hv) (hq I hAJ hBJ v V hv)
  | ex p ih =>
    intro A B f I hAJ hBJ v V hv
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨A', B', g, I', ha, hb, X, hg⟩ := universal_action_extend_covered_environment base ctx I hAJ hBJ v V hv x
      exact ⟨X, (ih I' ha hb (cons x v) (cons X V) hg).mp hx⟩
    · rintro ⟨X, hX⟩
      obtain ⟨g, ⟨Ig⟩, hg⟩ := coded_mask_isomorphism_inverse base I
      obtain ⟨B', A', k, Ik, hb, ha, x, hk⟩ := universal_action_extend_covered_environment base ctx Ig hBJ hAJ V v
        (fun j => (hg (v j).val (V j).val).mpr (hv j)) X
      exact ⟨x, (ih Ik hb ha (cons X V) (cons x v) hk).mp hX⟩
  | all p ih =>
    intro A B f I hAJ hBJ v V hv
    constructor
    · intro h X
      obtain ⟨g, ⟨Ig⟩, hg⟩ := coded_mask_isomorphism_inverse base I
      obtain ⟨B', A', k, Ik, hb, ha, x, hk⟩ := universal_action_extend_covered_environment base ctx Ig hBJ hAJ V v
        (fun j => (hg (v j).val (V j).val).mpr (hv j)) X
      exact (ih Ik hb ha (cons X V) (cons x v) hk).mpr (h x)
    · intro h x
      obtain ⟨A', B', g, I', ha, hb, X, hg⟩ := universal_action_extend_covered_environment base ctx I hAJ hBJ v V hv x
      exact (ih I' ha hb (cons x v) (cons X V) hg).mpr (h X)

#print axioms universal_action_iso_semantics
end FullBridge
