import PrescribedCoveredCandidates
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A transitive membership isomorphism preserves ambient bounded truth.
    This does not assert ambient elementarity for unbounded formulas. -/
theorem membership_iso_bounded_semantics {a b f : U}
    (ha : TransitiveCode s a) (hb : TransitiveCode s b) (hf : MembershipIsoCode s a b f)
    {n} (p : BoundedFormula n) (v V : Fin n → U)
    (hv : ∀ j, CodedRelation s f (v j) (V j)) : BoundedEval s p v ↔ BoundedEval s p V := by
  induction p with
  | equal i j =>
    exact ⟨fun h => coded_function_value_unique hf.1 (h ▸ hv i) (hv j),
      fun h => hf.2.1 (v i) (v j) (V j) (h ▸ hv i) (hv j)⟩
  | member i j => exact hf.2.2.2 (v j) (v i) (V j) (V i) (hv j) (hv i)
  | bottom => rfl
  | conj p q hp hq => exact and_congr (hp v V hv) (hq v V hv)
  | impl p q hp hq => exact imp_congr (hp v V hv) (hq v V hv)
  | exMem i p hp =>
    constructor
    · rintro ⟨x, hx, hpx⟩
      have hxa := ha (v i) (coded_function_domain hf.1 (hv i)) x hx
      obtain ⟨X, hxX, _⟩ := hf.1.2 x hxa
      exact ⟨X, (hf.2.2.2 (v i) x (V i) X (hv i) hxX).mp hx,
        (hp (cons x v) (cons X V) (fun j => Fin.cases hxX (fun j => hv j) j)).mp hpx⟩
    · rintro ⟨X, hX, hpX⟩
      have hVb := (hf.2.2.1 (V i)).mpr ⟨v i, coded_function_domain hf.1 (hv i), hv i⟩
      obtain ⟨x, _, hxX⟩ := (hf.2.2.1 X).mp (hb (V i) hVb X hX)
      exact ⟨x, (hf.2.2.2 (v i) x (V i) X (hv i) hxX).mpr hX,
        (hp (cons x v) (cons X V) (fun j => Fin.cases hxX (fun j => hv j) j)).mpr hpX⟩
  | allMem i p hp =>
    constructor
    · intro h X hX
      have hVb := (hf.2.2.1 (V i)).mpr ⟨v i, coded_function_domain hf.1 (hv i), hv i⟩
      obtain ⟨x, _, hxX⟩ := (hf.2.2.1 X).mp (hb (V i) hVb X hX)
      exact (hp (cons x v) (cons X V) (fun j => Fin.cases hxX (fun j => hv j) j)).mp
        (h x ((hf.2.2.2 (v i) x (V i) X (hv i) hxX).mpr hX))
    · intro h x hx
      have hxa := ha (v i) (coded_function_domain hf.1 (hv i)) x hx
      obtain ⟨X, hxX, _⟩ := hf.1.2 x hxa
      exact (hp (cons x v) (cons X V) (fun j => Fin.cases hxX (fun j => hv j) j)).mpr
        (h X ((hf.2.2.2 (v i) x (V i) X (hv i) hxX).mp hx))

theorem coded_mask_embedding_bounded_semantics (base : BaseCollection s) {w f : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    {n} (p : BoundedFormula n) (v V : Fin n → U)
    (hv : ∀ j, CodedRelation s f (v j) (V j)) : BoundedEval s p v ↔ BoundedEval s p V :=
  membership_iso_bounded_semantics A.transitive E.transitive E.iso p v V hv

theorem coded_mask_embedding_bounded_fixed_parameters (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    {n} (p : BoundedFormula (n+1)) (v : Fin n → U)
    (hv : ∀ j, CodedRelation s f (v j) (v j)) (hx : CodedRelation s f x X) :
    BoundedEval s p (cons x v) ↔ BoundedEval s p (cons X v) :=
  coded_mask_embedding_bounded_semantics base E p (cons x v) (cons X v)
    (fun j => Fin.cases hx (fun j => hv j) j)

/-- A locally covered witness becomes an actual Hc witness, preserving every
    bounded formula with parameters fixed by the embedding. -/
theorem coded_action_bounded_witness_into_Hc (base : BaseCollection s) {w f x X : U}
    {A B : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    {J : InternalMask s w → U → U}
    (hJ : ∀ i y Y, CodedRelation s (B.maps i) y Y → J i y = Y)
    {n} (p : BoundedFormula (n+1)) (v : Fin n → CoveredMaskCarrier s w J)
    (hv : ∀ j, CodedRelation s f (v j).val (v j).val)
    (hx : CodedRelation s f x X) (hxc : ActionCovered base A x) :
    ∃ Y : CoveredMaskCarrier s w J, Y.val = X ∧
      (BoundedEval s p (cons x (fun j => (v j).val)) ↔ BoundedEval (coveredMaskMember J) p (cons Y v)) := by
  have hXc := (action_covered_iff_global base B (coded_action_global_agreement base B hJ)
    (coded_mask_embedding_value base E hx)).mp (coded_mask_embedding_cover_forward base E hx hxc)
  let Y : CoveredMaskCarrier s w J := ⟨X, hXc⟩
  refine ⟨Y, rfl, (coded_mask_embedding_bounded_fixed_parameters base E p (fun j => (v j).val) hv hx).trans ?_⟩
  have hh := (covered_mask_bounded_absoluteness p (cons Y v)).symm
  rw [covered_mask_cons_values] at hh
  exact hh

#print axioms coded_action_bounded_witness_into_Hc
end FullBridge
