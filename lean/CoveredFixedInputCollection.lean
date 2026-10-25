import CoveredTailOrbitFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Source bounds are required only when every input and every formula
    parameter is individually fixed by one common tail subgroup. -/
def CoveredTailFixedSourceBounds (s : U → U → Prop) (w : U)
    (J : InternalMask s w → U → U) : Prop :=
  ∀ n (p : Formula (n+2)) (v : Fin n → CoveredMaskCarrier s w J) (a : CoveredMaskCarrier s w J)
    (N : U), s N w →
    (∀ i, TailMask s N i → ∀ j, J i (v j).val = (v j).val) →
    (∀ x, coveredMaskMember J x a → ∀ i, TailMask s N i → J i x.val = x.val) →
    (∀ x, coveredMaskMember J x a → ∃ y, Eval (coveredMaskMember J) p (cons y (cons x v))) →
    ∃ b, ∀ x, coveredMaskMember J x a → ∃ y : CoveredMaskCarrier s w J,
      s y.val b ∧ Eval (coveredMaskMember J) p (cons y (cons x v))

def orbitWitnessFormula {n} (p : Formula (n+2)) : Formula (n+2) :=
  .ex (.conj (.member 0 2) (p.rename (Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ.succ)))))

theorem eval_orbitWitnessFormula {n} (p : Formula (n+2)) (v : Fin n → U) (y O : U) :
    Eval s (orbitWitnessFormula p) (cons y (cons O v)) ↔
      ∃ x, s x O ∧ Eval s p (cons y (cons x v)) := by
  simp only [orbitWitnessFormula, Eval, eval_rename]
  have he : ∀ x : U, (fun i => cons x (cons y (cons O v))
      (Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ.succ)) i)) = cons y (cons x v) := by
    intro x
    funext i
    exact Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i) i
  simp only [he]
  rfl

theorem covered_collection_iff_tail_fixed_source_bounds (base : BaseCollection s) {z w : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T) :
    Collection (coveredMaskMember J) ↔ CoveredTailFixedSourceBounds s w J := by
  constructor
  · intro h n p v a N hN hv ha ht
    obtain ⟨b, hb⟩ := h n p v a ht
    exact ⟨b.val, hb⟩
  · intro h n p v a ht
    obtain ⟨N, hN, hfix⟩ := mask_fixed_finite_parameters base hw
      (fun j => (cons a v j).val)
      (fun j => hereditary_mask_root (internal_mask_covered_hereditary (cons a v j).property))
    have hv : ∀ i, TailMask s N i → ∀ j, J i (v j).val = (v j).val := fun i hi j => hfix i hi j.succ
    obtain ⟨F, hF, hpoint, hcover⟩ := covered_tail_orbit_family base hw hj hc hs hOne hMul hCover hN a
      (fun i hi => hfix i hi 0)
    have htotal : ∀ O, coveredMaskMember J O F →
        ∃ y, Eval (coveredMaskMember J) (orbitWitnessFormula p) (cons y (cons O v)) := by
      intro O hOF
      obtain ⟨x, hx, hO⟩ := (hF O).mp hOF
      obtain ⟨y, hy⟩ := ht x hx
      exact ⟨y, (eval_orbitWitnessFormula p v y O).mpr ⟨x, tail_orbit_contains_seed base hOne hO, hy⟩⟩
    obtain ⟨b, hb⟩ := h n (orbitWitnessFormula p) v F N hN hv hpoint htotal
    obtain ⟨C, _, hC⟩ := covered_mask_orbit_bound base hw hj hc hs hCover b
    refine ⟨C, fun x hx => ?_⟩
    obtain ⟨O, hOF, hxO⟩ := hcover x hx
    obtain ⟨y, hyb, hy⟩ := hb O hOF
    obtain ⟨u, huO, hu⟩ := (eval_orbitWitnessFormula p v y O).mp hy
    obtain ⟨r, _, hO⟩ := (hF O).mp hOF
    obtain ⟨i, hi, hix⟩ := tail_orbit_member_transport base hs hMul hO huO hxO
    have hux : coveredMaskMap hj hc hs i u = x := Subtype.ext hix
    refine ⟨coveredMaskMap hj hc hs i y, hC y hyb i, ?_⟩
    have hvp := covered_mask_witness_transport hj hc hs p v u y i (hv i hi) hu
    simpa only [hux] using hvp

/-- Genuine Collection for arbitrary formulas on a domain covered by finitely
    many parameter-fixing tail orbits. Finiteness is external, via Fin k. -/
theorem covered_finite_tail_orbit_collection (base : BaseCollection s) {z w N : U}
    (hw : OmegaCode s z w) {J : InternalMask s w → U → U}
    (hj : ∀ i, ElementaryMap s s (J i))
    (hc : ∀ i j x, J i (J j x) = J j (J i x)) (hs : ∀ i x, J i (J i x) = x)
    (hCover : ∀ d, ∃ T, TransitiveCode s T ∧ Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    {n k} (p : Formula (n+2)) (v : Fin n → CoveredMaskCarrier s w J)
    (a : CoveredMaskCarrier s w J) (reps : Fin k → CoveredMaskCarrier s w J)
    (hr : ∀ j, coveredMaskMember J (reps j) a)
    (hv : ∀ i, TailMask s N i → ∀ j, J i (v j).val = (v j).val)
    (horbit : ∀ x, coveredMaskMember J x a → ∃ j i, TailMask s N i ∧ J i (reps j).val = x.val)
    (ht : ∀ x, coveredMaskMember J x a → ∃ y, Eval (coveredMaskMember J) p (cons y (cons x v))) :
    ∃ C : CoveredMaskCarrier s w J, ∀ x, coveredMaskMember J x a →
      ∃ y, coveredMaskMember J y C ∧ Eval (coveredMaskMember J) p (cons y (cons x v)) := by
  classical
  let ys := fun j => Classical.choose (ht (reps j) (hr j))
  obtain ⟨e, _⟩ := base.empty
  obtain ⟨b, _, hb⟩ := power_finite_environment_bound base.pairing base.union e (fun j => (ys j).val)
  obtain ⟨C, _, hC⟩ := covered_mask_orbit_bound base hw hj hc hs hCover b
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨j, i, hi, hix⟩ := horbit x hx
  have hy := Classical.choose_spec (ht (reps j) (hr j))
  have hxx : coveredMaskMap hj hc hs i (reps j) = x := Subtype.ext hix
  refine ⟨coveredMaskMap hj hc hs i (ys j), hC (ys j) (hb j) i, ?_⟩
  have hp := covered_mask_witness_transport hj hc hs p v (reps j) (ys j) i (hv i hi) hy
  simpa only [hxx] using hp

#print axioms covered_collection_iff_tail_fixed_source_bounds
#print axioms covered_finite_tail_orbit_collection
end FullBridge
