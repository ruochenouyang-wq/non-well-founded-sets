import BoundedLocalDefinitions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Full Collection implies full Separation over Pairing, Union and bounded
    Separation. No Foundation, powerset, infinity, transitive containment,
    object Choice or strong-Collection scheme is assumed. -/
theorem collection_bounded_separation_full_separation (hc : Collection s)
    (hp : Pairing s) (hu : Union s) (hsep : BoundedSeparation s) : Separation s := by
  intro n p v a
  obtain ⟨d, had, hd⟩ := power_finite_environment_bound hp hu a v
  obtain ⟨k, q, w, hq⟩ := collection_local_bounded_definitions hc hp hu p d
  obtain ⟨b, hb⟩ := hsep (k+n) q (prefixEnv w v) a
  refine ⟨b, fun x => (hb x).trans ?_⟩
  have hh : s x a → (BoundedEval s q (cons x (prefixEnv w v)) ↔ Eval s p (cons x v)) := by
    intro hx
    exact hq (cons x v) (fun i => Fin.cases (had x hx) hd i)
  exact ⟨fun ⟨hx, he⟩ => ⟨hx, (hh hx).mp he⟩, fun ⟨hx, he⟩ => ⟨hx, (hh hx).mpr he⟩⟩

theorem collection_bounded_separation_replacement (hc : Collection s)
    (hp : Pairing s) (hu : Union s) (hsep : BoundedSeparation s) : Replacement s :=
  collection_separation_replacement s hc (collection_bounded_separation_full_separation hc hp hu hsep)

/-- This closes the separation obligation once the previously identified
    hereditary witness bounds have been proved; those bounds are not assumed
    to follow from the current construction. -/
theorem mask_witness_bounds_full_base (base : BaseCollection s) {z w : U} (hw : OmegaCode s z w)
    {J : InternalMask s w → U → U} (hj : ∀ i, ElementaryMap s s (J i))
    (ho : ∀ i y, ∃ x, J i x = y) (hl : ∀ i, LocallyInternalTransitiveMap s (J i))
    (hOne : ∀ x, J (internalMaskOne base w) x = x)
    (hMul : ∀ i j x, J (internalMaskMul base i j) x = J i (J j x))
    (hCover : ∀ d, ∃ T, Nonempty (JointMaskDomain s w J T) ∧ Subset s d T)
    (hb : MaskHereditaryWitnessBounds s w J) : BaseCollection (maskSupportedMember J) := by
  have hc := (mask_collection_iff_hereditary_witness_bounds base hw hj hOne hMul hCover).mpr hb
  have hp := mask_carrier_pairing base hw J hj
  have hu := mask_carrier_union base J hj ho
  have hsep := mask_carrier_bounded_separation base hw J hj ho
  have hcomm : ∀ i j x, J i (J j x) = J j (J i x) := fun i j x =>
    group_action_preserves_commutation (internalMaskGroup base w) J hMul (internal_mask_mul_comm base i j) x
  have hs : ∀ i x, J i (J i x) = x := by
    intro i x
    have h := hMul i i x
    rw [internal_mask_mul_self] at h
    exact h.symm.trans (hOne x)
  exact ⟨mask_carrier_extensional base.extensional J, mask_carrier_empty base hw J hj ho,
    hp, hu, mask_carrier_power_of_joint_covers base hj hcomm hs (fun d => hCover d.val),
    mask_carrier_infinity base hw J hl,
    collection_bounded_separation_full_separation hc hp hu hsep, hc⟩

#print axioms collection_bounded_separation_full_separation
#print axioms mask_witness_bounds_full_base
end FullBridge
