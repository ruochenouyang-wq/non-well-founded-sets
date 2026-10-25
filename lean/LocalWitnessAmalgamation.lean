import ActionFamilyAmalgamation
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- Collect local witnesses and transport all of them into one source action,
    keeping every input and every parameter fixed. -/
theorem local_witness_common_action (base : BaseCollection s) (hB : BAFACode s) {w : U}
    (A : CodedMaskAction base w) {n} (p : BoundedFormula (n+2)) (v : Fin n → U) (a : U)
    (ha : Subset s a A.domain) (hv : ∀ j, s (v j) A.domain)
    (ht : ∀ x, s x a → ∃ Q : CodedMaskAction base w, CodedMaskExtends base A Q ∧
      ∃ y, ActionCovered base Q y ∧ BoundedEval s p (cons y (cons x v))) :
    ∃ C : CodedMaskAction base w, CodedMaskExtends base A C ∧
      ∀ x, s x a → ∃ y, ActionCovered base C y ∧ BoundedEval s p (cons y (cons x v)) := by
  obtain ⟨O, hO, he, hw⟩ := local_witness_action_family base A p v a ht
  obtain ⟨C, hAC, hC⟩ := bafa_coded_mask_family_amalgamation base hB A hO he
  refine ⟨C, hAC, fun x hx => ?_⟩
  obtain ⟨P, hP, Q, y, hpar, _, hy, hpy⟩ := hw x hx
  obtain ⟨f, ⟨E⟩, hfix⟩ := hC P Q hP ⟨y, hpar⟩
  have hyQ : s y Q.domain := by
    obtain ⟨c, hc, _, hyc, _⟩ := hy
    exact hc y hyc
  obtain ⟨Y, hyY, _⟩ := E.iso.1.2 y hyQ
  have hsem := coded_mask_embedding_bounded_fixed_parameters base E p (cons x v)
    (fun j => Fin.cases (hfix x (ha x hx)) (fun j => hfix (v j) (hv j)) j) hyY
  exact ⟨Y, coded_mask_embedding_cover_forward base E hyY hy, hsem.mp hpy⟩

#print axioms local_witness_common_action
end FullBridge
