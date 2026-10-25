import FullActionSourceSyntax
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem universal_Hc_source_translation (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    {n} (p : Formula n) (v : Fin n → CoveredMaskCarrier s w J) (hv : ∀ j, s (v j).val A.domain) :
    Eval (coveredMaskMember J) p v ↔
      Eval s p.actionTranslate (cons w (cons A.domain (cons A.masks (cons A.family (fun j => (v j).val))))) := by
  have hc : ∀ j, ActionCovered base A (v j).val := fun j =>
    (action_covered_iff_global base A (coded_action_global_agreement base A hAJ) (hv j)).mpr (v j).property
  exact (global_action_local_truth_iff base ctx A hAJ p v hv).symm.trans
    (eval_actionTranslate base ctx p A (fun j => (v j).val) hc).symm

#print axioms universal_Hc_source_translation
end FullBridge
