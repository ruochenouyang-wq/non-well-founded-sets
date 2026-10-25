import JointUniverseStates
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A scheduled request is sealed into the next retained domain together
    with its solution whenever it is admissible and supported there. -/
def ScheduledRequestStep (base : BaseCollection s) {w : U}
    (A B : JointUniverseState base w) (p : U) : Prop :=
  CodedMaskExtends base A.retained B.retained ∧ s p B.retained.domain ∧
    (BafaRequestCode s p → HereditarilyMaskSupported s w B.maps p →
      ∃ t a r f, OrbitGraphParameters s p t a r ∧ s f B.retained.domain ∧
        DecorationCode s a r f ∧ InjectiveCode s f ∧
        (∀ x, s x t → CodedRelation s f x x) ∧ HereditarilyMaskSupported s w B.maps f)

theorem scheduled_request_step_exists (base : BaseCollection s) (hBAFA : BAFACode s)
    {z w : U} (hw : OmegaCode s z w) (A : JointUniverseState base w) (p : U)
    (enum : Nat → U) (henum : ∀ x, ∃ n, enum n = x) :
    ∃ B : JointUniverseState base w, ScheduledRequestStep base A B p := by
  classical
  obtain ⟨d, hd⟩ := base.pairing p p
  obtain ⟨A', hAA', hdA', _⟩ := joint_universe_retain base A d
  have hpA' : s p A'.retained.domain := hdA' p ((hd p).mpr (Or.inl rfl))
  by_cases hGood : BafaRequestCode s p ∧ HereditarilyMaskSupported s w A'.maps p
  · obtain ⟨t, a, r, hpar, _⟩ := hGood.1
    have hparams := hereditary_mask_request_components hpar hGood.2
    obtain ⟨Jdom⟩ := joint_universe_retained_joint base A'
    obtain ⟨O, hO, hpO, ⟨D⟩⟩ := actual_request_orbit_diagram base Jdom A'.retained.transitive
      (fun i => (A'.elementary i).1) (joint_universe_involutive base A') A'.one A'.mul hpA' hGood.1
    have hStable : ∀ i q, s q O → s (A'.maps i q) O := by
      intro i q hq
      obtain ⟨j, rfl⟩ := (hO q).mp hq
      exact (hO _).mpr ⟨internalMaskMul base i j, A'.mul i j p⟩
    have hReq : ∀ q, s q O → BafaRequestCode s q := by
      intro q hq
      obtain ⟨i, rfl⟩ := (hO q).mp hq
      exact (elementary_map_bafa_request (A'.elementary i).1 p).mp hGood.1
    obtain ⟨J, hJ, hOne, hMul, hOld, hCover, _, hSolutions⟩ :=
      countable_bafa_supported_orbit_extension base hBAFA hw D (fun i => (A'.elementary i).1)
        (joint_universe_involutive base A') A'.one A'.mul A'.covers hStable hReq A'.retained.domain enum henum
    obtain ⟨f, hf, hi, hfix, hfH, _⟩ := hSolutions p t a r hpO hpar hparams.1 hparams.2.1 hparams.2.2
    let M : JointUniverseState base w := ⟨J, hJ, hOne, hMul, hCover, A'.retained,
      fun i x y hxy => (hOld i x (coded_function_domain (A'.retained.iso i).1 hxy)).trans (A'.agrees i x y hxy)⟩
    obtain ⟨df, hdf⟩ := base.pairing f f
    obtain ⟨B, hMB, hdfB, hBM⟩ := joint_universe_retain base M df
    refine ⟨B, coded_mask_extends_trans base hAA' hMB, hMB.1 p hpA', ?_⟩
    intro _ _
    refine ⟨t, a, r, f, hpar, hdfB f ((hdf f).mpr (Or.inl rfl)), hf, hi, hfix, ?_⟩
    change HereditarilyMaskSupported s w B.maps f
    rw [hBM]
    exact hfH
  · exact ⟨A', hAA', hpA', fun hReq hH => False.elim (hGood ⟨hReq, hH⟩)⟩

#print axioms scheduled_request_step_exists
end FullBridge
