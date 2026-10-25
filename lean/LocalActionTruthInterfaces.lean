import LocalActionTruth
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_mask_one_graph (base : BaseCollection s) {w : U} (A : CodedMaskAction base w) (x X : U) :
    CodedRelation s (A.maps (internalMaskOne base w)) x X ↔ s x A.domain ∧ x = X := by
  constructor
  · intro h
    exact ⟨coded_function_domain (A.iso _).1 h, A.one x X h⟩
  · rintro ⟨hx, rfl⟩
    obtain ⟨y, hxy, _⟩ := (A.iso (internalMaskOne base w)).1.2 x hx
    exact (A.one x y hxy).symm ▸ hxy

theorem codedMaskIdentityIso (base : BaseCollection s) {w : U} (A : CodedMaskAction base w) :
    CodedMaskIsomorphism base A A (A.maps (internalMaskOne base w)) :=
  ⟨A.iso _, fun _ x y X Y hxy hx hy => (A.one x X hx) ▸ (A.one y Y hy) ▸ hxy⟩

def codedMaskExtensionEmbedding (base : BaseCollection s) {w : U} {A B : CodedMaskAction base w}
    (hAB : CodedMaskExtends base A B) : CodedMaskEmbedding base A B (A.maps (internalMaskOne base w)) :=
  ⟨A.domain, A.transitive, hAB.1, A.iso _, fun i x y X Y hxy hx hy =>
    (A.one x X hx) ▸ (A.one y Y hy) ▸ hAB.2 i x y hxy⟩

theorem local_action_truth_extension (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    {A B : CodedMaskAction base w} (hAB : CodedMaskExtends base A B)
    {n} (p : Formula n) (v : Fin n → U) (hv : ∀ j, s (v j) A.domain) :
    LocalActionTruth base J p A v ↔ LocalActionTruth base J p B v :=
  local_action_truth_embedding base ctx (codedMaskExtensionEmbedding base hAB) p v v
    (fun j => (coded_mask_one_graph base A (v j) (v j)).mpr ⟨hv j, rfl⟩)

theorem global_action_local_truth_iff (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} (ctx : UniversalActionContext base J)
    (A : CodedMaskAction base w) (hAJ : ∀ i x y, CodedRelation s (A.maps i) x y → J i x = y)
    {n} (p : Formula n) (v : Fin n → CoveredMaskCarrier s w J) (hv : ∀ j, s (v j).val A.domain) :
    LocalActionTruth base J p A (fun j => (v j).val) ↔ Eval (coveredMaskMember J) p v :=
  local_action_truth_realization_iff base ctx ((codedMaskIdentityIso base A).toEmbedding base) hAJ p
    (fun j => (v j).val) v (fun j => (coded_mask_one_graph base A (v j).val (v j).val).mpr ⟨hv j, rfl⟩)

theorem local_action_truth_exists_intro (base : BaseCollection s) {w : U}
    {J : InternalMask s w → U → U} {A : CodedMaskAction base w}
    {n} {p : Formula (n+1)} {v : Fin n → U} {x : U}
    (h : LocalActionTruth base J p A (cons x v)) : LocalActionTruth base J (.ex p) A v := by
  obtain ⟨B, f, E, hBJ, V, hv, hp⟩ := h
  have he : cons (V 0) (fun j => V j.succ) = V := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  refine ⟨B, f, E, hBJ, (fun j => V j.succ), (fun j => hv j.succ), V 0, ?_⟩
  exact he.symm ▸ hp

#print axioms local_action_truth_extension
end FullBridge
