import RecurrentEnumeration
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem coded_mask_action_ext (base : BaseCollection s) {w : U} (A B : CodedMaskAction base w)
    (hd : A.domain = B.domain) (hf : A.family = B.family) : A = B := by
  have hm : A.masks = B.masks := base.extensional _ _ (fun i => (A.maskMembers i).trans (B.maskMembers i).symm)
  have hmaps : A.maps = B.maps := by
    funext i
    exact coded_function_value_unique A.familyFunction (A.mapCodes i) (hf.symm ▸ B.mapCodes i)
  cases A
  cases B
  cases hd
  cases hm
  cases hf
  cases hmaps
  rfl

def ActionRequestCode (base : BaseCollection s) {w : U} (p t : U) (Q : CodedMaskAction base w) : Prop :=
  OrbitGraphParameters s p t Q.domain Q.family

theorem action_request_code_exists (base : BaseCollection s) {w : U} (t : U) (Q : CodedMaskAction base w) :
    ∃ p, ActionRequestCode base p t Q := orbit_graph_parameters_exists base t Q.domain Q.family

theorem action_request_code_unique (base : BaseCollection s) {w p t t' : U}
    {Q Q' : CodedMaskAction base w} (h : ActionRequestCode base p t Q) (h' : ActionRequestCode base p t' Q') :
    t = t' ∧ Q = Q' := by
  obtain ⟨ht, hd, hf⟩ := orbit_graph_parameters_unique h h'
  exact ⟨ht, coded_mask_action_ext base Q Q' hd hf⟩

def ActionRequestCompatible (base : BaseCollection s) {w : U}
    (P Q : CodedMaskAction base w) (t : U) : Prop :=
  TransitiveCode s t ∧ Subset s t P.domain ∧ Subset s t Q.domain ∧
  (∀ i x y, s x t → CodedRelation s (P.maps i) x y → s y t) ∧
  (∀ i x y, s x t → (CodedRelation s (P.maps i) x y ↔ CodedRelation s (Q.maps i) x y))

theorem coded_mask_embedding_mono (base : BaseCollection s) {w f : U}
    {A B C : CodedMaskAction base w} (E : CodedMaskEmbedding base A B f)
    (h : CodedMaskExtends base B C) : Nonempty (CodedMaskEmbedding base A C f) :=
  ⟨⟨E.range, E.transitive, fun x hx => h.1 x (E.subset x hx), E.iso,
    fun i x y X Y hxy hxX hyY => h.2 i X Y (E.intertwines i x y X Y hxy hxX hyY)⟩⟩

/-- Sealing retains a whole embedded action, not just one of its values. -/
def ActionRequestSealed (base : BaseCollection s) {w : U}
    (P C : CodedMaskAction base w) (p : U) : Prop :=
  ∀ t Q, ActionRequestCode base p t Q → ActionRequestCompatible base P Q t →
    ∃ f, Nonempty (CodedMaskEmbedding base Q C f) ∧ ∀ x, s x t → CodedRelation s f x x

theorem action_request_sealed_mono (base : BaseCollection s) {w p : U}
    {P B C : CodedMaskAction base w} (h : ActionRequestSealed base P B p)
    (hBC : CodedMaskExtends base B C) : ActionRequestSealed base P C p := by
  intro t Q hcode hcompat
  obtain ⟨f, ⟨E⟩, hfix⟩ := h t Q hcode hcompat
  exact ⟨f, coded_mask_embedding_mono base E hBC, hfix⟩

#print axioms action_request_code_unique
end FullBridge
