import InvariantGraphAttachments
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem masked_label_actions_commute (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c)
    (i j : InternalMask s w) {x : U} (hx : s x d) :
    maskedLabelAction P i.val (maskedLabelAction P j.val x) =
      maskedLabelAction P j.val (maskedLabelAction P i.val x) := by
  have h1 := masked_label_action_mul base P hd i j hx
  have h2 := masked_label_action_mul base P hd j i hx
  rw [internal_mask_mul_comm] at h1
  exact h1.symm.trans h2

/-- Every label points to its partner. This is an actual source graph,
    with extensionality and invariance proved for the whole internal group. -/
theorem mask_partner_graph_exists (base : BaseCollection s) {w : U}
    (P : InternalQuinePairs s w) (A : CodedMaskAction base w)
    (hd : ∀ x, s x A.domain ↔ ∃ c, s c P.family ∧ s x c)
    (hAr : ∀ i x y, CodedRelation s (A.maps i) x y ↔ s x A.domain ∧ y = maskedLabelAction P i.val x) :
    ∃ r, GraphCode s A.domain r ∧ GraphExtensionalCode s A.domain r ∧
      (∀ i, GraphIsoCode s A.domain r A.domain r (A.maps i)) ∧
      ∀ x y, CodedRelation s r x y ↔ s x A.domain ∧ y = maskedLabelAction P w x := by
  let all : InternalMask s w := ⟨w, fun _ h => h⟩
  obtain ⟨r, hf, hr⟩ := masked_label_action_code base P hd w
  have hG : GraphCode s A.domain r := by
    intro p hp
    obtain ⟨x, y, hx, hxy⟩ := hf.1 p hp
    have hy := ((hr x y).mp ⟨p, hp, hxy⟩).2
    exact ⟨x, y, hx, hy ▸ masked_label_action_mem base P hd w hx, hxy⟩
  have hExt : GraphExtensionalCode s A.domain r := by
    intro x hx y hy hrows
    have hpx := (hr x (maskedLabelAction P w x)).mpr ⟨hx, rfl⟩
    have hpy := (hrows _ (masked_label_action_mem base P hd w hx)).mp hpx
    have h := congrArg (maskedLabelAction P w) ((hr y _).mp hpy).2
    change maskedLabelAction P all.val (maskedLabelAction P all.val x) =
      maskedLabelAction P all.val (maskedLabelAction P all.val y) at h
    rw [masked_label_action_involutive base P hd all hx,
      masked_label_action_involutive base P hd all hy] at h
    exact h
  refine ⟨r, hG, hExt, ?_, hr⟩
  intro i
  refine ⟨(A.iso i).1, (A.iso i).2.1, (A.iso i).2.2.1, ?_⟩
  intro x y X Y hxX hyY
  obtain ⟨hx, rfl⟩ := (hAr i x X).mp hxX
  obtain ⟨hy, rfl⟩ := (hAr i y Y).mp hyY
  rw [hr, hr]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨masked_label_action_mem base P hd i.val hx, ?_⟩
    rw [h]
    exact masked_label_actions_commute base P hd i all hx
  · rintro ⟨_, h⟩
    have hc := masked_label_actions_commute base P hd i all hx
    have he : maskedLabelAction P i.val y = maskedLabelAction P i.val (maskedLabelAction P w x) :=
      h.trans hc.symm
    have hi := congrArg (maskedLabelAction P i.val) he
    rw [masked_label_action_involutive base P hd i hy,
      masked_label_action_involutive base P hd i (masked_label_action_mem base P hd w hx)] at hi
    exact ⟨hx, hi⟩

theorem partner_graph_rows (base : BaseCollection s) {w d r i l k : U}
    (P : InternalQuinePairs s w) (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c)
    (hr : ∀ x y, CodedRelation s r x y ↔ s x d ∧ y = maskedLabelAction P w x)
    (hl : CodedRelation s P.leftCode i l) (hk : CodedRelation s P.rightCode i k) :
    s l d ∧ s k d ∧ (∀ y, CodedRelation s r l y ↔ y = k) ∧
      (∀ y, CodedRelation s r k y ↔ y = l) := by
  have hi := coded_function_domain P.leftFunction hl
  obtain ⟨c, hc⟩ := base.pairing l k
  have hcF := (P.members c).mpr ⟨i, l, k, hi, hl, hk, hc⟩
  have hld := (hd l).mpr ⟨c, hcF, (hc l).mpr (Or.inl rfl)⟩
  have hkd := (hd k).mpr ⟨c, hcF, (hc k).mpr (Or.inr rfl)⟩
  refine ⟨hld, hkd, ?_, ?_⟩
  · intro y
    rw [hr, masked_label_action_left base P w hl hk, if_pos hi]
    exact ⟨fun h => h.2, fun h => ⟨hld, h⟩⟩
  · intro y
    rw [hr, masked_label_action_right base P w hl hk, if_pos hi]
    exact ⟨fun h => h.2, fun h => ⟨hkd, h⟩⟩

theorem partner_decoration_two_cycles (base : BaseCollection s) {w d r f i l k L K : U}
    (P : InternalQuinePairs s w) (hd : ∀ x, s x d ↔ ∃ c, s c P.family ∧ s x c)
    (hr : ∀ x y, CodedRelation s r x y ↔ s x d ∧ y = maskedLabelAction P w x)
    (hf : DecorationCode s d r f) (hfi : InjectiveCode s f)
    (hl : CodedRelation s P.leftCode i l) (hk : CodedRelation s P.rightCode i k)
    (hlL : CodedRelation s f l L) (hkK : CodedRelation s f k K) :
    L ≠ K ∧ (∀ y, s y L ↔ y = K) ∧ (∀ y, s y K ↔ y = L) := by
  obtain ⟨hld, hkd, hrl, hrk⟩ := partner_graph_rows base P hd hr hl hk
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact internal_quine_pair_distinct P hl hk (hfi l k K (h ▸ hlL) hkK)
  · intro y
    constructor
    · intro hy
      obtain ⟨x, _, hlx, hxy⟩ := (hf.2 l hld L hlL y).mp hy
      have hx := (hrl x).mp hlx
      exact coded_function_value_unique hf.1 (hx ▸ hxy) hkK
    · intro hy
      subst y
      exact (hf.2 l hld L hlL K).mpr ⟨k, hkd, (hrl k).mpr rfl, hkK⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨x, _, hkx, hxy⟩ := (hf.2 k hkd K hkK y).mp hy
      have hx := (hrk x).mp hkx
      exact coded_function_value_unique hf.1 (hx ▸ hxy) hlL
    · intro hy
      subst y
      exact (hf.2 k hkd K hkK L).mpr ⟨l, hld, (hrk l).mpr rfl, hlL⟩

#print axioms mask_partner_graph_exists
#print axioms partner_decoration_two_cycles
end FullBridge
