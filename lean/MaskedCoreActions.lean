import MaskedActionCodes
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

theorem finite_mask_core_action (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    {I : Type v} (G : FiniteGroupData I) (e : I → InternalMask s w)
    (hOne : e G.one = internalMaskOne base w)
    (hMul : ∀ i j, e (G.mul i j) = internalMaskMul base (e i) (e j)) :
    ∃ A : TransitiveGroupAction s G, A.domain = d ∧ ∀ i x y,
      CodedRelation s (A.code i) x y ↔ s x d ∧ y = maskedLabelAction P (e i).val x := by
  classical
  have hq : ∀ x, s x d → SelfSingleton s x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := (hd x).mp hx
    obtain ⟨i, l, r, _, hl, hr, hp⟩ := (P.members c).mp hc
    rcases (hp x).mp hxc with h | h
    · exact h ▸ P.leftQuine i l hl
    · exact h ▸ P.rightQuine i r hr
  have ht : TransitiveCode s d := fun x hx y hy => ((hq x hx y).mp hy).symm ▸ hx
  have hex := fun i => masked_label_action_code base P hd (e i).val
  let code := fun i => Classical.choose (hex i)
  have hf := fun i => (Classical.choose_spec (hex i)).1
  have hr := fun i => (Classical.choose_spec (hex i)).2
  have hm := fun i x hx => masked_label_action_mem base P hd (e i).val (x := x) hx
  have hs := fun i x hx => masked_label_action_involutive base P hd (e i) (x := x) hx
  have hi : ∀ i x y, s x d → s y d → maskedLabelAction P (e i).val x = maskedLabelAction P (e i).val y → x = y := by
    intro i x y hx hy he
    exact (hs i x hx).symm.trans ((congrArg (maskedLabelAction P (e i).val) he).trans (hs i y hy))
  have hIso : ∀ i, MembershipIsoCode s d d (code i) := by
    intro i
    refine ⟨hf i, ?_, ?_, ?_⟩
    · intro x y z hxz hyz
      obtain ⟨hx, hzX⟩ := (hr i x z).mp hxz
      obtain ⟨hy, hzY⟩ := (hr i y z).mp hyz
      exact hi i x y hx hy (hzX.symm.trans hzY)
    · intro y
      constructor
      · intro hy
        exact ⟨_, hm i y hy, (hr i _ y).mpr ⟨hm i y hy, (hs i y hy).symm⟩⟩
      · rintro ⟨x, _, hxy⟩
        obtain ⟨hx, rfl⟩ := (hr i x y).mp hxy
        exact hm i x hx
    · intro x y X Y hxX hyY
      obtain ⟨hx, rfl⟩ := (hr i x X).mp hxX
      obtain ⟨hy, rfl⟩ := (hr i y Y).mp hyY
      rw [hq x hx y, hq _ (hm i x hx) _]
      exact ⟨congrArg (maskedLabelAction P (e i).val), hi i y x hy hx⟩
  have hUnit : ∀ x y, CodedRelation s (code G.one) x y → x = y := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := (hr G.one x y).mp hxy
    rw [hOne] at hy
    exact (hy.trans (masked_label_action_one base P hd hx)).symm
  have hProd : ∀ i j x z, CodedRelation s (code (G.mul i j)) x z ↔
      ∃ y, CodedRelation s (code j) x y ∧ CodedRelation s (code i) y z := by
    intro i j x z
    have hact : s x d → maskedLabelAction P (e (G.mul i j)).val x =
        maskedLabelAction P (e i).val (maskedLabelAction P (e j).val x) := by
      intro hx
      rw [hMul]
      exact masked_label_action_mul base P hd (e i) (e j) hx
    constructor
    · intro hxz
      obtain ⟨hx, hz⟩ := (hr _ x z).mp hxz
      exact ⟨_, (hr j x _).mpr ⟨hx, rfl⟩,
        (hr i _ z).mpr ⟨hm j x hx, hz.trans (hact hx)⟩⟩
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨hx, rfl⟩ := (hr j x y).mp hxy
      exact (hr _ x z).mpr ⟨hx, ((hr i _ z).mp hyz).2.trans (hact hx).symm⟩
  exact ⟨⟨d, code, ht, hIso, hUnit, hProd⟩, rfl, hr⟩

theorem internal_mask_fixed_core_actions (base : BaseCollection s) {w d : U}
    (P : InternalQuinePairs s w) (hd : ∀ y, s y d ↔ ∃ c, s c P.family ∧ s y c)
    (E : FiniteGroupExhaustion.{u,v} (internalMaskGroup base w)) :
    ∃ A : FixedCoreActions s E, A.domain = d ∧ ∀ n i x y,
      CodedRelation s ((A.stage n).code i) x y ↔
        s x d ∧ y = maskedLabelAction P (E.embed n i).val x := by
  classical
  have hex := fun n => finite_mask_core_action base P hd (E.group n) (E.embed n)
    (E.map_one n) (E.map_mul n)
  let stage := fun n => Classical.choose (hex n)
  have hs := fun n => Classical.choose_spec (hex n)
  refine ⟨⟨d, stage, fun n => (hs n).1, ?_⟩, rfl, fun n => (hs n).2⟩
  intro n i x y hxy
  obtain ⟨hx, hy⟩ := ((hs n).2 i x y).mp hxy
  apply ((hs (n+1)).2 _ x y).mpr
  rw [exhaustion_lift_embed]
  exact ⟨hx, hy⟩

#print axioms internal_mask_fixed_core_actions
end FullBridge
