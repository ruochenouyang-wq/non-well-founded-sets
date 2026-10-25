import InternalCoinduction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem decoration_comparison_bisimulation (base : BaseCollection s) {a e f g : U}
    (hf : DecorationCode s a e f) (hg : DecorationCode s a e g) :
    ∃ r, Bisimulation s (CodedRelation s r) ∧
      ∀ u v, CodedRelation s r u v ↔ ∃ x, CodedRelation s f x u ∧ CodedRelation s g x v := by
  obtain ⟨fi, hfi⟩ := codedRelation_inverse base.pairing base.union base.powerset base.separation f
  obtain ⟨r, hr⟩ := codedRelation_composition base.pairing base.union base.powerset base.separation fi g
  have hi : ∀ u v, CodedRelation s r u v ↔ ∃ x, CodedRelation s f x u ∧ CodedRelation s g x v := by
    intro u v
    constructor
    · intro h
      obtain ⟨x, hux, hxv⟩ := (hr u v).mp h
      exact ⟨x, (hfi u x).mp hux, hxv⟩
    · rintro ⟨x, hxu, hxv⟩
      exact (hr u v).mpr ⟨x, (hfi u x).mpr hxu, hxv⟩
  refine ⟨r, ?_, hi⟩
  intro u v huv
  obtain ⟨x, hfxu, hgxv⟩ := (hi u v).mp huv
  have hx : s x a := by
    obtain ⟨p, hp, hpxu⟩ := hfxu
    obtain ⟨z, w, hz, hpzw⟩ := hf.1.1 p hp
    have h := (orderedPair_injective hpxu hpzw).1
    exact h ▸ hz
  constructor
  · intro w hw
    obtain ⟨y, hy, hexy, hfyw⟩ := (hf.2 x hx u hfxu w).mp hw
    obtain ⟨z, hgyz, _⟩ := hg.1.2 y hy
    exact ⟨z, (hg.2 x hx v hgxv z).mpr ⟨y, hy, hexy, hgyz⟩,
      (hi w z).mpr ⟨y, hfyw, hgyz⟩⟩
  · intro z hz
    obtain ⟨y, hy, hexy, hgyz⟩ := (hg.2 x hx v hgxv z).mp hz
    obtain ⟨w, hfyw, _⟩ := hf.1.2 y hy
    exact ⟨w, (hf.2 x hx u hfxu w).mpr ⟨y, hy, hexy, hfyw⟩,
      (hi w z).mpr ⟨y, hfyw, hgyz⟩⟩

theorem function_code_extensional (hext : Extensional s) {a f g : U}
    (hf : FunctionCode s a f) (hg : FunctionCode s a g)
    (hval : ∀ x u v, CodedRelation s f x u → CodedRelation s g x v → u = v) : f = g := by
  apply hext
  intro p
  constructor
  · intro hp
    obtain ⟨x, u, hx, hpxu⟩ := hf.1 p hp
    obtain ⟨v, hxv, _⟩ := hg.2 x hx
    have huv := hval x u v ⟨p, hp, hpxu⟩ hxv
    subst v
    obtain ⟨p', hp', hp'xu⟩ := hxv
    have hpp' := orderedPair_unique hext hpxu hp'xu
    exact hpp' ▸ hp'
  · intro hp
    obtain ⟨x, v, hx, hpxv⟩ := hg.1 p hp
    obtain ⟨u, hxu, _⟩ := hf.2 x hx
    have huv := hval x u v hxu ⟨p, hp, hpxv⟩
    subst v
    obtain ⟨p', hp', hp'xu⟩ := hxu
    have hpp' := orderedPair_unique hext hpxv hp'xu
    exact hpp' ▸ hp'

theorem internal_decoration_unique (base : BaseCollection s)
    {A E F G : InternalQuotient base}
    (hF : DecorationCode (internalMember base) A E F)
    (hG : DecorationCode (internalMember base) A E G) : F = G := by
  obtain ⟨R, hR, hi⟩ := decoration_comparison_bisimulation (internal_base_model base) hF hG
  apply function_code_extensional (internal_extensional base) hF.1 hG.1
  intro X V W hFV hGW
  exact internal_coded_coinduction base R hR V W ((hi V W).mpr ⟨X, hFV, hGW⟩)

theorem internal_afa (base : BaseCollection s) (hBAFA : BAFACode s) :
    AFACode (internalMember base) := by
  intro A E hGraph
  obtain ⟨F, hF⟩ := internal_graph_solvability base hBAFA A E hGraph
  exact ⟨F, hF, fun G hG => internal_decoration_unique base hG hF⟩

#print axioms internal_afa
end FullBridge
