import CodedMaskActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- A single source function codes the whole enlarged graph action. The
    group is all actual internal masks, not an external finite stage. -/
theorem coded_mask_graph_amalgam (base : BaseCollection s) {w B : U}
    (A : CodedMaskAction base w) (hB : TransitiveCode s B) (htB : Subset s A.domain B) :
    ∃ S e K, ∃ rho : InternalMask s w → U,
      GraphCode s S e ∧ EndExtensionCode s S e B ∧ FunctionCode s A.masks K ∧
      (∀ a, CodedRelation s K a.val (rho a)) ∧
      (∀ a, GraphIsoCode s S e S e (rho a)) ∧
      (∀ x y, CodedRelation s (rho (internalMaskOne base w)) x y → x = y) ∧
      (∀ a b x z, CodedRelation s (rho (internalMaskMul base a b)) x z ↔
        ∃ y, CodedRelation s (rho b) x y ∧ CodedRelation s (rho a) y z) ∧
      (∀ a x y, CodedRelation s (A.maps a) x y → CodedRelation s (rho a) x y) := by
  classical
  let F := codedMaskIsoFamily base A
  obtain ⟨M⟩ := internal_membership_amalgam base F A.transitive hB htB
  let ranges : InternalMask s w → U := fun a =>
    Classical.choose (M.copies.rangesFunction.2 a.val ((A.maskMembers a.val).mpr a.property))
  let codes : InternalMask s w → U := fun a =>
    Classical.choose (M.copies.codesFunction.2 a.val ((A.maskMembers a.val).mpr a.property))
  have hrange : ∀ a, CodedRelation s M.copies.ranges a.val (ranges a) := fun a =>
    (Classical.choose_spec (M.copies.rangesFunction.2 a.val ((A.maskMembers a.val).mpr a.property))).1
  have hcode : ∀ a, CodedRelation s M.copies.codes a.val (codes a) := fun a =>
    (Classical.choose_spec (M.copies.codesFunction.2 a.val ((A.maskMembers a.val).mpr a.property))).1
  have hc : ∀ a, CopyCode s A.domain B (A.maps a) (ranges a) (codes a) := fun a =>
    M.copies.copy a.val ((A.maskMembers a.val).mpr a.property) (ranges a) (codes a)
      (hrange a) (hcode a) (A.maps a) (A.mapCodes a)
  have hInt : ∀ a b, a ≠ b → ∀ x, s x (ranges a) ∧ s x (ranges b) ↔ s x A.domain := by
    intro a b hab x
    exact M.copies.overlaps a.val b.val _ _ (fun he => hab (Subtype.ext he)) (hrange a) (hrange b) x
  have hS : ∀ X, s X M.domain ↔ ∃ a, s X (ranges a) := by
    intro X
    constructor
    · intro hX
      obtain ⟨a, b, ha, hab, hXb⟩ := (M.domainMembers X).mp hX
      let a' : InternalMask s w := ⟨a, (A.maskMembers a).mp ha⟩
      have he := coded_function_value_unique M.copies.rangesFunction hab (hrange a')
      exact ⟨a', he ▸ hXb⟩
    · rintro ⟨a, hXa⟩
      exact (M.domainMembers X).mpr ⟨a.val, ranges a, (A.maskMembers a.val).mpr a.property, hrange a, hXa⟩
  let G := internalMaskGroup base w
  have htotal := general_copy_action_total_unique G A.maps ranges codes A.iso hc hInt hS A.mul
  have hev : ∀ a X Y, Eval s maskCopyTransitionFormula
      (cons Y (cons X (cons a.val (cons A.masks (cons M.copies.codes Fin.elim0))))) ↔
      ∃ b x, CodedRelation s (codes b) x X ∧ CodedRelation s (codes (internalMaskMul base a b)) x Y :=
    fun a X Y => (eval_maskCopyTransitionFormula a.val A.masks M.copies.codes X Y).trans
      (mask_copy_transition_iff base A.maskMembers M.copies.codesFunction codes hcode a X Y)
  have ht : ∀ a, s a A.masks → ∀ X, s X M.domain → ∃ Y,
      Eval s maskCopyTransitionFormula (cons Y (cons X (cons a (cons A.masks (cons M.copies.codes Fin.elim0))))) ∧
      ∀ Z, Eval s maskCopyTransitionFormula (cons Z (cons X (cons a (cons A.masks (cons M.copies.codes Fin.elim0))))) → Z = Y := by
    intro a ha X hX
    let a' : InternalMask s w := ⟨a, (A.maskMembers a).mp ha⟩
    obtain ⟨Y, hY, hu⟩ := htotal a' X hX
    exact ⟨Y, (hev a' X Y).mpr hY, fun Z hZ => hu Z ((hev a' X Z).mp hZ)⟩
  obtain ⟨K, hK, hKr⟩ := definable_function_family base maskCopyTransitionFormula
    (cons A.masks (cons M.copies.codes Fin.elim0)) A.masks M.domain ht
  let rho : InternalMask s w → U := fun a => Classical.choose (hK.2 a.val ((A.maskMembers a.val).mpr a.property))
  have hrho : ∀ a, CodedRelation s K a.val (rho a) := fun a =>
    (Classical.choose_spec (hK.2 a.val ((A.maskMembers a.val).mpr a.property))).1
  have hr : ∀ a, FunctionCode s M.domain (rho a) ∧ ∀ X Y, CodedRelation s (rho a) X Y ↔
      ∃ b x, CodedRelation s (codes b) x X ∧ CodedRelation s (codes (G.mul a b)) x Y := by
    intro a
    obtain ⟨_, hfun, hrel⟩ := (hKr a.val (rho a)).mp (hrho a)
    refine ⟨hfun, fun X Y => ?_⟩
    constructor
    · intro h
      exact (hev a X Y).mp ((hrel X Y).mp h).2
    · rintro ⟨b, x, hxX, hxY⟩
      have hX := (hS X).mpr ⟨b, ((hc b).2.2.1 X).mpr ⟨x, coded_function_domain (hc b).1 hxX, hxX⟩⟩
      exact (hrel X Y).mpr ⟨hX, (hev a X Y).mpr ⟨b, x, hxX, hxY⟩⟩
  have hId : ∀ x y, CodedRelation s (codes G.one) x y ↔ s x B ∧ y = x :=
    M.copies.identityMap _ (hcode G.one)
  have hClosed := fun a => M.closed a.val (ranges a) (hrange a)
  have hEdges := fun a => M.transported a.val (codes a) (hcode a)
  obtain ⟨hIso, hOne, hMul, hExt⟩ := general_copy_graph_action G A.maps ranges codes rho htB A.iso hc hS hId hClosed hEdges hr
  exact ⟨M.domain, M.edges, K, rho, M.graph, M.endExtension, hK, hrho, hIso, hOne, hMul, hExt⟩

#print axioms coded_mask_graph_amalgam
end FullBridge
