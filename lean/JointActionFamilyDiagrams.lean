import ActionFamilyMoves
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- All blocks and all internal masks are coded by one actual source function.
    No family of external action graphs is substituted for this code. -/
theorem action_family_joint_graph_action (base : BaseCollection s) {w O N E : U}
    (P : CodedMaskAction base w) (h : ActionFamilyCode base w O)
    (hN : ∀ X, s X N ↔ OrbitDiagramNode s O X)
    (hE : ∀ X Y, CodedRelation s E X Y ↔ FamilyDiagramEdge s O X Y) :
    ∃ G : CodedMaskGraphAction base P N E, ∀ i X Y,
      CodedRelation s (G.maps i) X Y ↔ FamilyDiagramMove s O i.val X Y := by
  classical
  have ht : ∀ i, s i P.masks → ∀ X, s X N → ∃ Y,
      Eval s familyDiagramMoveFormula (cons Y (cons X (cons i (cons O Fin.elim0)))) ∧
      ∀ Z, Eval s familyDiagramMoveFormula (cons Z (cons X (cons i (cons O Fin.elim0)))) → Z = Y := by
    intro i hi X hX
    let I : InternalMask s w := ⟨i, (P.maskMembers i).mp hi⟩
    obtain ⟨Y, hY, hu⟩ := family_diagram_move_total_unique base h I ((hN X).mp hX)
    exact ⟨Y, (eval_familyDiagramMoveFormula Y X i O).mpr hY,
      fun Z hZ => hu Z ((eval_familyDiagramMoveFormula Z X i O).mp hZ)⟩
  obtain ⟨K, hK, hk⟩ := definable_function_family base familyDiagramMoveFormula
    (cons O Fin.elim0) P.masks N ht
  let rho : InternalMask s w → U := fun i => Classical.choose (hK.2 i.val ((P.maskMembers i.val).mpr i.property))
  have hrho : ∀ i, CodedRelation s K i.val (rho i) := fun i =>
    (Classical.choose_spec (hK.2 i.val ((P.maskMembers i.val).mpr i.property))).1
  have hf : ∀ i, FunctionCode s N (rho i) := fun i => ((hk i.val (rho i)).mp (hrho i)).2.1
  have hr : ∀ i X Y, CodedRelation s (rho i) X Y ↔ FamilyDiagramMove s O i.val X Y := by
    intro i X Y
    have hh := ((hk i.val (rho i)).mp (hrho i)).2.2 X Y
    rw [eval_familyDiagramMoveFormula] at hh
    exact hh.trans ⟨fun h => h.2, fun hm => ⟨(hN X).mpr (family_diagram_move_nodes base h i hm).1, hm⟩⟩
  have hi : ∀ i, GraphIsoCode s N E N E (rho i) := by
    intro i
    refine ⟨hf i, ?_, ?_, ?_⟩
    · intro X Y Z hx hy
      exact family_diagram_move_injective base h i ((hr i X Z).mp hx) ((hr i Y Z).mp hy)
    · intro Y
      constructor
      · intro hY
        obtain ⟨X, hx, hxy⟩ := family_diagram_move_surjective base h i ((hN Y).mp hY)
        exact ⟨X, (hN X).mpr hx, (hr i X Y).mpr hxy⟩
      · rintro ⟨X, _, hxy⟩
        exact (hN Y).mpr (family_diagram_move_nodes base h i ((hr i X Y).mp hxy)).2
    · intro X Y XX YY hx hy
      exact (hE X Y).trans ((family_diagram_move_edges base h i
        ((hr i X XX).mp hx) ((hr i Y YY).mp hy)).trans (hE XX YY).symm)
  have hone : ∀ X Y, CodedRelation s (rho (internalMaskOne base w)) X Y → X = Y :=
    fun X Y hm => family_diagram_move_one base h ((hr _ X Y).mp hm)
  have hmul : ∀ i j X Z, CodedRelation s (rho (internalMaskMul base i j)) X Z ↔
      ∃ Y, CodedRelation s (rho j) X Y ∧ CodedRelation s (rho i) Y Z := by
    intro i j X Z
    rw [hr, family_diagram_move_mul base h]
    exact exists_congr (fun Y => and_congr (hr j X Y).symm (hr i Y Z).symm)
  exact ⟨⟨K, hK, rho, hrho, hi, hone, hmul⟩, hr⟩

#print axioms action_family_joint_graph_action
end FullBridge
