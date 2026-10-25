import FiniteCodedUnions
namespace FullBridge
universe u v
variable {U : Type u} {s : U → U → Prop}

def CopyCode (s : U → U → Prop) (t A p B k : U) : Prop :=
  FunctionCode s A k ∧ InjectiveCode s k ∧ RangeCode s A k B ∧ Subset s t B ∧
    ∀ x y, CodedRelation s p x y → CodedRelation s k x y

theorem copy_with_exact_overlap (base : BaseCollection s) {t A p L : U}
    (hp : MembershipIsoCode s t t p) (htA : Subset s t A) (htL : Subset s t L) :
    ∃ B k, CopyCode s t A p B k ∧ ∀ x, s x B ∧ s x L ↔ s x t := by
  classical
  obtain ⟨B, k, hk, hi, hr, htB, hpk, _, havoid⟩ :=
    extend_coded_bijection_avoiding base hp.1 hp.2.1 hp.2.2.1 htA htL
  refine ⟨B, k, ⟨hk, hi, hr, htB, hpk⟩, fun y => ?_⟩
  constructor
  · rintro ⟨hyB, hyL⟩
    obtain ⟨x, _, hxy⟩ := (hr y).mp hyB
    by_cases hxt : s x t
    · obtain ⟨z, hxz, _⟩ := hp.1.2 x hxt
      have hzy := coded_function_value_unique hk (hpk x z hxz) hxy
      exact hzy ▸ (hp.2.2.1 z).mpr ⟨x, hxt, hxz⟩
    · exact False.elim (havoid x y hxy hxt hyL)
  · exact fun hy => ⟨htB y hy, htL y hy⟩

/-- Copies already built at the distinguished index and finitely listed
    indices. The bound is an actual source set used to choose the next copy. -/
structure PartialCopyFamily (s : U → U → Prop) {I : Type v}
    (t A : U) (one : I) (act : I → U) (is : List I) where
  ranges : I → U
  codes : I → U
  bound : U
  contains_A : Subset s A bound
  original_range : ranges one = A
  original_map : ∀ x y, CodedRelation s (codes one) x y ↔ s x A ∧ y = x
  maps : ∀ i, i = one ∨ i ∈ is → CopyCode s t A (act i) (ranges i) (codes i)
  bounded : ∀ i, i = one ∨ i ∈ is → Subset s (ranges i) bound
  overlaps : ∀ i j, (i = one ∨ i ∈ is) → (j = one ∨ j ∈ is) → i ≠ j →
    ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t

/-- Actual finite construction, retaining A itself as the identity copy.
    Repeated indices are harmless and do not create additional copies. -/
theorem finite_partial_copy_family (base : BaseCollection s) {I : Type v}
    {t A : U} (hA : TransitiveCode s A) (htA : Subset s t A)
    (one : I) (act : I → U) (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hOne : ∀ x y, CodedRelation s (act one) x y → x = y) (is : List I) :
    Nonempty (PartialCopyFamily s t A one act is) := by
  classical
  induction is with
  | nil =>
    obtain ⟨_, k, _, hk, _, hkr⟩ := membership_graph_identity_decoration base hA
    have hId : CopyCode s t A (act one) A k := by
      refine ⟨hk.1, ?_, ?_, htA, ?_⟩
      · intro x y z hxz hyz
        exact ((hkr x z).mp hxz).2.symm.trans ((hkr y z).mp hyz).2
      · intro y
        exact ⟨fun hy => ⟨y, hy, (hkr y y).mpr ⟨hy, rfl⟩⟩,
          fun ⟨x, hx, hxy⟩ => ((hkr x y).mp hxy).2.symm ▸ hx⟩
      · intro x y hxy
        exact (hkr x y).mpr ⟨htA x (coded_function_domain (hp one).1 hxy), (hOne x y hxy).symm⟩
    refine ⟨⟨fun _ => A, fun _ => k, A, fun _ h => h, rfl, hkr, ?_, ?_, ?_⟩⟩
    · intro i hi
      have hi' : i = one := by simpa using hi
      exact hi'.symm ▸ hId
    · intro _ _ _ h
      exact h
    · intro i j hi hj hij
      have hi' : i = one := by simpa using hi
      have hj' : j = one := by simpa using hj
      exact False.elim (hij (hi'.trans hj'.symm))
  | cons i is ih =>
    obtain ⟨F⟩ := ih
    by_cases hi : i = one ∨ i ∈ is
    · have hback : ∀ j, j = one ∨ j ∈ i :: is → j = one ∨ j ∈ is := by
        intro j hj
        rcases hj with hj | hj
        · exact Or.inl hj
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact hi
          · exact Or.inr hj
      exact ⟨⟨F.ranges, F.codes, F.bound, F.contains_A, F.original_range, F.original_map,
        fun j hj => F.maps j (hback j hj), fun j hj => F.bounded j (hback j hj),
        fun j k hj hk => F.overlaps j k (hback j hj) (hback k hk)⟩⟩
    · have hiOne : i ≠ one := fun h => hi (Or.inl h)
      have hnot : ∀ j, j = one ∨ j ∈ is → j ≠ i := by
        intro j hj heq
        exact hi (heq ▸ hj)
      have hback : ∀ j, j = one ∨ j ∈ i :: is → j ≠ i → j = one ∨ j ∈ is := by
        intro j hj hji
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr ((List.mem_cons.mp hj).resolve_left hji)
      obtain ⟨B, k, hk, hInt⟩ := copy_with_exact_overlap base (hp i) htA
        (fun x hx => F.contains_A x (htA x hx))
      obtain ⟨L, hL⟩ := binary_union_exists base.pairing base.union F.bound B
      let ranges : I → U := fun j => if j = i then B else F.ranges j
      let codes : I → U := fun j => if j = i then k else F.codes j
      have hcross : ∀ j, j = one ∨ j ∈ is → ∀ x, s x B ∧ s x (F.ranges j) ↔ s x t := by
        intro j hj x
        exact ⟨fun h => (hInt x).mp ⟨h.1, F.bounded j hj x h.2⟩,
          fun h => ⟨hk.2.2.2.1 x h, (F.maps j hj).2.2.2.1 x h⟩⟩
      refine ⟨⟨ranges, codes, L, (fun x hx => (hL x).mpr (Or.inl (F.contains_A x hx))),
        ?_, ?_, ?_, ?_, ?_⟩⟩
      · simpa [ranges, Ne.symm hiOne] using F.original_range
      · simpa [codes, Ne.symm hiOne] using F.original_map
      · intro j hj
        by_cases hji : j = i
        · subst j
          simpa [ranges, codes] using hk
        · simpa [ranges, codes, hji] using F.maps j (hback j hj hji)
      · intro j hj x hx
        by_cases hji : j = i
        · subst j
          exact (hL x).mpr (Or.inr (by simpa [ranges] using hx))
        · exact (hL x).mpr (Or.inl (F.bounded j (hback j hj hji) x (by simpa [ranges, hji] using hx)))
      · intro j l hj hl hjl x
        by_cases hji : j = i
        · subst j
          have hli : l ≠ i := Ne.symm hjl
          simpa [ranges, hli] using hcross l (hback l hl hli) x
        · by_cases hli : l = i
          · subst l
            have h := hcross j (hback j hj hji) x
            simpa [ranges, hji, and_comm] using h
          · simpa [ranges, hji, hli] using
              F.overlaps j l (hback j hj hji) (hback l hl hli) hjl x

/-- A supplied finite enumeration is used to build every copy; no copy family
    or simultaneous freshness condition is assumed as an interface. -/
theorem finite_copy_family (base : BaseCollection s) {I : Type v}
    {t A : U} (hA : TransitiveCode s A) (htA : Subset s t A)
    (one : I) (act : I → U) (hp : ∀ i, MembershipIsoCode s t t (act i))
    (hOne : ∀ x y, CodedRelation s (act one) x y → x = y)
    (is : List I) (hAll : ∀ i, i ∈ is) :
    ∃ ranges codes : I → U, ranges one = A ∧
      (∀ x y, CodedRelation s (codes one) x y ↔ s x A ∧ y = x) ∧
      (∀ i, CopyCode s t A (act i) (ranges i) (codes i)) ∧
      ∀ i j, i ≠ j → ∀ x, s x (ranges i) ∧ s x (ranges j) ↔ s x t := by
  obtain ⟨F⟩ := finite_partial_copy_family base hA htA one act hp hOne is
  exact ⟨F.ranges, F.codes, F.original_range, F.original_map,
    fun i => F.maps i (Or.inr (hAll i)),
    fun i j => F.overlaps i j (Or.inr (hAll i)) (Or.inr (hAll j))⟩

#print axioms finite_copy_family
end FullBridge
