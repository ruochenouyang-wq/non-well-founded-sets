import CountableBafaAutomorphisms
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem extend_coded_bijection_avoiding (base : BaseCollection s) {a b p A L : U}
    (hp : FunctionCode s a p) (hi : InjectiveCode s p) (hr : RangeCode s a p b)
    (haA : Subset s a A) (hbL : Subset s b L) :
    ∃ B k, FunctionCode s A k ∧ InjectiveCode s k ∧ RangeCode s A k B ∧
      Subset s b B ∧ (∀ x y, CodedRelation s p x y → CodedRelation s k x y) ∧
      (∀ x y, CodedRelation s k x y → s y b → CodedRelation s p x y) ∧
      (∀ x y, CodedRelation s k x y → ¬s x a → ¬s y L) := by
  obtain ⟨c, hc⟩ := base.separation 1 (.impl (.member 0 1) .bottom) (cons a Fin.elim0) A
  have hc' : ∀ x, s x c ↔ s x A ∧ ¬s x a := hc
  obtain ⟨d, g, hg, hgi, hgd, hdis⟩ := fresh_parameter_copy base c L
  obtain ⟨B, hB⟩ := binary_union_exists base.pairing base.union b d
  obtain ⟨k, hkmem, hk⟩ := coded_relation_union base p g
  have hpB : ∀ x y, CodedRelation s p x y → s y b :=
    fun x y h => (hr y).mpr ⟨x, coded_function_domain hp h, h⟩
  have hgD : ∀ x y, CodedRelation s g x y → s y d :=
    fun x y h => (hgd y).mpr ⟨x, coded_function_domain hg h, h⟩
  have hsep : ∀ x y z, CodedRelation s p x z → CodedRelation s g y z → False :=
    fun x y z hpz hgz => hdis z (hgD y z hgz) (hbL z (hpB x z hpz))
  have hkFun : FunctionCode s A k := by
    constructor
    · intro z hz
      rcases (hkmem z).mp hz with hz | hz
      · obtain ⟨x, y, hx, hxy⟩ := hp.1 z hz
        exact ⟨x, y, haA x hx, hxy⟩
      · obtain ⟨x, y, hx, hxy⟩ := hg.1 z hz
        exact ⟨x, y, ((hc' x).mp hx).1, hxy⟩
    · intro x hx
      by_cases hxa : s x a
      · obtain ⟨y, hxy, hu⟩ := hp.2 x hxa
        refine ⟨y, (hk x y).mpr (Or.inl hxy), ?_⟩
        intro z hxz
        rcases (hk x z).mp hxz with hpz | hgz
        · exact hu z hpz
        · exact False.elim (((hc' x).mp (coded_function_domain hg hgz)).2 hxa)
      · have hxc := (hc' x).mpr ⟨hx, hxa⟩
        obtain ⟨y, hxy, hu⟩ := hg.2 x hxc
        refine ⟨y, (hk x y).mpr (Or.inr hxy), ?_⟩
        intro z hxz
        rcases (hk x z).mp hxz with hpz | hgz
        · exact False.elim (hxa (coded_function_domain hp hpz))
        · exact hu z hgz
  refine ⟨B, k, hkFun, ?_, ?_, (fun x hx => (hB x).mpr (Or.inl hx)),
    (fun x y h => (hk x y).mpr (Or.inl h)), ?_, ?_⟩
  · intro x y z hxz hyz
    rcases (hk x z).mp hxz with hx | hx <;> rcases (hk y z).mp hyz with hy | hy
    · exact hi x y z hx hy
    · exact False.elim (hsep x y z hx hy)
    · exact False.elim (hsep y x z hy hx)
    · exact hgi x y z hx hy
  · intro y
    constructor
    · intro hy
      rcases (hB y).mp hy with hy | hy
      · obtain ⟨x, hx, hxy⟩ := (hr y).mp hy
        exact ⟨x, haA x hx, (hk x y).mpr (Or.inl hxy)⟩
      · obtain ⟨x, hx, hxy⟩ := (hgd y).mp hy
        exact ⟨x, ((hc' x).mp hx).1, (hk x y).mpr (Or.inr hxy)⟩
    · rintro ⟨x, _, hxy⟩
      exact (hB y).mpr (((hk x y).mp hxy).elim (fun h => Or.inl (hpB x y h))
        (fun h => Or.inr (hgD x y h)))
  · intro x y hxy hyb
    rcases (hk x y).mp hxy with h | h
    · exact h
    · exact False.elim (hdis y (hgD x y h) (hbL y hyb))

  · intro x y hxy hxa
    rcases (hk x y).mp hxy with h | h
    · exact False.elim (hxa (coded_function_domain hp h))
    · exact hdis y (hgD x y h)

/-- Actual inverse of a coded bijection; the auxiliary empty graphs are used
    only to reuse the already verified graph-isomorphism inverse construction. -/
theorem coded_bijection_inverse (base : BaseCollection s) {a b p : U}
    (hf : FunctionCode s a p) (hi : InjectiveCode s p) (hr : RangeCode s a p b) :
    ∃ q, FunctionCode s b q ∧ InjectiveCode s q ∧ RangeCode s b q a ∧
      ∀ y x, CodedRelation s q y x ↔ CodedRelation s p x y := by
  obtain ⟨e, he⟩ := base.empty
  have hEmpty : ∀ x y, ¬CodedRelation s e x y := by
    rintro x y ⟨z, hz, _⟩
    exact he z hz
  have hp : GraphIsoCode s a e b e p := by
    refine ⟨hf, hi, hr, ?_⟩
    intro x y X Y _ _
    exact ⟨fun h => False.elim (hEmpty x y h), fun h => False.elim (hEmpty X Y h)⟩
  obtain ⟨q, hq, hqr⟩ := graph_iso_inverse base hp
  exact ⟨q, hq.1, hq.2.1, hq.2.2.1, hqr⟩

/-- Glue a bijection to its inverse when the overlap is already involutive. -/
theorem coded_bijection_involution_union (base : BaseCollection s) {a b p : U}
    (hf : FunctionCode s a p) (hi : InjectiveCode s p) (hr : RangeCode s a p b)
    (hover : ∀ x y, CodedRelation s p x y → s y a → CodedRelation s p y x) :
    ∃ S r, (∀ x, s x S ↔ s x a ∨ s x b) ∧
      FunctionCode s S r ∧ InjectiveCode s r ∧ RangeCode s S r S ∧
      (∀ x y, CodedRelation s r x y → CodedRelation s r y x) ∧
      (∀ x y, CodedRelation s r x y ↔ CodedRelation s p x y ∨ CodedRelation s p y x) := by
  obtain ⟨q, hq, _, _, hqr⟩ := coded_bijection_inverse base hf hi hr
  obtain ⟨S, hS⟩ := binary_union_exists base.pairing base.union a b
  obtain ⟨r, hrmem, hrr⟩ := coded_relation_union base p q
  have hr' : ∀ x y, CodedRelation s r x y ↔ CodedRelation s p x y ∨ CodedRelation s p y x := by
    intro x y
    rw [hrr x y, hqr x y]
  have hs : ∀ x y, CodedRelation s r x y → CodedRelation s r y x :=
    fun x y h => (hr' y x).mpr ((hr' x y).mp h).symm
  have hcross : ∀ x y z, CodedRelation s p x y → CodedRelation s p z x → y = z := by
    intro x y z hxy hzx
    exact coded_function_value_unique hf hxy (hover z x hzx (coded_function_domain hf hxy))
  have hfun : FunctionCode s S r := by
    constructor
    · intro z hz
      rcases (hrmem z).mp hz with hz | hz
      · obtain ⟨x, y, hx, hp⟩ := hf.1 z hz
        exact ⟨x, y, (hS x).mpr (Or.inl hx), hp⟩
      · obtain ⟨x, y, hx, hp⟩ := hq.1 z hz
        exact ⟨x, y, (hS x).mpr (Or.inr hx), hp⟩
    · intro x hx
      have hex : ∃ y, CodedRelation s r x y := by
        rcases (hS x).mp hx with hx | hx
        · obtain ⟨y, hxy, _⟩ := hf.2 x hx
          exact ⟨y, (hr' x y).mpr (Or.inl hxy)⟩
        · obtain ⟨y, hxy, _⟩ := hq.2 x hx
          exact ⟨y, (hrr x y).mpr (Or.inr hxy)⟩
      obtain ⟨y, hxy⟩ := hex
      refine ⟨y, hxy, ?_⟩
      intro z hxz
      rcases (hr' x z).mp hxz with hz | hz <;> rcases (hr' x y).mp hxy with hy | hy
      · exact coded_function_value_unique hf hz hy
      · exact hcross x z y hz hy
      · exact (hcross x y z hy hz).symm
      · exact hi z y x hz hy
  refine ⟨S, r, hS, hfun, ?_, ?_, hs, hr'⟩
  · intro x y z hxz hyz
    exact coded_function_value_unique hfun (hs x z hxz) (hs y z hyz)
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hyx, _⟩ := hfun.2 y hy
      have hxy := hs y x hyx
      exact ⟨x, coded_function_domain hfun hxy, hxy⟩
    · rintro ⟨x, _, hxy⟩
      exact coded_function_domain hfun (hs x y hxy)

/-- Two copies of A overlap exactly in the old domain t. The permutation on
    their union is an actual coded involution extending the prescribed one.
    Membership preservation of the later amalgamated graph is a separate obligation. -/
theorem internal_involution_two_copies (base : BaseCollection s) {t p A : U}
    (hp : MembershipIsoCode s t t p)
    (hinv : ∀ x y, CodedRelation s p x y → CodedRelation s p y x)
    (htA : Subset s t A) :
    ∃ B k S r, FunctionCode s A k ∧ InjectiveCode s k ∧ RangeCode s A k B ∧
      (∀ x, s x B ∧ s x A ↔ s x t) ∧
      (∀ x y, CodedRelation s p x y → CodedRelation s k x y) ∧
      (∀ x, s x S ↔ s x A ∨ s x B) ∧
      FunctionCode s S r ∧ InjectiveCode s r ∧ RangeCode s S r S ∧
      (∀ x y, CodedRelation s r x y → CodedRelation s r y x) ∧
      (∀ x y, CodedRelation s r x y ↔ CodedRelation s k x y ∨ CodedRelation s k y x) ∧
      (∀ x y, CodedRelation s p x y → CodedRelation s r x y) := by
  obtain ⟨B, k, hk, hki, hkr, htB, hpk, hOld, hFresh⟩ :=
    extend_coded_bijection_avoiding base hp.1 hp.2.1 hp.2.2.1 htA htA
  have hInt : ∀ x, s x B ∧ s x A ↔ s x t := by
    intro x
    constructor
    · rintro ⟨hxB, hxA⟩
      obtain ⟨y, _, hyx⟩ := (hkr x).mp hxB
      have hyt : s y t := by
        apply Classical.byContradiction
        intro hyt
        exact hFresh y x hyx hyt hxA
      obtain ⟨z, hyz, _⟩ := hp.1.2 y hyt
      have hzx := coded_function_value_unique hk (hpk y z hyz) hyx
      exact hzx ▸ (hp.2.2.1 z).mpr ⟨y, hyt, hyz⟩
    · exact fun h => ⟨htB x h, htA x h⟩
  have hover : ∀ x y, CodedRelation s k x y → s y A → CodedRelation s k y x := by
    intro x y hxy hyA
    have hyB := (hkr y).mpr ⟨x, coded_function_domain hk hxy, hxy⟩
    have hyt := (hInt y).mp ⟨hyB, hyA⟩
    exact hpk y x (hinv x y (hOld x y hxy hyt))
  obtain ⟨S, r, hS, hr, hri, hrr, hsym, hrk⟩ := coded_bijection_involution_union base hk hki hkr hover
  exact ⟨B, k, S, r, hk, hki, hkr, hInt, hpk, hS, hr, hri, hrr, hsym, hrk,
    fun x y h => (hrk x y).mpr (Or.inl (hpk x y h))⟩

theorem coded_symmetric_function_square {a r : U} (hf : FunctionCode s a r)
    (hs : ∀ x y, CodedRelation s r x y → CodedRelation s r y x)
    {x y z : U} (hxy : CodedRelation s r x y) (hyz : CodedRelation s r y z) : z = x :=
  coded_function_value_unique hf hyz (hs x y hxy)

#print axioms internal_involution_two_copies

end FullBridge
