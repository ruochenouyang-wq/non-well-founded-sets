import IndexedFunctionFamilies
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

/-- An actual source-set-indexed family of old membership isomorphisms,
    with a specified identity index. No group laws are assumed here. -/
structure InternalIsoFamily (s : U → U → Prop) (G t : U) where
  code : U
  function : FunctionCode s G code
  iso : ∀ i f, CodedRelation s code i f → MembershipIsoCode s t t f
  one : U
  one_mem : s one G
  identity : ∀ f, CodedRelation s code one f → ∀ x y, CodedRelation s f x y → x = y

def InternalCopyValue (s : U → U → Prop) (one t act tag i x y : U) : Prop :=
  (i = one ∧ y = x) ∨ (i ≠ one ∧
    ((s x t ∧ ∃ f, CodedRelation s act i f ∧ CodedRelation s f x y) ∨
      (¬s x t ∧ ∃ p, IsOrderedPair s p i x ∧ IsOrderedPair s y tag p)))

/-- Free variables [value,input,index,identity,old-domain,old-family,tag]. -/
def internalCopyValueFormula : Formula 7 :=
  ((Formula.conj (.equal 2 3) (.equal 0 1))).disj
    (.conj (.impl (.equal 2 3) .bottom)
      ((Formula.conj (.member 1 4) (.ex (.conj (relatedFormula 6 3 0) (relatedFormula 0 2 1)))).disj
        (.conj (.impl (.member 1 4) .bottom) (.ex (.conj (orderedPairFormula 0 3 2) (orderedPairFormula 1 7 0))))))

theorem eval_internalCopyValueFormula (one t act tag i x y : U) :
    Eval s internalCopyValueFormula
      (cons y (cons x (cons i (cons one (cons t (cons act (cons tag Fin.elim0))))))) ↔
      InternalCopyValue s one t act tag i x y := by
  simp only [internalCopyValueFormula, Eval, eval_disj, eval_relatedFormula, eval_orderedPairFormula, InternalCopyValue]
  rfl

theorem internal_copy_value_identity {one t act tag x y : U} :
    InternalCopyValue s one t act tag one x y ↔ y = x := by
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact False.elim (h rfl)
  · exact fun h => Or.inl ⟨rfl, h⟩

theorem internal_copy_value_total_unique (base : BaseCollection s) {G t tag : U}
    (F : InternalIsoFamily s G t) {i : U} (hi : s i G) (x : U) :
    ∃ y, InternalCopyValue s F.one t F.code tag i x y ∧
      ∀ z, InternalCopyValue s F.one t F.code tag i x z → z = y := by
  classical
  by_cases hio : i = F.one
  · subst i
    exact ⟨x, internal_copy_value_identity.mpr rfl,
      fun z hz => internal_copy_value_identity.mp hz⟩
  · by_cases hxt : s x t
    · obtain ⟨f, hif, _⟩ := F.function.2 i hi
      obtain ⟨y, hxy, hu⟩ := (F.iso i f hif).1.2 x hxt
      refine ⟨y, Or.inr ⟨hio, Or.inl ⟨hxt, f, hif, hxy⟩⟩, ?_⟩
      intro z hz
      rcases hz with ⟨he, _⟩ | ⟨_, ⟨_, g, hig, hxz⟩ | ⟨hn, _⟩⟩
      · exact False.elim (hio he)
      · have hgf := coded_function_value_unique F.function hig hif
        subst g
        exact hu z hxz
      · exact False.elim (hn hxt)
    · obtain ⟨p, hp⟩ := orderedPair_exists base.pairing i x
      obtain ⟨y, hy⟩ := orderedPair_exists base.pairing tag p
      refine ⟨y, Or.inr ⟨hio, Or.inr ⟨hxt, p, hp, hy⟩⟩, ?_⟩
      intro z hz
      rcases hz with ⟨he, _⟩ | ⟨_, ⟨hx, _⟩ | ⟨_, q, hq, hz⟩⟩
      · exact False.elim (hio he)
      · exact False.elim (hxt hx)
      · have he := orderedPair_unique base.extensional hq hp
        subst q
        exact orderedPair_unique base.extensional hz hy

theorem internal_copy_value_old {G t tag i x y : U} (F : InternalIsoFamily s G t)
    (hi : s i G) (hx : s x t) :
    InternalCopyValue s F.one t F.code tag i x y ↔
      ∃ f, CodedRelation s F.code i f ∧ CodedRelation s f x y := by
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨_, ⟨_, h⟩ | ⟨hn, _⟩⟩)
    · obtain ⟨f, hif, _⟩ := F.function.2 F.one hi
      obtain ⟨v, hxv, _⟩ := (F.iso F.one f hif).1.2 _ hx
      exact ⟨f, hif, (F.identity f hif _ v hxv).symm ▸ hxv⟩
    · exact h
    · exact False.elim (hn hx)
  · rintro ⟨f, hif, hxy⟩
    by_cases hio : i = F.one
    · exact Or.inl ⟨hio, (F.identity f (hio ▸ hif) x y hxy).symm⟩
    · exact Or.inr ⟨hio, Or.inl ⟨hx, f, hif, hxy⟩⟩

theorem internal_copy_old_range {G t tag i x y : U} (F : InternalIsoFamily s G t)
    (hi : s i G) (hx : s x t) (hxy : InternalCopyValue s F.one t F.code tag i x y) : s y t := by
  obtain ⟨f, hif, hxy⟩ := (internal_copy_value_old F hi hx).mp hxy
  exact ((F.iso i f hif).2.2.1 y).mpr ⟨x, hx, hxy⟩

theorem internal_copy_fresh_value {one t act tag i x y : U}
    (hi : i ≠ one) (hx : ¬s x t) (hxy : InternalCopyValue s one t act tag i x y) :
    ∃ p, IsOrderedPair s p i x ∧ IsOrderedPair s y tag p := by
  rcases hxy with ⟨he, _⟩ | ⟨_, ⟨hx', _⟩ | ⟨_, h⟩⟩
  · exact False.elim (hi he)
  · exact False.elim (hx hx')
  · exact h

theorem internal_copy_value_injective {G t A tag : U}
    (F : InternalIsoFamily s G t) (htA : Subset s t A)
    (hfresh : ∀ p y, IsOrderedPair s y tag p → ¬s y A)
    {i x z y : U} (hi : s i G)
    (hxy : InternalCopyValue s F.one t F.code tag i x y)
    (hzy : InternalCopyValue s F.one t F.code tag i z y) : x = z := by
  classical
  by_cases hio : i = F.one
  · subst i
    exact (internal_copy_value_identity.mp hxy).symm.trans (internal_copy_value_identity.mp hzy)
  · by_cases hxt : s x t
    · by_cases hzt : s z t
      · obtain ⟨f, hif, hxf⟩ := (internal_copy_value_old F hi hxt).mp hxy
        obtain ⟨g, hig, hzg⟩ := (internal_copy_value_old F hi hzt).mp hzy
        have hgf := coded_function_value_unique F.function hig hif
        subst g
        exact (F.iso i f hif).2.1 x z y hxf hzg
      · obtain ⟨p, _, hp⟩ := internal_copy_fresh_value hio hzt hzy
        exact False.elim (hfresh p y hp (htA y (internal_copy_old_range F hi hxt hxy)))
    · by_cases hzt : s z t
      · obtain ⟨p, _, hp⟩ := internal_copy_fresh_value hio hxt hxy
        exact False.elim (hfresh p y hp (htA y (internal_copy_old_range F hi hzt hzy)))
      · obtain ⟨p, hp, hpy⟩ := internal_copy_fresh_value hio hxt hxy
        obtain ⟨q, hq, hqy⟩ := internal_copy_fresh_value hio hzt hzy
        have he := (orderedPair_injective hpy hqy).2
        subst q
        exact (orderedPair_injective hp hq).2

theorem internal_copy_distinct_overlap {G t A tag : U} (F : InternalIsoFamily s G t)
    (hfresh : ∀ p y, IsOrderedPair s y tag p → ¬s y A)
    {i j x z y : U} (hi : s i G) (hj : s j G) (hij : i ≠ j) (hxA : s x A) (hzA : s z A)
    (hxy : InternalCopyValue s F.one t F.code tag i x y)
    (hzy : InternalCopyValue s F.one t F.code tag j z y) : s y t := by
  classical
  by_cases hxt : s x t
  · exact internal_copy_old_range F hi hxt hxy
  · by_cases hzt : s z t
    · exact internal_copy_old_range F hj hzt hzy
    · by_cases hio : i = F.one
      · have hjo : j ≠ F.one := fun h => hij (hio.trans h.symm)
        obtain ⟨p, _, hp⟩ := internal_copy_fresh_value hjo hzt hzy
        have hyx := internal_copy_value_identity.mp (hio ▸ hxy)
        exact False.elim (hfresh p y hp (hyx.symm ▸ hxA))
      · by_cases hjo : j = F.one
        · obtain ⟨p, _, hp⟩ := internal_copy_fresh_value hio hxt hxy
          have hyz := internal_copy_value_identity.mp (hjo ▸ hzy)
          exact False.elim (hfresh p y hp (hyz.symm ▸ hzA))
        · obtain ⟨p, hp, hpy⟩ := internal_copy_fresh_value hio hxt hxy
          obtain ⟨q, hq, hqy⟩ := internal_copy_fresh_value hjo hzt hzy
          have he := (orderedPair_injective hpy hqy).2
          subst q
          exact False.elim (hij (orderedPair_injective hp hq).1)
end FullBridge
