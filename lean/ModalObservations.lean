import MemberCoalgebraMaps

namespace FullBridge
universe u v w

inductive ModalFormula (Atom : Type w) : Type w where
  | atom : Atom → ModalFormula Atom
  | bottom : ModalFormula Atom
  | conj : ModalFormula Atom → ModalFormula Atom → ModalFormula Atom
  | impl : ModalFormula Atom → ModalFormula Atom → ModalFormula Atom
  | diamond : ModalFormula Atom → ModalFormula Atom
  | box : ModalFormula Atom → ModalFormula Atom

def ModalEval {U : Type u} {Atom : Type w} (s : U → U → Prop)
    (val : Atom → U → Prop) : ModalFormula Atom → U → Prop
  | .atom p, a => val p a
  | .bottom, _ => False
  | .conj p q, a => ModalEval s val p a ∧ ModalEval s val q a
  | .impl p q, a => ModalEval s val p a → ModalEval s val q a
  | .diamond p, a => ∃ x, s x a ∧ ModalEval s val p x
  | .box p, a => ∀ x, s x a → ModalEval s val p x

/-- Ordinary modal truth is preserved and reflected, provided atomic labels
    are pulled back along the map. Global surjectivity is unnecessary. -/
theorem exact_members_modal_invariance {U : Type u} {V : Type v} {Atom : Type w}
    {s : U → U → Prop} {t : V → V → Prop} {f : U → V}
    (hf : ExactMembers s t f) (valU : Atom → U → Prop) (valV : Atom → V → Prop)
    (hv : ∀ p x, valU p x ↔ valV p (f x)) (p : ModalFormula Atom) (a : U) :
    ModalEval s valU p a ↔ ModalEval t valV p (f a) := by
  induction p generalizing a with
  | atom p => exact hv p a
  | bottom => exact Iff.rfl
  | conj p q ihp ihq => exact and_congr (ihp a) (ihq a)
  | impl p q ihp ihq =>
      exact ⟨fun h hp => (ihq a).mp (h ((ihp a).mpr hp)),
        fun h hp => (ihq a).mpr (h ((ihp a).mp hp))⟩
  | diamond p ih =>
      constructor
      · rintro ⟨x, hx, hp⟩
        exact ⟨f x, (hf a (f x)).mpr ⟨x, hx, rfl⟩, (ih x).mp hp⟩
      · rintro ⟨y, hy, hp⟩
        obtain ⟨x, hx, rfl⟩ := (hf a y).mp hy
        exact ⟨x, hx, (ih x).mpr hp⟩
  | box p ih =>
      constructor
      · intro h y hy
        obtain ⟨x, hx, rfl⟩ := (hf a y).mp hy
        exact (ih x).mp (h x hx)
      · intro h x hx
        exact (ih x).mpr (h (f x) ((hf a (f x)).mpr ⟨x, hx, rfl⟩))

/-- External bisimulation invariance; stable labels are an explicit premise. -/
theorem bisimulation_modal_invariance {U : Type u} {Atom : Type w}
    {s R : U → U → Prop} (hR : Bisimulation s R) (val : Atom → U → Prop)
    (hv : ∀ p x y, R x y → (val p x ↔ val p y))
    (p : ModalFormula Atom) {a b : U} (hab : R a b) :
    ModalEval s val p a ↔ ModalEval s val p b := by
  induction p generalizing a b with
  | atom p => exact hv p a b hab
  | bottom => exact Iff.rfl
  | conj p q ihp ihq => exact and_congr (ihp hab) (ihq hab)
  | impl p q ihp ihq =>
      exact ⟨fun h hp => (ihq hab).mp (h ((ihp hab).mpr hp)),
        fun h hp => (ihq hab).mpr (h ((ihp hab).mp hp))⟩
  | diamond p ih =>
      constructor
      · rintro ⟨x, hx, hp⟩
        obtain ⟨y, hy, hxy⟩ := (hR a b hab).1 x hx
        exact ⟨y, hy, (ih hxy).mp hp⟩
      · rintro ⟨y, hy, hp⟩
        obtain ⟨x, hx, hxy⟩ := (hR a b hab).2 y hy
        exact ⟨x, hx, (ih hxy).mpr hp⟩
  | box p ih =>
      constructor
      · intro h y hy
        obtain ⟨x, hx, hxy⟩ := (hR a b hab).2 y hy
        exact (ih hxy).mp (h x hx)
      · intro h x hx
        obtain ⟨y, hy, hxy⟩ := (hR a b hab).1 x hx
        exact (ih hxy).mpr (h y hy)

abbrev PureModal := ModalFormula _root_.Empty
def pureVal {U : Type u} : _root_.Empty → U → Prop := fun p => nomatch p
def PureModalEval {U : Type u} (s : U → U → Prop) (p : PureModal) (a : U) : Prop :=
  ModalEval s pureVal p a

theorem internal_modal_invariance {U : Type u} {s : U → U → Prop}
    (base : BaseCollection s) {Atom : Type w}
    (val : Atom → InternalQuotient base → Prop) (p : ModalFormula Atom) (a : U) :
    ModalEval s (fun b x => val b (internalCode base x)) p a ↔
      ModalEval (internalMember base) val p (internalCode base a) :=
  exact_members_modal_invariance (internal_exact_members base) _ _ (fun _ _ => Iff.rfl) p a

theorem internal_pure_modal_invariance {U : Type u} {s : U → U → Prop}
    (base : BaseCollection s) (p : PureModal) (a : U) :
    PureModalEval s p a ↔ PureModalEval (internalMember base) p (internalCode base a) :=
  exact_members_modal_invariance (internal_exact_members base) _ _ (fun p => nomatch p) p a

theorem internal_code_same_modal_theory {U : Type u} {s : U → U → Prop}
    (base : BaseCollection s) {a b : U} (h : internalCode base a = internalCode base b)
    (p : PureModal) : PureModalEval s p a ↔ PureModalEval s p b := by
  rw [internal_pure_modal_invariance base p a, internal_pure_modal_invariance base p b, h]

/-- Standard translation uses membership in the direction child-in-parent. -/
def pureModalTranslate : PureModal → {n : Nat} → Fin n → Formula n
  | .atom p, _, _ => nomatch p
  | .bottom, _, _ => .bottom
  | .conj p q, _, i => .conj (pureModalTranslate p i) (pureModalTranslate q i)
  | .impl p q, _, i => .impl (pureModalTranslate p i) (pureModalTranslate q i)
  | .diamond p, _, i => .ex (.conj (.member 0 i.succ) (pureModalTranslate p 0))
  | .box p, _, i => .all (.impl (.member 0 i.succ) (pureModalTranslate p 0))

theorem pure_modal_standard_translation {U : Type u} (s : U → U → Prop)
    (p : PureModal) {n : Nat} (i : Fin n) (e : Fin n → U) :
    Eval s (pureModalTranslate p i) e ↔ PureModalEval s p (e i) := by
  induction p generalizing n with
  | atom p => exact nomatch p
  | bottom => exact Iff.rfl
  | conj p q ihp ihq => exact and_congr (ihp i e) (ihq i e)
  | impl p q ihp ihq =>
      exact ⟨fun h hp => (ihq i e).mp (h ((ihp i e).mpr hp)),
        fun h hp => (ihq i e).mpr (h ((ihp i e).mp hp))⟩
  | diamond p ih =>
      change (∃ x, s (cons x e 0) (cons x e i.succ) ∧
        Eval s (pureModalTranslate p 0) (cons x e)) ↔
        ∃ x, s x (e i) ∧ PureModalEval s p x
      simp only [cons_zero, cons_succ]
      exact exists_congr (fun x => and_congr Iff.rfl (ih 0 (cons x e)))
  | box p ih =>
      change (∀ x, s (cons x e 0) (cons x e i.succ) →
        Eval s (pureModalTranslate p 0) (cons x e)) ↔
        ∀ x, s x (e i) → PureModalEval s p x
      simp only [cons_zero, cons_succ]
      exact forall_congr' (fun x => imp_congr_right (fun _ => ih 0 (cons x e)))

end FullBridge
