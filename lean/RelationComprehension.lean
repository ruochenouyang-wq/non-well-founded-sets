import PairCoding

namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def relationRename {n : Nat} : Fin (n + 2) → Fin (n + 4) :=
  Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ))

def relationFormula {n} (p : Formula (n + 2)) : Formula (n + 2) :=
  .ex (.ex (.conj (.member 1 3) (.conj (.member 0 3)
    (.conj (orderedPairFormula 2 1 0) (p.rename relationRename)))))

theorem relation_env {n} (x y z d : U) (e : Fin n → U) :
    (fun i => cons y (cons x (cons z (cons d e))) (relationRename i)) =
      cons y (cons x e) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

theorem eval_relationFormula {n} (p : Formula (n + 2)) (z d : U) (e : Fin n → U) :
    Eval s (relationFormula p) (cons z (cons d e)) ↔
      ∃ x y, s x d ∧ s y d ∧ IsOrderedPair s z x y ∧ Eval s p (cons y (cons x e)) := by
  simp only [relationFormula, Eval, eval_orderedPairFormula, eval_rename, relation_env]
  rfl

theorem orderedPair_bound {d pd ppd x y p : U}
    (hpd : ∀ a, s a pd ↔ Subset s a d)
    (hppd : ∀ a, s a ppd ↔ Subset s a pd)
    (hx : s x d) (hy : s y d) (hp : IsOrderedPair s p x y) : s p ppd := by
  obtain ⟨a, b, ha, hb, hp⟩ := hp
  have had : s a pd := (hpd a).mpr (by
    intro z hz
    rcases (ha z).mp hz with rfl | rfl <;> exact hx)
  have hbd : s b pd := (hpd b).mpr (by
    intro z hz
    rcases (hb z).mp hz with rfl | rfl
    · exact hx
    · exact hy)
  apply (hppd p).mpr
  intro z hz
  rcases (hp z).mp hz with rfl | rfl
  · exact had
  · exact hbd

theorem bounded_relation_comprehension
    (hp : Pairing s) (hpow : PowerSet s) (hsep : Separation s)
    {n} (p : Formula (n + 2)) (e : Fin n → U) (d : U) :
    ∃ r, ∀ x y, CodedRelation s r x y ↔
      s x d ∧ s y d ∧ Eval s p (cons y (cons x e)) := by
  obtain ⟨pd, hpd⟩ := hpow d
  obtain ⟨ppd, hppd⟩ := hpow pd
  obtain ⟨r, hr⟩ := hsep (n + 1) (relationFormula p) (cons d e) ppd
  refine ⟨r, ?_⟩
  intro x y
  constructor
  · rintro ⟨z, hzr, hzxy⟩
    have hformula := ((hr z).mp hzr).2
    obtain ⟨a, b, had, hbd, hzab, hab⟩ := (eval_relationFormula p z d e).mp hformula
    obtain ⟨rfl, rfl⟩ := orderedPair_injective hzxy hzab
    exact ⟨had, hbd, hab⟩
  · rintro ⟨hxd, hyd, hxy⟩
    obtain ⟨z, hz⟩ := orderedPair_exists hp x y
    refine ⟨z, (hr z).mpr ?_, hz⟩
    exact ⟨orderedPair_bound hpd hppd hxd hyd hz,
      (eval_relationFormula p z d e).mpr ⟨x, y, hxd, hyd, hz, hxy⟩⟩

#print axioms bounded_relation_comprehension
end FullBridge
