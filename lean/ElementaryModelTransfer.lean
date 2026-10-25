import ModelMaps
import ChoiceAxiom

namespace FullBridge
universe u v
variable {U : Type u} {V : Type v}
variable {s : U → U → Prop} {t : V → V → Prop}

/-- Sentences are preserved in both directions without any surjectivity assumption. -/
theorem elementary_map_sentence {j : U → V} (hj : ElementaryMap s t j)
    (p : Formula 0) : Eval s p Fin.elim0 ↔ Eval t p Fin.elim0 := by
  have h := hj p Fin.elim0
  have he : (fun i : Fin 0 => j (Fin.elim0 i)) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [he] at h
  exact h

namespace ElementaryBaseSyntax

def extensionalSentence : Formula 0 :=
  .all (.all (.impl (.all ((Formula.member 0 2).iffF (.member 0 1))) (.equal 1 0)))

def emptySentence : Formula 0 :=
  .ex (.all (.impl (.member 0 1) .bottom))

def pairingSentence : Formula 0 :=
  .all (.all (.ex (pairFormula 0 2 1)))

def unionSentence : Formula 0 :=
  .all (.ex (.all ((Formula.member 0 1).iffF
    (.ex (.conj (.member 0 3) (.member 1 0))))))

def powerSentence : Formula 0 :=
  .all (.ex (.all ((Formula.member 0 1).iffF
    (.all (.impl (.member 0 1) (.member 0 3))))))

def infinitySentence : Formula 0 :=
  .ex (.conj (.ex (.conj (.member 0 1) (.all (.impl (.member 0 1) .bottom))))
    (.all (.impl (.member 0 1) (.ex (.conj (.member 0 2)
      (.all ((Formula.member 0 1).iffF ((Formula.member 0 2).disj (.equal 0 2)))))))))

/-- This finite conjunction contains precisely the six non-schematic base axioms. -/
def finiteBaseSentence : Formula 0 :=
  .conj extensionalSentence (.conj emptySentence (.conj pairingSentence
    (.conj unionSentence (.conj powerSentence infinitySentence))))

end ElementaryBaseSyntax

open ElementaryBaseSyntax

theorem eval_finiteBaseSentence (r : U → U → Prop) :
    Eval r finiteBaseSentence Fin.elim0 ↔
      Extensional r ∧ Empty r ∧ Pairing r ∧ Union r ∧ PowerSet r ∧ Infinity r := by
  simp only [finiteBaseSentence, extensionalSentence, emptySentence, pairingSentence,
    unionSentence, powerSentence, infinitySentence, Eval, eval_iffF, eval_disj,
    eval_pairFormula, Extensional, Empty, Pairing, Union, PowerSet, Subset,
    Infinity, IsEmpty, IsSuccessor, IsPair, cons_zero]
  rfl

namespace ElementaryBaseSyntax

/-- Instance with free variables [a, parameters], and bound variables [x, b]. -/
def separationInstance {n} (p : Formula (n+1)) : Formula (n+1) :=
  .ex (.all ((Formula.member 0 1).iffF (.conj (.member 0 2)
    (p.rename (Fin.cases 0 (fun i => i.succ.succ.succ))))))

end ElementaryBaseSyntax

open ElementaryBaseSyntax

theorem eval_separationInstance (r : U → U → Prop) {n} (p : Formula (n+1))
    (a : U) (v : Fin n → U) :
    Eval r (separationInstance p) (cons a v) ↔
      ∃ b, ∀ x, r x b ↔ r x a ∧ Eval r p (cons x v) := by
  have he (x b : U) :
      (fun i => cons x (cons b (cons a v))
        (Fin.cases 0 (fun i => i.succ.succ.succ) i)) = cons x v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [separationInstance, Eval, eval_iffF, eval_rename, he, cons_zero]
  rfl

namespace ElementaryBaseSyntax

/-- A full Collection instance, retaining the actual finite relation formula. -/
def collectionInstance {n} (p : Formula (n+2)) : Formula (n+1) :=
  .impl
    (.all (.impl (.member 0 1)
      (.ex (p.rename (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ)))))))
    (.ex (.all (.impl (.member 0 2)
      (.ex (.conj (.member 0 2)
        (p.rename (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ)))))))))

end ElementaryBaseSyntax

open ElementaryBaseSyntax

theorem eval_collectionInstance (r : U → U → Prop) {n} (p : Formula (n+2))
    (a : U) (v : Fin n → U) :
    Eval r (collectionInstance p) (cons a v) ↔
      ((∀ x, r x a → ∃ y, Eval r p (cons y (cons x v))) →
        ∃ b, ∀ x, r x a → ∃ y, r y b ∧ Eval r p (cons y (cons x v))) := by
  have he (x y : U) :
      (fun i => cons y (cons x (cons a v))
        (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ)) i)) =
      cons y (cons x v) := by
    funext i
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) i
  have hf (b x y : U) :
      (fun i => cons y (cons x (cons b (cons a v)))
        (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ)) i)) =
      cons y (cons x v) := by
    funext i
    exact Fin.cases rfl (fun k => Fin.cases rfl (fun _ => rfl) k) i
  simp only [collectionInstance, Eval, eval_rename, he, hf, cons_zero]
  rfl

namespace ElementaryBaseSyntax

end ElementaryBaseSyntax

/-- Reflection covers every finite formula and every source parameter tuple. -/
theorem elementary_map_separation_reflect {j : U → V} (hj : ElementaryMap s t j)
    (ht : Separation t) : Separation s := by
  intro n p v a
  apply (eval_separationInstance s p a v).mp
  apply (hj (ElementaryBaseSyntax.separationInstance p) (cons a v)).mpr
  have he : (fun i => j (cons a v i)) = cons (j a) (fun i => j (v i)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he]
  exact (eval_separationInstance t p (j a) (fun i => j (v i))).mpr
    (ht n p (fun i => j (v i)) (j a))

theorem elementary_map_collection_reflect {j : U → V} (hj : ElementaryMap s t j)
    (ht : Collection t) : Collection s := by
  intro n p v a
  apply (eval_collectionInstance s p a v).mp
  apply (hj (ElementaryBaseSyntax.collectionInstance p) (cons a v)).mpr
  have he : (fun i => j (cons a v i)) = cons (j a) (fun i => j (v i)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [he]
  exact (eval_collectionInstance t p (j a) (fun i => j (v i))).mpr
    (ht n p (fun i => j (v i)) (j a))

theorem elementary_map_base_reflect {j : U → V} (hj : ElementaryMap s t j)
    (bt : BaseCollection t) : BaseCollection s := by
  have hf := (eval_finiteBaseSentence s).mp
    ((elementary_map_sentence hj ElementaryBaseSyntax.finiteBaseSentence).mpr
      ((eval_finiteBaseSentence t).mpr
        ⟨bt.extensional, bt.empty, bt.pairing, bt.union, bt.powerset, bt.infinity⟩))
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2,
    elementary_map_separation_reflect hj bt.separation,
    elementary_map_collection_reflect hj bt.collection⟩

theorem elementary_map_afa_iff {j : U → V} (hj : ElementaryMap s t j) :
    AFACode s ↔ AFACode t :=
  (eval_afaSentence s).symm.trans ((elementary_map_sentence hj afaSentence).trans
    (eval_afaSentence t))

theorem elementary_map_bafa_iff {j : U → V} (hj : ElementaryMap s t j) :
    BAFACode s ↔ BAFACode t :=
  (eval_bafaSentence s).symm.trans ((elementary_map_sentence hj bafaSentence).trans
    (eval_bafaSentence t))

theorem elementary_map_choice_iff {j : U → V} (hj : ElementaryMap s t j) :
    ChoiceCode s ↔ ChoiceCode t :=
  (eval_choiceSentence s).symm.trans ((elementary_map_sentence hj choiceSentence).trans
    (eval_choiceSentence t))

#print axioms elementary_map_sentence
#print axioms eval_finiteBaseSentence
#print axioms eval_separationInstance
#print axioms eval_collectionInstance
#print axioms elementary_map_separation_reflect
#print axioms elementary_map_collection_reflect
#print axioms elementary_map_base_reflect
#print axioms elementary_map_afa_iff
#print axioms elementary_map_bafa_iff
#print axioms elementary_map_choice_iff
end FullBridge
