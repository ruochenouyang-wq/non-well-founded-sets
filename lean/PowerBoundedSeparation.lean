import PowerBoundedReduction
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

def powerSeparationRename {n} : Fin (n+1) → Fin (n+2) :=
  Fin.cases 0 (fun i => i.succ.succ)

theorem power_separation_env {n} (x B : U) (v : Fin n → U) :
    (fun i => cons x (cons B v) (powerSeparationRename i)) = cons x v := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- This implication uses only the four displayed hypotheses. In particular,
    it does not assume Collection, full Separation, Foundation or choice. -/
theorem power_bounded_separation_of_bounded (hp : Pairing s) (hu : Union s)
    (hpow : PowerSet s) (hsep : BoundedSeparation s) : PowerBoundedSeparation s := by
  intro n p v a
  obtain ⟨d, had, hd⟩ := power_finite_environment_bound hp hu a v
  obtain ⟨B, hB⟩ := power_quantifier_control_exists hp hu hpow d p.depth
  let q : BoundedFormula (n+2) := p.restrict powerSeparationRename 1
  obtain ⟨b, hb⟩ := hsep (n+1) q (cons B v) a
  have heval : ∀ x, s x a →
      (BoundedEval s q (cons x (cons B v)) ↔ PowerBoundedEval s p (cons x v)) := by
    intro x hx
    have hh : ∀ i, PowerQuantifierControl s B p.depth (cons x v i) := by
      intro i
      exact Fin.cases (hB x (had x hx)) (fun j => hB (v j) (hd j)) i
    have hh' : ∀ i, PowerQuantifierControl s (cons x (cons B v) 1) p.depth
        (cons x (cons B v) (powerSeparationRename i)) := by
      intro i
      change PowerQuantifierControl s B p.depth ((fun j => cons x (cons B v) (powerSeparationRename j)) i)
      rw [power_separation_env]
      exact hh i
    simpa only [power_separation_env] using
      power_bounded_restrict_correct p powerSeparationRename 1 (cons x (cons B v)) hh'
  refine ⟨b, fun x => ?_⟩
  exact (hb x).trans ⟨fun ⟨hx, hq⟩ => ⟨hx, (heval x hx).mp hq⟩,
    fun ⟨hx, hq⟩ => ⟨hx, (heval x hx).mpr hq⟩⟩

#print axioms power_bounded_separation_of_bounded
end FullBridge
