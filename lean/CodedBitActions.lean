import FiniteInvolutionActions
namespace FullBridge
universe u
variable {U : Type u} {s : U → U → Prop}

theorem finite_involution_action_codes (base : BaseCollection s) {d : U}
    (hd : TransitiveCode s d) (f : Nat → U → U)
    (hm : ∀ k x, s x d → s (f k x) d)
    (hc : ∀ k, ∃ c, FunctionCode s d c ∧ ∀ x y, CodedRelation s c x y ↔ s x d ∧ y = f k x)
    (n : Nat) (v : Fin n → Bool) :
    ∃ c, FunctionCode s d c ∧ ∀ x y, CodedRelation s c x y ↔ s x d ∧ y = finiteInvolutionAction f n v x := by
  induction n with
  | zero =>
    obtain ⟨_, c, _, hf, _, hr⟩ := membership_graph_identity_decoration base hd
    exact ⟨c, hf.1, hr⟩
  | succ n ih =>
    obtain ⟨c, hcF, hcR⟩ := ih (fun i => v i.castSucc)
    cases hv : v (Fin.last n)
    · exact ⟨c, hcF, by simpa only [finiteInvolutionAction, hv, Bool.false_eq_true, ↓reduceIte] using hcR⟩
    · obtain ⟨b, hbF, hbR⟩ := hc n
      obtain ⟨r, hrF, hrR⟩ := coded_functions_compose base hcF hbF (by
        intro x y hxy
        obtain ⟨hx, rfl⟩ := (hcR x y).mp hxy
        exact finite_involution_action_mem f hm n _ hx)
      refine ⟨r, hrF, fun x y => ?_⟩
      simp only [finiteInvolutionAction, hv, ↓reduceIte]
      rw [hrR]
      constructor
      · rintro ⟨z, hxz, hzy⟩
        obtain ⟨hx, rfl⟩ := (hcR x z).mp hxz
        exact ⟨hx, ((hbR _ y).mp hzy).2⟩
      · rintro ⟨hx, rfl⟩
        exact ⟨_, (hcR x _).mpr ⟨hx, rfl⟩, (hbR _ _).mpr
          ⟨finite_involution_action_mem f hm n _ hx, rfl⟩⟩

theorem finite_quine_bit_action (base : BaseCollection s) {d : U}
    (hq : ∀ x, s x d → SelfSingleton s x) (f : Nat → U → U)
    (hm : ∀ k x, s x d → s (f k x) d)
    (hi : ∀ k x, f k (f k x) = x) (hcomm : ∀ k l x, f k (f l x) = f l (f k x))
    (hc : ∀ k, ∃ c, FunctionCode s d c ∧ ∀ x y, CodedRelation s c x y ↔ s x d ∧ y = f k x)
    (n : Nat) : ∃ P : TransitiveGroupAction s (finiteBitGroup n), P.domain = d ∧
      ∀ v x y, CodedRelation s (P.code v) x y ↔ s x d ∧ y = finiteInvolutionAction f n v x := by
  classical
  have hd : TransitiveCode s d := fun x hx y hy => ((hq x hx y).mp hy).symm ▸ hx
  have hex := fun v => finite_involution_action_codes base hd f hm hc n v
  let code := fun v => Classical.choose (hex v)
  have hf := fun v => (Classical.choose_spec (hex v)).1
  have hr := fun v => (Classical.choose_spec (hex v)).2
  have hIso : ∀ v, MembershipIsoCode s d d (code v) := by
    intro v
    let j := finiteInvolutionAction f n v
    have hs : ∀ x, j (j x) = x := finite_involution_action_involutive f hi hcomm n v
    have hjm : ∀ x, s x d → s (j x) d := fun x hx => finite_involution_action_mem f hm n v hx
    have hji : ∀ x y, j x = j y → x = y := fun x y he => (hs x).symm.trans ((congrArg j he).trans (hs y))
    refine ⟨hf v, ?_, ?_, ?_⟩
    · intro x y z hxz hyz
      exact hji x y (((hr v x z).mp hxz).2.symm.trans ((hr v y z).mp hyz).2)
    · intro y
      constructor
      · intro hy
        exact ⟨j y, hjm y hy, (hr v _ _).mpr ⟨hjm y hy, (hs y).symm⟩⟩
      · rintro ⟨x, _, hxy⟩
        obtain ⟨hx, rfl⟩ := (hr v x y).mp hxy
        exact hjm x hx
    · intro x y X Y hxX hyY
      obtain ⟨hx, rfl⟩ := (hr v x X).mp hxX
      obtain ⟨hy, rfl⟩ := (hr v y Y).mp hyY
      rw [hq x hx y, hq (j x) (hjm x hx) (j y)]
      exact ⟨congrArg j, hji y x⟩
  have hOne : ∀ x y, CodedRelation s (code (finiteBitGroup n).one) x y → x = y := by
    intro x y hxy
    have hy := ((hr (finiteBitGroup n).one x y).mp hxy).2
    exact (hy.trans (finite_involution_action_identity f n x)).symm
  have hMul : ∀ v w x z, CodedRelation s (code ((finiteBitGroup n).mul v w)) x z ↔
      ∃ y, CodedRelation s (code w) x y ∧ CodedRelation s (code v) y z := by
    intro v w x z
    constructor
    · intro hxz
      obtain ⟨hx, hz⟩ := (hr _ x z).mp hxz
      exact ⟨_, (hr w x _).mpr ⟨hx, rfl⟩, (hr v _ z).mpr
        ⟨finite_involution_action_mem f hm n w hx, hz.trans (finite_involution_action_multiplication f hi hcomm n v w x)⟩⟩
    · rintro ⟨y, hxy, hyz⟩
      obtain ⟨hx, rfl⟩ := (hr w x y).mp hxy
      exact (hr _ x z).mpr ⟨hx, ((hr v _ z).mp hyz).2.trans
        (finite_involution_action_multiplication f hi hcomm n v w x).symm⟩
  exact ⟨⟨d, code, hd, hIso, hOne, hMul⟩, rfl, hr⟩

theorem coded_bit_core_actions (base : BaseCollection s) {d : U}
    (hq : ∀ x, s x d → SelfSingleton s x) (f : Nat → U → U)
    (hm : ∀ k x, s x d → s (f k x) d)
    (hi : ∀ k x, f k (f k x) = x) (hcomm : ∀ k l x, f k (f l x) = f l (f k x))
    (hc : ∀ k, ∃ c, FunctionCode s d c ∧ ∀ x y, CodedRelation s c x y ↔ s x d ∧ y = f k x) :
    ∃ A : FixedCoreActions s finiteBitExhaustion, A.domain = d ∧
      ∀ n v x y, CodedRelation s ((A.stage n).code v) x y ↔ s x d ∧ y = finiteInvolutionAction f n v x := by
  classical
  have hex := fun n => finite_quine_bit_action base hq f hm hi hcomm hc n
  let stage := fun n => Classical.choose (hex n)
  have hs := fun n => Classical.choose_spec (hex n)
  refine ⟨⟨d, stage, fun n => (hs n).1, ?_⟩, rfl, fun n => (hs n).2⟩
  intro n v x y hxy
  obtain ⟨hx, hy⟩ := ((hs n).2 v x y).mp hxy
  apply ((hs (n+1)).2 _ x y).mpr
  exact ⟨hx, hy.trans (finite_involution_action_prefix_step f v
    (exhaustionLift finiteBitExhaustion (Nat.le_succ n) v)
    (exhaustion_lift_embed finiteBitExhaustion (Nat.le_succ n) v) x).symm⟩

#print axioms coded_bit_core_actions
end FullBridge
