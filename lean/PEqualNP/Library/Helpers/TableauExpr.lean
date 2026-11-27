import PEqualNP.Defs
import Mathlib.Tactic

/-!
# Layered circuits from formulas

Helper module (proofs only, no statement may use it).

* `Ex α`: formulas over variables `α` with constants, NOT, binary AND and OR; `Ex.eval`,
  `Ex.size` (number of nodes), `Ex.bind` (substitution).
* `Sim F s`: a fan-in-two AND/OR/NOT gate list of at most `s` gates that, appended to any wire
  list whose wires `w a` carry `ρ a`, makes wires `w' b` carry `F ρ b`. The gate list depends
  only on the length of the wire list and on `w`, not on the values.
* `sim_comp`, `sim_iter`, `sim_layer`: composition, iteration and one layer of formulas.
* `exists_ex`: every function of the bits of a finite type is a formula of size bounded by the
  size of the type; `exists_ex_det`: the same for a quantity determined by an encoding.
-/

namespace PEqualNP.Library.Helpers.Tableau

open PEqualNP.CircuitLowerBounds

/-- Formulas. -/
inductive Ex (α : Type) where
  | var : α → Ex α
  | const : Bool → Ex α
  | not : Ex α → Ex α
  | and : Ex α → Ex α → Ex α
  | or : Ex α → Ex α → Ex α

namespace Ex

variable {α β : Type}

/-- Value of a formula. -/
def eval (ρ : α → Bool) : Ex α → Bool
  | var a => ρ a
  | const b => b
  | not e => !(eval ρ e)
  | and e f => eval ρ e && eval ρ f
  | or e f => eval ρ e || eval ρ f

/-- Number of nodes. -/
def size : Ex α → ℕ
  | var _ => 1
  | const _ => 1
  | not e => size e + 1
  | and e f => size e + size f + 1
  | or e f => size e + size f + 1

/-- Substitution. -/
def bind (σ : α → Ex β) : Ex α → Ex β
  | var a => σ a
  | const b => const b
  | not e => not (bind σ e)
  | and e f => and (bind σ e) (bind σ f)
  | or e f => or (bind σ e) (bind σ f)

theorem eval_bind (ρ : β → Bool) (σ : α → Ex β) (e : Ex α) :
    eval ρ (bind σ e) = eval (fun a => eval ρ (σ a)) e := by
  induction e with
  | var a => rfl
  | const b => rfl
  | not e ih => simp [bind, eval, ih]
  | and e f ih1 ih2 => simp [bind, eval, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, eval, ih1, ih2]

theorem size_bind (σ : α → Ex β) (hσ : ∀ a, size (σ a) = 1) (e : Ex α) :
    size (bind σ e) = size e := by
  induction e with
  | var a => exact hσ a
  | const b => rfl
  | not e ih => simp [bind, size, ih]
  | and e f ih1 ih2 => simp [bind, size, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, size, ih1, ih2]

end Ex

open Ex

/-! ## Wires -/

/-- All wires after running a gate list on the wire list `W`. -/
def run (gs : List Gate) (W : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W

theorem run_wires (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_nil (W : List Bool) : run [] W = W := rfl

theorem run_single (g : Gate) (W : List Bool) :
    run [g] W = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := rfl

theorem run_prefix (gs : List Gate) : ∀ W : List Bool, ∃ t, run gs W = W ++ t := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht⟩ := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => W.getD i false)] ++ t, ?_⟩
    change run gs _ = _
    rw [ht, List.append_assoc]

theorem length_run (gs : List Gate) : ∀ W : List Bool, (run gs W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp [run]
  | cons g gs ih =>
    intro W
    change (run gs _).length = _
    rw [ih]; simp; omega

theorem getD_run (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht⟩ := run_prefix gs W
  rw [ht, List.getD_append _ _ _ _ h]

/-- `W` carries `ρ` on the wires `w`. -/
def Rep {α : Type} (W : List Bool) (w : α → ℕ) (ρ : α → Bool) : Prop :=
  ∀ a, w a < W.length ∧ W.getD (w a) false = ρ a

theorem rep_run {α : Type} {W : List Bool} {w : α → ℕ} {ρ : α → Bool} (h : Rep W w ρ)
    (gs : List Gate) : Rep (run gs W) w ρ := by
  intro a
  refine ⟨?_, ?_⟩
  · rw [length_run]; have := (h a).1; omega
  · rw [getD_run _ _ _ (h a).1]; exact (h a).2

/-- A gate allowed in `SIZE`. -/
def Basic (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-! ## Compiling one formula -/

section compile

variable {α : Type} (w : α → ℕ)

/-- The gates of a formula appended after `N` wires, and its output wire. -/
def compile : Ex α → ℕ → List Gate × ℕ
  | .var a, _ => ([], w a)
  | .const b, N => ([⟨if b then GateOp.and else GateOp.or, []⟩], N)
  | .not e, N =>
    let p := compile e N
    (p.1 ++ [⟨GateOp.not, [p.2]⟩], N + p.1.length)
  | .and e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.and, [p.2, q.2]⟩], N + p.1.length + q.1.length)
  | .or e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.or, [p.2, q.2]⟩], N + p.1.length + q.1.length)

theorem compile_basic : ∀ (e : Ex α) (N : ℕ), ∀ g ∈ (compile w e N).1, Basic g
  | .var a, N => by simp [compile]
  | .const b, N => by
    intro g hg
    simp only [compile, List.mem_singleton] at hg
    subst hg
    cases b <;> simp [Basic]
  | .not e, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact compile_basic e N g hg
    · subst hg; simp [Basic]
  | .and e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]
  | .or e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]

theorem compile_length : ∀ (e : Ex α) (N : ℕ), (compile w e N).1.length ≤ size e
  | .var a, N => by simp [compile, size]
  | .const b, N => by simp [compile, size]
  | .not e, N => by
    have := compile_length e N
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .and e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .or e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega

theorem getD_snoc_len (W : List Bool) (b : Bool) : (W ++ [b]).getD W.length false = b := by
  simp

theorem compile_spec : ∀ (e : Ex α) (W : List Bool) (ρ : α → Bool), Rep W w ρ →
    (compile w e W.length).2 < W.length + (compile w e W.length).1.length ∧
    (run (compile w e W.length).1 W).getD (compile w e W.length).2 false = eval ρ e
  | .var a, W, ρ, h => by
    simp only [compile, List.length_nil, Nat.add_zero, run_nil, eval]
    exact h a
  | .const b, W, ρ, h => by
    simp only [compile, List.length_singleton, run_single, eval]
    refine ⟨by omega, ?_⟩
    rw [getD_snoc_len]
    cases b <;> simp [GateOp.eval]
  | .not e, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    have hl := length_run (compile w e W.length).1 W
    rw [← hl, getD_snoc_len]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    exact congrArg _ h2
  | .and e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    exact congrArg₂ _ e2 h4
  | .or e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    exact congrArg₂ _ e2 h4

end compile

/-! ## Simulations -/

/-- A gate list of at most `s` gates computing `F` from wires `w` to wires `w'`. -/
def Sim {α β : Type} (F : (α → Bool) → (β → Bool)) (s : ℕ) : Prop :=
  ∀ (N : ℕ) (w : α → ℕ), ∃ (gs : List Gate) (w' : β → ℕ), (∀ g ∈ gs, Basic g) ∧
    gs.length ≤ s ∧ ∀ (W : List Bool) (ρ : α → Bool), W.length = N → Rep W w ρ →
      Rep (run gs W) w' (F ρ)

theorem sim_mono {α β : Type} {F : (α → Bool) → (β → Bool)} {s t : ℕ} (h : Sim F s)
    (hst : s ≤ t) : Sim F t := by
  intro N w
  obtain ⟨gs, w', h1, h2, h3⟩ := h N w
  exact ⟨gs, w', h1, h2.trans hst, h3⟩

theorem sim_id {α : Type} : Sim (fun ρ : α → Bool => ρ) 0 := by
  intro N w
  exact ⟨[], w, by simp, by simp, fun W ρ _ h => h⟩

theorem sim_comp {α β γ : Type} {F : (α → Bool) → (β → Bool)} {G : (β → Bool) → (γ → Bool)}
    {s t : ℕ} (hF : Sim F s) (hG : Sim G t) : Sim (fun ρ => G (F ρ)) (s + t) := by
  intro N w
  obtain ⟨gs, w', h1, h2, h3⟩ := hF N w
  obtain ⟨gs', w'', h1', h2', h3'⟩ := hG (N + gs.length) w'
  refine ⟨gs ++ gs', w'', ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · exact h1' g hg
  · rw [List.length_append]; omega
  · intro W ρ hW hR
    rw [run_append]
    exact h3' _ _ (by rw [length_run, hW]) (h3 W ρ hW hR)

theorem sim_iter {α : Type} {F : (α → Bool) → (α → Bool)} {s : ℕ} (hF : Sim F s) :
    ∀ k : ℕ, Sim (F^[k]) (k * s) := by
  intro k
  induction k with
  | zero => rw [Nat.zero_mul]; exact sim_id
  | succ k ih =>
    have := sim_comp hF ih
    refine sim_mono ?_ (by rw [Nat.succ_mul, Nat.add_comm])
    rw [Function.iterate_succ]; exact this

theorem sim_layer_list {α β : Type} (e : β → Ex α) (l : List β) (N : ℕ) (w : α → ℕ) :
    ∃ (gs : List Gate) (w' : β → ℕ), (∀ g ∈ gs, Basic g) ∧
      gs.length ≤ (l.map fun b => size (e b)).sum ∧
      ∀ (W : List Bool) (ρ : α → Bool), W.length = N → Rep W w ρ →
        ∀ b ∈ l, w' b < (run gs W).length ∧ (run gs W).getD (w' b) false = eval ρ (e b) := by
  classical
  induction l generalizing N with
  | nil => exact ⟨[], fun _ => 0, by simp, by simp, fun W ρ _ _ b hb => by simp at hb⟩
  | cons b l ih =>
    have c0 := compile_basic w (e b) N
    have cL := compile_length w (e b) N
    have cS : ∀ (W : List Bool) (ρ : α → Bool), W.length = N → Rep W w ρ →
        (compile w (e b) N).2 < N + (compile w (e b) N).1.length ∧
        (run (compile w (e b) N).1 W).getD (compile w (e b) N).2 false = eval ρ (e b) := by
      intro W ρ hW hR; subst hW; exact compile_spec w (e b) W ρ hR
    generalize compile w (e b) N = p at c0 cL cS
    obtain ⟨gs, w', h1, h2, h3⟩ := ih (N + p.1.length)
    refine ⟨p.1 ++ gs, fun b' => if b' = b then p.2 else w' b', ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact c0 g hg
      · exact h1 g hg
    · simp only [List.length_append, List.map_cons, List.sum_cons]; omega
    · intro W ρ hW hR b' hb'
      rw [run_append]
      have hl := length_run p.1 W
      have hR' := rep_run hR p.1
      by_cases hbb : b' = b
      · subst hbb
        simp only [ite_true]
        obtain ⟨c1, c2⟩ := cS W ρ hW hR
        refine ⟨?_, ?_⟩
        · rw [length_run, hl]; omega
        · rw [getD_run _ _ _ (by rw [hl]; omega)]; exact c2
      · simp only [hbb, ite_false]
        have hb'' : b' ∈ l := by
          rcases List.mem_cons.1 hb' with h | h
          · exact absurd h hbb
          · exact h
        exact h3 (run p.1 W) ρ (by rw [hl, hW]) hR' b' hb''

theorem sim_layer {α β : Type} [Fintype β] (e : β → Ex α) :
    Sim (fun ρ b => eval ρ (e b)) (∑ b, size (e b)) := by
  classical
  intro N w
  obtain ⟨gs, w', h1, h2, h3⟩ := sim_layer_list e Finset.univ.toList N w
  refine ⟨gs, w', h1, ?_, ?_⟩
  · refine h2.trans (le_of_eq ?_)
    rw [Finset.sum_map_toList]
  · intro W ρ hW hR b
    exact h3 W ρ hW hR b (Finset.mem_toList.2 (Finset.mem_univ b))

/-! ## Every function of finitely many bits is a formula -/

theorem exists_ex_fin : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool),
    ∃ E : Ex (Fin k), size E + 6 ≤ 7 * 2 ^ k ∧ ∀ ρ, eval ρ E = f ρ
  | 0, f => ⟨Ex.const (f fun i => i.elim0), by simp [size], fun ρ => by
      simp only [eval]; congr 1; funext i; exact i.elim0⟩
  | k + 1, f => by
    obtain ⟨E1, s1, e1⟩ := exists_ex_fin k (fun τ => f (Fin.snoc τ true))
    obtain ⟨E0, s0, e0⟩ := exists_ex_fin k (fun τ => f (Fin.snoc τ false))
    let σ : Fin k → Ex (Fin (k + 1)) := fun i => Ex.var i.castSucc
    have hσ : ∀ i, size (σ i) = 1 := fun i => rfl
    refine ⟨Ex.or (Ex.and (Ex.var (Fin.last k)) (bind σ E1))
      (Ex.and (Ex.not (Ex.var (Fin.last k))) (bind σ E0)),
      ?_, ?_⟩
    · simp only [size, size_bind σ hσ]; rw [pow_succ]; omega
    · intro ρ
      simp only [eval, eval_bind, σ, e1, e0]
      have h := Fin.snoc_init_self ρ
      cases hl : ρ (Fin.last k)
      · simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
        conv_rhs => rw [← h, hl]
        rfl
      · simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
        conv_rhs => rw [← h, hl]
        rfl

theorem exists_ex {V : Type} [Fintype V] (f : (V → Bool) → Bool) :
    ∃ E : Ex V, size E + 6 ≤ 7 * 2 ^ Fintype.card V ∧ ∀ ρ, eval ρ E = f ρ := by
  let e := Fintype.equivFin V
  obtain ⟨E, s, h⟩ := exists_ex_fin (Fintype.card V) (fun τ => f (fun v => τ (e v)))
  let σ : Fin (Fintype.card V) → Ex V := fun i => Ex.var (e.symm i)
  refine ⟨bind σ E, by rw [size_bind σ (fun _ => rfl)]; exact s, fun ρ => ?_⟩
  rw [eval_bind, h]
  simp [σ, eval]

theorem exists_ex_det {X V : Type} [Fintype V] (enc : X → V → Bool) (P : X → Prop)
    (f : X → Bool) (hdet : ∀ x y, P x → P y → enc x = enc y → f x = f y) :
    ∃ E : Ex V, size E + 6 ≤ 7 * 2 ^ Fintype.card V ∧ ∀ x, P x → eval (enc x) E = f x := by
  classical
  let F : (V → Bool) → Bool := fun b => if h : ∃ x, P x ∧ enc x = b then f h.choose else false
  obtain ⟨E, s, h⟩ := exists_ex F
  refine ⟨E, s, fun x hx => ?_⟩
  rw [h]
  have hex : ∃ y, P y ∧ enc y = enc x := ⟨x, hx, rfl⟩
  simp only [F, hex]
  exact hdet _ _ hex.choose_spec.1 hx hex.choose_spec.2

end PEqualNP.Library.Helpers.Tableau
