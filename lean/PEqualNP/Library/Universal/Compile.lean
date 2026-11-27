import PEqualNP.Library.Universal.IM
import Mathlib.Computability.TuringMachine.Computable

/-!
# Compiling a stack machine to the numbered micro-instruction machine

Helper module (proofs only, no statement may use it). Every finite multi-stack machine with
input alphabet `Bool ⊕ Bool` and output alphabet `Bool` has a micro-instruction code that, on
the numbered input, halts with the numbered answer bit on its output stack within a constant
factor of the running time of the machine (`compile`).

How the code is built.

* Flattening. `subs q` lists the statement `q` and all its sub-statements in preorder; the
  blocks `subs (m l)` of all labels are concatenated into one list `L`. Program position `p`
  holds the single instruction for the head constructor of `L[p]`. `Placed L p q` says that the
  block of `q` sits in `L` from position `p`.
* States and stacks are numbered through the finiteness of their types.
* Symbols are NOT numbered (only the input alphabet is finite). Instead numbers are decoded:
  on the input stack the numbers below `4` decode to input symbols, and the number
  `4 + (a + nσ * p)` decodes to the symbol pushed by the push statement at position `p` from
  the state numbered `a`. A stack of numbers represents a stack of symbols when it decodes
  elementwise.
* A `halt` statement becomes a jump to a final block of three instructions placed after `L`:
  pop the output symbol and put its bit number in the state, push that number, halt. This makes
  the output stack exactly `[bitCode b]`, also when the input and output stacks coincide.
-/

namespace PEqualNP.Library.Universal

open Turing

/-- The number of an input symbol. -/
def symIn : Bool ⊕ Bool → ℕ
  | Sum.inl false => 0 | Sum.inl true => 1 | Sum.inr false => 2 | Sum.inr true => 3

/-- The number of an output bit. -/
def bitCode (b : Bool) : ℕ := if b then 1 else 0

/-- The input symbol of a number (inverse of `symIn` on `0..3`). -/
def symOut : ℕ → Bool ⊕ Bool
  | 0 => Sum.inl false | 1 => Sum.inl true | 2 => Sum.inr false | _ => Sum.inr true

theorem symOut_symIn (x : Bool ⊕ Bool) : symOut (symIn x) = x := by
  rcases x with (_ | _) | (_ | _) <;> rfl

theorem symIn_lt (x : Bool ⊕ Bool) : symIn x < 4 := by
  rcases x with (_ | _) | (_ | _) <;> simp [symIn]

theorem bitCode_le (b : Bool) : bitCode b ≤ 1 := by
  cases b <;> simp [bitCode]

/-! ### Halted configurations stay halted -/

theorem step_of_pc_none (P : List Instr) (c : Cfg) (h : c.pc = none) : step P c = c := by
  unfold step; rw [h]

theorem iterate_step_of_pc_none (P : List Instr) (c : Cfg) (h : c.pc = none) (t : ℕ) :
    (step P)^[t] c = c :=
  Function.iterate_fixed (step_of_pc_none P c h) t

theorem Code.outputsWithin_mono (c : Code) (input : List ℕ) {t t' : ℕ} (h : t ≤ t')
    (out : List ℕ) : c.outputsWithin input t out → c.outputsWithin input t' out := by
  intro ho
  have hrun : c.run input t' = c.run input t := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
    unfold Code.run
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact iterate_step_of_pc_none _ _ ho.1 s
  unfold Code.outputsWithin
  rw [hrun]
  exact ho

/-! ### Flattening statements -/

section Flatten

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- A statement and all its sub-statements, in preorder. -/
def subs : TM2.Stmt Γ Λ σ → List (TM2.Stmt Γ Λ σ)
  | .push k f q => .push k f q :: subs q
  | .peek k f q => .peek k f q :: subs q
  | .pop k f q => .pop k f q :: subs q
  | .load a q => .load a q :: subs q
  | .branch f q₁ q₂ => .branch f q₁ q₂ :: (subs q₁ ++ subs q₂)
  | .goto f => [.goto f]
  | .halt => [.halt]

theorem subs_head (q : TM2.Stmt Γ Λ σ) : ∃ t, subs q = q :: t := by
  cases q <;> (rw [subs]; exact ⟨_, rfl⟩)

/-- The block of `q` sits in `L` from position `p`. -/
def Placed (L : List (TM2.Stmt Γ Λ σ)) (p : ℕ) (q : TM2.Stmt Γ Λ σ) : Prop :=
  ∃ A B, L = A ++ subs q ++ B ∧ A.length = p

theorem Placed.get {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) : L[p]? = some q := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  obtain ⟨t, ht⟩ := subs_head q
  rw [ht]
  simp

theorem Placed.le {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) : p + (subs q).length ≤ L.length := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  simp only [List.length_append]
  omega

theorem Placed.sub {L : List (TM2.Stmt Γ Λ σ)} {p : ℕ} {q r : TM2.Stmt Γ Λ σ}
    (h : Placed L p q) (X Y : List (TM2.Stmt Γ Λ σ)) (hq : subs q = q :: (X ++ subs r ++ Y)) :
    Placed L (p + 1 + X.length) r := by
  obtain ⟨A, B, rfl, rfl⟩ := h
  refine ⟨A ++ q :: X, Y ++ B, ?_, ?_⟩
  · rw [hq]; simp
  · simp; omega

theorem forall₂_tail {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : List.Forall₂ R l₁.tail l₂.tail := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons _ h2 => exact h2

theorem forall₂_singleton {α β : Type} {R : α → β → Prop} {l₁ : List α} {y : β}
    (h : List.Forall₂ R l₁ [y]) : ∃ s, l₁ = [s] ∧ R s y := by
  cases h with
  | cons h1 h3 => cases h3; exact ⟨_, rfl, h1⟩

theorem exists_placed (M : Λ → TM2.Stmt Γ Λ σ) (ls : List Λ) (l : Λ) (h : l ∈ ls) :
    ∃ p, Placed ((ls.map fun l => subs (M l)).flatten) p (M l) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem h
  exact ⟨((s.map fun l => subs (M l)).flatten).length, (s.map fun l => subs (M l)).flatten,
    (t.map fun l => subs (M l)).flatten, by simp, rfl⟩

end Flatten

/-! ### The compilation environment -/

/-- Everything the compilation needs: the machine, numberings of states and stacks, the
flattened statement list with the start position of every label, and the readings of input
numbers and output symbols. -/
structure Env (K : Type) [DecidableEq K] (Γ : K → Type) (Λ σ : Type) where
  M : Λ → TM2.Stmt Γ Λ σ
  nσ : ℕ
  nσ_pos : 0 < nσ
  num : σ → ℕ
  σof : ℕ → σ
  σof_num : ∀ v, σof (num v) = v
  num_lt : ∀ v, num v < nσ
  nK : ℕ
  numK : K → ℕ
  numK_lt : ∀ k, numK k < nK
  numK_inj : Function.Injective numK
  L : List (TM2.Stmt Γ Λ σ)
  start : Λ → ℕ
  placed_start : ∀ l, Placed L (start l) (M l)
  k₀ : K
  inSym : ℕ → Γ k₀
  k₁ : K
  outBit : Γ k₁ → ℕ

namespace Env

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (E : Env K Γ Λ σ)

/-- Row width of the two-dimensional tables: one more than the number of symbol numbers,
plus one for the empty stack. -/
def W : ℕ := 4 + E.nσ * E.L.length + 1

theorem W_pos : 0 < E.W := by unfold W; omega

/-- The stack and symbol a number stands for. -/
def decS (s : ℕ) : Option (Σ k, Γ k) :=
  if s < 4 then some ⟨E.k₀, E.inSym s⟩
  else match E.L[(s - 4) / E.nσ]? with
    | some (.push k f _) => some ⟨k, f (E.σof ((s - 4) % E.nσ))⟩
    | _ => none

/-- The symbol of stack `k` a number stands for. -/
def decode (k : K) (s : ℕ) : Option (Γ k) :=
  match E.decS s with
  | some ⟨k', y⟩ => if h : k' = k then some (h ▸ y) else none
  | none => none

theorem decode_of_decS {k : K} {s : ℕ} {y : Γ k} (h : E.decS s = some ⟨k, y⟩) :
    E.decode k s = some y := by
  simp [decode, h]

theorem decode_in {s : ℕ} (h : s < 4) : E.decode E.k₀ s = some (E.inSym s) :=
  E.decode_of_decS (by simp [decS, h])

theorem decode_push {p : ℕ} {k : K} {f : σ → Γ k} {r : TM2.Stmt Γ Λ σ}
    (h : E.L[p]? = some (.push k f r)) {a : ℕ} (ha : a < E.nσ) :
    E.decode k (4 + (a + E.nσ * p)) = some (f (E.σof a)) := by
  apply E.decode_of_decS
  unfold decS
  have e : 4 + (a + E.nσ * p) - 4 = a + E.nσ * p := by omega
  have h4 : ¬ (4 + (a + E.nσ * p) < 4) := by omega
  simp only [h4, ↓reduceIte]
  rw [e, Nat.add_mul_div_left _ _ E.nσ_pos, Nat.div_eq_of_lt ha, zero_add, h,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem decode_lt {k : K} {s : ℕ} {y : Γ k} (h : E.decode k s = some y) : s + 1 < E.W := by
  by_contra hc
  unfold W at hc
  have hd : E.decS s = none := by
    unfold decS
    have h1 : E.L.length ≤ (s - 4) / E.nσ := by
      rw [Nat.le_div_iff_mul_le E.nσ_pos, Nat.mul_comm]
      omega
    have h4 : ¬ (s < 4) := by omega
    simp only [h4, ↓reduceIte]
    rw [List.getElem?_eq_none h1]
  simp [decode, hd] at h

/-- The reading of the index used by `pop` and `peek`. -/
def arg (k : K) : ℕ → Option (Γ k)
  | 0 => none
  | s + 1 => E.decode k s

theorem top_spec {k : K} {ns : List ℕ} {ys : List (Γ k)}
    (h : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    topIndex ns < E.W ∧ E.arg k (topIndex ns) = ys.head? := by
  cases h with
  | nil => exact ⟨E.W_pos, rfl⟩
  | cons h1 _ => exact ⟨E.decode_lt h1, by simpa [topIndex, arg] using h1⟩

/-- A table indexed by the state number. -/
def tbl1 (g : ℕ → ℕ) : List ℕ := (List.range E.nσ).map g

/-- A table indexed by the state number and a stack reading. -/
def tbl2 (g : ℕ → ℕ → ℕ) : List ℕ :=
  (List.range (E.nσ * E.W)).map fun i => g (i / E.W) (i % E.W)

theorem tbl1_get (g : ℕ → ℕ) {a : ℕ} (ha : a < E.nσ) : (E.tbl1 g)[a]?.getD 0 = g a := by
  simp [tbl1, ha]

theorem tbl2_get (g : ℕ → ℕ → ℕ) {a c : ℕ} (ha : a < E.nσ) (hc : c < E.W) :
    (E.tbl2 g)[a * E.W + c]?.getD 0 = g a c := by
  have hlt : a * E.W + c < E.nσ * E.W :=
    calc a * E.W + c < a * E.W + E.W := by omega
      _ = (a + 1) * E.W := by ring
      _ ≤ E.nσ * E.W := Nat.mul_le_mul_right _ ha
  have h1 : (a * E.W + c) / E.W = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ E.W_pos, Nat.div_eq_of_lt hc, zero_add]
  have h2 : (a * E.W + c) % E.W = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp [tbl2, hlt, h1, h2]

/-- The program counter of a label, or of the final block for the halted label. -/
def pcOf : Option Λ → ℕ
  | some l => E.start l
  | none => E.L.length

/-- The instruction at position `p`, for the statement at that position. -/
def instrOf (p : ℕ) : TM2.Stmt Γ Λ σ → Instr
  | .push k _ _ => .push (E.numK k) (E.tbl1 fun a => 4 + (a + E.nσ * p)) (p + 1)
  | .peek k f _ =>
    .peek (E.numK k) (E.tbl2 fun a c => E.num (f (E.σof a) (E.arg k c))) E.W (p + 1)
  | .pop k f _ =>
    .pop (E.numK k) (E.tbl2 fun a c => E.num (f (E.σof a) (E.arg k c))) E.W (p + 1)
  | .load f _ => .load (E.tbl1 fun a => E.num (f (E.σof a))) (p + 1)
  | .branch f q₁ _ =>
    .branch (E.tbl1 fun a => if f (E.σof a) then 1 else 0) (p + 1) (p + 1 + (subs q₁).length)
  | .goto f => .goto (E.tbl1 fun a => E.start (f (E.σof a)))
  | .halt => .branch [] E.L.length E.L.length

/-- The table of the final pop: the bit number of the decoded output symbol. -/
def finTbl : List ℕ :=
  E.tbl2 fun _ c => match E.arg E.k₁ c with
    | some y => E.outBit y
    | none => 0

/-- The program: one instruction per position of `L`, then the final block. -/
def P : List Instr :=
  E.L.mapIdx E.instrOf ++
    [.pop (E.numK E.k₁) E.finTbl E.W (E.L.length + 1),
     .push (E.numK E.k₁) [0, 1] (E.L.length + 2),
     .halt]

theorem step_at {p : ℕ} {q : TM2.Stmt Γ Λ σ} (h : E.L[p]? = some q) (a : ℕ)
    (T : List (List ℕ)) : step E.P ⟨some p, a, T⟩ = exec (E.instrOf p q) a T := by
  have hp : p < E.L.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have : E.P[p]? = some (E.instrOf p q) := by
    unfold P
    rw [List.getElem?_append_left (by simpa using hp), List.getElem?_mapIdx, h]
    rfl
  simp [step, this]

theorem step_fin (i : ℕ) (I : Instr)
    (h : [Instr.pop (E.numK E.k₁) E.finTbl E.W (E.L.length + 1),
      Instr.push (E.numK E.k₁) [0, 1] (E.L.length + 2), Instr.halt][i]? = some I)
    (a : ℕ) (T : List (List ℕ)) : step E.P ⟨some (E.L.length + i), a, T⟩ = exec I a T := by
  have : E.P[E.L.length + i]? = some I := by
    unfold P
    rw [List.getElem?_append_right (by simp)]
    simpa using h
  simp [step, this]

/-- A list of number stacks represents a family of symbol stacks. -/
def StkRel (T : List (List ℕ)) (S : ∀ k, List (Γ k)) : Prop :=
  T.length = E.nK ∧
    ∀ k, List.Forall₂ (fun s y => E.decode k s = some y) (T.getD (E.numK k) []) (S k)

variable {E}

theorem StkRel.set {T : List (List ℕ)} {S : ∀ k, List (Γ k)} (h : E.StkRel T S) (k : K)
    {ns : List ℕ} {ys : List (Γ k)}
    (h2 : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    E.StkRel (T.set (E.numK k) ns) (Function.update S k ys) := by
  refine ⟨by simp [h.1], fun k' => ?_⟩
  by_cases hk : k' = k
  · subst hk
    have hlt : E.numK k' < T.length := by rw [h.1]; exact E.numK_lt k'
    simpa [List.getD_eq_getElem?_getD, hlt] using h2
  · have hne : E.numK k ≠ E.numK k' := fun e => hk (E.numK_inj e).symm
    rw [Function.update_of_ne hk]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne] using h.2 k'

theorem StkRel.init (k : K) {ns : List ℕ} {ys : List (Γ k)}
    (h2 : List.Forall₂ (fun s y => E.decode k s = some y) ns ys) :
    E.StkRel ((List.replicate E.nK []).set (E.numK k) ns)
      (Function.update (fun _ => []) k ys) := by
  refine StkRel.set ⟨by simp, fun k' => ?_⟩ k h2
  simp [List.getD_eq_getElem?_getD, E.numK_lt k']

variable (E)

/-! ### Simulation of one statement -/

theorem sim_stmt (q : TM2.Stmt Γ Λ σ) : ∀ (p : ℕ) (v : σ) (S : ∀ k, List (Γ k))
    (T : List (List ℕ)), Placed E.L p q → E.StkRel T S →
    ∃ t ≤ (subs q).length, ∃ T', (step E.P)^[t] ⟨some p, E.num v, T⟩ =
        ⟨some (E.pcOf (TM2.stepAux q v S).l), E.num (TM2.stepAux q v S).var, T'⟩ ∧
      E.StkRel T' (TM2.stepAux q v S).stk := by
  induction q with
  | push k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    have hd := E.decode_push hp.get (E.num_lt v)
    rw [E.σof_num] at hd
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) v (Function.update S k (f v :: S k)) _
      (hp.sub [] [] (by simp [subs])) (hr.set k (List.Forall₂.cons hd (hr.2 k)))
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v)] using h
  | peek k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨htop, harg⟩ := E.top_spec (hr.2 k)
    rw [List.getD_eq_getElem?_getD] at htop harg
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (f v (S k).head?) S T
      (hp.sub [] [] (by simp [subs])) hr
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl2_get _ (E.num_lt v) htop, harg, E.σof_num] using h
  | pop k f q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨htop, harg⟩ := E.top_spec (hr.2 k)
    rw [List.getD_eq_getElem?_getD] at htop harg
    have htail : List.Forall₂ (fun s y => E.decode k s = some y)
        (T.getD (E.numK k) []).tail (S k).tail := by
      exact forall₂_tail (hr.2 k)
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (f v (S k).head?) (Function.update S k (S k).tail) _
      (hp.sub [] [] (by simp [subs])) (hr.set k htail)
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl2_get _ (E.num_lt v) htop, harg, E.σof_num] using h
  | load a q ih =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    obtain ⟨t, ht, T', h, hr'⟩ := ih (p + 1) (a v) S T (hp.sub [] [] (by simp [subs])) hr
    refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa using hr'⟩
    rw [Function.iterate_succ_apply, hs]
    simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num] using h
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    cases hf : f v
    · obtain ⟨t, ht, T', h, hr'⟩ := ih₂ (p + 1 + (subs q₁).length) v S T
        (hp.sub (subs q₁) [] (by simp [subs])) hr
      refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa [hf] using hr'⟩
      rw [Function.iterate_succ_apply, hs]
      simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, hf] using h
    · obtain ⟨t, ht, T', h, hr'⟩ := ih₁ (p + 1) v S T
        (hp.sub [] (subs q₂) (by simp [subs])) hr
      refine ⟨t + 1, by simp [subs]; omega, T', ?_, by simpa [hf] using hr'⟩
      rw [Function.iterate_succ_apply, hs]
      simpa [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, hf] using h
  | goto f =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    refine ⟨1, by simp [subs], T, ?_, by simpa using hr⟩
    rw [Function.iterate_one, hs]
    simp [instrOf, exec, E.tbl1_get _ (E.num_lt v), E.σof_num, pcOf]
  | halt =>
    intro p v S T hp hr
    have hs := E.step_at hp.get (E.num v) T
    refine ⟨1, by simp [subs], T, ?_, by simpa using hr⟩
    rw [Function.iterate_one, hs]
    simp [instrOf, exec, pcOf]

/-! ### Simulation of a run -/

/-- A machine configuration is represented by a micro-instruction configuration. -/
def Rel (c : TM2.Cfg Γ Λ σ) (X : Cfg) : Prop :=
  X.pc = some (E.pcOf c.l) ∧ X.state = E.num c.var ∧ E.StkRel X.stk c.stk

theorem iterate_bind_none {α : Type} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem sim_run : ∀ (n : ℕ) (c c' : TM2.Cfg Γ Λ σ) (X : Cfg),
    (flip bind (TM2.step E.M))^[n] (some c) = some c' → E.Rel c X →
    ∃ t ≤ E.L.length * n, E.Rel c' ((step E.P)^[t] X) := by
  intro n
  induction n with
  | zero =>
    intro c c' X h hr
    simp only [Function.iterate_zero, id, Option.some.injEq] at h
    subst h
    exact ⟨0, by simp, hr⟩
  | succ n ih =>
    intro c c' X h hr
    rw [Function.iterate_succ_apply] at h
    obtain ⟨l, v, S⟩ := c
    obtain ⟨pc, a, T⟩ := X
    obtain ⟨h1, h2, h3⟩ := hr
    simp only at h1 h2 h3
    subst h1 h2
    cases l with
    | none =>
      have : flip bind (TM2.step E.M) (some (⟨none, v, S⟩ : TM2.Cfg Γ Λ σ)) = none := rfl
      rw [this, iterate_bind_none] at h
      cases h
    | some l =>
      have : flip bind (TM2.step E.M) (some (⟨some l, v, S⟩ : TM2.Cfg Γ Λ σ)) =
          some (TM2.stepAux (E.M l) v S) := rfl
      rw [this] at h
      obtain ⟨t₁, ht₁, T', hs, hr'⟩ := E.sim_stmt (E.M l) (E.start l) v S T (E.placed_start l) h3
      have hle := (E.placed_start l).le
      obtain ⟨t₂, ht₂, hfin⟩ := ih _ c' ((step E.P)^[t₁] ⟨some (E.start l), E.num v, T⟩) h
        (by rw [hs]; exact ⟨rfl, rfl, hr'⟩)
      refine ⟨t₂ + t₁, ?_, ?_⟩
      · rw [Nat.mul_succ]; omega
      · rw [Function.iterate_add_apply]; exact hfin

/-- The final block: from its entry, with a single decodable symbol on the output stack, three
steps halt with the bit number of that symbol alone on the output stack. -/
theorem sim_fin (a : ℕ) (ha : a < E.nσ) (T : List (List ℕ)) (hT : T.length = E.nK) (s : ℕ)
    (y : Γ E.k₁) (hs : T.getD (E.numK E.k₁) [] = [s]) (hy : E.decode E.k₁ s = some y)
    (hb : E.outBit y ≤ 1) :
    ∃ T', (step E.P)^[3] ⟨some E.L.length, a, T⟩ = ⟨none, E.outBit y, T'⟩ ∧
      T'.getD (E.numK E.k₁) [] = [E.outBit y] := by
  have hlt : E.numK E.k₁ < T.length := by rw [hT]; exact E.numK_lt _
  have e1 := E.step_fin 0 _ rfl a T
  have e2 := E.step_fin 1 _ rfl
  have e3 := E.step_fin 2 _ rfl
  have hget : E.finTbl.getD (a * E.W + (s + 1)) 0 = E.outBit y := by
    unfold finTbl
    rw [List.getD_eq_getElem?_getD, E.tbl2_get _ ha (E.decode_lt hy)]
    simp [arg, hy]
  have hpush : [0, 1].getD (E.outBit y) 0 = E.outBit y := by
    generalize E.outBit y = c at hb
    interval_cases c <;> rfl
  refine ⟨(T.set (E.numK E.k₁) []).set (E.numK E.k₁) [E.outBit y], ?_, ?_⟩
  · simp only [Function.iterate_succ_apply, Function.iterate_zero, id, Nat.add_zero] at e1 ⊢
    rw [e1]
    simp only [exec, hs, topIndex, hget, List.tail_cons]
    rw [e2]
    simp only [exec, hpush]
    rw [e3]
    simp [exec, List.getD_eq_getElem?_getD, hlt]
  · simp [List.getD_eq_getElem?_getD, hlt]

end Env

/-! ### The environment of a finite stack machine -/

section Compile

variable (tm : Turing.FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool ⊕ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)

/-- The numbering of the states. -/
noncomputable def σEquiv : tm.σ ≃ Fin (@Fintype.card tm.σ tm.σFin) :=
  @Fintype.equivFin tm.σ tm.σFin

/-- The numbering of the stacks. -/
noncomputable def kEquiv : tm.K ≃ Fin (@Fintype.card tm.K tm.kFin) :=
  @Fintype.equivFin tm.K tm.kFin

/-- The flattened statement list of a machine: the blocks of all labels. -/
noncomputable def flatList : List (TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  ((@Finset.univ tm.Λ tm.ΛFin).toList.map fun l => subs (tm.m l)).flatten

theorem flatList_placed (l : tm.Λ) : ∃ p, Placed (flatList tm) p (tm.m l) :=
  exists_placed tm.m _ l (by simp)

/-- The compilation environment of a machine. -/
noncomputable def envOf : Env tm.K tm.Γ tm.Λ tm.σ where
  M := tm.m
  nσ := @Fintype.card tm.σ tm.σFin
  nσ_pos := @Fintype.card_pos tm.σ tm.σFin ⟨tm.initialState⟩
  num v := (σEquiv tm v).val
  σof n := if h : n < @Fintype.card tm.σ tm.σFin then (σEquiv tm).symm ⟨n, h⟩ else tm.initialState
  σof_num v := by simp
  num_lt v := (σEquiv tm v).isLt
  nK := @Fintype.card tm.K tm.kFin
  numK k := (kEquiv tm k).val
  numK_lt k := (kEquiv tm k).isLt
  numK_inj := fun a b h => (kEquiv tm).injective (Fin.ext h)
  L := flatList tm
  start l := Classical.choose (flatList_placed tm l)
  placed_start l := Classical.choose_spec (flatList_placed tm l)
  k₀ := tm.k₀
  inSym n := eIn.symm (symOut n)
  k₁ := tm.k₁
  outBit y := bitCode (eOut y)

theorem compile :
    ∃ (c : Code) (d : ℕ), ∀ (l : List (Bool ⊕ Bool)) (b : Bool) (n : ℕ),
      (flip bind (Turing.TM2.step tm.m))^[n] (some (Turing.initList tm (l.map eIn.invFun))) =
          some (Turing.haltList tm [eOut.invFun b]) →
      c.outputsWithin (l.map symIn) (d * n + d) [bitCode b] := by
  let E := envOf tm eIn eOut
  refine ⟨⟨E.P, E.nK, E.start tm.main, E.num tm.initialState, E.numK tm.k₀, E.numK tm.k₁⟩,
    E.L.length + 3, fun l b n hrun => ?_⟩
  -- the initial configurations are related
  have hin : List.Forall₂ (fun s y => E.decode tm.k₀ s = some y) (l.map symIn)
      (l.map eIn.invFun) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun x _ => ?_
    have := E.decode_in (symIn_lt x)
    simpa [E, envOf, symOut_symIn] using this
  have hstk : (Turing.initList tm (l.map eIn.invFun)).stk =
      Function.update (fun _ => []) tm.k₀ (l.map eIn.invFun) := by
    funext k
    by_cases hk : k = tm.k₀
    · subst hk; simp [Turing.initList]
    · simp [Turing.initList, hk]
  have hrel : E.Rel (Turing.initList tm (l.map eIn.invFun))
      ⟨some (E.start tm.main), E.num tm.initialState,
        (List.replicate E.nK []).set (E.numK tm.k₀) (l.map symIn)⟩ := by
    refine ⟨rfl, rfl, ?_⟩
    rw [hstk]
    exact Env.StkRel.init tm.k₀ hin
  obtain ⟨t, ht, hpc, hst, hsr⟩ := E.sim_run n _ _ _ hrun hrel
  -- read off the final configuration
  generalize hX : (step E.P)^[t] _ = X at hpc hst hsr
  obtain ⟨pc, a, T⟩ := X
  simp only at hpc hst hsr
  have hout : (Turing.haltList tm [eOut.invFun b]).stk tm.k₁ = [eOut.invFun b] := by
    simp [Turing.haltList]
  have h2 := hsr.2 tm.k₁
  rw [hout] at h2
  obtain ⟨s, hs, hy⟩ : ∃ s, T.getD (E.numK tm.k₁) [] = [s] ∧
      E.decode tm.k₁ s = some (eOut.invFun b) := by
    exact forall₂_singleton (R := fun s y => E.decode tm.k₁ s = some y) h2
  have hbit : E.outBit (eOut.invFun b) = bitCode b := by simp [E, envOf]
  obtain ⟨T', hfin, hT'⟩ := E.sim_fin a (by rw [hst]; exact E.num_lt _) T hsr.1 s
    (eOut.invFun b) hs hy (by rw [hbit]; exact bitCode_le b)
  have hpc' : pc = some E.L.length := hpc
  subst hpc'
  rw [← hX, ← Function.iterate_add_apply, hbit] at hfin
  rw [hbit] at hT'
  refine Code.outputsWithin_mono _ _ (t := 3 + t) ?_ _ ?_
  · have : E.L.length * n ≤ (E.L.length + 3) * n := Nat.mul_le_mul_right _ (by omega)
    omega
  · unfold Code.outputsWithin Code.run Code.init
    simp only
    rw [hfin]
    exact ⟨rfl, hT'⟩

end Compile

end PEqualNP.Library.Universal
