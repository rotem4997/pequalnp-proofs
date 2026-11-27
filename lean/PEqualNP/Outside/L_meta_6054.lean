import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6054

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The graph of the statement: row u is joined to column v exactly when u + v is at most 3.
abbrev A : Fin 4 → Fin 4 → Bool := fun u v => (4991 : ℕ).testBit (4 * u.val + v.val)

-- Part 1. The wire list of a circuit as a fold over its gates.

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length : ∀ (gs : List Gate) (w : List Bool), (W gs w).length = w.length + gs.length
  | [], w => by simp [W]
  | g :: gs, w => by rw [W_cons, W_length gs, step_len, List.length_cons]; omega

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false)
      else w.getD i false :=
  getD_snoc w _ i

theorem W_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (W gs w).getD i false = w.getD i false
  | [], _, _, _ => rfl
  | g :: gs, w, i, hi => by
    rw [W_cons, W_prefix gs (step w g) i (by rw [step_len]; omega), step_getD,
      if_neg (by omega)]

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false :=
  List.getD_eq_default _ _ (by rw [W_length]; exact h)

theorem W_at (pre : List Gate) (g : Gate) (post : List Gate) (w : List Bool) :
    (W (pre ++ g :: post) w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  rw [W_append, W_cons, W_prefix post _ _ (by rw [step_len, W_length]; omega), step_getD,
    if_pos (by rw [W_length])]

theorem split_at : ∀ (l : List Gate) (j : ℕ) (g : Gate), l[j]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = j
  | [], j, g, h => by simp at h
  | a :: l, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨[], l, rfl, rfl⟩
  | a :: l, j + 1, g, h => by
    simp only [List.getElem?_cons_succ] at h
    obtain ⟨pre, post, rfl, hl⟩ := split_at l j g h
    exact ⟨a :: pre, post, rfl, by simp [hl]⟩

-- Part 2. AND and OR gates are monotone, also when some wires are set aside.

theorem and1 (x : Bool) : GateOp.and.eval [x] = x := by cases x <;> rfl

theorem or1 (x : Bool) : GateOp.or.eval [x] = x := by cases x <;> rfl

theorem and2 (x y : Bool) : GateOp.and.eval [x, y] = (x && y) := by
  cases x <;> cases y <;> rfl

theorem or2 (x y : Bool) : GateOp.or.eval [x, y] = (x || y) := by
  cases x <;> cases y <;> rfl

theorem gate_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (a b : ℕ → Bool) (h : ∀ i ∈ g.inputs, a i = true → b i = true)
    (hv : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h1 | h1
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id] at hv ⊢
    exact fun i hi => h i hi (hv i hi)
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
      id] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    exact ⟨i, hi, h i hi hvi⟩

-- If the input P is below the input Q on every wire outside E, and no gate outside E reads a
-- wire of E, then every wire outside E is below as well.
theorem cmp (E : ℕ → Prop) : ∀ (gs : List Gate) (wP wQ : List Bool),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
    wP.length = wQ.length →
    (∀ i, ¬ E i → wP.getD i false = true → wQ.getD i false = true) →
    (∀ j g, gs[j]? = some g → ¬ E (wP.length + j) → ∀ i ∈ g.inputs, ¬ E i) →
    ∀ i, ¬ E i → (W gs wP).getD i false = true → (W gs wQ).getD i false = true
  | [], _, _, _, _, h0, _ => h0
  | g :: gs, wP, wQ, hop, hlen, h0, h1 => by
    refine cmp E gs (step wP g) (step wQ g) (fun g' hg' => hop g' (by simp [hg']))
      (by rw [step_len, step_len, hlen]) ?_ ?_
    · intro i hi
      rw [step_getD, step_getD, ← hlen]
      by_cases hil : i = wP.length
      · rw [if_pos hil, if_pos hil]
        have hE0 : ¬ E (wP.length + 0) := by rw [Nat.add_zero, ← hil]; exact hi
        exact gate_mono g (hop g (by simp)) _ _
          (fun x hx => h0 x (h1 0 g (by simp) hE0 x hx))
      · rw [if_neg hil, if_neg hil]
        exact h0 i hi
    · intro j g' hj hE
      have e : (step wP g).length + j = wP.length + (j + 1) := by rw [step_len]; omega
      rw [e] at hE
      exact h1 (j + 1) g' (by simpa using hj) hE

-- Part 3. A search over bit masks: one bit for each of the nine inputs with a row in 1..3 and a
-- column in 1..3 on. A circuit adds one mask per gate.

def stepC (pool : List ℕ) : List ℕ :=
  511 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def myDedup : List ℕ → List ℕ
  | [] => []
  | a :: l => if l.contains a then myDedup l else a :: myDedup l

theorem mem_myDedup : ∀ (l : List ℕ) (c : ℕ), c ∈ l → c ∈ myDedup l
  | [], c, h => by simp at h
  | a :: l, c, h => by
    unfold myDedup
    rcases List.mem_cons.mp h with rfl | h
    · split
      · rename_i hc; exact mem_myDedup l _ (by simpa using hc)
      · simp
    · split
      · exact mem_myDedup l c h
      · exact List.mem_cons_of_mem _ (mem_myDedup l c h)

def hitP (T : ℕ) (pool : List ℕ) : Bool := pool.any (fun m => m % 512 == T)

def hit2 (T : ℕ) (pool : List ℕ) : Bool :=
  T == 511 || T == 0 || hitP T pool ||
    pool.any (fun a => pool.any (fun b => (a &&& b) % 512 == T || (a ||| b) % 512 == T))

theorem hit2_of (T : ℕ) (pool : List ℕ) (c : ℕ) (hc : c ∈ stepC pool) (h : c % 512 = T) :
    hit2 T pool = true := by
  simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap] at hc
  simp only [hit2, hitP, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  rcases hc with rfl | rfl | hc | ⟨a, ha, b, hb, hc⟩
  · left; left; left; omega
  · left; left; right; omega
  · left; right; exact ⟨c, hc, h⟩
  · right; refine ⟨a, ha, b, hb, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · left; exact h
    · right; exact h

def reach (T : ℕ) : List ℕ → ℕ → Bool
  | pool, 0 => hitP T pool
  | pool, 1 => hitP T pool || hit2 T pool
  | pool, k + 2 => hitP T pool || reach T pool (k + 1) ||
      (myDedup (stepC pool)).any (fun c => !pool.contains c && reach T (pool ++ [c]) (k + 1))

theorem reach_of_hit (T : ℕ) (pool : List ℕ) (h : hitP T pool = true) :
    ∀ k, reach T pool k = true
  | 0 => by simp only [reach]; exact h
  | 1 => by simp only [reach, Bool.or_eq_true]; exact Or.inl h
  | k + 2 => by simp only [reach, Bool.or_eq_true]; exact Or.inl (Or.inl h)

theorem reach_mono (T : ℕ) (pool : List ℕ) :
    ∀ k, reach T pool k = true → reach T pool (k + 1) = true
  | 0, h => by
    simp only [reach] at h
    simp only [reach, Bool.or_eq_true]
    exact Or.inl h
  | k + 1, h => by
    simp only [reach, Bool.or_eq_true]
    exact Or.inl (Or.inr h)

theorem reach_step (T : ℕ) (pool : List ℕ) (c : ℕ) (hc : c ∈ stepC pool) (hcin : c ∉ pool) :
    ∀ k, reach T (pool ++ [c]) k = true → reach T pool (k + 1) = true
  | 0, h => by
    simp only [reach] at h
    rw [hitP, List.any_append, Bool.or_eq_true] at h
    simp only [reach, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl h
    · simp at h
      exact Or.inr (hit2_of T pool c hc h)
  | k + 1, h => by
    simp only [reach, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨c, mem_myDedup _ c hc, by simp [hcin, h]⟩

-- Every wire is one of the masks of the pool.
def Inv (pool : List ℕ) (ws : Fin 9 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 9, m.testBit p = (ws p).getD i false

theorem testBit_511 : ∀ p : Fin 9, (511 : ℕ).testBit p = true := by decide

theorem gate_vec (pool : List ℕ) (ws : Fin 9 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ stepC pool, ∀ p : Fin 9,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨511, by simp [stepC], fun p => by simp [GateOp.eval, testBit_511 p]⟩
    · exact ⟨0, by simp [stepC], fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    refine ⟨ma, by simp [stepC, hma], fun p => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval, ha p]
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    obtain ⟨mb, hmb, hb⟩ := h b
    rcases hop with rfl | rfl
    · refine ⟨ma &&& mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem out_hit (T : ℕ) (hT : T < 512) (pool : List ℕ) (ws : Fin 9 → List Bool) (o : ℕ)
    (hI : Inv pool ws) (hout : ∀ p : Fin 9, (ws p).getD o false = T.testBit p) :
    hitP T pool = true := by
  obtain ⟨m, hm, hmb⟩ := hI o
  have hmT : m % 512 = T := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow]
    by_cases hi : i < 9
    · simp only [hi, decide_true, Bool.true_and]
      exact (hmb ⟨i, hi⟩).trans (hout ⟨i, hi⟩)
    · simp only [hi, decide_false, Bool.false_and]
      symm
      apply Nat.testBit_eq_false_of_lt
      calc T < 2 ^ 9 := hT
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact List.any_eq_true.mpr ⟨m, hm, by simp [hmT]⟩

theorem inv_step (pool pool' : List ℕ) (ws : Fin 9 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 9 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 9, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  intro i
  obtain ⟨m, hm, hmb⟩ := hI i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

-- Part 4. A gate reading a wire that is off at all nine inputs adds no new mask.

def Dead (g : Gate) (ws : Fin 9 → List Bool) : Prop :=
  ∃ i ∈ g.inputs, ∀ p : Fin 9, (ws p).getD i false = false

open Classical in
noncomputable def deadCount : List Gate → (Fin 9 → List Bool) → ℕ
  | [], _ => 0
  | g :: gs, ws => (if Dead g ws then 1 else 0) + deadCount gs (fun p => step (ws p) g)

theorem deadCount_le : ∀ (gs : List Gate) (ws : Fin 9 → List Bool), deadCount gs ws ≤ gs.length
  | [], _ => by simp [deadCount]
  | g :: gs, ws => by
    have := deadCount_le gs (fun p => step (ws p) g)
    rw [deadCount, List.length_cons]
    split_ifs <;> omega

theorem dead_vec (pool : List ℕ) (ws : Fin 9 → List Bool) (hI : Inv pool ws) (hz : 0 ∈ pool)
    (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (hd : Dead g ws) :
    ∃ m ∈ pool, ∀ p : Fin 9,
      m.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨i, hi, hfalse⟩ := hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen hi ⊢
  match ins, hlen, hi with
  | [], _, hi => simp at hi
  | [a], _, hi =>
    simp only [List.mem_singleton] at hi
    subst hi
    refine ⟨0, hz, fun p => ?_⟩
    simp only [List.map_cons, List.map_nil]
    rcases hop with rfl | rfl
    · rw [and1, hfalse p, Nat.zero_testBit]
    · rw [or1, hfalse p, Nat.zero_testBit]
  | [a, b], _, hi =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hop with rfl | rfl
    · refine ⟨0, hz, fun p => ?_⟩
      simp only [List.map_cons, List.map_nil]
      rcases hi with rfl | rfl
      · rw [and2, hfalse p, Nat.zero_testBit, Bool.false_and]
      · rw [and2, hfalse p, Nat.zero_testBit, Bool.and_false]
    · rcases hi with rfl | rfl
      · obtain ⟨mb, hmb, hb⟩ := hI b
        refine ⟨mb, hmb, fun p => ?_⟩
        simp only [List.map_cons, List.map_nil]
        rw [or2, hfalse p, Bool.false_or, hb p]
      · obtain ⟨ma, hma, ha⟩ := hI a
        refine ⟨ma, hma, fun p => ?_⟩
        simp only [List.map_cons, List.map_nil]
        rw [or2, hfalse p, Bool.or_false, ha p]
  | _ :: _ :: _ :: _, hl, _ => simp at hl

-- A circuit with k gates beyond its dead ones reaches the target in the search with budget k.
theorem mainD (T : ℕ) (hT : T < 512) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 9 → List Bool) (L k o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k + deadCount gs ws → (∀ p, (ws p).length = L) → Inv pool ws → 0 ∈ pool →
    (∀ p : Fin 9, (W gs (ws p)).getD o false = T.testBit p) →
    reach T pool k = true
  | [], pool, ws, _, k, o, _, _, _, hI, _, hout =>
    reach_of_hit T pool (out_hit T hT pool ws o hI hout) k
  | g :: gs, pool, ws, L, k, o, hg, hk, hL, hI, hz, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have hL' : ∀ p, (step (ws p) g).length = L + 1 := fun p => by rw [step_len, hL p]
    have hout' : ∀ p : Fin 9, (W gs (step (ws p) g)).getD o false = T.testBit p := hout
    by_cases hd : Dead g ws
    · obtain ⟨m, hm, hmv⟩ := dead_vec pool ws hI hz g hop hlen hd
      have hI' : Inv pool (fun p => step (ws p) g) :=
        inv_step pool pool ws L hL hI _ m hmv (fun _ h => h) hm
      have hk' : gs.length ≤ k + deadCount gs (fun p => step (ws p) g) := by
        rw [deadCount, if_pos hd, List.length_cons] at hk
        omega
      exact mainD T hT gs pool _ (L + 1) k o hg' hk' hL' hI' hz hout'
    · obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
      have hk' : gs.length + 1 ≤ k + deadCount gs (fun p => step (ws p) g) := by
        rw [deadCount, if_neg hd, List.length_cons] at hk
        omega
      have hle := deadCount_le gs (fun p => step (ws p) g)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      by_cases hcin : c ∈ pool
      · have hI' : Inv pool (fun p => step (ws p) g) :=
          inv_step pool pool ws L hL hI _ c hcv (fun _ h => h) hcin
        exact reach_mono T pool k'
          (mainD T hT gs pool _ (L + 1) k' o hg' (by omega) hL' hI' hz hout')
      · have hI' : Inv (pool ++ [c]) (fun p => step (ws p) g) :=
          inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp)
        exact reach_step T pool c hc hcin k'
          (mainD T hT gs (pool ++ [c]) _ (L + 1) k' o hg' (by omega) hL' hI' (by simp [hz]) hout')

-- Gate number j is dead: at the moment it is evaluated one of its wires is off at all inputs.
def DeadAt (gs : List Gate) (ws : Fin 9 → List Bool) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧
    ∃ i ∈ g.inputs, ∀ p : Fin 9, (W (gs.take j) (ws p)).getD i false = false

theorem deadAt_zero (g : Gate) (gs : List Gate) (ws : Fin 9 → List Bool)
    (h : DeadAt (g :: gs) ws 0) : Dead g ws := by
  obtain ⟨g', hg', i, hi, hp⟩ := h
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hg'
  subst hg'
  exact ⟨i, hi, hp⟩

theorem deadAt_succ (g : Gate) (gs : List Gate) (ws : Fin 9 → List Bool) (j : ℕ)
    (h : DeadAt (g :: gs) ws (j + 1)) : DeadAt gs (fun p => step (ws p) g) j := by
  obtain ⟨g', hg', i, hi, hp⟩ := h
  simp only [List.getElem?_cons_succ] at hg'
  exact ⟨g', hg', i, hi, hp⟩

theorem dc_one : ∀ (gs : List Gate) (ws : Fin 9 → List Bool) (j : ℕ),
    DeadAt gs ws j → 1 ≤ deadCount gs ws
  | [], _, _, h => by obtain ⟨g, hg, _⟩ := h; simp at hg
  | g :: gs, ws, 0, h => by
    rw [deadCount, if_pos (deadAt_zero g gs ws h)]
    omega
  | g :: gs, ws, j + 1, h => by
    have := dc_one gs _ j (deadAt_succ g gs ws j h)
    rw [deadCount]
    exact le_trans this (Nat.le_add_left _ _)

theorem dc_two : ∀ (gs : List Gate) (ws : Fin 9 → List Bool) (j1 j2 : ℕ), j1 < j2 →
    DeadAt gs ws j1 → DeadAt gs ws j2 → 2 ≤ deadCount gs ws
  | [], _, _, _, _, h, _ => by obtain ⟨g, hg, _⟩ := h; simp at hg
  | _ :: _, _, _, 0, hlt, _, _ => absurd hlt (Nat.not_lt_zero _)
  | g :: gs, ws, 0, j2 + 1, _, h1, h2 => by
    have := dc_one gs _ j2 (deadAt_succ g gs ws j2 h2)
    rw [deadCount, if_pos (deadAt_zero g gs ws h1)]
    omega
  | g :: gs, ws, j1 + 1, j2 + 1, hlt, h1, h2 => by
    have := dc_two gs _ j1 j2 (by omega) (deadAt_succ g gs ws j1 h1) (deadAt_succ g gs ws j2 h2)
    rw [deadCount]
    exact le_trans this (Nat.le_add_left _ _)

theorem dc_two' (gs : List Gate) (ws : Fin 9 → List Bool) (j1 j2 : ℕ) (hne : j1 ≠ j2)
    (h1 : DeadAt gs ws j1) (h2 : DeadAt gs ws j2) : 2 ≤ deadCount gs ws := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact dc_two gs ws j1 j2 h h1 h2
  · exact dc_two gs ws j2 j1 h h2 h1

-- Part 5. The nine inputs, and the two wires that are off at all of them.

def X9 (p : Fin 9) : List Bool :=
  oneEach (⟨1 + p.val / 3, by omega⟩ : Fin 4) (⟨1 + p.val % 3, by omega⟩ : Fin 4)

theorem X9_len (p : Fin 9) : (X9 p).length = 8 := by simp [X9, oneEach]

theorem oe_len (u v : Fin 4) : (oneEach u v).length = 8 := by simp [oneEach]

def pool9 : List ℕ := [0, 7, 56, 448, 0, 73, 146, 292]

theorem inv9 : Inv pool9 X9 := by
  intro i
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 9, (pool9.getD j 0).testBit p = (X9 p).getD j false := by
      decide
    exact ⟨pool9.getD i 0, by interval_cases i <;> simp [pool9], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by simp [pool9], fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X9_len]; omega)]

theorem X9_0 : ∀ p : Fin 9, (X9 p).getD 0 false = false := by decide

theorem X9_4 : ∀ p : Fin 9, (X9 p).getD 4 false = false := by decide

theorem tgt9 : ∀ p : Fin 9,
    A (⟨1 + p.val / 3, by omega⟩ : Fin 4) (⟨1 + p.val % 3, by omega⟩ : Fin 4) =
      (11 : ℕ).testBit p := by decide

-- Row 0 with column 3 is joined, row 1 with column 3 is not: wire 0 has to be read.
theorem h03 (i : ℕ) (hi : i ≠ 0) (h : (oneEach (0 : Fin 4) (3 : Fin 4)).getD i false = true) :
    (oneEach (1 : Fin 4) (3 : Fin 4)).getD i false = true := by
  by_cases h8 : i < 8
  · have key : ∀ j : Fin 8, j.val ≠ 0 →
        (oneEach (0 : Fin 4) (3 : Fin 4)).getD j false = true →
        (oneEach (1 : Fin 4) (3 : Fin 4)).getD j false = true := by decide
    exact key ⟨i, h8⟩ hi h
  · rw [List.getD_eq_default _ _ (by rw [oe_len]; omega)] at h
    exact absurd h (by simp)

-- Row 3 with column 0 is joined, row 3 with column 1 is not: wire 4 has to be read.
theorem h30 (i : ℕ) (hi : i ≠ 4) (h : (oneEach (3 : Fin 4) (0 : Fin 4)).getD i false = true) :
    (oneEach (3 : Fin 4) (1 : Fin 4)).getD i false = true := by
  by_cases h8 : i < 8
  · have key : ∀ j : Fin 8, j.val ≠ 4 →
        (oneEach (3 : Fin 4) (0 : Fin 4)).getD j false = true →
        (oneEach (3 : Fin 4) (1 : Fin 4)).getD j false = true := by decide
    exact key ⟨i, h8⟩ hi h
  · rw [List.getD_eq_default _ _ (by rw [oe_len]; omega)] at h
    exact absurd h (by simp)

theorem read0 (gs : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hrep : ∀ u v : Fin 4, (W gs (oneEach u v)).getD o false = A u v) :
    ∃ (j : ℕ) (g : Gate), gs[j]? = some g ∧ 0 ∈ g.inputs := by
  by_contra hno
  push_neg at hno
  have hE := cmp (fun i => i = 0) gs (oneEach 0 3) (oneEach 1 3) hops (by rw [oe_len, oe_len])
    h03 (fun j g hj _ i hi h => hno j g hj (h ▸ hi))
  by_cases ho : o = 0
  · have h := hrep 1 0
    rw [ho, W_prefix gs _ 0 (by rw [oe_len]; omega)] at h
    revert h
    decide
  · have h1 := hE o ho (by rw [hrep]; decide)
    rw [hrep] at h1
    revert h1
    decide

theorem read4 (gs : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hrep : ∀ u v : Fin 4, (W gs (oneEach u v)).getD o false = A u v) :
    ∃ (j : ℕ) (g : Gate), gs[j]? = some g ∧ 4 ∈ g.inputs := by
  by_contra hno
  push_neg at hno
  have hE := cmp (fun i => i = 4) gs (oneEach 3 0) (oneEach 3 1) hops (by rw [oe_len, oe_len])
    h30 (fun j g hj _ i hi h => hno j g hj (h ▸ hi))
  by_cases ho : o = 4
  · have h := hrep 0 1
    rw [ho, W_prefix gs _ 4 (by rw [oe_len]; omega)] at h
    revert h
    decide
  · have h1 := hE o ho (by rw [hrep]; decide)
    rw [hrep] at h1
    revert h1
    decide

-- A gate reading exactly wires 0 and 4 is off wherever both of them are off.
theorem wire_dead (gs : List Gate) (j : ℕ) (g : Gate) (w : List Bool) (hw : w.length = 8)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hins : g.inputs = [0, 4] ∨ g.inputs = [4, 0])
    (h0 : w.getD 0 false = false) (h4 : w.getD 4 false = false)
    (hj : gs[j]? = some g ∨ gs.length ≤ j) : (W gs w).getD (8 + j) false = false := by
  rcases hj with hj | hj
  · obtain ⟨pre, post, rfl, hpre⟩ := split_at gs j g hj
    have key := W_at pre g post w
    rw [hw, hpre] at key
    rw [key]
    have e0 : (W pre w).getD 0 false = false := by rw [W_prefix pre w 0 (by omega)]; exact h0
    have e4 : (W pre w).getD 4 false = false := by rw [W_prefix pre w 4 (by omega)]; exact h4
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hins with h | h <;> rcases hop with h1 | h1 <;> rw [h, h1] <;>
      simp only [List.map_cons, List.map_nil] <;> rw [e0, e4] <;> rfl
  · exact W_ge gs w (8 + j) (by omega)

theorem two_ins : ∀ (l : List ℕ), 0 ∈ l → 4 ∈ l → l.length ≤ 2 → l = [0, 4] ∨ l = [4, 0]
  | [], h0, _, _ => by simp at h0
  | [a], h0, h4, _ => by
    simp only [List.mem_singleton] at h0 h4
    omega
  | [a, b], h0, h4, _ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h4
    rcases h0 with h0 | h0 <;> rcases h4 with h4 | h4
    · omega
    · left; rw [← h0, ← h4]
    · right; rw [← h0, ← h4]
    · omega
  | _ :: _ :: _ :: _, _, _, hl => by simp at hl

-- If one gate alone reads wires 0 and 4, some gate has to read that gate.
theorem read8 (gs : List Gate) (o j : ℕ) (g : Gate)
    (hops : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hrep : ∀ u v : Fin 4, (W gs (oneEach u v)).getD o false = A u v)
    (hj : gs[j]? = some g) (hins : g.inputs = [0, 4] ∨ g.inputs = [4, 0])
    (honly : ∀ j' g', j' ≠ j → gs[j']? = some g' → 0 ∉ g'.inputs) :
    ∃ (j' : ℕ) (g' : Gate), gs[j']? = some g' ∧ (8 + j) ∈ g'.inputs := by
  by_contra hno
  push_neg at hno
  have hE := cmp (fun i => i = 0 ∨ i = 8 + j) gs (oneEach 0 3) (oneEach 1 3) hops
    (by rw [oe_len, oe_len]) (fun i hi => h03 i (fun h => hi (Or.inl h)))
    (fun j' g' hj' hE i hi h => by
      rw [oe_len] at hE
      rcases h with h | h
      · exact honly j' g' (fun e => hE (Or.inr (by rw [e]))) hj' (h ▸ hi)
      · exact hno j' g' hj' (h ▸ hi))
  by_cases ho : o = 0 ∨ o = 8 + j
  · rcases ho with ho | ho
    · have h := hrep 1 0
      rw [ho, W_prefix gs _ 0 (by rw [oe_len]; omega)] at h
      revert h
      decide
    · have h := hrep 1 1
      rw [ho, wire_dead gs j g _ (oe_len 1 1) (hops g (List.mem_of_getElem? hj)) hins
        (by decide) (by decide) (Or.inl hj)] at h
      revert h
      decide
  · have h1 := hE o ho (by rw [hrep]; decide)
    rw [hrep] at h1
    revert h1
    decide

theorem dead_of0 (gs : List Gate) (j : ℕ) (g : Gate) (hj : gs[j]? = some g)
    (h : 0 ∈ g.inputs) : DeadAt gs X9 j :=
  ⟨g, hj, 0, h, fun p => by rw [W_prefix _ _ 0 (by rw [X9_len]; omega)]; exact X9_0 p⟩

theorem dead_of4 (gs : List Gate) (j : ℕ) (g : Gate) (hj : gs[j]? = some g)
    (h : 4 ∈ g.inputs) : DeadAt gs X9 j :=
  ⟨g, hj, 4, h, fun p => by rw [W_prefix _ _ 4 (by rw [X9_len]; omega)]; exact X9_4 p⟩

theorem dead_of8 (gs : List Gate) (j j' : ℕ) (g g' : Gate) (hj : gs[j]? = some g)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hins : g.inputs = [0, 4] ∨ g.inputs = [4, 0])
    (hj' : gs[j']? = some g') (h : (8 + j) ∈ g'.inputs) : DeadAt gs X9 j' :=
  ⟨g', hj', 8 + j, h, fun p =>
    wire_dead (gs.take j') j g (X9 p) (X9_len p) hop hins (X9_0 p) (X9_4 p) (by
      by_cases hlt : j < j'
      · left
        rw [List.getElem?_take_of_lt hlt]
        exact hj
      · right
        rw [List.length_take]
        omega)⟩

-- Every circuit for the graph has two dead gates on the nine inputs.
theorem twoDead (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hrep : ∀ u v : Fin 4, (W gs (oneEach u v)).getD o false = A u v) :
    2 ≤ deadCount gs X9 := by
  have hops : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g h => (hg g h).1
  obtain ⟨j0, g0, hj0, h0⟩ := read0 gs o hops hrep
  obtain ⟨j4, g4, hj4, h4⟩ := read4 gs o hops hrep
  by_cases hne : j0 = j4
  · subst hne
    have hgg : g0 = g4 := by
      rw [hj0] at hj4
      exact Option.some.inj hj4
    subst hgg
    by_cases hother : ∃ (j' : ℕ) (g' : Gate), j' ≠ j0 ∧ gs[j']? = some g' ∧
        (0 ∈ g'.inputs ∨ 4 ∈ g'.inputs)
    · obtain ⟨j', g', hne', hj', h04⟩ := hother
      have hd' : DeadAt gs X9 j' := by
        rcases h04 with h | h
        · exact dead_of0 gs j' g' hj' h
        · exact dead_of4 gs j' g' hj' h
      exact dc_two' gs X9 j0 j' (Ne.symm hne') (dead_of0 gs j0 g0 hj0 h0) hd'
    · push_neg at hother
      have hmem : g0 ∈ gs := List.mem_of_getElem? hj0
      have hins := two_ins g0.inputs h0 h4 (hg g0 hmem).2
      obtain ⟨j', g', hj', h8⟩ := read8 gs o j0 g0 hops hrep hj0 hins
        (fun j' g' hne' hj' => (hother j' g' hne' hj').1)
      have hne' : j' ≠ j0 := by
        rintro rfl
        rw [hj0] at hj'
        have e := Option.some.inj hj'
        subst e
        rcases hins with h | h <;> rw [h] at h8 <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h8 <;> omega
      exact dc_two' gs X9 j0 j' (Ne.symm hne') (dead_of0 gs j0 g0 hj0 h0)
        (dead_of8 gs j0 j' g0 g' hj0 (hops g0 hmem) hins hj' h8)
  · exact dc_two' gs X9 j0 j4 hne (dead_of0 gs j0 g0 hj0 h0) (dead_of4 gs j4 g4 hj4 h4)

-- Part 6. The two halves.

theorem low_reach : reach 11 pool9 3 = false := by decide +kernel

theorem lower : ¬ RepSizeAtMost A 5 := by
  rintro ⟨C, hC, hs, hrep⟩
  have hrep' : ∀ u v : Fin 4, (W C.gates (oneEach u v)).getD C.output false = A u v := hrep
  have h2 := twoDead C.gates C.output hC hrep'
  have hlen : C.gates.length ≤ 3 + deadCount C.gates X9 := by
    have h5 : C.gates.length ≤ 5 := hs
    omega
  have h := mainD 11 (by norm_num) C.gates pool9 X9 8 3 C.output hC hlen X9_len inv9
    (by simp [pool9])
    (fun p => (hrep' (⟨1 + p.val / 3, by omega⟩ : Fin 4)
      (⟨1 + p.val % 3, by omega⟩ : Fin 4)).trans (tgt9 p))
  rw [low_reach] at h
  exact absurd h (by simp)

theorem upper : RepSizeAtMost A 6 := by
  refine ⟨⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_6054

theorem PEqualNP.Outside.L_meta_6054 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4991 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4991 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_6054.upper, PEqualNP.Outside.L_meta_6054.lower⟩
