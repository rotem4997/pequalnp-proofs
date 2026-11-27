import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5464_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def cands : ℕ → List ℕ → List ℕ
  | 0, pool => stepC pool
  | _ + 1, pool => (stepC pool).dedup

theorem mem_cands (k : ℕ) (pool : List ℕ) (c : ℕ) (h : c ∈ stepC pool) : c ∈ cands k pool := by
  cases k with
  | zero => exact h
  | succ k => exact List.mem_dedup.mpr h

def reach (T : ℕ) : List ℕ → ℕ → Bool
  | pool, 0 => pool.any (fun m => m % 65536 == T)
  | pool, k + 1 => pool.any (fun m => m % 65536 == T) || reach T pool k ||
      (cands k pool).any (fun c => !pool.contains c && reach T (pool ++ [c]) k)

def Inv (pool : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem testBit_65535 : ∀ p : Fin 16, (65535 : ℕ).testBit p = true := by decide

theorem gate_vec (pool : List ℕ) (ws : Fin 16 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ stepC pool, ∀ p : Fin 16,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨65535, by simp [stepC], fun p => by simp [GateOp.eval, testBit_65535 p]⟩
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
      · simp [GateOp.eval, Nat.testBit_land, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, Nat.testBit_lor, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem main (T : ℕ) (hT : T < 65536) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L k o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → (∀ p, (ws p).length = L) → Inv pool ws →
    (∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    reach T pool k = true
  | [], pool, ws, L, k, o, _, _, _, hI, hout => by
    obtain ⟨m, hm, hmb⟩ := hI o
    have hmT : m % 65536 = T := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
      by_cases hi : i < 16
      · simp only [hi, decide_true, Bool.true_and]
        have h2 := hout ⟨i, hi⟩
        simp only [List.foldl_nil] at h2
        exact (hmb ⟨i, hi⟩).trans h2
      · simp only [hi, decide_false, Bool.false_and]
        symm; apply Nat.testBit_eq_false_of_lt
        calc T < 2 ^ 16 := hT
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hany : pool.any (fun m => m % 65536 == T) = true :=
      List.any_eq_true.mpr ⟨m, hm, by simp [hmT]⟩
    cases k with
    | zero => simpa [reach] using hany
    | succ k => simp only [reach, Bool.or_eq_true]; exact Or.inl (Or.inl hany)
  | g :: gs, pool, ws, L, k, o, hg, hk, hL, hI, hout => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hinv : ∀ pool' : List ℕ, (∀ m ∈ pool, m ∈ pool') → c ∈ pool' → Inv pool'
        (fun p => ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]) := by
      intro pool' hsub hcp i
      obtain ⟨m, hm, hmb⟩ := hI i
      by_cases hi : i = L
      · subst hi
        exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
      · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩
    have hout' : ∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false = T.testBit p :=
      fun p => by have h3 := hout p; rw [List.foldl_cons] at h3; exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hk' : gs.length ≤ k := by simp at hk; omega
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length = L + 1 :=
      fun p => by simp [hL p]
    by_cases hcin : c ∈ pool
    · have IH := main T hT gs pool _ (L + 1) k o hg' hk' hL' (hinv pool (fun m hm => hm) hcin) hout'
      simp only [reach, Bool.or_eq_true]
      exact Or.inl (Or.inr IH)
    · have IH := main T hT gs (pool ++ [c]) _ (L + 1) k o hg' hk' hL'
        (hinv (pool ++ [c]) (fun m hm => by simp [hm]) (by simp)) hout'
      simp only [reach, Bool.or_eq_true, List.any_eq_true]
      refine Or.inr ⟨c, mem_cands k pool c hc, ?_⟩
      simp [hcin, IH]

def pool0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952, 0]

def X (p : Fin 16) : List Bool :=
  oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4)

theorem X_len (p : Fin 16) : (X p).length = 8 := by simp [X, oneEach]

theorem inv0 : Inv pool0 X := by
  intro i
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 16, (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by simp [pool0], fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

theorem lower (T : ℕ) (hT : T < 65536) (k : ℕ) (hr : reach T pool0 k = false) :
    ¬ RepSizeAtMost (fun u v : Fin 4 => T.testBit (4 * u.val + v.val)) k := by
  rintro ⟨C, hC, hs, hrep⟩
  have := main T hT C.gates pool0 X 8 k C.output hC hs X_len inv0 (fun p => by
    have h := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
    have he : T.testBit (4 * (p.val / 4) + p.val % 4) = T.testBit p := by
      rw [Nat.div_add_mod p.val 4]
    exact h.trans he)
  rw [hr] at this; exact absurd this (by simp)

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  refine ⟨⟨[⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [8, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_5464_aux

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_5464 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (18 : ℕ).testBit (4 * u.val + v.val)) 2 := by
  exact ⟨PEqualNP.Outside.L_meta_5464_aux.upper,
    PEqualNP.Outside.L_meta_5464_aux.lower 18 (by norm_num) 2 (by decide +kernel)⟩
