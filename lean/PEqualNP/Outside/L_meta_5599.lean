import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5599_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

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

def hitP (T : ℕ) (pool : List ℕ) : Bool := pool.any (fun m => m % 65536 == T)

def hit2 (T : ℕ) (pool : List ℕ) : Bool :=
  T == 65535 || T == 0 || hitP T pool ||
    pool.any (fun a => pool.any (fun b => (a &&& b) % 65536 == T || (a ||| b) % 65536 == T))

theorem hit2_of (T : ℕ) (pool : List ℕ) (c : ℕ) (hc : c ∈ stepC pool) (h : c % 65536 = T) :
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

def hit3 (T : ℕ) (pool : List ℕ) : Bool :=
  (stepC pool).any (fun c => pool.any (fun a => (c ||| a) % 65536 == T || (c &&& a) % 65536 == T))

def reach (T : ℕ) : List ℕ → ℕ → Bool
  | pool, 0 => hitP T pool
  | pool, 1 => hitP T pool || hit2 T pool
  | pool, 2 => hitP T pool || hit2 T pool || hit3 T pool
  | pool, k + 3 => hitP T pool || reach T pool (k + 2) ||
      (myDedup (stepC pool)).any (fun c => !pool.contains c && reach T (pool ++ [c]) (k + 2))

theorem reach_split (T : ℕ) (pool : List ℕ) (k : ℕ) (h1 : hitP T pool = false)
    (h2 : reach T pool (k + 2) = false)
    (h3 : ∀ c ∈ myDedup (stepC pool), pool.contains c = false →
      reach T (pool ++ [c]) (k + 2) = false) :
    reach T pool (k + 3) = false := by
  simp only [reach, h1, h2, Bool.false_or]
  apply List.any_eq_false.mpr
  intro c hc
  cases hcc : pool.contains c
  · simp [h3 c hc hcc]
  · simp

theorem reach_of_hit (T : ℕ) (pool : List ℕ) (h : hitP T pool = true) :
    ∀ k, reach T pool k = true
  | 0 => by simp only [reach]; exact h
  | 1 => by simp only [reach, Bool.or_eq_true]; exact Or.inl h
  | 2 => by simp only [reach, Bool.or_eq_true]; exact Or.inl (Or.inl h)
  | k + 3 => by simp only [reach, Bool.or_eq_true]; exact Or.inl (Or.inl h)

theorem two_step (T : ℕ) (pool : List ℕ) (c d m : ℕ) (hc : c ∈ stepC pool)
    (hd : d ∈ stepC (pool ++ [c])) (hm : m ∈ pool ++ [c] ++ [d]) (h : m % 65536 = T) :
    (hitP T pool || hit2 T pool || hit3 T pool) = true := by
  have hP : ∀ x ∈ pool, x % 65536 = T → (hitP T pool || hit2 T pool || hit3 T pool) = true := by
    intro x hx hxT
    simp only [Bool.or_eq_true]
    exact Or.inl (Or.inl (List.any_eq_true.mpr ⟨x, hx, by simp [hxT]⟩))
  have h2 : ∀ x ∈ stepC pool, x % 65536 = T →
      (hitP T pool || hit2 T pool || hit3 T pool) = true := by
    intro x hx hxT
    simp only [Bool.or_eq_true]
    exact Or.inl (Or.inr (hit2_of T pool x hx hxT))
  have h3 : ∀ x ∈ stepC pool, ∀ y ∈ pool, ((x ||| y) % 65536 = T ∨ (x &&& y) % 65536 = T) →
      (hitP T pool || hit2 T pool || hit3 T pool) = true := by
    intro x hx y hy hxy
    simp only [Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.mpr ⟨x, hx, List.any_eq_true.mpr ⟨y, hy, ?_⟩⟩)
    simpa using hxy
  have hpair : ∀ x ∈ pool, ∀ y ∈ pool, x &&& y ∈ stepC pool ∧ x ||| y ∈ stepC pool := by
    intro x hx y hy
    simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
    exact ⟨Or.inr (Or.inr (Or.inr ⟨x, hx, y, hy, by simp⟩)),
      Or.inr (Or.inr (Or.inr ⟨x, hx, y, hy, by simp⟩))⟩
  simp only [List.mem_append, List.mem_singleton] at hm
  rcases hm with (hm | rfl) | rfl
  · exact hP m hm h
  · exact h2 m hc h
  · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap,
      List.mem_singleton, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | (hd | rfl) | ⟨x, hx, y, hy, hd⟩
    · exact h2 65535 (by simp [stepC]) h
    · exact h2 0 (by simp [stepC]) h
    · exact hP _ hd h
    · exact h2 _ hc h
    · try simp only [List.mem_append, List.mem_singleton] at hx hy
      try simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · rcases hd with rfl | rfl
        · exact h2 _ (hpair x hx y hy).1 h
        · exact h2 _ (hpair x hx y hy).2 h
      · subst y
        rcases hd with rfl | rfl
        · exact h3 _ hc x hx (Or.inr (by rw [Nat.land_comm]; exact h))
        · exact h3 _ hc x hx (Or.inl (by rw [Nat.lor_comm]; exact h))
      · subst x
        rcases hd with rfl | rfl
        · exact h3 _ hc y hy (Or.inr h)
        · exact h3 _ hc y hy (Or.inl h)
      · subst x; subst y
        rcases hd with rfl | rfl
        · exact h2 _ hc (by first | (rw [Nat.and_self] at h; exact h) | simpa using h)
        · exact h2 _ hc (by first | (rw [Nat.or_self] at h; exact h) | simpa using h)

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
      · simp [GateOp.eval, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem out_hit (T : ℕ) (hT : T < 65536) (pool : List ℕ) (ws : Fin 16 → List Bool) (o : ℕ)
    (hI : Inv pool ws) (hout : ∀ p : Fin 16, (ws p).getD o false = T.testBit p) :
    hitP T pool = true := by
  obtain ⟨m, hm, hmb⟩ := hI o
  have hmT : m % 65536 = T := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
    by_cases hi : i < 16
    · simp only [hi, decide_true, Bool.true_and]
      exact (hmb ⟨i, hi⟩).trans (hout ⟨i, hi⟩)
    · simp only [hi, decide_false, Bool.false_and]
      symm; apply Nat.testBit_eq_false_of_lt
      calc T < 2 ^ 16 := hT
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact List.any_eq_true.mpr ⟨m, hm, by simp [hmT]⟩

theorem inv_step (pool pool' : List ℕ) (ws : Fin 16 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 16 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 16, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  intro i
  obtain ⟨m, hm, hmb⟩ := hI i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

abbrev stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem le1 (T : ℕ) (hT : T < 65536) (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L o : ℕ)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hk : gs.length ≤ 1) (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws)
    (hout : ∀ p : Fin 16, (gs.foldl stepW (ws p)).getD o false = T.testBit p) :
    (hitP T pool || hit2 T pool) = true := by
  match gs, hk with
  | [], _ =>
    simp only [Bool.or_eq_true]
    exact Or.inl (out_hit T hT pool ws o hI (fun p => hout p))
  | [g], _ =>
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hh := out_hit T hT (pool ++ [c]) _ o
      (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
      (fun p => hout p)
    rw [hitP, List.any_append, Bool.or_eq_true] at hh
    simp only [Bool.or_eq_true]
    rcases hh with hh | hh
    · exact Or.inl hh
    · simp at hh
      exact Or.inr (hit2_of T pool c hc hh)
  | _ :: _ :: _, h => simp at h

theorem le2 (T : ℕ) (hT : T < 65536) (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L o : ℕ)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hk : gs.length ≤ 2) (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws)
    (hout : ∀ p : Fin 16, (gs.foldl stepW (ws p)).getD o false = T.testBit p) :
    (hitP T pool || hit2 T pool || hit3 T pool) = true := by
  match gs, hk with
  | [g1, g2], _ =>
    obtain ⟨hop, hlen⟩ := hg g1 (by simp)
    obtain ⟨hop2, hlen2⟩ := hg g2 (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g1 hop hlen
    have hI1 := inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp)
    obtain ⟨d, hd, hdv⟩ := gate_vec (pool ++ [c]) _ hI1 g2 hop2 hlen2
    have hL1 : ∀ p, (ws p ++ [g1.op.eval (g1.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 := fun p => by simp [hL p]
    have hI2 := inv_step (pool ++ [c]) (pool ++ [c] ++ [d]) _ (L + 1) hL1 hI1 _ d hdv
      (fun m hm => List.mem_append_left _ hm) (by simp)
    have hh := out_hit T hT (pool ++ [c] ++ [d]) _ o hI2 (fun p => hout p)
    obtain ⟨m, hm, hmT⟩ := List.any_eq_true.mp hh
    exact two_step T pool c d m hc hd hm (by simpa using hmT)
  | [], _ =>
    have := le1 T hT [] pool ws L o (by simp) (by simp) hL hI hout
    simp only [Bool.or_eq_true] at this ⊢; exact Or.inl this
  | [g], _ =>
    have := le1 T hT [g] pool ws L o hg (by simp) hL hI hout
    simp only [Bool.or_eq_true] at this ⊢; exact Or.inl this
  | _ :: _ :: _ :: _, h => simp at h

theorem main (T : ℕ) (hT : T < 65536) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L k o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → (∀ p, (ws p).length = L) → Inv pool ws →
    (∀ p : Fin 16, (gs.foldl stepW (ws p)).getD o false = T.testBit p) →
    reach T pool k = true
  | gs, pool, ws, L, 0, o, hg, hk, hL, hI, hout => by
    have := le1 T hT gs pool ws L o hg (by omega) hL hI hout
    have hgs : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hgs
    simp only [reach]; exact out_hit T hT pool ws o hI (fun p => hout p)
  | gs, pool, ws, L, 1, o, hg, hk, hL, hI, hout => by
    simp only [reach]; exact le1 T hT gs pool ws L o hg hk hL hI hout
  | gs, pool, ws, L, 2, o, hg, hk, hL, hI, hout => by
    simp only [reach]; exact le2 T hT gs pool ws L o hg hk hL hI hout
  | [], pool, ws, L, k + 3, o, _, _, _, hI, hout =>
    reach_of_hit T pool (out_hit T hT pool ws o hI (fun p => hout p)) (k + 3)
  | g :: gs, pool, ws, L, k + 3, o, hg, hk, hL, hI, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 16, (gs.foldl stepW
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by have h3 := hout p; rw [List.foldl_cons] at h3; exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hkl : gs.length ≤ k + 2 := by simp only [List.length_cons] at hk; omega
    by_cases hcin : c ∈ pool
    · have IH := main T hT gs pool _ (L + 1) (k + 2) o hg' hkl hL'
        (inv_step pool pool ws L hL hI _ c hcv (fun m hm => hm) hcin) hout'
      simp only [reach, Bool.or_eq_true]
      exact Or.inl (Or.inr IH)
    · have IH := main T hT gs (pool ++ [c]) _ (L + 1) (k + 2) o hg' hkl hL'
        (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        hout'
      simp only [reach, Bool.or_eq_true, List.any_eq_true]
      refine Or.inr ⟨c, mem_myDedup _ c hc, ?_⟩
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

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (51 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [8, 9]⟩], 10⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem low_reach : reach 51 pool0 2 = false := by decide +kernel

end PEqualNP.Outside.L_meta_5599_aux

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_5599 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (51 : ℕ).testBit (4 * u.val + v.val)) 3 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (51 : ℕ).testBit (4 * u.val + v.val)) 2 := by
  exact ⟨PEqualNP.Outside.L_meta_5599_aux.upper, PEqualNP.Outside.L_meta_5599_aux.lower 51 (by norm_num) 2 PEqualNP.Outside.L_meta_5599_aux.low_reach⟩
