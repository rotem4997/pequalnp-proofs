import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5576
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The declarations stepC, Inv, getD_snoc, testBit_65535, gate_vec, inv_step, pool0, X, X_len, inv0
-- are taken from the checked file lean/PEqualNP/Outside/L_meta_5471.lean of this repository
-- (Apache-2.0). The search (Build, Live, srch and their lemmas) is new.

def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

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


theorem stepC_mem (pool : List ℕ) (c : ℕ) (h : c ∈ stepC pool) :
    c = 65535 ∨ c = 0 ∨ c ∈ pool ∨ ∃ a ∈ pool, ∃ b ∈ pool, c = a &&& b ∨ c = a ||| b := by
  simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    or_false] at h
  rcases h with h | h | h | ⟨a, ha, b, hb, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, h⟩))

theorem stepC_lt (pool : List ℕ) (hp : ∀ m ∈ pool, m < 65536) (c : ℕ) (hc : c ∈ stepC pool) :
    c < 65536 := by
  rcases stepC_mem pool c hc with h | h | h | ⟨a, ha, b, hb, h | h⟩
  · omega
  · omega
  · exact hp c h
  · rw [h]; exact lt_of_le_of_lt Nat.and_le_left (hp a ha)
  · rw [h]; exact Nat.or_lt_two_pow (n := 16) (hp a ha) (hp b hb)

-- A wire z may be added to the set s of available wires at the cost of one gate.
def Ok (s : Finset ℕ) (z : ℕ) : Prop :=
  z ∈ s ∨ ∃ a ∈ s, ∃ b ∈ s, z = a &&& b ∨ z = a ||| b ∨ z = 65535

-- T is obtained from the available wires s with at most k gates.
def Build (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => T ∈ s
  | k + 1, s => T ∈ s ∨ ∃ z, Ok s z ∧ Build T k (insert z s)

-- What is left of the live set s after a gate reads a and b: each of them may be kept.
def Shape (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ) : Prop :=
  r = (s.erase a).erase b ∨ r = insert a ((s.erase a).erase b) ∨
    r = insert b ((s.erase a).erase b) ∨ r = insert a (insert b ((s.erase a).erase b))

-- A derivation in which every wire of s is consumed, ending at exactly T.
def Live (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => s = {T}
  | k + 1, s => s = {T} ∨ ∃ a ∈ s, ∃ b ∈ s, ∃ z r,
      (z = a &&& b ∨ z = a ||| b ∨ z = 65535) ∧ z ∉ r ∧ Shape s a b r ∧ Live T k (insert z r)

theorem live_mono (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Live T k s → Live T (k + 1) s
  | 0, s, h => by
    simp only [Live] at h ⊢
    exact Or.inl h
  | k + 1, s, h => by
    rw [Live] at h
    rw [Live]
    rcases h with h | ⟨a, ha, b, hb, z, r, hz, hzr, hsh, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, z, r, hz, hzr, hsh, live_mono T k _ hl⟩

theorem shape_of (r : Finset ℕ) (a b : ℕ) : Shape (insert a (insert b r)) a b r := by
  unfold Shape
  by_cases har : a ∈ r <;> by_cases hbr : b ∈ r
  · right; right; right
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  · right; left
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  · right; right; left
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  · left
    ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all

theorem compress (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Build T k s → ∃ s' ⊆ s, Live T k s'
  | 0, s, h => by
    simp only [Build] at h
    exact ⟨{T}, by simpa using h, by simp [Live]⟩
  | k + 1, s, h => by
    rw [Build] at h
    rcases h with h | ⟨z, hz, hb⟩
    · exact ⟨{T}, by simpa using h, by simp [Live]⟩
    · obtain ⟨s', hs', hl⟩ := compress T k _ hb
      by_cases hsub : s' ⊆ s
      · exact ⟨s', hsub, live_mono T k s' hl⟩
      · have hzs : z ∈ s' := by
          by_contra hn
          exact hsub (fun x hx => by
            rcases Finset.mem_insert.1 (hs' hx) with h' | h'
            · rw [h'] at hx; exact absurd hx hn
            · exact h')
        have hzn : z ∉ s := fun hzin => hsub (fun x hx => by
          rcases Finset.mem_insert.1 (hs' hx) with h' | h'
          · rw [h']; exact hzin
          · exact h')
        rcases hz with hz | ⟨a, ha, b, hb', hzab⟩
        · exact absurd hz hzn
        · obtain ⟨r, hrdef⟩ : ∃ r, r = s'.erase z := ⟨_, rfl⟩
          have hr : r ⊆ s := fun x hx => by
            rw [hrdef] at hx
            have hx' := Finset.mem_erase.1 hx
            rcases Finset.mem_insert.1 (hs' hx'.2) with h' | h'
            · exact absurd h' hx'.1
            · exact h'
          have hzr : z ∉ r := by rw [hrdef]; simp
          have hins : insert z r = s' := by rw [hrdef, Finset.insert_erase hzs]
          refine ⟨insert a (insert b r), ?_, ?_⟩
          · intro x hx
            simp only [Finset.mem_insert] at hx
            rcases hx with h' | h' | hx
            · rw [h']; exact ha
            · rw [h']; exact hb'
            · exact hr hx
          · rw [Live]
            refine Or.inr ⟨a, by simp, b, by simp, z, r, hzab, hzr, shape_of r a b, ?_⟩
            rw [hins]; exact hl

theorem shape_sub (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ) (ha : a ∈ s) (hb : b ∈ s)
    (hsh : Shape s a b r) : ∀ x ∈ r, x ∈ s := by
  intro x hx
  unfold Shape at hsh
  rcases hsh with h | h | h | h <;> rw [h] at hx <;>
    simp only [Finset.mem_insert, Finset.mem_erase] at hx
  · exact hx.2.2
  · rcases hx with h' | hx
    · rw [h']; exact ha
    · exact hx.2.2
  · rcases hx with h' | hx
    · rw [h']; exact hb
    · exact hx.2.2
  · rcases hx with h' | h' | hx
    · rw [h']; exact ha
    · rw [h']; exact hb
    · exact hx.2.2

theorem shape_sup (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ)
    (hsh : Shape s a b r) : s ⊆ insert a (insert b r) := by
  intro x hx
  simp only [Finset.mem_insert]
  by_cases hxa : x = a
  · exact Or.inl hxa
  · by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    · right; right
      have hm : x ∈ (s.erase a).erase b := by simp [hxa, hxb, hx]
      unfold Shape at hsh
      rcases hsh with h | h | h | h <;> rw [h]
      · exact hm
      · exact Finset.mem_insert_of_mem hm
      · exact Finset.mem_insert_of_mem hm
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)

theorem live_card (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Live T k s → s.card ≤ k + 1
  | 0, s, h => by
    simp only [Live] at h
    simp [h]
  | k + 1, s, h => by
    rw [Live] at h
    rcases h with h | ⟨a, ha, b, hb, z, r, hz, hzr, hsh, hl⟩
    · simp [h]
    · have h1 := live_card T k _ hl
      rw [Finset.card_insert_of_notMem hzr] at h1
      have h3 := Finset.card_le_card (shape_sup s a b r hsh)
      have h4 := Finset.card_insert_le a (insert b r)
      have h5 := Finset.card_insert_le b r
      omega

-- Every accepted point is told apart from every rejected point by a live wire.
def Sep (T : ℕ) (s : Finset ℕ) : Prop :=
  ∀ p < 16, ∀ q < 16, T.testBit p = true → T.testBit q = false →
    ∃ w ∈ s, w.testBit p = true ∧ w.testBit q = false

theorem tb_full (q : ℕ) (hq : q < 16) : (65535 : ℕ).testBit q = true := by
  interval_cases q <;> rfl

theorem live_sep (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Live T k s → Sep T s
  | 0, s, h => by
    simp only [Live] at h
    intro p _ q _ hp hq
    exact ⟨T, by simp [h], hp, hq⟩
  | k + 1, s, h => by
    rw [Live] at h
    rcases h with h | ⟨a, ha, b, hb, z, r, hz, hzr, hsh, hl⟩
    · intro p _ q _ hp hq
      exact ⟨T, by simp [h], hp, hq⟩
    · have ih := live_sep T k _ hl
      intro p hp16 q hq16 hp hq
      obtain ⟨w, hw, hwp, hwq⟩ := ih p hp16 q hq16 hp hq
      rcases Finset.mem_insert.1 hw with hwz | hw
      · rw [hwz] at hwp hwq
        rcases hz with hz | hz | hz <;> rw [hz] at hwp hwq
        · rw [Nat.testBit_and, Bool.and_eq_true] at hwp
          rw [Nat.testBit_and, Bool.and_eq_false_iff] at hwq
          rcases hwq with hwq | hwq
          · exact ⟨a, ha, hwp.1, hwq⟩
          · exact ⟨b, hb, hwp.2, hwq⟩
        · rw [Nat.testBit_or, Bool.or_eq_true] at hwp
          rw [Nat.testBit_or, Bool.or_eq_false_iff] at hwq
          rcases hwp with hwp | hwp
          · exact ⟨a, ha, hwp, hwq.1⟩
          · exact ⟨b, hb, hwp, hwq.2⟩
        · rw [tb_full q hq16] at hwq; cases hwq
      · exact ⟨w, shape_sub s a b r ha hb hsh w hw, hwp, hwq⟩

def ins (a : ℕ) (l : List ℕ) : List ℕ := if l.contains a then l else a :: l

def rem (a b : ℕ) (l : List ℕ) : List ℕ := l.filter fun x => !(x == a) && !(x == b)

def sepB (T : ℕ) (ws : List ℕ) : Bool :=
  (List.range 16).all fun p => !T.testBit p ||
    (ws.foldl (fun acc w => if w.testBit p then acc &&& w else acc) (65535 ^^^ T) == 0)

def pairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | a :: l => (a, a) :: (l.map (fun b => (a, b)) ++ pairs l)

theorem pairs_mem : ∀ (l : List ℕ) (a b : ℕ), a ∈ l → b ∈ l → (a, b) ∈ pairs l ∨ (b, a) ∈ pairs l
  | [], a, b, ha, _ => by simp at ha
  | c :: l, a, b, ha, hb => by
    simp only [pairs, List.mem_cons, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 ha with ha | ha <;> rcases List.mem_cons.1 hb with hb | hb
    · left; left; exact ⟨ha, hb⟩
    · left; right; left; exact ⟨b, hb, ha.symm, rfl⟩
    · right; right; left; exact ⟨a, ha, hb.symm, rfl⟩
    · rcases pairs_mem l a b ha hb with h | h
      · left; right; right; exact h
      · right; right; right; exact h

theorem shape_symm (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ) (h : Shape s a b r) :
    Shape s b a r := by
  unfold Shape at h ⊢
  rw [Finset.erase_right_comm]
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (by rw [h]; ext x; simp only [Finset.mem_insert]; tauto)))

-- The search: all live derivations with at most k gates from the list ws.
def srch (T : ℕ) : ℕ → List ℕ → Bool
  | 0, ws => ws == [T]
  | k + 1, ws => ws == [T] || (decide (ws.length ≤ k + 2) && sepB T ws &&
      (pairs ws).any fun ab =>
        [rem ab.1 ab.2 ws, ins ab.1 (rem ab.1 ab.2 ws), ins ab.2 (rem ab.1 ab.2 ws),
          ins ab.1 (ins ab.2 (rem ab.1 ab.2 ws))].any
          fun r => [ab.1 &&& ab.2, ab.1 ||| ab.2, 65535].any
            fun z => !r.contains z && srch T k (z :: r))

theorem ins_nodup (a : ℕ) (l : List ℕ) (h : l.Nodup) : (ins a l).Nodup := by
  unfold ins
  split_ifs with hc
  · exact h
  · exact List.nodup_cons.2 ⟨by simpa using hc, h⟩

theorem ins_fin (a : ℕ) (l : List ℕ) : (ins a l).toFinset = insert a l.toFinset := by
  unfold ins
  split_ifs with hc
  · have hm : a ∈ l := by simpa using hc
    simp [hm]
  · simp

theorem rem_nodup (a b : ℕ) (l : List ℕ) (h : l.Nodup) : (rem a b l).Nodup := h.filter _

theorem rem_fin (a b : ℕ) (l : List ℕ) :
    (rem a b l).toFinset = (l.toFinset.erase a).erase b := by
  ext x
  simp only [rem, List.mem_toFinset, List.mem_filter, Finset.mem_erase, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  tauto

theorem fold_bit (p q : ℕ) : ∀ (ws : List ℕ) (acc : ℕ),
    (acc.testBit q = false ∨ ∃ w ∈ ws, w.testBit p = true ∧ w.testBit q = false) →
    (ws.foldl (fun acc w => if w.testBit p then acc &&& w else acc) acc).testBit q = false
  | [], acc, h => by
    rcases h with h | ⟨w, hw, _⟩
    · exact h
    · simp at hw
  | w :: ws, acc, h => by
    rw [List.foldl_cons]
    apply fold_bit p q ws
    rcases h with h | ⟨w', hw', hp, hq⟩
    · left
      split_ifs
      · rw [Nat.testBit_and, h]; rfl
      · exact h
    · rcases List.mem_cons.1 hw' with h' | hw'
      · left
        rw [h'] at hp hq
        rw [if_pos hp, Nat.testBit_and, hq]; simp
      · right; exact ⟨w', hw', hp, hq⟩

theorem sepB_of (T : ℕ) (hT : T < 65536) (ws : List ℕ) (h : Sep T ws.toFinset) :
    sepB T ws = true := by
  unfold sepB
  rw [List.all_eq_true]
  intro p hp
  have hp16 : p < 16 := List.mem_range.1 hp
  cases hTp : T.testBit p
  · simp
  · simp only [Bool.not_true, Bool.false_or, beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.zero_testBit]
    apply fold_bit
    by_cases hq16 : q < 16
    · cases hTq : T.testBit q
      · right
        obtain ⟨w, hw, h1, h2⟩ := h p hp16 q hq16 hTp hTq
        exact ⟨w, by simpa using hw, h1, h2⟩
      · left
        rw [Nat.testBit_xor, hTq, tb_full q hq16]; rfl
    · left
      have h1 : (65535 : ℕ).testBit q = false := Nat.testBit_eq_false_of_lt
        (calc 65535 < 2 ^ 16 := by norm_num
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : T.testBit q = false := Nat.testBit_eq_false_of_lt
        (calc T < 2 ^ 16 := hT
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_xor, h1, h2]; rfl

theorem single (T : ℕ) (ws : List ℕ) (hn : ws.Nodup) (h : ws.toFinset = {T}) : ws = [T] := by
  have hc : ws.length = 1 := by
    rw [← List.toFinset_card_of_nodup hn, h]; rfl
  match ws, hc, h with
  | [x], _, h =>
    have hx : x ∈ ({T} : Finset ℕ) := by rw [← h]; simp
    rw [Finset.mem_singleton.1 hx]

theorem srch_step (T : ℕ) (hT : T < 65536) (k : ℕ) (ws : List ℕ) (hn : ws.Nodup)
    (ih : ∀ ws' : List ℕ, ws'.Nodup → Live T k ws'.toFinset → srch T k ws' = true)
    (hcard : ws.length ≤ k + 2) (hsep : Sep T ws.toFinset) (a b z : ℕ) (r : Finset ℕ)
    (hab : (a, b) ∈ pairs ws) (hz : z = a &&& b ∨ z = a ||| b ∨ z = 65535) (hzr : z ∉ r)
    (hsh : Shape ws.toFinset a b r) (hl : Live T k (insert z r)) : srch T (k + 1) ws = true := by
  have key : ∃ rl ∈ [rem a b ws, ins a (rem a b ws), ins b (rem a b ws),
      ins a (ins b (rem a b ws))], rl.Nodup ∧ rl.toFinset = r := by
    have h0 := rem_nodup a b ws hn
    unfold Shape at hsh
    rcases hsh with h | h | h | h <;> rw [h]
    · exact ⟨_, by simp, h0, rem_fin a b ws⟩
    · exact ⟨ins a (rem a b ws), by simp, ins_nodup _ _ h0, by rw [ins_fin, rem_fin]⟩
    · exact ⟨ins b (rem a b ws), by simp, ins_nodup _ _ h0, by rw [ins_fin, rem_fin]⟩
    · exact ⟨ins a (ins b (rem a b ws)), by simp, ins_nodup _ _ (ins_nodup _ _ h0),
        by rw [ins_fin, ins_fin, rem_fin]⟩
  obtain ⟨rl, hrl, hrn, hrf⟩ := key
  have hzl : z ∉ rl := by
    rw [← hrf] at hzr
    simpa using hzr
  have ih' := ih (z :: rl) (List.nodup_cons.2 ⟨hzl, hrn⟩)
    (by rw [List.toFinset_cons, hrf]; exact hl)
  rw [srch]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  right
  refine ⟨⟨hcard, sepB_of T hT ws hsep⟩, (a, b), hab, rl, hrl, z, ?_, ?_⟩
  · rcases hz with hz | hz | hz <;> rw [hz] <;> simp
  · simp [hzl, ih']

theorem srch_complete (T : ℕ) (hT : T < 65536) : ∀ (k : ℕ) (ws : List ℕ), ws.Nodup →
    Live T k ws.toFinset → srch T k ws = true
  | 0, ws, hn, h => by
    simp only [Live] at h
    simp [srch, single T ws hn h]
  | k + 1, ws, hn, h => by
    have hcard := live_card T (k + 1) _ h
    have hsep := live_sep T (k + 1) _ h
    rw [Live] at h
    rcases h with h | ⟨a, ha, b, hb, z, r, hz, hzr, hsh, hl⟩
    · simp [srch, single T ws hn h]
    · rw [List.toFinset_card_of_nodup hn] at hcard
      rcases pairs_mem ws a b (by simpa using ha) (by simpa using hb) with hab | hab
      · exact srch_step T hT k ws hn (srch_complete T hT k) (by omega) hsep a b z r hab hz hzr
          hsh hl
      · refine srch_step T hT k ws hn (srch_complete T hT k) (by omega) hsep b a z r hab ?_ hzr
          (shape_symm _ a b r hsh) hl
        rcases hz with hz | hz | hz
        · exact Or.inl (by rw [hz, Nat.land_comm])
        · exact Or.inr (Or.inl (by rw [hz, Nat.lor_comm]))
        · exact Or.inr (Or.inr hz)

theorem main (T : ℕ) (hT : T < 65536) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L k o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → (∀ p, (ws p).length = L) → Inv pool ws → (∀ m ∈ pool, m < 65536) →
    0 ∈ pool →
    (∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    Build T k pool.toFinset
  | [], pool, ws, L, k, o, _, _, _, hI, hlt, _, hout => by
    obtain ⟨m, hm, hmb⟩ := hI o
    have hmT : m = T := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 16
      · exact (hmb ⟨i, hi⟩).trans (hout ⟨i, hi⟩)
      · rw [Nat.testBit_eq_false_of_lt (calc m < 2 ^ 16 := hlt m hm
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)),
          Nat.testBit_eq_false_of_lt (calc T < 2 ^ 16 := hT
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))]
    have hTin : T ∈ pool.toFinset := by
      rw [← hmT]
      simpa using hm
    cases k with
    | zero => rw [Build]; exact hTin
    | succ k => rw [Build]; exact Or.inl hTin
  | g :: gs, pool, ws, L, k, o, hg, hk, hL, hI, hlt, h0, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 16, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by have h3 := hout p; rw [List.foldl_cons] at h3; exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hkl : gs.length + 1 ≤ k := by simp only [List.length_cons] at hk; omega
    match k, hkl with
    | 0, hkl => omega
    | k + 1, hkl =>
      have IH := main T hT gs (c :: pool) _ (L + 1) k o hg' (by omega) hL'
        (inv_step pool (c :: pool) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        (fun m hm => by
          rcases List.mem_cons.1 hm with h' | hm
          · rw [h']; exact stepC_lt pool hlt _ hc
          · exact hlt m hm)
        (by simp [h0]) hout'
      rw [List.toFinset_cons] at IH
      rw [Build]
      refine Or.inr ⟨c, ?_, IH⟩
      have h0' : (0 : ℕ) ∈ pool.toFinset := by simpa using h0
      rcases stepC_mem pool c hc with h | h | h | ⟨a, ha, b, hb, h⟩
      · exact Or.inr ⟨0, h0', 0, h0', Or.inr (Or.inr h)⟩
      · exact Or.inl (by rw [h]; exact h0')
      · exact Or.inl (by simpa using h)
      · refine Or.inr ⟨a, by simpa using ha, b, by simpa using hb, ?_⟩
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)

def subs : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: l => subs l ++ (subs l).map (fun s => a :: s)

theorem filter_mem_subs (p : ℕ → Bool) : ∀ l : List ℕ, l.filter p ∈ subs l
  | [] => by simp [subs]
  | a :: l => by
    have ih := filter_mem_subs p l
    simp only [subs, List.mem_append, List.mem_map, List.filter_cons]
    cases hpa : p a
    · left; simpa using ih
    · right; exact ⟨_, ih, by simp⟩

theorem lower (T : ℕ) (hT : T < 65536) (k : ℕ)
    (hr : (subs pool0).all (fun s => !srch T k s) = true) :
    ¬ RepSizeAtMost (fun u v : Fin 4 => T.testBit (4 * u.val + v.val)) k := by
  rintro ⟨C, hC, hs, hrep⟩
  have hb := main T hT C.gates pool0 X 8 k C.output hC hs X_len inv0 (by decide) (by decide)
    (fun p => by
      have h := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
      have he : T.testBit (4 * (p.val / 4) + p.val % 4) = T.testBit p := by
        rw [Nat.div_add_mod p.val 4]
      exact h.trans he)
  obtain ⟨s', hs', hl⟩ := compress T k _ hb
  classical
  have hn : (pool0.filter (fun x => decide (x ∈ s'))).Nodup := List.Nodup.filter _ (by decide)
  have hf : (pool0.filter (fun x => decide (x ∈ s'))).toFinset = s' := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using hs' h, h⟩⟩
  have h1 := srch_complete T hT k _ hn (by rw [hf]; exact hl)
  have h2 := List.all_eq_true.1 hr (pool0.filter (fun x => decide (x ∈ s')))
    (filter_mem_subs _ pool0)
  rw [h1] at h2
  cases h2

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4698 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  refine ⟨⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.or, [9, 6]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [11, 10]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [13, 8]⟩, ⟨GateOp.or, [14, 12]⟩], 15⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem low : (subs pool0).all (fun s => !srch 4698 7 s) = true := by decide +kernel

end PEqualNP.Outside.L_meta_5576

theorem PEqualNP.Outside.L_meta_5576 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4698 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4698 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_5576.upper, PEqualNP.Outside.L_meta_5576.lower 4698 (by norm_num) 7 PEqualNP.Outside.L_meta_5576.low⟩
