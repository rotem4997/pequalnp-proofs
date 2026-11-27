import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6014_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The declarations stepC, Inv, getD_snoc, testBit_65535, gate_vec, inv_step, pool0, X, X_len, inv0
-- are adapted from the checked file lean/PEqualNP/Outside/L_meta_5471.lean of this repository
-- (Apache-2.0). The semantic live-wire normalization and its supporting lemmas
-- below are from Tristan Hornetz, PR #11547, commit 4de8c1b7.

def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp; omega),
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
    exact ⟨c, hcp, fun p => by rw [getD_snoc, ite_eq_left (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, ite_eq_right (by rw [hL p]; exact hi), hmb p]⟩

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
        rw [ite_eq_left hp, Nat.testBit_and, hq]; simp
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

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4702 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  let C : Circuit := ⟨[⟨.or,[0,4]⟩, ⟨.or,[1,5]⟩, ⟨.or,[2,8]⟩, ⟨.or,[3,6]⟩, ⟨.or,[6,10]⟩, ⟨.or,[7,11]⟩, ⟨.and,[8,13]⟩, ⟨.and,[9,12]⟩, ⟨.or,[14,15]⟩], 16⟩
  exact ⟨C, by simp [Monotone2, C], by decide, by decide⟩


open PEqualNP.Represents
-- Explore one gate, leaving verification of its successor to the caller.
def one (ws : List Nat) (P : List Nat → Bool) : Bool :=
  ws == [4702] || (pairs ws).any fun ab =>
    [rem ab.1 ab.2 ws, ins ab.1 (rem ab.1 ab.2 ws), ins ab.2 (rem ab.1 ab.2 ws),
      ins ab.1 (ins ab.2 (rem ab.1 ab.2 ws))].any fun r =>
      [ab.1 &&& ab.2, ab.1 ||| ab.2, 65535].any fun z => !r.contains z && P (z::r)

theorem step_ordered (k : Nat) (ws : List Nat) (hn : ws.Nodup)
    (P : List Nat → Bool) (ih : ∀ w : List Nat, w.Nodup → Live 4702 k w.toFinset → P w = true)
    (a b z : ℕ) (r : Finset ℕ) (hab : (a, b) ∈ pairs ws)
    (hz : z = a &&& b ∨ z = a ||| b ∨ z = 65535) (hzr : z ∉ r)
    (hsh : Shape ws.toFinset a b r) (hl : Live 4702 k (insert z r)) : one ws P = true := by
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

  simp only [one,Bool.or_eq_true,Bool.and_eq_true,List.any_eq_true]
  right
  refine ⟨(a,b),hab,rl,hrl,z,?_,?_⟩
  · rcases hz with hz | hz | hz <;> rw [hz] <;> simp
  · simp [hzl,ih']

theorem step_cover (k : Nat) (ws : List Nat) (hn : ws.Nodup) (h : Live 4702 (k+1) ws.toFinset)
    (P : List Nat → Bool) (ih : ∀ w : List Nat, w.Nodup → Live 4702 k w.toFinset → P w = true) :
    one ws P = true := by
  rw [Live] at h
  rcases h with h | ⟨a, ha, b, hb, z, r, hz, hzr, hsh, hl⟩
  · simp [one, single _ _ hn h]
  · rcases pairs_mem ws a b (by simpa using ha) (by simpa using hb) with hab | hab
    · exact step_ordered k ws hn P ih a b z r hab hz hzr hsh hl
    · refine step_ordered k ws hn P ih b a z r hab ?_ hzr ?_ hl

      · rcases hz with h|h|h
        · exact Or.inl (h.trans (Nat.and_comm _ _))
        · exact Or.inr (Or.inl (h.trans (Nat.or_comm _ _)))
        · exact Or.inr (Or.inr h)
      · exact shape_symm _ _ _ _ hsh

-- Sort by insertion so the kernel can compute the canonical wire sets directly.
private def place (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: place a bs

private theorem mem_place (a z : Nat) (ws : List Nat) : z ∈ place a ws ↔ z = a ∨ z ∈ ws := by
  induction ws with
  | nil => simp [place]
  | cons b bs ih => by_cases h : a ≤ b <;> simp [place,h,ih,or_left_comm]

private def canonical (ws : List Nat) := ws.foldr place []
private theorem canon_fin (ws : List Nat) : (canonical ws).toFinset = ws.toFinset := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    ext x
    change x ∈ (place a (canonical ws)).toFinset ↔ _
    simp only [List.mem_toFinset,mem_place,List.mem_cons]
    apply or_congr_right
    simpa only [List.mem_toFinset] using (Finset.ext_iff.mp ih x)

private def lookup (table : List (List Nat)) (w : List Nat) := table.contains (canonical w)
private def viable (k : Nat) (ws : List Nat) := decide (ws.length ≤ k+1) && sepB 4702 ws

private theorem viable_of (k : Nat) (ws : List Nat) (hn : ws.Nodup) (hl : Live 4702 k ws.toFinset) :
    viable k ws = true := by
  have card := live_card _ k _ hl
  rw [List.toFinset_card_of_nodup hn] at card
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true card,sepB_of _ (by decide) _ (live_sep _ _ _ hl)⟩

def closes (k : Nat) (next : List (List Nat)) (ws : List Nat) :=
  !one ws (fun w => viable k w && !lookup next w)

theorem close_of (k : Nat) (next : List (List Nat)) (ws : List Nat) (hn : ws.Nodup)
    (h : closes k next ws = true) (rest : ∀ t ∈ next, ¬Live 4702 k t.toFinset) :
    ¬Live 4702 (k+1) ws.toFinset := by
  intro live
  have yes := step_cover k ws hn live (fun w => viable k w && !lookup next w) (fun w nod good => by
    have absent : canonical w ∉ next := fun hit => rest _ hit (canon_fin w ▸ good)
    simp [lookup,viable_of k w nod good,absent])
  simp [closes,yes] at h

-- Each level lists the viable wire sets reached with that many gates remaining.
-- A live derivation cannot enter an unlisted state: every gate transition is
-- checked against the next level, including constant gates and repeated pins.
private def S2 : List (List Nat) := []
private theorem bad2 : ∀ w ∈ S2, ¬Live 4702 2 w.toFinset := by simp [S2]
private def s3_0 : List (List Nat) := [[15,4624,17476,43770],[240,4895,17476,64170],[240,4895,43690,62532],[3840,4383,8946,21580],[3840,4383,13050,17476],[4383,4610,17476,35064],[4383,8946,17988,63624],[4383,8946,20292,64716],[4383,17988,43770,61440],[4895,8946,17476,63624],[4895,17476,35064,61986],[4895,17476,43770,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good3_0 : (s3_0.all (fun w => decide w.Nodup && closes 2 S2 w)) = true := by decide +kernel
private def S3 := s3_0
private theorem bad3 (w : List Nat) (h : w ∈ S3) : ¬ Live 4702 3 w.toFinset := by
  have cert : S3.all (fun w => decide w.Nodup && closes 2 S2 w) = true := by
    exact good3_0
  have row := List.all_eq_true.mp cert w h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at row
  exact close_of 2 S2 w row.1 row.2 bad2
private def s4_0 : List (List Nat) := [[15,240,4881,17476,64170],[15,240,4881,43690,62532],[15,240,7953,17476,61994],[15,240,7953,17484,61986],[15,248,7953,17476,61986],[15,4112,8946,20292,34952],[15,4369,8946,17988,63624],[15,4369,8946,20292,39048],[15,4369,8946,20292,61448],[15,4369,8946,20292,63624],[15,4369,8946,20292,63736],[15,4369,8946,20292,64170]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_0 : (s4_0.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_1 : List (List Nat) := [[15,4369,8946,20292,64250],[15,4369,8946,20292,64716],[15,4369,8946,20300,61440],[15,4369,8954,20292,61440],[15,4369,13042,20292,34952],[15,4369,17988,43770,61440],[15,4369,20292,43770,62194],[15,4383,8946,20292,63624],[15,4624,8946,17476,34952],[15,4881,8946,17476,63624],[15,4881,17476,35064,61986],[15,4881,17476,43770,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_1 : (s4_1.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_2 : List (List Nat) := [[15,7953,8946,17476,61448],[15,7953,8946,17484,61440],[15,7953,8954,17476,61440],[15,7953,13042,17476,34952],[15,7953,17476,35064,62194],[15,7953,17476,43770,62194],[240,512,4383,17476,64170],[240,512,4383,43690,62532],[240,514,4383,17476,63624],[240,514,4383,34952,62532],[240,527,4369,17476,64170],[240,527,4369,43690,62532]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_2 : (s4_2.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_3 : List (List Nat) := [[240,3840,4383,8738,21580],[240,3840,4383,8738,62540],[240,3840,4383,8746,62532],[240,3840,4383,12842,17476],[240,3840,4383,17476,61994],[240,3840,4383,17484,61986],[240,4383,4610,17476,34952],[240,4383,8738,17988,63624],[240,4383,8738,20292,64716],[240,4383,8738,35464,62532],[240,4383,17988,43690,61440],[240,4895,8738,17476,63624]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_3 : (s4_3.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_4 : List (List Nat) := [[240,4895,8738,34952,62532],[240,4895,17476,34952,61986],[240,4895,17476,43690,61440],[248,3840,4383,8738,62532],[248,3840,4383,17476,61986],[512,4383,8946,17476,63624],[512,4383,17476,35064,61986],[512,4383,17476,43770,61440],[514,4383,17476,35064,61440],[527,4369,8946,17476,63624],[527,4369,17476,35064,61986],[527,4369,17476,43770,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_4 : (s4_4.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_5 : List (List Nat) := [[3840,4104,4383,8946,17476],[3840,4344,4383,8738,17476],[3840,4383,8738,17476,39160],[3840,4383,8738,21572,35064],[3840,4383,8946,17476,39048],[3840,4383,8946,17476,61448],[3840,4383,8946,17476,63624],[3840,4383,8946,17476,63736],[3840,4383,8946,17476,64170],[3840,4383,8946,17476,64250],[3840,4383,8946,17476,64716],[3840,4383,8946,17484,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_5 : (s4_5.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_6 : List (List Nat) := [[3840,4383,8946,21572,34952],[3840,4383,8946,35064,62532],[3840,4383,8946,52428,62532],[3840,4383,8954,17476,61440],[3840,4383,12834,17476,35064],[3840,4383,13042,17476,34952],[3840,4383,17476,35064,61986],[3840,4383,17476,35064,62194],[3840,4383,17476,43770,61986],[3840,4383,17476,43770,62194],[3855,4383,8946,17476,63624],[3855,4383,17476,35064,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_6 : (s4_6.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def s4_7 : List (List Nat) := [[4383,7953,8946,17476,63624],[4383,7953,17476,35064,61986],[4383,7967,8946,17476,63624],[4383,7967,17476,35064,61986],[4383,8738,17988,35064,61440],[4383,8738,20292,35064,62532],[4383,8946,17476,20292,63624],[4383,8946,17988,34952,61440],[4383,8946,20292,34952,62532],[4383,8946,20292,52428,61440],[4895,8738,17476,35064,61440],[4895,8946,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good4_7 : (s4_7.all (fun w => decide w.Nodup && closes 3 S3 w)) = true := by decide +kernel
private def S4 := s4_0 ++ s4_1 ++ s4_2 ++ s4_3 ++ s4_4 ++ s4_5 ++ s4_6 ++ s4_7
private theorem bad4 (w : List Nat) (h : w ∈ S4) : ¬ Live 4702 4 w.toFinset := by
  have cert : S4.all (fun w => decide w.Nodup && closes 3 S3 w) = true := by
    simp only [S4,List.all_append,good4_0, good4_1, good4_2, good4_3, good4_4, good4_5, good4_6, good4_7,Bool.and_true]
  have row := List.all_eq_true.mp cert w h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at row
  exact close_of 3 S3 w row.1 row.2 bad3
private def s5_0 : List (List Nat) := [[0,15,4369,8946,20292,63624],[0,3840,4383,8946,17476,63624],[0,3840,4383,17476,35064,61986],[8,15,240,7953,17476,61986],[8,15,4369,8946,20292,61440],[8,15,7953,8946,17476,61440],[8,240,3840,4383,8738,62532],[8,240,3840,4383,17476,61986],[8,3840,4383,8946,17476,61440],[15,240,512,4369,17476,64170],[15,240,512,4369,43690,62532],[15,240,514,4369,17476,63624]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_0 : (s5_0.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_1 : List (List Nat) := [[15,240,514,4369,34952,62532],[15,240,3840,4369,8738,62540],[15,240,3840,4369,8746,62532],[15,240,3840,4369,17476,61994],[15,240,3840,4369,17484,61986],[15,240,3848,4369,8738,62532],[15,240,3848,4369,17476,61986],[15,240,4112,8738,17476,36744],[15,240,4112,8738,20292,34952],[15,240,4369,8738,17988,63624],[15,240,4369,8738,20292,39048],[15,240,4369,8738,20292,61448]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_1 : (s5_1.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_2 : List (List Nat) := [[15,240,4369,8738,20292,63624],[15,240,4369,8738,20292,63736],[15,240,4369,8738,20292,64170],[15,240,4369,8738,20292,64716],[15,240,4369,8738,20300,61440],[15,240,4369,8738,21572,36744],[15,240,4369,8738,35464,62532],[15,240,4369,8738,36744,62532],[15,240,4369,8738,53196,62532],[15,240,4369,8746,20292,61440],[15,240,4369,8946,20292,63624],[15,240,4369,12834,17476,36744]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_2 : (s5_2.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_3 : List (List Nat) := [[15,240,4369,12834,20292,34952],[15,240,4369,17988,43690,61440],[15,240,4369,20292,36744,61986],[15,240,4369,20292,43690,61986],[15,240,4383,8738,20292,63624],[15,240,4383,8738,36744,62532],[15,240,4881,8738,17476,63624],[15,240,4881,8738,34952,62532],[15,240,4881,17476,34952,61986],[15,240,4881,17476,43690,61440],[15,240,7953,8738,17476,61448],[15,240,7953,8738,17484,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_3 : (s5_3.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_4 : List (List Nat) := [[15,240,7953,8738,62532,63624],[15,240,7953,8746,17476,61440],[15,240,7953,12834,17476,34952],[15,240,7953,17476,34952,61986],[15,240,7953,17476,34952,62194],[15,240,7953,17476,35064,61986],[15,240,7953,17476,36744,61986],[15,240,7953,17476,43690,61986],[15,240,7953,17476,52428,61986],[15,240,7953,17476,61986,63624],[15,240,7953,17476,61986,64170],[15,240,7953,20292,34952,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_4 : (s5_4.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_5 : List (List Nat) := [[15,240,7953,34952,61986,62532],[15,240,7967,17476,34952,61986],[15,248,3840,4369,8738,62532],[15,248,3840,4369,17476,61986],[15,248,4369,8738,20292,61440],[15,248,7953,8738,17476,61440],[15,512,4369,8946,17476,63624],[15,512,4369,17476,35064,61986],[15,512,4369,17476,43770,61440],[15,514,4369,17476,35064,61440],[15,3840,4112,8738,17476,35064],[15,3840,4112,8946,17476,34952]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_5 : (s5_5.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_6 : List (List Nat) := [[15,3840,4369,8738,17476,39160],[15,3840,4369,8738,21572,35064],[15,3840,4369,8946,17476,39048],[15,3840,4369,8946,17476,61448],[15,3840,4369,8946,17476,63624],[15,3840,4369,8946,17476,63736],[15,3840,4369,8946,17476,64170],[15,3840,4369,8946,17476,64250],[15,3840,4369,8946,17476,64716],[15,3840,4369,8946,17484,61440],[15,3840,4369,8946,20292,63624],[15,3840,4369,8946,21572,34952]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_6 : (s5_6.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_7 : List (List Nat) := [[15,3840,4369,8946,35064,62532],[15,3840,4369,8946,52428,62532],[15,3840,4369,8954,17476,61440],[15,3840,4369,12834,17476,35064],[15,3840,4369,13042,17476,34952],[15,3840,4369,17476,35064,61986],[15,3840,4369,17476,35064,62194],[15,3840,4369,17476,43770,61986],[15,3840,4369,17476,43770,62194],[15,3840,4383,8946,17476,63624],[15,3840,4383,17476,35064,61986],[15,3848,4369,8946,17476,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_7 : (s5_7.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_8 : List (List Nat) := [[15,3855,4369,8946,17476,63624],[15,3855,4369,17476,35064,61986],[15,4096,4369,8946,20292,34952],[15,4096,7953,8946,17476,34952],[15,4336,4369,8738,17476,36744],[15,4336,4369,8738,20292,34952],[15,4336,7953,8738,17476,34952],[15,4369,7953,8946,17476,63624],[15,4369,7953,17476,35064,61986],[15,4369,8738,8946,20292,63624],[15,4369,8738,17988,35064,61440],[15,4369,8738,20292,35064,61680]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_8 : (s5_8.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_9 : List (List Nat) := [[15,4369,8738,20292,35064,62532],[15,4369,8946,17476,20292,63624],[15,4369,8946,17476,36744,61986],[15,4369,8946,17988,34952,61440],[15,4369,8946,20292,34952,61440],[15,4369,8946,20292,34952,61680],[15,4369,8946,20292,34952,61986],[15,4369,8946,20292,34952,62194],[15,4369,8946,20292,34952,62532],[15,4369,8946,20292,34952,63624],[15,4369,8946,20292,35064,61440],[15,4369,8946,20292,36744,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_9 : (s5_9.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_10 : List (List Nat) := [[15,4369,8946,20292,43690,61440],[15,4369,8946,20292,43770,61440],[15,4369,8946,20292,52428,61440],[15,4369,8946,20292,53196,61440],[15,4369,8946,20292,61440,63624],[15,4369,8946,20292,63624],[15,4383,8946,20292,34952,61440],[15,4881,8738,17476,35064,61440],[15,4881,8946,17476,34952,61440],[15,7953,8738,17476,35064,61680],[15,7953,8946,17476,34952,61440],[15,7953,8946,17476,34952,61680]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_10 : (s5_10.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_11 : List (List Nat) := [[15,7953,8946,17476,34952,61986],[15,7953,8946,17476,34952,62194],[15,7953,8946,17476,35064,61440],[15,7953,8946,17476,36744,61440],[15,7953,8946,17476,43690,61440],[15,7953,8946,17476,43770,61440],[15,7953,8946,17476,52428,61440],[15,7953,8946,17476,61440,63624],[15,7953,8946,20292,34952,61440],[15,7967,8946,17476,34952,61440],[240,512,4383,8738,17476,63624],[240,512,4383,8738,34952,62532]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_11 : (s5_11.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_12 : List (List Nat) := [[240,512,4383,17476,34952,61986],[240,512,4383,17476,43690,61440],[240,514,4383,17476,34952,61440],[240,527,4369,8738,17476,63624],[240,527,4369,8738,34952,62532],[240,527,4369,17476,34952,61986],[240,527,4369,17476,43690,61440],[240,3840,4104,4383,8738,17476],[240,3840,4383,8738,17476,39048],[240,3840,4383,8738,17476,61448],[240,3840,4383,8738,17476,63624],[240,3840,4383,8738,17476,63736]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_12 : (s5_12.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_13 : List (List Nat) := [[240,3840,4383,8738,17476,64170],[240,3840,4383,8738,17476,64716],[240,3840,4383,8738,17484,61440],[240,3840,4383,8738,21572,34952],[240,3840,4383,8738,34952,62532],[240,3840,4383,8738,35064,62532],[240,3840,4383,8738,43690,62532],[240,3840,4383,8738,52428,62532],[240,3840,4383,8738,62532,63624],[240,3840,4383,8738,62532,64716],[240,3840,4383,8746,17476,61440],[240,3840,4383,8946,17476,63624]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_13 : (s5_13.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_14 : List (List Nat) := [[240,3840,4383,8946,34952,62532],[240,3840,4383,12834,17476,34952],[240,3840,4383,17476,34952,61986],[240,3840,4383,17476,34952,62194],[240,3840,4383,17476,35064,61986],[240,3840,4383,17476,43690,61986],[240,3840,4383,17476,52428,61986],[240,3840,4383,17476,61986,63624],[240,3840,4383,17476,61986,64170],[240,3840,4383,34952,61986,62532],[240,3855,4383,8738,17476,63624],[240,3855,4383,8738,34952,62532]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_14 : (s5_14.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_15 : List (List Nat) := [[240,3855,4383,17476,34952,61986],[240,4383,7953,8738,17476,63624],[240,4383,7953,8738,34952,62532],[240,4383,7953,17476,34952,61986],[240,4383,7967,8738,17476,63624],[240,4383,7967,8738,34952,62532],[240,4383,7967,17476,34952,61986],[240,4383,8738,17476,20292,63624],[240,4383,8738,17476,35464,61440],[240,4383,8738,17476,36744,63624],[240,4383,8738,17988,34952,61440],[240,4383,8738,20292,34952,62532]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_15 : (s5_15.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_16 : List (List Nat) := [[240,4383,8738,20292,52428,61440],[240,4383,8738,34952,36744,62532],[240,4895,8738,17476,34952,61440],[248,3840,4383,8738,17476,61440],[512,4383,8738,17476,35064,61440],[512,4383,8946,17476,34952,61440],[527,4369,8738,17476,35064,61440],[527,4369,8946,17476,34952,61440],[3840,4096,4383,8738,17476,35064],[3840,4096,4383,8946,17476,34952],[3840,4336,4383,8738,17476,34952],[3840,4369,4383,8946,17476,63624]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_16 : (s5_16.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_17 : List (List Nat) := [[3840,4369,4383,17476,35064,61986],[3840,4383,8738,8946,17476,63624],[3840,4383,8738,17476,35064,61440],[3840,4383,8738,17476,35064,61680],[3840,4383,8738,17476,35064,61986],[3840,4383,8738,17476,35064,62532],[3840,4383,8738,17476,35064,63624],[3840,4383,8738,17476,35064,63736],[3840,4383,8738,17476,43770,61440],[3840,4383,8946,17476,34952,61440],[3840,4383,8946,17476,34952,61680],[3840,4383,8946,17476,34952,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_17 : (s5_17.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_18 : List (List Nat) := [[3840,4383,8946,17476,34952,62194],[3840,4383,8946,17476,34952,62532],[3840,4383,8946,17476,34952,63624],[3840,4383,8946,17476,35064,61440],[3840,4383,8946,17476,43690,61440],[3840,4383,8946,17476,43770,61440],[3840,4383,8946,17476,52428,61440],[3840,4383,8946,17476,61440,63624],[3840,4383,8946,17476,63624],[3840,4383,17476,34952,35064,61986],[3840,4383,17476,35064,61440,61986],[3840,4383,17476,35064,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_18 : (s5_18.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def s5_19 : List (List Nat) := [[3855,4383,8738,17476,35064,61440],[3855,4383,8946,17476,34952,61440],[4383,7953,8738,17476,35064,61440],[4383,7953,8946,17476,34952,61440],[4383,7967,8738,17476,35064,61440],[4383,7967,8946,17476,34952,61440],[4383,8738,17476,20292,35064,61440],[4383,8738,17476,35064,36744,61440],[4383,8946,17476,20292,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good5_19 : (s5_19.all (fun w => decide w.Nodup && closes 4 S4 w)) = true := by decide +kernel
private def S5 := s5_0 ++ s5_1 ++ s5_2 ++ s5_3 ++ s5_4 ++ s5_5 ++ s5_6 ++ s5_7 ++ s5_8 ++ s5_9 ++ s5_10 ++ s5_11 ++ s5_12 ++ s5_13 ++ s5_14 ++ s5_15 ++ s5_16 ++ s5_17 ++ s5_18 ++ s5_19
private theorem bad5 (w : List Nat) (h : w ∈ S5) : ¬ Live 4702 5 w.toFinset := by
  have cert : S5.all (fun w => decide w.Nodup && closes 4 S4 w) = true := by
    simp only [S5,List.all_append,good5_0, good5_1, good5_2, good5_3, good5_4, good5_5, good5_6, good5_7, good5_8, good5_9, good5_10, good5_11, good5_12, good5_13, good5_14, good5_15, good5_16, good5_17, good5_18, good5_19,Bool.and_true]
  have row := List.all_eq_true.mp cert w h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at row
  exact close_of 4 S4 w row.1 row.2 bad4
private def s6_0 : List (List Nat) := [[0,15,240,4369,8738,20292,63624],[0,15,240,4369,8738,36744,62532],[0,15,240,7953,17476,34952,61986],[0,15,3840,4369,8946,17476,63624],[0,15,3840,4369,17476,35064,61986],[0,15,4369,8946,20292,34952,61440],[0,15,7953,8946,17476,34952,61440],[0,240,3840,4383,8738,17476,63624],[0,240,3840,4383,8738,34952,62532],[0,240,3840,4383,17476,34952,61986],[0,3840,4383,8738,17476,35064,61440],[0,3840,4383,8946,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_0 : (s6_0.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_1 : List (List Nat) := [[8,15,240,3840,4369,8738,62532],[8,15,240,3840,4369,17476,61986],[8,15,240,4369,8738,20292,61440],[8,15,240,7953,8738,17476,61440],[8,15,3840,4369,8946,17476,61440],[8,240,3840,4383,8738,17476,61440],[15,240,512,4369,8738,17476,63624],[15,240,512,4369,8738,34952,62532],[15,240,512,4369,17476,34952,61986],[15,240,512,4369,17476,43690,61440],[15,240,514,4369,17476,34952,61440],[15,240,3840,4112,8738,17476,34952]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_1 : (s6_1.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_2 : List (List Nat) := [[15,240,3840,4369,8738,17476,39048],[15,240,3840,4369,8738,17476,61448],[15,240,3840,4369,8738,17476,63624],[15,240,3840,4369,8738,17476,63736],[15,240,3840,4369,8738,17476,64170],[15,240,3840,4369,8738,17476,64716],[15,240,3840,4369,8738,17484,61440],[15,240,3840,4369,8738,20292,63624],[15,240,3840,4369,8738,21572,34952],[15,240,3840,4369,8738,34952,62532],[15,240,3840,4369,8738,35064,62532],[15,240,3840,4369,8738,36744,62532]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_2 : (s6_2.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_3 : List (List Nat) := [[15,240,3840,4369,8738,43690,62532],[15,240,3840,4369,8738,52428,62532],[15,240,3840,4369,8738,62532,63624],[15,240,3840,4369,8738,62532,64716],[15,240,3840,4369,8746,17476,61440],[15,240,3840,4369,8946,17476,63624],[15,240,3840,4369,8946,34952,62532],[15,240,3840,4369,12834,17476,34952],[15,240,3840,4369,17476,34952,61986],[15,240,3840,4369,17476,34952,62194],[15,240,3840,4369,17476,35064,61986],[15,240,3840,4369,17476,36744,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_3 : (s6_3.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_4 : List (List Nat) := [[15,240,3840,4369,17476,43690,61986],[15,240,3840,4369,17476,52428,61986],[15,240,3840,4369,17476,61986,63624],[15,240,3840,4369,17476,61986,64170],[15,240,3840,4369,20292,34952,61986],[15,240,3840,4369,34952,61986,62532],[15,240,3840,4383,8738,17476,63624],[15,240,3840,4383,8738,34952,62532],[15,240,3840,4383,17476,34952,61986],[15,240,3840,7953,17476,34952,61986],[15,240,3848,4369,8738,17476,61440],[15,240,3855,4369,8738,17476,63624]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_4 : (s6_4.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_5 : List (List Nat) := [[15,240,3855,4369,8738,34952,62532],[15,240,3855,4369,17476,34952,61986],[15,240,4096,4369,8738,17476,36744],[15,240,4096,4369,8738,20292,34952],[15,240,4096,7953,8738,17476,34952],[15,240,4369,7953,8738,17476,63624],[15,240,4369,7953,8738,34952,62532],[15,240,4369,7953,17476,34952,61986],[15,240,4369,8738,17476,20292,63624],[15,240,4369,8738,17476,35464,61440],[15,240,4369,8738,17476,36744,61440],[15,240,4369,8738,17476,36744,61680]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_5 : (s6_5.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_6 : List (List Nat) := [[15,240,4369,8738,17476,36744,61986],[15,240,4369,8738,17476,36744,62532],[15,240,4369,8738,17476,36744,63624],[15,240,4369,8738,17476,53196,61440],[15,240,4369,8738,17988,34952,61440],[15,240,4369,8738,20292,34952,61440],[15,240,4369,8738,20292,34952,61680],[15,240,4369,8738,20292,34952,61986],[15,240,4369,8738,20292,34952,62532],[15,240,4369,8738,20292,34952,63624],[15,240,4369,8738,20292,35064,61440],[15,240,4369,8738,20292,36744,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_6 : (s6_6.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_7 : List (List Nat) := [[15,240,4369,8738,20292,43690,61440],[15,240,4369,8738,20292,52428,61440],[15,240,4369,8738,20292,53196,61440],[15,240,4369,8738,20292,61440,63624],[15,240,4369,8738,20292,63624],[15,240,4369,8738,34952,36744,62532],[15,240,4369,8738,36744,61440,62532],[15,240,4369,8738,36744,62532],[15,240,4369,8946,20292,34952,61440],[15,240,4383,8738,17476,36744,61440],[15,240,4383,8738,20292,34952,61440],[15,240,4881,8738,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_7 : (s6_7.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_8 : List (List Nat) := [[15,240,7953,8738,17476,34952,61440],[15,240,7953,8738,17476,34952,61680],[15,240,7953,8738,17476,34952,61986],[15,240,7953,8738,17476,35064,61440],[15,240,7953,8738,17476,36744,61440],[15,240,7953,8738,17476,43690,61440],[15,240,7953,8738,17476,52428,61440],[15,240,7953,8738,17476,61440,63624],[15,240,7953,8738,20292,34952,61440],[15,240,7953,8738,34952,61440,62532],[15,240,7953,8946,17476,34952,61440],[15,240,7953,17476,34952,61440,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_8 : (s6_8.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_9 : List (List Nat) := [[15,240,7953,17476,34952,61986],[15,240,7967,8738,17476,34952,61440],[15,248,3840,4369,8738,17476,61440],[15,512,4369,8738,17476,35064,61440],[15,512,4369,8946,17476,34952,61440],[15,3840,4096,4369,8738,17476,35064],[15,3840,4096,4369,8946,17476,34952],[15,3840,4336,4369,8738,17476,34952],[15,3840,4369,8738,8946,17476,63624],[15,3840,4369,8738,17476,35064,61440],[15,3840,4369,8738,17476,35064,61680],[15,3840,4369,8738,17476,35064,61986]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_9 : (s6_9.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_10 : List (List Nat) := [[15,3840,4369,8738,17476,35064,62532],[15,3840,4369,8738,17476,35064,63624],[15,3840,4369,8738,17476,35064,63736],[15,3840,4369,8738,17476,43770,61440],[15,3840,4369,8946,17476,34952,61440],[15,3840,4369,8946,17476,34952,61680],[15,3840,4369,8946,17476,34952,61986],[15,3840,4369,8946,17476,34952,62194],[15,3840,4369,8946,17476,34952,62532],[15,3840,4369,8946,17476,34952,63624],[15,3840,4369,8946,17476,35064,61440],[15,3840,4369,8946,17476,36744,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_10 : (s6_10.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_11 : List (List Nat) := [[15,3840,4369,8946,17476,43690,61440],[15,3840,4369,8946,17476,43770,61440],[15,3840,4369,8946,17476,52428,61440],[15,3840,4369,8946,17476,61440,63624],[15,3840,4369,8946,17476,63624],[15,3840,4369,8946,20292,34952,61440],[15,3840,4369,17476,34952,35064,61986],[15,3840,4369,17476,35064,61440,61986],[15,3840,4369,17476,35064,61986],[15,3840,4383,8738,17476,35064,61440],[15,3840,4383,8946,17476,34952,61440],[15,3840,7953,8946,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_11 : (s6_11.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_12 : List (List Nat) := [[15,3855,4369,8738,17476,35064,61440],[15,3855,4369,8946,17476,34952,61440],[15,4369,7953,8738,17476,35064,61440],[15,4369,7953,8946,17476,34952,61440],[15,4369,8738,8946,17476,36744,61440],[15,4369,8738,8946,20292,34952,61440],[15,4369,8738,17476,20292,35064,61440],[15,4369,8738,17476,35064,36744,61440],[15,4369,8946,17476,20292,34952,61440],[15,4369,8946,20292,34952,61440],[15,7953,8738,8946,17476,34952,61440],[15,7953,8946,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_12 : (s6_12.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_13 : List (List Nat) := [[240,512,4383,8738,17476,34952,61440],[240,527,4369,8738,17476,34952,61440],[240,3840,4096,4383,8738,17476,34952],[240,3840,4369,4383,8738,17476,63624],[240,3840,4369,4383,8738,34952,62532],[240,3840,4369,4383,17476,34952,61986],[240,3840,4383,8738,17476,34952,61440],[240,3840,4383,8738,17476,34952,61680],[240,3840,4383,8738,17476,34952,61986],[240,3840,4383,8738,17476,34952,62532],[240,3840,4383,8738,17476,34952,63624],[240,3840,4383,8738,17476,35064,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_13 : (s6_13.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_14 : List (List Nat) := [[240,3840,4383,8738,17476,43690,61440],[240,3840,4383,8738,17476,52428,61440],[240,3840,4383,8738,17476,61440,63624],[240,3840,4383,8738,17476,63624],[240,3840,4383,8738,34952,61440,62532],[240,3840,4383,8738,34952,62532],[240,3840,4383,8946,17476,34952,61440],[240,3840,4383,17476,34952,61440,61986],[240,3840,4383,17476,34952,61986],[240,3855,4383,8738,17476,34952,61440],[240,4383,7953,8738,17476,34952,61440],[240,4383,7967,8738,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_14 : (s6_14.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def s6_15 : List (List Nat) := [[240,4383,8738,17476,20292,34952,61440],[240,4383,8738,17476,34952,36744,61440],[3840,4369,4383,8738,17476,35064,61440],[3840,4369,4383,8946,17476,34952,61440],[3840,4383,8738,8946,17476,34952,61440],[3840,4383,8738,17476,34952,35064,61440],[3840,4383,8738,17476,35064,61440],[3840,4383,8946,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good6_15 : (s6_15.all (fun w => decide w.Nodup && closes 5 S5 w)) = true := by decide +kernel
private def S6 := s6_0 ++ s6_1 ++ s6_2 ++ s6_3 ++ s6_4 ++ s6_5 ++ s6_6 ++ s6_7 ++ s6_8 ++ s6_9 ++ s6_10 ++ s6_11 ++ s6_12 ++ s6_13 ++ s6_14 ++ s6_15
private theorem bad6 (w : List Nat) (h : w ∈ S6) : ¬ Live 4702 6 w.toFinset := by
  have cert : S6.all (fun w => decide w.Nodup && closes 5 S5 w) = true := by
    simp only [S6,List.all_append,good6_0, good6_1, good6_2, good6_3, good6_4, good6_5, good6_6, good6_7, good6_8, good6_9, good6_10, good6_11, good6_12, good6_13, good6_14, good6_15,Bool.and_true]
  have row := List.all_eq_true.mp cert w h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at row
  exact close_of 5 S5 w row.1 row.2 bad5
private def s7_0 : List (List Nat) := [[0,15,240,3840,4369,8738,17476,63624],[0,15,240,3840,4369,8738,34952,62532],[0,15,240,3840,4369,17476,34952,61986],[0,15,240,4369,8738,17476,36744,61440],[0,15,240,4369,8738,20292,34952,61440],[0,15,240,7953,8738,17476,34952,61440],[0,15,3840,4369,8738,17476,35064,61440],[0,15,3840,4369,8946,17476,34952,61440],[0,240,3840,4383,8738,17476,34952,61440],[8,15,240,3840,4369,8738,17476,61440],[15,240,512,4369,8738,17476,34952,61440],[15,240,3840,4096,4369,8738,17476,34952]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good7_0 : (s7_0.all (fun w => decide w.Nodup && closes 6 S6 w)) = true := by decide +kernel
private def s7_1 : List (List Nat) := [[15,240,3840,4369,8738,17476,34952,61440],[15,240,3840,4369,8738,17476,34952,61680],[15,240,3840,4369,8738,17476,34952,61986],[15,240,3840,4369,8738,17476,34952,62532],[15,240,3840,4369,8738,17476,34952,63624],[15,240,3840,4369,8738,17476,35064,61440],[15,240,3840,4369,8738,17476,36744,61440],[15,240,3840,4369,8738,17476,43690,61440],[15,240,3840,4369,8738,17476,52428,61440],[15,240,3840,4369,8738,17476,61440,63624],[15,240,3840,4369,8738,17476,63624],[15,240,3840,4369,8738,20292,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good7_1 : (s7_1.all (fun w => decide w.Nodup && closes 6 S6 w)) = true := by decide +kernel
private def s7_2 : List (List Nat) := [[15,240,3840,4369,8738,34952,61440,62532],[15,240,3840,4369,8738,34952,62532],[15,240,3840,4369,8946,17476,34952,61440],[15,240,3840,4369,17476,34952,61440,61986],[15,240,3840,4369,17476,34952,61986],[15,240,3840,4383,8738,17476,34952,61440],[15,240,3840,7953,8738,17476,34952,61440],[15,240,3855,4369,8738,17476,34952,61440],[15,240,4369,7953,8738,17476,34952,61440],[15,240,4369,8738,17476,20292,34952,61440],[15,240,4369,8738,17476,34952,36744,61440],[15,240,4369,8738,17476,36744,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good7_2 : (s7_2.all (fun w => decide w.Nodup && closes 6 S6 w)) = true := by decide +kernel
private def s7_3 : List (List Nat) := [[15,240,4369,8738,20292,34952,61440],[15,240,7953,8738,17476,34952,61440],[15,3840,4369,8738,8946,17476,34952,61440],[15,3840,4369,8738,17476,34952,35064,61440],[15,3840,4369,8738,17476,35064,61440],[15,3840,4369,8946,17476,34952,61440],[240,3840,4369,4383,8738,17476,34952,61440],[240,3840,4383,8738,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good7_3 : (s7_3.all (fun w => decide w.Nodup && closes 6 S6 w)) = true := by decide +kernel
private def S7 := s7_0 ++ s7_1 ++ s7_2 ++ s7_3
private theorem bad7 (w : List Nat) (h : w ∈ S7) : ¬ Live 4702 7 w.toFinset := by
  have cert : S7.all (fun w => decide w.Nodup && closes 6 S6 w) = true := by
    simp only [S7,List.all_append,good7_0, good7_1, good7_2, good7_3,Bool.and_true]
  have row := List.all_eq_true.mp cert w h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at row
  exact close_of 6 S6 w row.1 row.2 bad6
private def s8_0 : List (List Nat) := [[0,15,240,3840,4369,8738,17476,34952,61440],[15,240,3840,4369,8738,17476,34952,61440]]
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem good8_0 : (s8_0.all (fun w => decide w.Nodup && closes 7 S7 w)) = true := by decide +kernel
private def S8 := s8_0
private theorem bad8 (w : List Nat) (h : w ∈ S8) : ¬ Live 4702 8 w.toFinset := by
  have cert : S8.all (fun w => decide w.Nodup && closes 7 S7 w) = true := by
    exact good8_0
  have row := List.all_eq_true.mp cert w h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at row
  exact close_of 7 S7 w row.1 row.2 bad7

private theorem first_checked : (subs pool0).all (fun w => !viable 8 w || lookup S8 w) = true := by decide +kernel

theorem lower6014 : ¬RepSizeAtMost (fun u v : Fin 4 => (4702 : Nat).testBit (4*u.val+v.val)) 8 := by
  rintro ⟨C,hC,hs,hrep⟩
  have hb := main 4702 (by decide) C.gates pool0 X 8 8 C.output hC hs X_len inv0 (by decide) (by decide)
    (fun p => by
      have h := hrep ⟨p.val / 4,by omega⟩ ⟨p.val % 4,by omega⟩
      simpa only [X, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, Nat.div_add_mod] using h)
  obtain ⟨s', hs', hl⟩ := compress 4702 8 _ hb
  classical
  have hn : (pool0.filter (fun x => decide (x ∈ s'))).Nodup := List.Nodup.filter _ (by decide)
  have hf : (pool0.filter (fun x => decide (x ∈ s'))).toFinset = s' := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using hs' h, h⟩⟩

  let w := pool0.filter (fun x => decide (x ∈ s'))
  have live : Live 4702 8 w.toFinset := hf ▸ hl
  have covered := List.all_eq_true.mp first_checked w (filter_mem_subs _ pool0)
  have hit : canonical w ∈ S8 := by simpa [viable_of 8 w hn live, lookup] using covered
  exact bad8 _ hit (canon_fin w ▸ live)



end PEqualNP.Outside.L_meta_6014_aux

open PEqualNP.Outside.L_meta_6014_aux

theorem PEqualNP.Outside.L_meta_6014 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4702 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4702 : ℕ).testBit (4 * u.val + v.val)) 8 := ⟨upper, lower6014⟩
