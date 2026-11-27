import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5982
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

-- A wire z may be added to the set s of available wires at the cost of one gate
-- (the constant 65535 included).
def Ok1 (s : Finset ℕ) (z : ℕ) : Prop :=
  z ∈ s ∨ z = 65535 ∨ ∃ a ∈ s, ∃ b ∈ s, z = a &&& b ∨ z = a ||| b

def Build1 (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => T ∈ s
  | k + 1, s => T ∈ s ∨ ∃ z, Ok1 s z ∧ Build1 T k (insert z s)

-- The same without the constant.
def Ok (s : Finset ℕ) (z : ℕ) : Prop :=
  z ∈ s ∨ ∃ a ∈ s, ∃ b ∈ s, z = a &&& b ∨ z = a ||| b

-- T is obtained from the available wires s with at most k gates.
def Build (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => T ∈ s
  | k + 1, s => T ∈ s ∨ ∃ z, Ok s z ∧ Build T k (insert z s)

theorem build_mono (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Build T k s → Build T (k + 1) s
  | 0, s, h => by
    simp only [Build] at h ⊢
    exact Or.inl h
  | k + 1, s, h => by
    rw [Build] at h
    rw [Build]
    rcases h with h | ⟨z, hz, hb⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, hz, build_mono T k _ hb⟩

theorem tb_full (q : ℕ) (hq : q < 16) : (65535 : ℕ).testBit q = true := by
  interval_cases q <;> rfl

theorem tb_high (b q : ℕ) (hb : b < 65536) (hq : ¬ q < 16) : b.testBit q = false :=
  Nat.testBit_eq_false_of_lt
    (calc b < 2 ^ 16 := hb
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega))

theorem top_and (b : ℕ) (hb : b < 65536) : 65535 &&& b = b := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_and]
  by_cases hq : q < 16
  · rw [tb_full q hq]; simp
  · rw [tb_high b q hb hq]; simp

theorem top_or (b : ℕ) (hb : b < 65536) : 65535 ||| b = 65535 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_or]
  by_cases hq : q < 16
  · rw [tb_full q hq]; simp
  · rw [tb_high b q hb hq, tb_high 65535 q (by norm_num) hq]; simp

-- Every wire of s is the constant or a wire of s'.
def Sim (s s' : Finset ℕ) : Prop := ∀ z ∈ s, z < 65536 ∧ (z = 65535 ∨ z ∈ s')

theorem sim_same (s s' : Finset ℕ) (h : Sim s s') (z : ℕ) (hz : z < 65536)
    (hz' : z = 65535 ∨ z ∈ s') : Sim (insert z s) s' := by
  intro x hx
  rcases Finset.mem_insert.1 hx with h' | h'
  · rw [h']; exact ⟨hz, hz'⟩
  · exact h x h'

theorem notop (T : ℕ) (hT : T ≠ 65535) : ∀ (k : ℕ) (s s' : Finset ℕ), Sim s s' →
    Build1 T k s → Build T k s'
  | 0, s, s', hs, h => by
    simp only [Build1] at h
    simp only [Build]
    rcases (hs T h).2 with h' | h'
    · exact absurd h' hT
    · exact h'
  | k + 1, s, s', hs, h => by
    rw [Build1] at h
    rcases h with h | ⟨z, hz, hb⟩
    · rw [Build]
      rcases (hs T h).2 with h' | h'
      · exact absurd h' hT
      · exact Or.inl h'
    · have same : z < 65536 → (z = 65535 ∨ z ∈ s') → Build T (k + 1) s' := fun h1 h2 =>
        build_mono T k s' (notop T hT k _ s' (sim_same s s' hs z h1 h2) hb)
      rcases hz with hz | hz | ⟨a, ha, b, hb', hz⟩
      · exact same (hs z hz).1 (hs z hz).2
      · exact same (by omega) (Or.inl hz)
      · obtain ⟨ha1, ha2⟩ := hs a ha
        obtain ⟨hb1, hb2⟩ := hs b hb'
        have hzlt : z < 65536 := by
          rcases hz with hz | hz
          · rw [hz]; exact lt_of_le_of_lt Nat.and_le_left ha1
          · rw [hz]; exact Nat.or_lt_two_pow (n := 16) ha1 hb1
        rcases ha2 with ha2 | ha2
        · rcases hz with hz | hz
          · rw [ha2, top_and b hb1] at hz
            exact same hzlt (by rw [hz]; exact hb2)
          · rw [ha2, top_or b hb1] at hz
            exact same hzlt (Or.inl hz)
        · rcases hb2 with hb2 | hb2
          · rcases hz with hz | hz
            · rw [hb2, Nat.land_comm, top_and a ha1] at hz
              exact same hzlt (by rw [hz]; exact Or.inr ha2)
            · rw [hb2, Nat.lor_comm, top_or a ha1] at hz
              exact same hzlt (Or.inl hz)
          · rw [Build]
            refine Or.inr ⟨z, Or.inr ⟨a, ha2, b, hb2, hz⟩, ?_⟩
            refine notop T hT k _ _ ?_ hb
            intro x hx
            rcases Finset.mem_insert.1 hx with h' | h'
            · rw [h']; exact ⟨hzlt, Or.inr (Finset.mem_insert_self z s')⟩
            · exact ⟨(hs x h').1, (hs x h').2.imp id (fun h2 => Finset.mem_insert_of_mem h2)⟩

-- What is left of the live set s after a gate reads a and b: each of them may be kept.
def Shape (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ) : Prop :=
  r = (s.erase a).erase b ∨ r = insert a ((s.erase a).erase b) ∨
    r = insert b ((s.erase a).erase b) ∨ r = insert a (insert b ((s.erase a).erase b))

-- A derivation in which every wire of s is consumed, ending at exactly T.
def Live (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => s = {T}
  | k + 1, s => s = {T} ∨ ∃ a ∈ s, ∃ b ∈ s, ∃ z r, a ≠ b ∧
      (z = a &&& b ∨ z = a ||| b) ∧ z ∉ r ∧ Shape s a b r ∧ Live T k (insert z r)

theorem live_mono (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Live T k s → Live T (k + 1) s
  | 0, s, h => by
    simp only [Live] at h ⊢
    exact Or.inl h
  | k + 1, s, h => by
    rw [Live] at h
    rw [Live]
    rcases h with h | ⟨a, ha, b, hb, z, r, hab, hz, hzr, hsh, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, z, r, hab, hz, hzr, hsh, live_mono T k _ hl⟩

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
          · have hne : a ≠ b := by
              intro hab
              apply hzn
              rcases hzab with h' | h'
              · rw [h', hab, Nat.and_self]; exact hb'
              · rw [h', hab, Nat.or_self]; exact hb'
            rw [Live]
            refine Or.inr ⟨a, by simp, b, by simp, z, r, hne, hzab, hzr, shape_of r a b, ?_⟩
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
    rcases h with h | ⟨a, ha, b, hb, z, r, hab, hz, hzr, hsh, hl⟩
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

theorem live_sep (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Live T k s → Sep T s
  | 0, s, h => by
    simp only [Live] at h
    intro p _ q _ hp hq
    exact ⟨T, by simp [h], hp, hq⟩
  | k + 1, s, h => by
    rw [Live] at h
    rcases h with h | ⟨a, ha, b, hb, z, r, hab, hz, hzr, hsh, hl⟩
    · intro p _ q _ hp hq
      exact ⟨T, by simp [h], hp, hq⟩
    · have ih := live_sep T k _ hl
      intro p hp16 q hq16 hp hq
      obtain ⟨w, hw, hwp, hwq⟩ := ih p hp16 q hq16 hp hq
      rcases Finset.mem_insert.1 hw with hwz | hw
      · rw [hwz] at hwp hwq
        rcases hz with hz | hz <;> rw [hz] at hwp hwq
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
      · exact ⟨w, shape_sub s a b r ha hb hsh w hw, hwp, hwq⟩

def ins (a : ℕ) (l : List ℕ) : List ℕ := if l.contains a then l else a :: l

def rem (a b : ℕ) (l : List ℕ) : List ℕ := l.filter fun x => !(x == a) && !(x == b)

def sepB (T : ℕ) (ws : List ℕ) : Bool :=
  (List.range 16).all fun p => !T.testBit p ||
    (ws.foldl (fun acc w => if w.testBit p then acc &&& w else acc) (65535 ^^^ T) == 0)

def pairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ pairs l

theorem pairs_mem : ∀ (l : List ℕ) (a b : ℕ), a ∈ l → b ∈ l → a ≠ b →
    (a, b) ∈ pairs l ∨ (b, a) ∈ pairs l
  | [], a, b, ha, _, _ => by simp at ha
  | c :: l, a, b, ha, hb, hab => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 ha with ha | ha <;> rcases List.mem_cons.1 hb with hb | hb
    · exact absurd (ha.trans hb.symm) hab
    · left; left; exact ⟨b, hb, ha.symm, rfl⟩
    · right; left; exact ⟨a, ha, hb.symm, rfl⟩
    · rcases pairs_mem l a b ha hb hab with h | h
      · left; right; exact h
      · right; right; exact h

theorem shape_symm (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ) (h : Shape s a b r) :
    Shape s b a r := by
  unfold Shape at h ⊢
  rw [Finset.erase_right_comm]
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (by rw [h]; ext x; simp only [Finset.mem_insert]; tauto)))

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

-- A gate at the live set s: it reads a and b, makes z, and leaves r.
def Mv (s : Finset ℕ) (a b z : ℕ) (r : Finset ℕ) : Prop :=
  a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ (z = a &&& b ∨ z = a ||| b) ∧ z ∉ r ∧ Shape s a b r

-- After the gate (a, b, z), the gate (c, d, y) is allowed next unless the two are
-- unrelated and y is the smaller output (then the other order is taken).
def okP (a b z c d y : ℕ) : Prop :=
  ¬ (y < z ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ z ∧ d ≠ z ∧ y ≠ a ∧ y ≠ b)

def okB (a b z c d y : ℕ) : Bool :=
  !(decide (y < z) && !(c == a) && !(c == b) && !(d == a) && !(d == b) && !(c == z) &&
    !(d == z) && !(y == a) && !(y == b))

theorem okB_iff (a b z c d y : ℕ) : okB a b z c d y = true ↔ okP a b z c d y := by
  simp only [okB, okP, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.not_eq_false', beq_iff_eq, ne_eq]
  tauto

theorem okP_swap1 (a b z c d y : ℕ) (h : okP a b z c d y) : okP b a z c d y := by
  unfold okP at h ⊢
  tauto

theorem okP_swap2 (a b z c d y : ℕ) (h : okP a b z c d y) : okP a b z d c y := by
  unfold okP at h ⊢
  tauto

-- Live derivations in which consecutive gates respect okP; A restricts the first gate.
def LiveO (T : ℕ) : ℕ → Finset ℕ → (ℕ → ℕ → ℕ → Prop) → Prop
  | 0, s, _ => s = {T}
  | k + 1, s, A => s = {T} ∨ ∃ a b z r, Mv s a b z r ∧ A a b z ∧
      LiveO T k (insert z r) (okP a b z)

theorem liveO_live (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ) (A : ℕ → ℕ → ℕ → Prop),
    LiveO T k s A → Live T k s
  | 0, s, A, h => by
    simp only [LiveO] at h
    simp only [Live]
    exact h
  | k + 1, s, A, h => by
    rw [LiveO] at h
    rw [Live]
    rcases h with h | ⟨a, b, z, r, ⟨ha, hb, hab, hz, hzr, hsh⟩, _, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, ha, b, hb, z, r, hab, hz, hzr, hsh, liveO_live T k _ _ hl⟩

theorem shape_spec (s : Finset ℕ) (a b : ℕ) (r : Finset ℕ) (h : Shape s a b r) :
    ∃ ka kb : Prop, ∀ x, x ∈ r ↔ ((x ∈ s ∧ x ≠ a ∧ x ≠ b) ∨ (x = a ∧ ka) ∨ (x = b ∧ kb)) := by
  unfold Shape at h
  rcases h with h | h | h | h
  · exact ⟨False, False, fun x => by rw [h]; simp only [Finset.mem_erase]; tauto⟩
  · exact ⟨True, False, fun x => by
      rw [h]; simp only [Finset.mem_insert, Finset.mem_erase]; tauto⟩
  · exact ⟨False, True, fun x => by
      rw [h]; simp only [Finset.mem_insert, Finset.mem_erase]; tauto⟩
  · exact ⟨True, True, fun x => by
      rw [h]; simp only [Finset.mem_insert, Finset.mem_erase]; tauto⟩

theorem shape_mk (s : Finset ℕ) (a b : ℕ) (ka kb : Prop) :
    ∃ r, Shape s a b r ∧
      ∀ x, x ∈ r ↔ ((x ∈ s ∧ x ≠ a ∧ x ≠ b) ∨ (x = a ∧ ka) ∨ (x = b ∧ kb)) := by
  unfold Shape
  by_cases hka : ka <;> by_cases hkb : kb
  · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), fun x => by
      simp only [Finset.mem_insert, Finset.mem_erase]; tauto⟩
  · exact ⟨_, Or.inr (Or.inl rfl), fun x => by
      simp only [Finset.mem_insert, Finset.mem_erase]; tauto⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), fun x => by
      simp only [Finset.mem_insert, Finset.mem_erase]; tauto⟩
  · exact ⟨_, Or.inl rfl, fun x => by
      simp only [Finset.mem_erase]; tauto⟩

-- Two unrelated consecutive gates may be done in the other order.
theorem swap (s : Finset ℕ) (a b z : ℕ) (r : Finset ℕ) (c d y : ℕ) (r' : Finset ℕ)
    (h1 : Mv s a b z r) (h2 : Mv (insert z r) c d y r')
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcz : c ≠ z) (hdz : d ≠ z)
    (hya : y ≠ a) (hyb : y ≠ b) :
    ∃ q q' : Finset ℕ, Mv s c d y q ∧ Mv (insert y q) a b z q' ∧ insert z q' = insert y r' := by
  obtain ⟨ha, hb, hab, hz, hzr, hsh⟩ := h1
  obtain ⟨hc, hd, hcd, hy, hyr, hsh'⟩ := h2
  obtain ⟨ka, kb, e1⟩ := shape_spec s a b r hsh
  obtain ⟨kc, kd, e2⟩ := shape_spec _ c d r' hsh'
  obtain ⟨q, hq, e3⟩ := shape_mk s c d kc kd
  obtain ⟨q', hq', e4⟩ := shape_mk (insert y q) a b ka kb
  have hcr : c ∈ r := by
    rcases Finset.mem_insert.1 hc with h | h
    · exact absurd h hcz
    · exact h
  have hdr : d ∈ r := by
    rcases Finset.mem_insert.1 hd with h | h
    · exact absurd h hdz
    · exact h
  have hcs : c ∈ s := by
    rcases (e1 c).1 hcr with h | h | h
    · exact h.1
    · exact absurd h.1 hca
    · exact absurd h.1 hcb
  have hds : d ∈ s := by
    rcases (e1 d).1 hdr with h | h | h
    · exact h.1
    · exact absurd h.1 hda
    · exact absurd h.1 hdb
  have e2' : ∀ x, x ∈ r' ↔ (((x = z ∨ x ∈ r) ∧ x ≠ c ∧ x ≠ d) ∨ (x = c ∧ kc) ∨ (x = d ∧ kd)) := by
    intro x
    rw [e2 x, Finset.mem_insert]
  have e4' : ∀ x, x ∈ q' ↔ (((x = y ∨ x ∈ q) ∧ x ≠ a ∧ x ≠ b) ∨ (x = a ∧ ka) ∨ (x = b ∧ kb)) := by
    intro x
    rw [e4 x, Finset.mem_insert]
  have hyz : y ≠ z := by
    intro h
    apply hyr
    rw [e2' y]
    left
    exact ⟨Or.inl h, by rw [h]; exact fun h' => hcz h'.symm, by rw [h]; exact fun h' => hdz h'.symm⟩
  have hyq : y ∉ q := by
    intro h
    apply hyr
    rw [e2' y]
    rcases (e3 y).1 h with h' | h' | h'
    · left
      refine ⟨Or.inr ((e1 y).2 (Or.inl ⟨h'.1, hya, hyb⟩)), h'.2.1, h'.2.2⟩
    · right; left; exact h'
    · right; right; exact h'
  have hzq' : z ∉ q' := by
    intro h
    apply hzr
    rw [e1 z]
    rcases (e4' z).1 h with h' | h' | h'
    · rcases h'.1 with h'' | h''
      · exact absurd h''.symm hyz
      · rcases (e3 z).1 h'' with h3 | h3 | h3
        · left; exact ⟨h3.1, h'.2.1, h'.2.2⟩
        · exact absurd h3.1.symm hcz
        · exact absurd h3.1.symm hdz
    · right; left; exact h'
    · right; right; exact h'
  refine ⟨q, q', ⟨hcs, hds, hcd, hy, hyq, hq⟩,
    ⟨Finset.mem_insert_of_mem ((e3 a).2 (Or.inl ⟨ha, fun h => hca h.symm, fun h => hda h.symm⟩)),
      Finset.mem_insert_of_mem ((e3 b).2 (Or.inl ⟨hb, fun h => hcb h.symm, fun h => hdb h.symm⟩)),
      hab, hz, hzq', hq'⟩, ?_⟩
  ext x
  simp only [Finset.mem_insert]
  constructor
  · rintro (h | h)
    · right
      rw [e2' x]
      left
      exact ⟨Or.inl h, by rw [h]; exact fun h' => hcz h'.symm, by rw [h]; exact fun h' => hdz h'.symm⟩
    · rcases (e4' x).1 h with ⟨h1 | h1, h2, h3⟩ | h1 | h1
      · exact Or.inl h1
      · right
        rw [e2' x]
        rcases (e3 x).1 h1 with h4 | h4 | h4
        · left
          exact ⟨Or.inr ((e1 x).2 (Or.inl ⟨h4.1, h2, h3⟩)), h4.2.1, h4.2.2⟩
        · right; left; exact h4
        · right; right; exact h4
      · right
        rw [e2' x]
        left
        exact ⟨Or.inr ((e1 x).2 (Or.inr (Or.inl h1))), by rw [h1.1]; exact fun h' => hca h'.symm,
          by rw [h1.1]; exact fun h' => hda h'.symm⟩
      · right
        rw [e2' x]
        left
        exact ⟨Or.inr ((e1 x).2 (Or.inr (Or.inr h1))), by rw [h1.1]; exact fun h' => hcb h'.symm,
          by rw [h1.1]; exact fun h' => hdb h'.symm⟩
  · rintro (h | h)
    · right
      rw [e4' x]
      left
      exact ⟨Or.inl h, by rw [h]; exact hya, by rw [h]; exact hyb⟩
    · rcases (e2' x).1 h with ⟨h1 | h1, h2, h3⟩ | h1 | h1
      · exact Or.inl h1
      · right
        rw [e4' x]
        rcases (e1 x).1 h1 with h4 | h4 | h4
        · left
          exact ⟨Or.inr ((e3 x).2 (Or.inl ⟨h4.1, h2, h3⟩)), h4.2.1, h4.2.2⟩
        · right; left; exact h4
        · right; right; exact h4
      · right
        rw [e4' x]
        left
        exact ⟨Or.inr ((e3 x).2 (Or.inr (Or.inl h1))), by rw [h1.1]; exact hca,
          by rw [h1.1]; exact hcb⟩
      · right
        rw [e4' x]
        left
        exact ⟨Or.inr ((e3 x).2 (Or.inr (Or.inr h1))), by rw [h1.1]; exact hda,
          by rw [h1.1]; exact hdb⟩

theorem ins_move (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ) (a b z : ℕ) (r : Finset ℕ)
    (A A' : ℕ → ℕ → ℕ → Prop), Mv s a b z r → A a b z → (∀ c d y, A' c d y → A c d y) →
    LiveO T k (insert z r) A' → LiveO T (k + 1) s A
  | 0, s, a, b, z, r, A, A', hm, hA, _, h => by
    simp only [LiveO] at h
    rw [LiveO]
    refine Or.inr ⟨a, b, z, r, hm, hA, ?_⟩
    simp only [LiveO]
    exact h
  | k + 1, s, a, b, z, r, A, A', hm, hA, hAA, h => by
    rw [LiveO] at h
    rcases h with h | ⟨c, d, y, r', hm', hA', tl⟩
    · rw [LiveO]
      refine Or.inr ⟨a, b, z, r, hm, hA, ?_⟩
      rw [LiveO]
      exact Or.inl h
    · by_cases hok : okP a b z c d y
      · rw [LiveO]
        refine Or.inr ⟨a, b, z, r, hm, hA, ?_⟩
        rw [LiveO]
        exact Or.inr ⟨c, d, y, r', hm', hok, tl⟩
      · unfold okP at hok
        obtain ⟨hyz, hca, hcb, hda, hdb, hcz, hdz, hya, hyb⟩ := not_not.1 hok
        obtain ⟨q, q', m1, m2, e⟩ := swap s a b z r c d y r' hm hm' hca hcb hda hdb hcz hdz hya hyb
        have tl' : LiveO T k (insert z q') (okP c d y) := by rw [e]; exact tl
        have h3 := ins_move T k (insert y q) a b z q' (okP c d y) (okP c d y) m2
          (by unfold okP; intro h'; omega) (fun _ _ _ h' => h') tl'
        rw [LiveO]
        exact Or.inr ⟨c, d, y, q, m1, hAA c d y hA', h3⟩

theorem norm (T : ℕ) : ∀ (k : ℕ) (s : Finset ℕ), Live T k s → LiveO T k s (fun _ _ _ => True)
  | 0, s, h => by
    simp only [Live] at h
    simp only [LiveO]
    exact h
  | k + 1, s, h => by
    rw [Live] at h
    rcases h with h | ⟨a, ha, b, hb, z, r, hab, hz, hzr, hsh, hl⟩
    · rw [LiveO]; exact Or.inl h
    · exact ins_move T k s a b z r _ _ ⟨ha, hb, hab, hz, hzr, hsh⟩ trivial (fun _ _ _ _ => trivial)
        (norm T k _ hl)

-- The search: all live derivations with at most k gates from the list ws, consecutive
-- gates respecting okB; (pa, pb, pz) is the previous gate ((0, 0, 0) at the start).
def srch (T : ℕ) : ℕ → List ℕ → ℕ → ℕ → ℕ → Bool
  | 0, ws, _, _, _ => ws == [T]
  | k + 1, ws, pa, pb, pz => ws == [T] || (decide (ws.length ≤ k + 2) && sepB T ws &&
      (pairs ws).any fun ab =>
        [rem ab.1 ab.2 ws, ins ab.1 (rem ab.1 ab.2 ws), ins ab.2 (rem ab.1 ab.2 ws),
          ins ab.1 (ins ab.2 (rem ab.1 ab.2 ws))].any
          fun r => [ab.1 &&& ab.2, ab.1 ||| ab.2].any
            fun z => okB pa pb pz ab.1 ab.2 z && !r.contains z && srch T k (z :: r) ab.1 ab.2 z)

theorem srch_step (T : ℕ) (hT : T < 65536) (k : ℕ) (ws : List ℕ) (pa pb pz : ℕ) (hn : ws.Nodup)
    (hcard : ws.length ≤ k + 2) (hsep : Sep T ws.toFinset) (a b z : ℕ) (r : Finset ℕ)
    (ih : ∀ ws' : List ℕ, ws'.Nodup → ws'.toFinset = insert z r → srch T k ws' a b z = true)
    (hab : (a, b) ∈ pairs ws) (hz : z = a &&& b ∨ z = a ||| b) (hzr : z ∉ r)
    (hsh : Shape ws.toFinset a b r) (hok : okB pa pb pz a b z = true) :
    srch T (k + 1) ws pa pb pz = true := by
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
  have ih' := ih (z :: rl) (List.nodup_cons.2 ⟨hzl, hrn⟩) (by rw [List.toFinset_cons, hrf])
  rw [srch]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  right
  refine ⟨⟨hcard, sepB_of T hT ws hsep⟩, (a, b), hab, rl, hrl, z, ?_, ?_⟩
  · rcases hz with hz | hz <;> rw [hz] <;> simp
  · exact ⟨⟨hok, by simpa using hzl⟩, ih'⟩

theorem srch_complete (T : ℕ) (hT : T < 65536) : ∀ (k : ℕ) (ws : List ℕ) (pa pb pz : ℕ)
    (A : ℕ → ℕ → ℕ → Prop), ws.Nodup → (∀ c d y, A c d y → okP pa pb pz c d y) →
    LiveO T k ws.toFinset A → srch T k ws pa pb pz = true
  | 0, ws, pa, pb, pz, A, hn, _, h => by
    simp only [LiveO] at h
    simp [srch, single T ws hn h]
  | k + 1, ws, pa, pb, pz, A, hn, hA, h => by
    have hlive := liveO_live T (k + 1) _ _ h
    have hcard := live_card T (k + 1) _ hlive
    have hsep := live_sep T (k + 1) _ hlive
    rw [LiveO] at h
    rcases h with h | ⟨a, b, z, r, ⟨ha, hb, hab, hz, hzr, hsh⟩, hAz, hl⟩
    · simp [srch, single T ws hn h]
    · rw [List.toFinset_card_of_nodup hn] at hcard
      have hok := hA a b z hAz
      rcases pairs_mem ws a b (by simpa using ha) (by simpa using hb) hab with hp | hp
      · refine srch_step T hT k ws pa pb pz hn (by omega) hsep a b z r ?_ hp hz hzr hsh
          ((okB_iff _ _ _ _ _ _).2 hok)
        intro ws' hn' hf
        exact srch_complete T hT k ws' a b z (okP a b z) hn' (fun _ _ _ h' => h')
          (by rw [hf]; exact hl)
      · refine srch_step T hT k ws pa pb pz hn (by omega) hsep b a z r ?_ hp ?_ hzr
          (shape_symm _ a b r hsh) ((okB_iff _ _ _ _ _ _).2 (okP_swap2 _ _ _ _ _ _ hok))
        · intro ws' hn' hf
          exact srch_complete T hT k ws' b a z (okP a b z) hn'
            (fun c d y h' => okP_swap1 _ _ _ _ _ _ h') (by rw [hf]; exact hl)
        · rcases hz with hz | hz
          · exact Or.inl (by rw [hz, Nat.land_comm])
          · exact Or.inr (by rw [hz, Nat.lor_comm])

theorem main (T : ℕ) (hT : T < 65536) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L k o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → (∀ p, (ws p).length = L) → Inv pool ws → (∀ m ∈ pool, m < 65536) →
    0 ∈ pool →
    (∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    Build1 T k pool.toFinset
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
    | zero => rw [Build1]; exact hTin
    | succ k => rw [Build1]; exact Or.inl hTin
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
      rw [Build1]
      refine Or.inr ⟨c, ?_, IH⟩
      have h0' : (0 : ℕ) ∈ pool.toFinset := by simpa using h0
      rcases stepC_mem pool c hc with h | h | h | ⟨a, ha, b, hb, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl (by rw [h]; exact h0')
      · exact Or.inl (by simpa using h)
      · exact Or.inr (Or.inr ⟨a, by simpa using ha, b, by simpa using hb, h⟩)

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

theorem lower (T : ℕ) (hT : T < 65536) (hT1 : T ≠ 65535) (k : ℕ)
    (hr : (subs pool0).all (fun s => !srch T k s 0 0 0) = true) :
    ¬ RepSizeAtMost (fun u v : Fin 4 => T.testBit (4 * u.val + v.val)) k := by
  rintro ⟨C, hC, hs, hrep⟩
  have hb1 := main T hT C.gates pool0 X 8 k C.output hC hs X_len inv0 (by decide) (by decide)
    (fun p => by
      have h := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
      have he : T.testBit (4 * (p.val / 4) + p.val % 4) = T.testBit p := by
        rw [Nat.div_add_mod p.val 4]
      exact h.trans he)
  have hp0 : ∀ z ∈ pool0.toFinset, z < 65536 := by decide
  have hb := notop T hT1 k _ _ (fun z hz => ⟨hp0 z hz, Or.inr hz⟩) hb1
  obtain ⟨s', hs', hl⟩ := compress T k _ hb
  classical
  have hn : (pool0.filter (fun x => decide (x ∈ s'))).Nodup := List.Nodup.filter _ (by decide)
  have hf : (pool0.filter (fun x => decide (x ∈ s'))).toFinset = s' := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨by simpa using hs' h, h⟩⟩
  have h1 := srch_complete T hT k _ 0 0 0 (fun _ _ _ => True) hn
    (fun c d y _ => by unfold okP; omega)
    (by rw [hf]; exact norm T k _ hl)
  have h2 := List.all_eq_true.1 hr (pool0.filter (fun x => decide (x ∈ s')))
    (filter_mem_subs _ pool0)
  rw [h1] at h2
  cases h2

-- The part of the body of srch under one choice of a pair.
def body (T k : ℕ) (ws : List ℕ) (pa pb pz : ℕ) (ab : ℕ × ℕ) : Bool :=
  [rem ab.1 ab.2 ws, ins ab.1 (rem ab.1 ab.2 ws), ins ab.2 (rem ab.1 ab.2 ws),
    ins ab.1 (ins ab.2 (rem ab.1 ab.2 ws))].any
    fun r => [ab.1 &&& ab.2, ab.1 ||| ab.2].any
      fun z => okB pa pb pz ab.1 ab.2 z && !r.contains z && srch T k (z :: r) ab.1 ab.2 z

theorem srch_split (T k : ℕ) (ws : List ℕ) (pa pb pz : ℕ) (hne : (ws == [T]) = false)
    (h : ∀ ab ∈ pairs ws, (!body T k ws pa pb pz ab) = true) :
    srch T (k + 1) ws pa pb pz = false := by
  have h1 : ((pairs ws).any (body T k ws pa pb pz)) = false := by
    rw [List.any_eq_false]
    intro ab hab
    have h2 := h ab hab
    simpa using h2
  rw [srch, hne, Bool.false_or, Bool.and_eq_false_iff]
  right
  exact h1

theorem all_of_getD {α : Type} (l : List α) (d : α) (f : α → Bool) (n : ℕ) (hl : l.length = n)
    (h : ∀ i < n, f (l.getD i d) = true) : ∀ q ∈ l, f q = true := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
  have h2 := h i (hl ▸ hi)
  rwa [List.getD_eq_getElem _ _ hi] at h2

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [9, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [11, 1]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [14, 0]⟩, ⟨GateOp.or, [15, 13]⟩], 16⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def hv : List (List ℕ) := [[15, 240, 3840, 61440, 4369, 8738, 17476, 34952]]

theorem hv0_0 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 0 (0, 0))) = true := by
  decide +kernel

theorem hv0_1 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 1 (0, 0))) = true := by
  decide +kernel

theorem hv0_2 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 2 (0, 0))) = true := by
  decide +kernel

theorem hv0_3 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 3 (0, 0))) = true := by
  decide +kernel

theorem hv0_4 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 4 (0, 0))) = true := by
  decide +kernel

theorem hv0_5 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 5 (0, 0))) = true := by
  decide +kernel

theorem hv0_6 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 6 (0, 0))) = true := by
  decide +kernel

theorem hv0_7 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 7 (0, 0))) = true := by
  decide +kernel

theorem hv0_8 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 8 (0, 0))) = true := by
  decide +kernel

theorem hv0_9 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 9 (0, 0))) = true := by
  decide +kernel

theorem hv0_10 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 10 (0, 0))) = true := by
  decide +kernel

theorem hv0_11 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 11 (0, 0))) = true := by
  decide +kernel

theorem hv0_12 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 12 (0, 0))) = true := by
  decide +kernel

theorem hv0_13 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 13 (0, 0))) = true := by
  decide +kernel

theorem hv0_14 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 14 (0, 0))) = true := by
  decide +kernel

theorem hv0_15 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 15 (0, 0))) = true := by
  decide +kernel

theorem hv0_16 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 16 (0, 0))) = true := by
  decide +kernel

theorem hv0_17 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 17 (0, 0))) = true := by
  decide +kernel

theorem hv0_18 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 18 (0, 0))) = true := by
  decide +kernel

theorem hv0_19 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 19 (0, 0))) = true := by
  decide +kernel

theorem hv0_20 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 20 (0, 0))) = true := by
  decide +kernel

theorem hv0_21 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 21 (0, 0))) = true := by
  decide +kernel

theorem hv0_22 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 22 (0, 0))) = true := by
  decide +kernel

theorem hv0_23 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 23 (0, 0))) = true := by
  decide +kernel

theorem hv0_24 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 24 (0, 0))) = true := by
  decide +kernel

theorem hv0_25 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 25 (0, 0))) = true := by
  decide +kernel

theorem hv0_26 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 26 (0, 0))) = true := by
  decide +kernel

theorem hv0_27 : (!body 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 ((pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]).getD 27 (0, 0))) = true := by
  decide +kernel

theorem hv0 : srch 4459 (7 + 1) [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 = false := by
  refine srch_split 4459 7 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 (by decide) (all_of_getD (pairs [15, 240, 3840, 61440, 4369, 8738, 17476, 34952]) (0, 0) _ 28 (by decide) ?_)
  intro i hi
  interval_cases i
  · exact hv0_0
  · exact hv0_1
  · exact hv0_2
  · exact hv0_3
  · exact hv0_4
  · exact hv0_5
  · exact hv0_6
  · exact hv0_7
  · exact hv0_8
  · exact hv0_9
  · exact hv0_10
  · exact hv0_11
  · exact hv0_12
  · exact hv0_13
  · exact hv0_14
  · exact hv0_15
  · exact hv0_16
  · exact hv0_17
  · exact hv0_18
  · exact hv0_19
  · exact hv0_20
  · exact hv0_21
  · exact hv0_22
  · exact hv0_23
  · exact hv0_24
  · exact hv0_25
  · exact hv0_26
  · exact hv0_27

theorem light : (subs pool0).all (fun s => hv.contains s || !srch 4459 8 s 0 0 0) = true := by
  decide +kernel

theorem low : (subs pool0).all (fun s => !srch 4459 8 s 0 0 0) = true := by
  rw [List.all_eq_true]
  intro s hs
  have h := List.all_eq_true.1 light s hs
  simp only [Bool.or_eq_true] at h
  rcases h with h1 | h1
  · have h2 : s ∈ hv := by simpa using h1
    simp only [hv, List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with h2
    · rw [h2, show srch 4459 8 [15, 240, 3840, 61440, 4369, 8738, 17476, 34952] 0 0 0 = false from hv0]; rfl
  · exact h1

end PEqualNP.Outside.L_meta_5982

theorem PEqualNP.Outside.L_meta_5982 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) 9 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4459 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_5982.upper, PEqualNP.Outside.L_meta_5982.lower 4459 (by norm_num) (by norm_num) 8 PEqualNP.Outside.L_meta_5982.low⟩
