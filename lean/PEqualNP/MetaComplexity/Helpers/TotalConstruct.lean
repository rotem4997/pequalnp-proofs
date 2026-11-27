import PEqualNP.MetaComplexity.Helpers.LocalConstruct

/-!
# A local reduction of parity to total MCSP, with four blocks

A witness for the hypotheses of `L-meta-040`. The input is cut into four blocks of at most `q`
bits, `y 0, ..., y 3` are the block parities, and the map writes the size bound `4` and the
table of a function of three variables that takes the same value at a point and at its
complement:

  entry `p` and entry `7 - p` hold `y 0`, `y 1`, `y 2`, `! y 3` for `p = 0, 1, 2, 3`.

Each entry reads one block, so the map is `q`-local, and `3 q < n ≤ 4 q` is possible.

* If the parity of `y` is odd, the table has an even number of the four pairs set: it is a
  constant, or the XOR or XNOR of two of the three variables. Four gates suffice.
* If the parity of `y` is even, one or three pairs are set: the function is "all three literals
  equal" or its complement, for some choice of literals. These eight functions need more than
  four gates (in fact six).

The lower bound is a finite search checked by the kernel. A function of three variables is
coded by a number below `256` (bit `p` is the value at the point of table index `p`); a gate of
fan-in at most two maps codes to codes by bitwise operations; `fnd` searches all sequences of
at most four new codes, never adding a code twice, and finds none of the eight targets.
`search_sound` shows that every circuit is covered by the search.
-/

namespace PEqualNP.MetaComplexity.Helpers.TotalConstruct

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-! ## Codes of functions of three variables -/

/-- The value at `x` of the function coded by `c`. -/
def tb (x : Fin 3 → Bool) (c : ℕ) : Bool := c.testBit (tableIndex x)

theorem idx3 (x : Fin 3 → Bool) : tableIndex x
    = (if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0)
      + (if x 2 = true then 4 else 0) := by
  simp [tableIndex, Fin.sum_univ_three]

theorem idx_lt (x : Fin 3 → Bool) : tableIndex x < 8 := by
  rw [idx3]
  split_ifs <;> omega

theorem idx_surj (p : ℕ) (hp : p < 8) : ∃ x : Fin 3 → Bool, tableIndex x = p := by
  refine ⟨fun i => p.testBit i, ?_⟩
  rw [idx3]
  interval_cases p <;> decide

theorem tb_zero (x : Fin 3 → Bool) : tb x 0 = false := by simp [tb]

theorem tb_full (x : Fin 3 → Bool) : tb x 255 = true := by
  have h : ∀ p : ℕ, p < 8 → Nat.testBit 255 p = true := by
    intro p hp
    interval_cases p <;> rfl
  exact h _ (idx_lt x)

theorem tb_and (x : Fin 3 → Bool) (a b : ℕ) : tb x (a &&& b) = (tb x a && tb x b) := by
  simp [tb, Nat.testBit_and]

theorem tb_or (x : Fin 3 → Bool) (a b : ℕ) : tb x (a ||| b) = (tb x a || tb x b) := by
  simp [tb, Nat.testBit_or]

theorem tb_not (x : Fin 3 → Bool) (a : ℕ) : tb x (255 ^^^ a) = !tb x a := by
  have h := tb_full x
  unfold tb at h ⊢
  rw [Nat.testBit_xor, h]
  simp

theorem code_inj (c t : ℕ) (hc : c < 256) (ht : t < 256)
    (h : ∀ x : Fin 3 → Bool, tb x c = tb x t) : c = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · obtain ⟨x, rfl⟩ := idx_surj i hi
    exact h x
  · have h8 : 256 ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 8 ≤ i by omega)
      norm_num at this ⊢
      exact this
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h8),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht h8)]

/-- The code of a table: entry `i` is bit `i`. -/
def codeOf : List Bool → ℕ
  | [] => 0
  | b :: T => 2 * codeOf T + (if b = true then 1 else 0)

theorem testBit_codeOf : ∀ (T : List Bool) (i : ℕ), (codeOf T).testBit i = T.getD i false
  | [], i => by simp [codeOf]
  | b :: T, 0 => by
    cases b <;> simp [codeOf, Nat.testBit_zero]
  | b :: T, i + 1 => by
    have e : (2 * codeOf T + (if b = true then 1 else 0)) / 2 = codeOf T := by
      split_ifs <;> omega
    rw [codeOf, Nat.testBit_succ, e, testBit_codeOf T i]
    simp

theorem tableFun_code (T : List Bool) (x : Fin 3 → Bool) : tableFun 3 T x = tb x (codeOf T) := by
  unfold tableFun tb
  rw [testBit_codeOf]

/-! ## Gates on codes -/

/-- The code of the output of gate `g`, when the wires present have codes `ws`. -/
def gcode (ws : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => 255
  | GateOp.and, [i] => ws.getD i 0
  | GateOp.and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | GateOp.or, [] => 0
  | GateOp.or, [i] => ws.getD i 0
  | GateOp.or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | GateOp.not, [] => 255
  | GateOp.not, i :: _ => 255 ^^^ ws.getD i 0
  | _, _ => 0

/-- The codes of all wires, starting from the codes `ws` of the wires present. -/
def codesFrom (gs : List Gate) (ws : List ℕ) : List ℕ :=
  gs.foldl (fun ws g => ws ++ [gcode ws g]) ws

theorem getD_map_tb (x : Fin 3 → Bool) (ws : List ℕ) (i : ℕ) :
    (ws.map (tb x)).getD i false = tb x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega), tb_zero]

theorem gate_step (x : Fin 3 → Bool) (ws : List ℕ) (g : Gate) (hg : Ok g) :
    g.op.eval (g.inputs.map fun i => (ws.map (tb x)).getD i false) = tb x (gcode ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map_tb]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => simp [gcode, GateOp.eval, tb_full]
    | [i], _ => simp [gcode, GateOp.eval]
    | [i, j], _ => simp [gcode, GateOp.eval, tb_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gcode, GateOp.eval, tb_zero]
    | [i], _ => simp [gcode, GateOp.eval]
    | [i, j], _ => simp [gcode, GateOp.eval, tb_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    match ins with
    | [] => simp [gcode, GateOp.eval, tb_full]
    | i :: _ => simp [gcode, GateOp.eval, tb_not]
  | mod m => simp at hop
  | maj => simp at hop

theorem wires_codes (x : Fin 3 → Bool) : ∀ (gs : List Gate) (ws : List ℕ), (∀ g ∈ gs, Ok g) →
    wiresFrom gs (ws.map (tb x)) = (codesFrom gs ws).map (tb x) := by
  intro gs
  induction gs with
  | nil => intro ws _; rfl
  | cons g gs ih =>
    intro ws hok
    have e : wiresFrom (g :: gs) (ws.map (tb x))
        = wiresFrom gs ((ws ++ [gcode ws g]).map (tb x)) := by
      show wiresFrom gs (ws.map (tb x)
        ++ [g.op.eval (g.inputs.map fun i => (ws.map (tb x)).getD i false)]) = _
      rw [List.map_append, List.map_singleton,
        gate_step x ws g (hok g List.mem_cons_self)]
    rw [e, ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]
    rfl

theorem getD_mem (ws : List ℕ) (i : ℕ) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_cons_self

/-- `c` is obtained from codes in `vs` by one operation. -/
def Gen (vs : List ℕ) (c : ℕ) : Prop :=
  (∃ a ∈ vs, c = 255 ^^^ a) ∨ ∃ a ∈ vs, ∃ b ∈ vs, c = a &&& b ∨ c = a ||| b

theorem gcode_gen (ws : List ℕ) (g : Gate) (hg : Ok g) :
    gcode ws g ∈ 0 :: ws ∨ Gen (0 :: ws) (gcode ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => exact Or.inr (Or.inl ⟨0, List.mem_cons_self, rfl⟩)
    | [i], _ => exact Or.inl (getD_mem ws i)
    | [i, j], _ =>
      exact Or.inr (Or.inr ⟨_, getD_mem ws i, _, getD_mem ws j, Or.inl rfl⟩)
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact Or.inl List.mem_cons_self
    | [i], _ => exact Or.inl (getD_mem ws i)
    | [i, j], _ =>
      exact Or.inr (Or.inr ⟨_, getD_mem ws i, _, getD_mem ws j, Or.inr rfl⟩)
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    match ins with
    | [] => exact Or.inr (Or.inl ⟨0, List.mem_cons_self, rfl⟩)
    | i :: _ => exact Or.inr (Or.inl ⟨_, getD_mem ws i, rfl⟩)
  | mod m => simp at hop
  | maj => simp at hop

theorem gen_lt (vs : List ℕ) (h : ∀ a ∈ vs, a < 256) (c : ℕ) (hc : Gen vs c) : c < 256 := by
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact Nat.xor_lt_two_pow (n := 8) (by norm_num) (h a ha)
  · exact Nat.and_lt_two_pow (n := 8) a (h b hb)
  · exact Nat.or_lt_two_pow (n := 8) (h a ha) (h b hb)

theorem codes_lt : ∀ (gs : List Gate) (ws : List ℕ), (∀ g ∈ gs, Ok g) → (∀ a ∈ ws, a < 256) →
    ∀ a ∈ codesFrom gs ws, a < 256 := by
  intro gs
  induction gs with
  | nil => intro ws _ h; exact h
  | cons g gs ih =>
    intro ws hok h
    have h0 : ∀ a ∈ 0 :: ws, a < 256 := by
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · norm_num
      · exact h a ha
    have hc : gcode ws g < 256 := by
      rcases gcode_gen ws g (hok g List.mem_cons_self) with hm | hm
      · exact h0 _ hm
      · exact gen_lt _ h0 _ hm
    show ∀ a ∈ codesFrom gs (ws ++ [gcode ws g]), a < 256
    refine ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) ?_
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.1 ha]; exact hc

/-! ## The search -/

/-- Membership in a list of numbers, as a Boolean. -/
def memb (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => Nat.beq a b || memb a l

theorem memb_iff (a : ℕ) : ∀ l : List ℕ, memb a l = true ↔ a ∈ l
  | [] => by simp [memb]
  | b :: l => by simp [memb, memb_iff a l]

/-- The AND and the OR of every pair of entries at two different positions. -/
def pairs : List ℕ → List ℕ
  | [] => []
  | a :: l => l.flatMap (fun b => [a &&& b, a ||| b]) ++ pairs l

theorem mem_pairs : ∀ (l : List ℕ) (c : ℕ), c ∈ pairs l →
    ∃ a ∈ l, ∃ b ∈ l, c = a &&& b ∨ c = a ||| b
  | [], c, h => by simp [pairs] at h
  | a :: l, c, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨b, hb, hc⟩ := List.mem_flatMap.1 h
      refine ⟨a, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, ?_⟩
      simpa using hc
    · obtain ⟨a', ha', b, hb, hc⟩ := mem_pairs l c h
      exact ⟨a', List.mem_cons_of_mem _ ha', b, List.mem_cons_of_mem _ hb, hc⟩

theorem pairs_mem : ∀ (l : List ℕ) (a b : ℕ), a ∈ l → b ∈ l →
    a = b ∨ (a &&& b ∈ pairs l ∧ a ||| b ∈ pairs l)
  | [], a, b, ha, _ => by simp at ha
  | d :: l, a, b, ha, hb => by
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩)⟩
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩)⟩
      · rw [Nat.and_comm]; simp
      · rw [Nat.or_comm]; simp
    · rcases pairs_mem l a b ha' hb' with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_right _ h1, List.mem_append_right _ h2⟩

/-- The candidates for a new code. -/
def cands (vs : List ℕ) : List ℕ := vs.map (fun a => 255 ^^^ a) ++ pairs vs

theorem cands_gen (vs : List ℕ) (c : ℕ) (h : c ∈ cands vs) : Gen vs c := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨a, ha, rfl⟩
  · exact Or.inr (mem_pairs vs c h)

theorem gen_cands (vs : List ℕ) (c : ℕ) (h : Gen vs c) : c ∈ vs ∨ c ∈ cands vs := by
  rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hc⟩
  · exact Or.inr (List.mem_append_left _ (List.mem_map.2 ⟨a, ha, rfl⟩))
  · rcases pairs_mem vs a b ha hb with rfl | ⟨h1, h2⟩
    · left
      rcases hc with rfl | rfl
      · rw [Nat.and_self]; exact ha
      · rw [Nat.or_self]; exact ha
    · right
      rcases hc with rfl | rfl
      · exact List.mem_append_right _ h1
      · exact List.mem_append_right _ h2

theorem gen_mono (vs vs' : List ℕ) (h : ∀ a ∈ vs, a ∈ vs') (c : ℕ) (hc : Gen vs c) :
    Gen vs' c := by
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hc⟩
  · exact Or.inl ⟨a, h a ha, rfl⟩
  · exact Or.inr ⟨a, h a ha, b, h b hb, hc⟩

/-- Some target is obtained from the codes `vs` by at most `k` new codes, none of them added
twice. Meant for `vs` holding no target. -/
def fnd (ts : List ℕ) : ℕ → List ℕ → Bool
  | 0, _ => false
  | k + 1, vs => (cands vs).any fun c =>
      memb c ts || (match k with
        | 0 => false
        | _ => !memb c vs && fnd ts k (c :: vs))

theorem fnd_succ (ts : List ℕ) (k : ℕ) (vs : List ℕ) : fnd ts (k + 1) vs = true ↔
    ∃ c ∈ cands vs, c ∈ ts ∨ (c ∉ vs ∧ fnd ts k (c :: vs) = true) := by
  cases k with
  | zero => simp [fnd, memb_iff]
  | succ k =>
    rw [fnd]
    simp only [List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      memb_iff, ← Bool.not_eq_true]

/-- Some target is among the codes `vs`. -/
def Hit (ts vs : List ℕ) : Prop := ∃ t ∈ ts, t ∈ vs

theorem fnd_mono (ts : List ℕ) : ∀ (k : ℕ) (vs vs' : List ℕ) (k' : ℕ), (∀ a ∈ vs, a ∈ vs') →
    k ≤ k' → fnd ts k vs = true → Hit ts vs' ∨ fnd ts k' vs' = true := by
  intro k
  induction k with
  | zero => intro vs vs' k' _ _ h; simp [fnd] at h
  | succ k ih =>
    intro vs vs' k' hsub hk h
    obtain ⟨k', rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    obtain ⟨c, hc, hcase⟩ := (fnd_succ ts k vs).1 h
    have hgen : Gen vs' c := gen_mono vs vs' hsub c (cands_gen vs c hc)
    by_cases hin : c ∈ vs'
    · rcases hcase with ht | ⟨_, hf⟩
      · exact Or.inl ⟨c, ht, hin⟩
      · refine ih (c :: vs) vs' (k' + 1) ?_ (by omega) hf
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hin
        · exact hsub a ha
    · have hc' : c ∈ cands vs' := (gen_cands vs' c hgen).resolve_left hin
      rcases hcase with ht | ⟨_, hf⟩
      · exact Or.inr ((fnd_succ ts k' vs').2 ⟨c, hc', Or.inl ht⟩)
      · have := ih (c :: vs) (c :: vs') k' (by
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub a ha)) (by omega) hf
        rcases this with ⟨t, ht, htv⟩ | hf'
        · rcases List.mem_cons.1 htv with rfl | htv
          · exact Or.inr ((fnd_succ ts k' vs').2 ⟨t, hc', Or.inl ht⟩)
          · exact Or.inl ⟨t, ht, htv⟩
        · exact Or.inr ((fnd_succ ts k' vs').2 ⟨c, hc', Or.inr ⟨hin, hf'⟩⟩)

/-- Every circuit is covered by the search: if a circuit with at most `k` gates over wires of
codes `ws` has a wire whose code is a target, the search from `0 :: ws` finds a target. -/
theorem search_sound (ts : List ℕ) : ∀ (gs : List Gate) (ws : List ℕ) (k o : ℕ),
    (∀ g ∈ gs, Ok g) → gs.length ≤ k → (codesFrom gs ws).getD o 0 ∈ ts →
    Hit ts (0 :: ws) ∨ fnd ts k (0 :: ws) = true := by
  intro gs
  induction gs with
  | nil =>
    intro ws k o _ _ h
    exact Or.inl ⟨_, h, getD_mem ws o⟩
  | cons g gs ih =>
    intro ws k o hok hk h
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    set c := gcode ws g with hcdef
    have h1 := ih (ws ++ [c]) k o (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp at hk; omega) h
    have hsub : ∀ a ∈ 0 :: (ws ++ [c]), a ∈ c :: 0 :: ws := by
      intro a ha
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
      tauto
    -- move to the list `c :: 0 :: ws`
    have h2 : Hit ts (c :: 0 :: ws) ∨ fnd ts k (c :: 0 :: ws) = true := by
      rcases h1 with ⟨t, ht, htv⟩ | hf
      · exact Or.inl ⟨t, ht, hsub t htv⟩
      · exact fnd_mono ts k _ _ k hsub le_rfl hf
    by_cases hin : c ∈ 0 :: ws
    · have hsub' : ∀ a ∈ c :: 0 :: ws, a ∈ 0 :: ws := by
        intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hin
        · exact ha
      rcases h2 with ⟨t, ht, htv⟩ | hf
      · exact Or.inl ⟨t, ht, hsub' t htv⟩
      · exact fnd_mono ts k _ _ (k + 1) hsub' (by omega) hf
    · have hgen : Gen (0 :: ws) c :=
        (gcode_gen ws g (hok g List.mem_cons_self)).resolve_left hin
      have hc' : c ∈ cands (0 :: ws) := (gen_cands _ c hgen).resolve_left hin
      rcases h2 with ⟨t, ht, htv⟩ | hf
      · rcases List.mem_cons.1 htv with he | htv
        · exact Or.inr ((fnd_succ ts k _).2 ⟨c, hc', Or.inl (he ▸ ht)⟩)
        · exact Or.inl ⟨t, ht, htv⟩
      · exact Or.inr ((fnd_succ ts k _).2 ⟨c, hc', Or.inr ⟨hin, hf⟩⟩)

/-! ## The two bounds -/

/-- The codes of the three inputs. -/
def inputs : List ℕ := [170, 204, 240]

theorem ofFn_codes (x : Fin 3 → Bool) : List.ofFn x = inputs.map (tb x) := by
  have hx : List.ofFn x = [x 0, x 1, x 2] := by
    simp [List.ofFn_succ]
  rw [hx]
  simp only [inputs, List.map_cons, List.map_nil, tb, idx3]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

/-- The eight functions "the three literals are equal" and "not all equal". -/
def targets : List ℕ := [129, 66, 36, 24, 126, 189, 219, 231]

theorem search_empty : fnd targets 4 (0 :: inputs) = false := by decide +kernel

/-- A table whose code is a target has no circuit with four gates. -/
theorem lower (T : List Bool) (h : memb (codeOf T) targets = true) :
    ¬ HasCircuitSize 3 (tableFun 3 T) 4 := by
  rintro ⟨C, ok, hsz, hev⟩
  have hw : ∀ x : Fin 3 → Bool,
      C.eval (List.ofFn x) = tb x ((codesFrom C.gates inputs).getD C.output 0) := by
    intro x
    show (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
    rw [ofFn_codes, wires_codes x C.gates inputs ok, getD_map_tb]
  have hlt : (codesFrom C.gates inputs).getD C.output 0 < 256 := by
    have hm := getD_mem (codesFrom C.gates inputs) C.output
    rcases List.mem_cons.1 hm with e | hm
    · rw [e]; norm_num
    · exact codes_lt C.gates inputs ok (by decide) _ hm
  have ht : codeOf T ∈ targets := (memb_iff _ _).1 h
  have htlt : codeOf T < 256 := by
    revert ht
    generalize codeOf T = t
    intro ht
    simp only [targets, List.mem_cons, List.not_mem_nil, or_false] at ht
    omega
  have e : (codesFrom C.gates inputs).getD C.output 0 = codeOf T := by
    apply code_inj _ _ hlt htlt
    intro x
    rw [← hw x, hev x, tableFun_code]
  have := search_sound targets C.gates inputs 4 C.output ok hsz (by rw [e]; exact ht)
  rcases this with hh | hf
  · revert hh
    unfold Hit
    decide
  · rw [search_empty] at hf
    exact absurd hf (by decide)

/-- A table whose code is the code of the output of a circuit with four gates. -/
theorem upper (T : List Bool) (gs : List Gate) (o : ℕ) (ok : ∀ g ∈ gs, Ok g)
    (hlen : gs.length ≤ 4) (h : (codesFrom gs inputs).getD o 0 = codeOf T) :
    HasCircuitSize 3 (tableFun 3 T) 4 := by
  refine ⟨⟨gs, o⟩, ok, hlen, ?_⟩
  intro x
  show (wiresFrom gs (List.ofFn x)).getD o false = _
  rw [ofFn_codes, wires_codes x gs inputs ok, getD_map_tb, h, tableFun_code]

/-- XOR of wires `i` and `j`, at wire `6`. -/
def xorC (i j : ℕ) : List Gate :=
  [⟨GateOp.or, [i, j]⟩, ⟨GateOp.and, [i, j]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [3, 5]⟩]

/-- XNOR of wires `i` and `j`, at wire `6`. -/
def xnorC (i j : ℕ) : List Gate :=
  [⟨GateOp.and, [i, j]⟩, ⟨GateOp.or, [i, j]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [3, 5]⟩]

theorem xorC_ok (i j : ℕ) : ∀ g ∈ xorC i j, Ok g := by
  intro g hg
  simp only [xorC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [Ok]

theorem xnorC_ok (i j : ℕ) : ∀ g ∈ xnorC i j, Ok g := by
  intro g hg
  simp only [xnorC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [Ok]

theorem trueC_ok : ∀ g ∈ [(⟨GateOp.not, []⟩ : Gate)], Ok g := by
  intro g hg
  rw [List.mem_singleton.1 hg]
  simp [Ok]

/-! ## The gadget -/

/-- The table: entries `p` and `7 - p` hold the same bit. -/
def tab (a b c d : Bool) : List Bool := [a, b, c, !d, !d, c, b, a]

theorem odd_small (a b c d : Bool) (h : xor (xor (xor a b) c) d = true) :
    HasCircuitSize 3 (tableFun 3 (tab a b c d)) 4 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | exact absurd h (by decide)
    | exact upper _ [] 3 (by simp) (by decide) rfl
    | exact upper _ [⟨GateOp.not, []⟩] 3 trueC_ok (by decide) rfl
    | exact upper _ (xorC 0 1) 6 (xorC_ok _ _) (by decide) rfl
    | exact upper _ (xorC 0 2) 6 (xorC_ok _ _) (by decide) rfl
    | exact upper _ (xorC 1 2) 6 (xorC_ok _ _) (by decide) rfl
    | exact upper _ (xnorC 0 1) 6 (xnorC_ok _ _) (by decide) rfl
    | exact upper _ (xnorC 0 2) 6 (xnorC_ok _ _) (by decide) rfl
    | exact upper _ (xnorC 1 2) 6 (xnorC_ok _ _) (by decide) rfl

theorem even_large (a b c d : Bool) (h : xor (xor (xor a b) c) d = false) :
    ¬ HasCircuitSize 3 (tableFun 3 (tab a b c d)) 4 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | exact absurd h (by decide)
    | exact lower _ (by decide)

theorem gadget (a b c d : Bool) :
    HasCircuitSize 3 (tableFun 3 (tab a b c d)) 4 ↔ xor (xor (xor a b) c) d = true := by
  constructor
  · intro h
    by_contra hx
    exact even_large a b c d (by simpa using hx) h
  · exact odd_small a b c d

/-! ## The word and its locality -/

/-- The instance: the bound `4` in unary, the separator, the table. -/
def word (y : ℕ → Bool) : List Bool :=
  [true, true, true, true, false, y 0, y 1, y 2, !y 3, !y 3, y 2, y 1, y 0]

theorem word_eq (y : ℕ → Bool) :
    word y = List.replicate 4 true ++ false :: tab (y 0) (y 1) (y 2) (y 3) := rfl

/-- The index of the bit of `y` read by position `j` of the word. -/
def ix (j : ℕ) : ℕ := if j ≤ 8 then j - 5 else 12 - j

theorem word_get (y y' : ℕ → Bool) (j : ℕ) (h : y' (ix j) = y (ix j)) :
    (word y')[j]? = (word y)[j]? := by
  by_cases hj : j < 13
  · interval_cases j <;> simp [word, ix] at h ⊢ <;> simp [h]
  · rw [List.getElem?_eq_none (by simp [word]; omega),
      List.getElem?_eq_none (by simp [word]; omega)]

theorem word_mem_iff (y : ℕ → Bool) :
    word y ∈ MCSP ↔ LocalConstruct.par y 3 = true := by
  have hp : LocalConstruct.par y 3 = xor (xor (xor (y 0) (y 1)) (y 2)) (y 3) := rfl
  rw [hp, ← gadget]
  constructor
  · rintro ⟨n', s, T, hw, hlen, hs⟩
    rw [word_eq] at hw
    obtain ⟨e1, e2⟩ := LocalConstruct.split_unique 4 s _ _ hw
    subst e1
    subst e2
    have e3 : 3 = n' := Nat.pow_right_injective (Nat.le_refl 2) (by simpa [tab] using hlen)
    subst e3
    exact hs
  · intro h
    exact ⟨3, 4, tab (y 0) (y 1) (y 2) (y 3), word_eq y, rfl, h⟩

/-- A `q`-local reduction of parity on `n ≤ 4 q` bits to total MCSP. Every image is an instance
with size bound `4` and a table of length `2 ^ 3`. -/
theorem main : ∀ n q : ℕ, n ≤ 4 * q → ∃ w : (Fin n → Bool) → List Bool,
    PEqualNP.MetaComplexity.QueryLocal n q w ∧
    (∀ x : Fin n → Bool, (w x).length = 13) ∧
    (∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔
        w x ∈ PEqualNP.MetaComplexity.MCSP) ∧
    ∀ x : Fin n → Bool, ∃ T : List Bool,
      w x = List.replicate 4 true ++ false :: T ∧ T.length = 2 ^ 3 := by
  intro n q hnq
  refine ⟨fun x => word (LocalConstruct.blockPar n q x), ?_, ?_, ?_, ?_⟩
  · intro j x
    refine ⟨Finset.univ.filter fun i : Fin n => (i : ℕ) / q = ix j, ?_, fun x' hx' => ?_⟩
    · rcases Nat.eq_zero_or_pos q with hq | hq
      · have hn : n = 0 := by omega
        subst hn
        simp
      · exact LocalConstruct.block_card n q _ hq
    · apply word_get
      apply LocalConstruct.blockPar_congr
      intro i hi
      exact hx' i (by simp [hi])
  · intro x
    rfl
  · intro x
    show _ ↔ word (LocalConstruct.blockPar n q x) ∈ MCSP
    rw [word_mem_iff, LocalConstruct.par_blockPar]
    have e : (Finset.univ.filter fun j : Fin n => (j : ℕ) / q ≤ 3 ∧ x j = true)
        = Finset.univ.filter fun i : Fin n => x i = true := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      have hj := j.isLt
      have hq : 0 < q := by omega
      have h4 : (j : ℕ) / q < 4 := (Nat.div_lt_iff_lt_mul hq).2 (by omega)
      omega
    rw [e]
    simp
  · intro x
    exact ⟨_, word_eq _, rfl⟩

end PEqualNP.MetaComplexity.Helpers.TotalConstruct
