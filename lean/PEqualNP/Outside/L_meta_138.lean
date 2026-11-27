import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta138

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def tb (x : Fin 4 → Bool) (c : ℕ) : Bool := c.testBit (tableIndex x)

theorem idx4 (x : Fin 4 → Bool) : tableIndex x
    = (if x 0 = true then 1 else 0) + (if x 1 = true then 2 else 0)
      + (if x 2 = true then 4 else 0) + (if x 3 = true then 8 else 0) := by
  simp [tableIndex, Fin.sum_univ_four]

theorem idx_lt (x : Fin 4 → Bool) : tableIndex x < 16 := by
  rw [idx4]
  split_ifs <;> omega

theorem idx_surj (p : ℕ) (hp : p < 16) : ∃ x : Fin 4 → Bool, tableIndex x = p := by
  refine ⟨fun i => p.testBit i, ?_⟩
  rw [idx4]
  interval_cases p <;> decide

theorem tb_zero (x : Fin 4 → Bool) : tb x 0 = false := by simp [tb]

theorem tb_full (x : Fin 4 → Bool) : tb x 65535 = true := by
  have h : ∀ p : ℕ, p < 16 → Nat.testBit 65535 p = true := by
    intro p hp
    interval_cases p <;> rfl
  exact h _ (idx_lt x)

theorem tb_and (x : Fin 4 → Bool) (a b : ℕ) : tb x (a &&& b) = (tb x a && tb x b) := by
  simp [tb, Nat.testBit_and]

theorem tb_or (x : Fin 4 → Bool) (a b : ℕ) : tb x (a ||| b) = (tb x a || tb x b) := by
  simp [tb, Nat.testBit_or]

theorem tb_not (x : Fin 4 → Bool) (a : ℕ) : tb x (65535 ^^^ a) = !tb x a := by
  have h := tb_full x
  unfold tb at h ⊢
  rw [Nat.testBit_xor, h]
  simp

theorem code_inj (c t : ℕ) (hc : c < 65536) (ht : t < 65536)
    (h : ∀ x : Fin 4 → Bool, tb x c = tb x t) : c = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · obtain ⟨x, rfl⟩ := idx_surj i hi
    exact h x
  · have h8 : 65536 ≤ 2 ^ i := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 16 ≤ i by omega)
      norm_num at this ⊢
      exact this
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h8),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ht h8)]

def gcode (ws : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => 65535
  | GateOp.and, [i] => ws.getD i 0
  | GateOp.and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | GateOp.or, [] => 0
  | GateOp.or, [i] => ws.getD i 0
  | GateOp.or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | GateOp.not, [] => 65535
  | GateOp.not, i :: _ => 65535 ^^^ ws.getD i 0
  | _, _ => 0

def codesFrom (gs : List Gate) (ws : List ℕ) : List ℕ :=
  gs.foldl (fun ws g => ws ++ [gcode ws g]) ws

theorem getD_map_tb (x : Fin 4 → Bool) (ws : List ℕ) (i : ℕ) :
    (ws.map (tb x)).getD i false = tb x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega), tb_zero]

theorem gate_step (x : Fin 4 → Bool) (ws : List ℕ) (g : Gate) (hg : Ok g) :
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

theorem wires_codes (x : Fin 4 → Bool) : ∀ (gs : List Gate) (ws : List ℕ), (∀ g ∈ gs, Ok g) →
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

def Gen (vs : List ℕ) (c : ℕ) : Prop :=
  (∃ a ∈ vs, c = 65535 ^^^ a) ∨ ∃ a ∈ vs, ∃ b ∈ vs, c = a &&& b ∨ c = a ||| b

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

theorem gen_lt (vs : List ℕ) (h : ∀ a ∈ vs, a < 65536) (c : ℕ) (hc : Gen vs c) : c < 65536 := by
  rcases hc with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, rfl | rfl⟩
  · exact Nat.xor_lt_two_pow (n := 16) (by norm_num) (h a ha)
  · exact Nat.and_lt_two_pow (n := 16) a (h b hb)
  · exact Nat.or_lt_two_pow (n := 16) (h a ha) (h b hb)

theorem codes_lt : ∀ (gs : List Gate) (ws : List ℕ), (∀ g ∈ gs, Ok g) → (∀ a ∈ ws, a < 65536) →
    ∀ a ∈ codesFrom gs ws, a < 65536 := by
  intro gs
  induction gs with
  | nil => intro ws _ h; exact h
  | cons g gs ih =>
    intro ws hok h
    have h0 : ∀ a ∈ 0 :: ws, a < 65536 := by
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · norm_num
      · exact h a ha
    have hc : gcode ws g < 65536 := by
      rcases gcode_gen ws g (hok g List.mem_cons_self) with hm | hm
      · exact h0 _ hm
      · exact gen_lt _ h0 _ hm
    show ∀ a ∈ codesFrom gs (ws ++ [gcode ws g]), a < 65536
    refine ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) ?_
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton.1 ha]; exact hc

def memb (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => Nat.beq a b || memb a l

theorem memb_iff (a : ℕ) : ∀ l : List ℕ, memb a l = true ↔ a ∈ l
  | [] => by simp [memb]
  | b :: l => by simp [memb, memb_iff a l]

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

def cands (vs : List ℕ) : List ℕ := vs.map (fun a => 65535 ^^^ a) ++ pairs vs

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

def inputs : List ℕ := [43690, 52428, 61680, 65280]

theorem ofFn_codes (x : Fin 4 → Bool) : List.ofFn x = inputs.map (tb x) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3] := by
    simp [List.ofFn_succ]
  rw [hx]
  simp only [inputs, List.map_cons, List.map_nil, tb, idx4]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

def paw (x : Fin 4 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)

theorem paw_code (x : Fin 4 → Bool) : paw x = tb x 60136 := by
  simp only [paw, tb, idx4]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

theorem s_65535_21845 : fnd [60136] 2 (21845 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_13107 : fnd [60136] 2 (13107 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_3855 : fnd [60136] 2 (3855 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_255 : fnd [60136] 2 (255 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_34952 : fnd [60136] 2 (34952 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_61166 : fnd [60136] 2 (61166 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_41120 : fnd [60136] 2 (41120 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_64250 : fnd [60136] 2 (64250 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_43520 : fnd [60136] 2 (43520 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_65450 : fnd [60136] 2 (65450 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_49344 : fnd [60136] 2 (49344 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_64764 : fnd [60136] 2 (64764 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_52224 : fnd [60136] 2 (52224 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_65484 : fnd [60136] 2 (65484 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_61440 : fnd [60136] 2 (61440 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535_65520 : fnd [60136] 2 (65520 :: 65535 :: 0 :: inputs) = false := by decide +kernel
theorem s_65535 : fnd [60136] 3 (65535 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (65535 :: 0 :: inputs)).1 h
  have hcs : cands (65535 :: 0 :: inputs) = [0, 65535, 21845, 13107, 3855, 255, 0, 65535, 43690, 65535, 52428, 65535, 61680, 65535, 65280, 65535, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535_65520] at hf
      exact absurd hf (by decide)

theorem s_21845_65535 : fnd [60136] 2 (65535 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_13107 : fnd [60136] 2 (13107 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_3855 : fnd [60136] 2 (3855 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_255 : fnd [60136] 2 (255 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_17476 : fnd [60136] 2 (17476 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_56797 : fnd [60136] 2 (56797 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_20560 : fnd [60136] 2 (20560 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_62965 : fnd [60136] 2 (62965 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_21760 : fnd [60136] 2 (21760 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_65365 : fnd [60136] 2 (65365 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_34952 : fnd [60136] 2 (34952 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_61166 : fnd [60136] 2 (61166 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_41120 : fnd [60136] 2 (41120 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_64250 : fnd [60136] 2 (64250 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_43520 : fnd [60136] 2 (43520 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_65450 : fnd [60136] 2 (65450 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_49344 : fnd [60136] 2 (49344 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_64764 : fnd [60136] 2 (64764 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_52224 : fnd [60136] 2 (52224 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_65484 : fnd [60136] 2 (65484 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_61440 : fnd [60136] 2 (61440 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845_65520 : fnd [60136] 2 (65520 :: 21845 :: 0 :: inputs) = false := by decide +kernel
theorem s_21845 : fnd [60136] 3 (21845 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (21845 :: 0 :: inputs)).1 h
  have hcs : cands (21845 :: 0 :: inputs) = [43690, 65535, 21845, 13107, 3855, 255, 0, 21845, 0, 65535, 17476, 56797, 20560, 62965, 21760, 65365, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_17476] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_56797] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_20560] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_62965] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_21760] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_65365] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845_65520] at hf
      exact absurd hf (by decide)

theorem s_13107_65535 : fnd [60136] 2 (65535 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_21845 : fnd [60136] 2 (21845 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_3855 : fnd [60136] 2 (3855 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_255 : fnd [60136] 2 (255 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_8738 : fnd [60136] 2 (8738 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_48059 : fnd [60136] 2 (48059 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_12336 : fnd [60136] 2 (12336 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_62451 : fnd [60136] 2 (62451 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_13056 : fnd [60136] 2 (13056 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_65331 : fnd [60136] 2 (65331 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_34952 : fnd [60136] 2 (34952 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_61166 : fnd [60136] 2 (61166 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_41120 : fnd [60136] 2 (41120 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_64250 : fnd [60136] 2 (64250 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_43520 : fnd [60136] 2 (43520 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_65450 : fnd [60136] 2 (65450 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_49344 : fnd [60136] 2 (49344 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_64764 : fnd [60136] 2 (64764 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_52224 : fnd [60136] 2 (52224 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_65484 : fnd [60136] 2 (65484 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_61440 : fnd [60136] 2 (61440 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107_65520 : fnd [60136] 2 (65520 :: 13107 :: 0 :: inputs) = false := by decide +kernel
theorem s_13107 : fnd [60136] 3 (13107 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (13107 :: 0 :: inputs)).1 h
  have hcs : cands (13107 :: 0 :: inputs) = [52428, 65535, 21845, 13107, 3855, 255, 0, 13107, 8738, 48059, 0, 65535, 12336, 62451, 13056, 65331, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_8738] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_48059] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_12336] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_62451] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_13056] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_65331] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107_65520] at hf
      exact absurd hf (by decide)

theorem s_3855_65535 : fnd [60136] 2 (65535 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_21845 : fnd [60136] 2 (21845 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_13107 : fnd [60136] 2 (13107 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_255 : fnd [60136] 2 (255 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_2570 : fnd [60136] 2 (2570 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_44975 : fnd [60136] 2 (44975 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_3084 : fnd [60136] 2 (3084 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_53199 : fnd [60136] 2 (53199 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_3840 : fnd [60136] 2 (3840 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_65295 : fnd [60136] 2 (65295 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_34952 : fnd [60136] 2 (34952 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_61166 : fnd [60136] 2 (61166 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_41120 : fnd [60136] 2 (41120 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_64250 : fnd [60136] 2 (64250 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_43520 : fnd [60136] 2 (43520 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_65450 : fnd [60136] 2 (65450 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_49344 : fnd [60136] 2 (49344 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_64764 : fnd [60136] 2 (64764 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_52224 : fnd [60136] 2 (52224 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_65484 : fnd [60136] 2 (65484 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_61440 : fnd [60136] 2 (61440 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855_65520 : fnd [60136] 2 (65520 :: 3855 :: 0 :: inputs) = false := by decide +kernel
theorem s_3855 : fnd [60136] 3 (3855 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (3855 :: 0 :: inputs)).1 h
  have hcs : cands (3855 :: 0 :: inputs) = [61680, 65535, 21845, 13107, 3855, 255, 0, 3855, 2570, 44975, 3084, 53199, 0, 65535, 3840, 65295, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_2570] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_44975] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_3084] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_53199] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_3840] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_65295] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855_65520] at hf
      exact absurd hf (by decide)

theorem s_255_65535 : fnd [60136] 2 (65535 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_21845 : fnd [60136] 2 (21845 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_13107 : fnd [60136] 2 (13107 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_3855 : fnd [60136] 2 (3855 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_170 : fnd [60136] 2 (170 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_43775 : fnd [60136] 2 (43775 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_204 : fnd [60136] 2 (204 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_52479 : fnd [60136] 2 (52479 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_240 : fnd [60136] 2 (240 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_61695 : fnd [60136] 2 (61695 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_34952 : fnd [60136] 2 (34952 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_61166 : fnd [60136] 2 (61166 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_41120 : fnd [60136] 2 (41120 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_64250 : fnd [60136] 2 (64250 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_43520 : fnd [60136] 2 (43520 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_65450 : fnd [60136] 2 (65450 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_49344 : fnd [60136] 2 (49344 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_64764 : fnd [60136] 2 (64764 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_52224 : fnd [60136] 2 (52224 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_65484 : fnd [60136] 2 (65484 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_61440 : fnd [60136] 2 (61440 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255_65520 : fnd [60136] 2 (65520 :: 255 :: 0 :: inputs) = false := by decide +kernel
theorem s_255 : fnd [60136] 3 (255 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (255 :: 0 :: inputs)).1 h
  have hcs : cands (255 :: 0 :: inputs) = [65280, 65535, 21845, 13107, 3855, 255, 0, 255, 170, 43775, 204, 52479, 240, 61695, 0, 65535, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_170] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_43775] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_204] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_52479] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_240] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_61695] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255_65520] at hf
      exact absurd hf (by decide)

theorem s_34952_30583 : fnd [60136] 2 (30583 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_65535 : fnd [60136] 2 (65535 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_21845 : fnd [60136] 2 (21845 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_13107 : fnd [60136] 2 (13107 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_3855 : fnd [60136] 2 (3855 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_255 : fnd [60136] 2 (255 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_32896 : fnd [60136] 2 (32896 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_63736 : fnd [60136] 2 (63736 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_34816 : fnd [60136] 2 (34816 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_65416 : fnd [60136] 2 (65416 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_61166 : fnd [60136] 2 (61166 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_41120 : fnd [60136] 2 (41120 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_64250 : fnd [60136] 2 (64250 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_43520 : fnd [60136] 2 (43520 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_65450 : fnd [60136] 2 (65450 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_49344 : fnd [60136] 2 (49344 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_64764 : fnd [60136] 2 (64764 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_52224 : fnd [60136] 2 (52224 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_65484 : fnd [60136] 2 (65484 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_61440 : fnd [60136] 2 (61440 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952_65520 : fnd [60136] 2 (65520 :: 34952 :: 0 :: inputs) = false := by decide +kernel
theorem s_34952 : fnd [60136] 3 (34952 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (34952 :: 0 :: inputs)).1 h
  have hcs : cands (34952 :: 0 :: inputs) = [30583, 65535, 21845, 13107, 3855, 255, 0, 34952, 34952, 43690, 34952, 52428, 32896, 63736, 34816, 65416, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_30583] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_32896] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_63736] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_34816] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_65416] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952_65520] at hf
      exact absurd hf (by decide)

theorem s_61166_4369 : fnd [60136] 2 (4369 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_65535 : fnd [60136] 2 (65535 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_21845 : fnd [60136] 2 (21845 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_13107 : fnd [60136] 2 (13107 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_3855 : fnd [60136] 2 (3855 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_255 : fnd [60136] 2 (255 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_57568 : fnd [60136] 2 (57568 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_65278 : fnd [60136] 2 (65278 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_60928 : fnd [60136] 2 (60928 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_65518 : fnd [60136] 2 (65518 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_34952 : fnd [60136] 2 (34952 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_41120 : fnd [60136] 2 (41120 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_64250 : fnd [60136] 2 (64250 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_43520 : fnd [60136] 2 (43520 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_65450 : fnd [60136] 2 (65450 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_49344 : fnd [60136] 2 (49344 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_64764 : fnd [60136] 2 (64764 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_52224 : fnd [60136] 2 (52224 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_65484 : fnd [60136] 2 (65484 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_61440 : fnd [60136] 2 (61440 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166_65520 : fnd [60136] 2 (65520 :: 61166 :: 0 :: inputs) = false := by decide +kernel
theorem s_61166 : fnd [60136] 3 (61166 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (61166 :: 0 :: inputs)).1 h
  have hcs : cands (61166 :: 0 :: inputs) = [4369, 65535, 21845, 13107, 3855, 255, 0, 61166, 43690, 61166, 52428, 61166, 57568, 65278, 60928, 65518, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_4369] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_57568] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_65278] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_60928] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_65518] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166_65520] at hf
      exact absurd hf (by decide)

theorem s_41120_24415 : fnd [60136] 2 (24415 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_65535 : fnd [60136] 2 (65535 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_21845 : fnd [60136] 2 (21845 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_13107 : fnd [60136] 2 (13107 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_3855 : fnd [60136] 2 (3855 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_255 : fnd [60136] 2 (255 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_32896 : fnd [60136] 2 (32896 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_60652 : fnd [60136] 2 (60652 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_40960 : fnd [60136] 2 (40960 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_65440 : fnd [60136] 2 (65440 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_34952 : fnd [60136] 2 (34952 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_61166 : fnd [60136] 2 (61166 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_64250 : fnd [60136] 2 (64250 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_43520 : fnd [60136] 2 (43520 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_65450 : fnd [60136] 2 (65450 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_49344 : fnd [60136] 2 (49344 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_64764 : fnd [60136] 2 (64764 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_52224 : fnd [60136] 2 (52224 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_65484 : fnd [60136] 2 (65484 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_61440 : fnd [60136] 2 (61440 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120_65520 : fnd [60136] 2 (65520 :: 41120 :: 0 :: inputs) = false := by decide +kernel
theorem s_41120 : fnd [60136] 3 (41120 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (41120 :: 0 :: inputs)).1 h
  have hcs : cands (41120 :: 0 :: inputs) = [24415, 65535, 21845, 13107, 3855, 255, 0, 41120, 41120, 43690, 32896, 60652, 41120, 61680, 40960, 65440, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_24415] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_32896] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_60652] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_40960] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_65440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120_65520] at hf
      exact absurd hf (by decide)

theorem s_64250_1285 : fnd [60136] 2 (1285 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_65535 : fnd [60136] 2 (65535 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_21845 : fnd [60136] 2 (21845 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_13107 : fnd [60136] 2 (13107 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_3855 : fnd [60136] 2 (3855 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_255 : fnd [60136] 2 (255 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_51400 : fnd [60136] 2 (51400 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_65278 : fnd [60136] 2 (65278 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_64000 : fnd [60136] 2 (64000 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_65530 : fnd [60136] 2 (65530 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_34952 : fnd [60136] 2 (34952 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_61166 : fnd [60136] 2 (61166 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_41120 : fnd [60136] 2 (41120 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_43520 : fnd [60136] 2 (43520 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_65450 : fnd [60136] 2 (65450 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_49344 : fnd [60136] 2 (49344 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_64764 : fnd [60136] 2 (64764 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_52224 : fnd [60136] 2 (52224 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_65484 : fnd [60136] 2 (65484 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_61440 : fnd [60136] 2 (61440 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250_65520 : fnd [60136] 2 (65520 :: 64250 :: 0 :: inputs) = false := by decide +kernel
theorem s_64250 : fnd [60136] 3 (64250 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (64250 :: 0 :: inputs)).1 h
  have hcs : cands (64250 :: 0 :: inputs) = [1285, 65535, 21845, 13107, 3855, 255, 0, 64250, 43690, 64250, 51400, 65278, 61680, 64250, 64000, 65530, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_1285] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_51400] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_65278] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_64000] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_65530] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250_65520] at hf
      exact absurd hf (by decide)

theorem s_43520_22015 : fnd [60136] 2 (22015 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_65535 : fnd [60136] 2 (65535 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_21845 : fnd [60136] 2 (21845 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_13107 : fnd [60136] 2 (13107 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_3855 : fnd [60136] 2 (3855 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_255 : fnd [60136] 2 (255 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_34816 : fnd [60136] 2 (34816 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_61132 : fnd [60136] 2 (61132 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_40960 : fnd [60136] 2 (40960 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_64240 : fnd [60136] 2 (64240 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_34952 : fnd [60136] 2 (34952 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_61166 : fnd [60136] 2 (61166 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_41120 : fnd [60136] 2 (41120 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_64250 : fnd [60136] 2 (64250 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_65450 : fnd [60136] 2 (65450 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_49344 : fnd [60136] 2 (49344 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_64764 : fnd [60136] 2 (64764 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_52224 : fnd [60136] 2 (52224 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_65484 : fnd [60136] 2 (65484 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_61440 : fnd [60136] 2 (61440 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520_65520 : fnd [60136] 2 (65520 :: 43520 :: 0 :: inputs) = false := by decide +kernel
theorem s_43520 : fnd [60136] 3 (43520 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (43520 :: 0 :: inputs)).1 h
  have hcs : cands (43520 :: 0 :: inputs) = [22015, 65535, 21845, 13107, 3855, 255, 0, 43520, 43520, 43690, 34816, 61132, 40960, 64240, 43520, 65280, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_22015] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_34816] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_61132] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_40960] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_64240] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520_65520] at hf
      exact absurd hf (by decide)

theorem s_65450_85 : fnd [60136] 2 (85 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_65535 : fnd [60136] 2 (65535 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_21845 : fnd [60136] 2 (21845 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_13107 : fnd [60136] 2 (13107 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_3855 : fnd [60136] 2 (3855 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_255 : fnd [60136] 2 (255 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_52360 : fnd [60136] 2 (52360 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_65518 : fnd [60136] 2 (65518 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_61600 : fnd [60136] 2 (61600 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_65530 : fnd [60136] 2 (65530 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_34952 : fnd [60136] 2 (34952 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_61166 : fnd [60136] 2 (61166 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_41120 : fnd [60136] 2 (41120 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_64250 : fnd [60136] 2 (64250 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_43520 : fnd [60136] 2 (43520 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_49344 : fnd [60136] 2 (49344 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_64764 : fnd [60136] 2 (64764 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_52224 : fnd [60136] 2 (52224 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_65484 : fnd [60136] 2 (65484 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_61440 : fnd [60136] 2 (61440 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450_65520 : fnd [60136] 2 (65520 :: 65450 :: 0 :: inputs) = false := by decide +kernel
theorem s_65450 : fnd [60136] 3 (65450 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (65450 :: 0 :: inputs)).1 h
  have hcs : cands (65450 :: 0 :: inputs) = [85, 65535, 21845, 13107, 3855, 255, 0, 65450, 43690, 65450, 52360, 65518, 61600, 65530, 65280, 65450, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_85] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_52360] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_65518] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_61600] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_65530] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450_65520] at hf
      exact absurd hf (by decide)

theorem s_49344_16191 : fnd [60136] 2 (16191 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_65535 : fnd [60136] 2 (65535 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_21845 : fnd [60136] 2 (21845 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_13107 : fnd [60136] 2 (13107 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_3855 : fnd [60136] 2 (3855 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_255 : fnd [60136] 2 (255 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_32896 : fnd [60136] 2 (32896 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_60138 : fnd [60136] 2 (60138 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_49152 : fnd [60136] 2 (49152 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_65472 : fnd [60136] 2 (65472 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_34952 : fnd [60136] 2 (34952 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_61166 : fnd [60136] 2 (61166 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_41120 : fnd [60136] 2 (41120 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_64250 : fnd [60136] 2 (64250 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_43520 : fnd [60136] 2 (43520 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_65450 : fnd [60136] 2 (65450 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_64764 : fnd [60136] 2 (64764 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_52224 : fnd [60136] 2 (52224 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_65484 : fnd [60136] 2 (65484 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_61440 : fnd [60136] 2 (61440 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344_65520 : fnd [60136] 2 (65520 :: 49344 :: 0 :: inputs) = false := by decide +kernel
theorem s_49344 : fnd [60136] 3 (49344 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (49344 :: 0 :: inputs)).1 h
  have hcs : cands (49344 :: 0 :: inputs) = [16191, 65535, 21845, 13107, 3855, 255, 0, 49344, 32896, 60138, 49344, 52428, 49344, 61680, 49152, 65472, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_16191] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_32896] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_60138] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_49152] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_65472] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344_65520] at hf
      exact absurd hf (by decide)

theorem s_64764_771 : fnd [60136] 2 (771 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_65535 : fnd [60136] 2 (65535 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_21845 : fnd [60136] 2 (21845 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_13107 : fnd [60136] 2 (13107 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_3855 : fnd [60136] 2 (3855 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_255 : fnd [60136] 2 (255 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_43176 : fnd [60136] 2 (43176 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_65278 : fnd [60136] 2 (65278 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_64512 : fnd [60136] 2 (64512 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_65532 : fnd [60136] 2 (65532 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_34952 : fnd [60136] 2 (34952 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_61166 : fnd [60136] 2 (61166 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_41120 : fnd [60136] 2 (41120 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_64250 : fnd [60136] 2 (64250 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_43520 : fnd [60136] 2 (43520 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_65450 : fnd [60136] 2 (65450 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_49344 : fnd [60136] 2 (49344 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_52224 : fnd [60136] 2 (52224 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_65484 : fnd [60136] 2 (65484 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_61440 : fnd [60136] 2 (61440 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764_65520 : fnd [60136] 2 (65520 :: 64764 :: 0 :: inputs) = false := by decide +kernel
theorem s_64764 : fnd [60136] 3 (64764 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (64764 :: 0 :: inputs)).1 h
  have hcs : cands (64764 :: 0 :: inputs) = [771, 65535, 21845, 13107, 3855, 255, 0, 64764, 43176, 65278, 52428, 64764, 61680, 64764, 64512, 65532, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_771] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_43176] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_65278] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_64512] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_65532] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764_65520] at hf
      exact absurd hf (by decide)

theorem s_52224_13311 : fnd [60136] 2 (13311 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_65535 : fnd [60136] 2 (65535 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_21845 : fnd [60136] 2 (21845 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_13107 : fnd [60136] 2 (13107 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_3855 : fnd [60136] 2 (3855 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_255 : fnd [60136] 2 (255 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_34816 : fnd [60136] 2 (34816 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_61098 : fnd [60136] 2 (61098 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_49152 : fnd [60136] 2 (49152 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_64752 : fnd [60136] 2 (64752 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_34952 : fnd [60136] 2 (34952 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_61166 : fnd [60136] 2 (61166 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_41120 : fnd [60136] 2 (41120 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_64250 : fnd [60136] 2 (64250 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_43520 : fnd [60136] 2 (43520 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_65450 : fnd [60136] 2 (65450 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_49344 : fnd [60136] 2 (49344 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_64764 : fnd [60136] 2 (64764 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_65484 : fnd [60136] 2 (65484 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_61440 : fnd [60136] 2 (61440 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224_65520 : fnd [60136] 2 (65520 :: 52224 :: 0 :: inputs) = false := by decide +kernel
theorem s_52224 : fnd [60136] 3 (52224 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (52224 :: 0 :: inputs)).1 h
  have hcs : cands (52224 :: 0 :: inputs) = [13311, 65535, 21845, 13107, 3855, 255, 0, 52224, 34816, 61098, 52224, 52428, 49152, 64752, 52224, 65280, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_13311] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_34816] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_61098] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_49152] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_64752] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224_65520] at hf
      exact absurd hf (by decide)

theorem s_65484_51 : fnd [60136] 2 (51 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_65535 : fnd [60136] 2 (65535 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_21845 : fnd [60136] 2 (21845 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_13107 : fnd [60136] 2 (13107 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_3855 : fnd [60136] 2 (3855 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_255 : fnd [60136] 2 (255 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_43656 : fnd [60136] 2 (43656 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_65518 : fnd [60136] 2 (65518 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_61632 : fnd [60136] 2 (61632 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_65532 : fnd [60136] 2 (65532 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_34952 : fnd [60136] 2 (34952 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_61166 : fnd [60136] 2 (61166 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_41120 : fnd [60136] 2 (41120 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_64250 : fnd [60136] 2 (64250 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_43520 : fnd [60136] 2 (43520 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_65450 : fnd [60136] 2 (65450 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_49344 : fnd [60136] 2 (49344 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_64764 : fnd [60136] 2 (64764 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_52224 : fnd [60136] 2 (52224 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_61440 : fnd [60136] 2 (61440 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484_65520 : fnd [60136] 2 (65520 :: 65484 :: 0 :: inputs) = false := by decide +kernel
theorem s_65484 : fnd [60136] 3 (65484 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (65484 :: 0 :: inputs)).1 h
  have hcs : cands (65484 :: 0 :: inputs) = [51, 65535, 21845, 13107, 3855, 255, 0, 65484, 43656, 65518, 52428, 65484, 61632, 65532, 65280, 65484, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_51] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_43656] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_65518] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_61632] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_65532] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484_65520] at hf
      exact absurd hf (by decide)

theorem s_61440_4095 : fnd [60136] 2 (4095 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_65535 : fnd [60136] 2 (65535 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_21845 : fnd [60136] 2 (21845 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_13107 : fnd [60136] 2 (13107 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_3855 : fnd [60136] 2 (3855 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_255 : fnd [60136] 2 (255 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_40960 : fnd [60136] 2 (40960 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_64170 : fnd [60136] 2 (64170 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_49152 : fnd [60136] 2 (49152 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_64716 : fnd [60136] 2 (64716 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_34952 : fnd [60136] 2 (34952 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_61166 : fnd [60136] 2 (61166 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_41120 : fnd [60136] 2 (41120 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_64250 : fnd [60136] 2 (64250 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_43520 : fnd [60136] 2 (43520 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_65450 : fnd [60136] 2 (65450 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_49344 : fnd [60136] 2 (49344 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_64764 : fnd [60136] 2 (64764 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_52224 : fnd [60136] 2 (52224 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_65484 : fnd [60136] 2 (65484 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440_65520 : fnd [60136] 2 (65520 :: 61440 :: 0 :: inputs) = false := by decide +kernel
theorem s_61440 : fnd [60136] 3 (61440 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (61440 :: 0 :: inputs)).1 h
  have hcs : cands (61440 :: 0 :: inputs) = [4095, 65535, 21845, 13107, 3855, 255, 0, 61440, 40960, 64170, 49152, 64716, 61440, 61680, 61440, 65280, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_4095] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_40960] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_64170] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_49152] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_64716] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440_65520] at hf
      exact absurd hf (by decide)

theorem s_65520_15 : fnd [60136] 2 (15 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_65535 : fnd [60136] 2 (65535 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_21845 : fnd [60136] 2 (21845 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_13107 : fnd [60136] 2 (13107 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_3855 : fnd [60136] 2 (3855 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_255 : fnd [60136] 2 (255 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_43680 : fnd [60136] 2 (43680 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_65530 : fnd [60136] 2 (65530 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_52416 : fnd [60136] 2 (52416 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_65532 : fnd [60136] 2 (65532 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_34952 : fnd [60136] 2 (34952 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_61166 : fnd [60136] 2 (61166 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_41120 : fnd [60136] 2 (41120 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_64250 : fnd [60136] 2 (64250 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_43520 : fnd [60136] 2 (43520 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_65450 : fnd [60136] 2 (65450 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_49344 : fnd [60136] 2 (49344 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_64764 : fnd [60136] 2 (64764 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_52224 : fnd [60136] 2 (52224 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_65484 : fnd [60136] 2 (65484 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520_61440 : fnd [60136] 2 (61440 :: 65520 :: 0 :: inputs) = false := by decide +kernel
theorem s_65520 : fnd [60136] 3 (65520 :: 0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 2 (65520 :: 0 :: inputs)).1 h
  have hcs : cands (65520 :: 0 :: inputs) = [15, 65535, 21845, 13107, 3855, 255, 0, 65520, 43680, 65530, 52416, 65532, 61680, 65520, 65280, 65520, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_15] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_43680] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_65530] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_52416] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_65532] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn

theorem search_empty : fnd [60136] 4 (0 :: inputs) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨c, hc, hcase⟩ := (fnd_succ [60136] 3 (0 :: inputs)).1 h
  have hcs : cands (0 :: inputs) = [65535, 21845, 13107, 3855, 255, 0, 43690, 0, 52428, 0, 61680, 0, 65280, 34952, 61166, 41120, 64250, 43520, 65450, 49344, 64764, 52224, 65484, 61440, 65520] := by decide +kernel
  rw [hcs] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65535] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_21845] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_13107] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_3855] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_255] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨hn, _⟩
    · exact absurd ht (by decide)
    · exact absurd (by decide) hn
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_34952] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61166] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_41120] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64250] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_43520] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65450] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_49344] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_64764] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_52224] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65484] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_61440] at hf
      exact absurd hf (by decide)
  · rcases hcase with ht | ⟨_, hf⟩
    · exact absurd ht (by decide)
    · rw [s_65520] at hf
      exact absurd hf (by decide)

theorem lower : ¬ HasCircuitSize 4 paw 4 := by
  rintro ⟨C, ok, hsz, hev⟩
  have hw : ∀ x : Fin 4 → Bool,
      C.eval (List.ofFn x) = tb x ((codesFrom C.gates inputs).getD C.output 0) := by
    intro x
    show (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
    rw [ofFn_codes, wires_codes x C.gates inputs ok, getD_map_tb]
  have hlt : (codesFrom C.gates inputs).getD C.output 0 < 65536 := by
    have hm := getD_mem (codesFrom C.gates inputs) C.output
    rcases List.mem_cons.1 hm with e | hm
    · rw [e]; norm_num
    · exact codes_lt C.gates inputs ok (by decide) _ hm
  have e : (codesFrom C.gates inputs).getD C.output 0 = 60136 := by
    apply code_inj _ _ hlt (by norm_num)
    intro x
    rw [← hw x, hev x, paw_code]
  have := search_sound [60136] C.gates inputs 4 C.output ok hsz (by rw [e]; exact List.mem_singleton.2 rfl)
  rcases this with hh | hf
  · revert hh
    unfold Hit
    decide
  · rw [search_empty] at hf
    exact absurd hf (by decide)

def pawC : List Gate :=
  [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [6, 7]⟩]

theorem pawC_ok : ∀ g ∈ pawC, Ok g := by
  intro g hg
  simp only [pawC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp [Ok]

theorem upper : HasCircuitSize 4 paw 5 := by
  refine ⟨⟨pawC, 8⟩, pawC_ok, by decide, ?_⟩
  intro x
  show (wiresFrom pawC (List.ofFn x)).getD 8 false = _
  rw [ofFn_codes, wires_codes x pawC inputs pawC_ok, getD_map_tb, paw_code]
  rfl

end PEqualNP.Outside.Meta138

theorem PEqualNP.Outside.L_meta_138 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · intro h
    by_contra hs
    obtain ⟨C, ok, hsz, hev⟩ := h
    exact PEqualNP.Outside.Meta138.lower ⟨C, ok, by omega, hev⟩
  · intro hs
    obtain ⟨C, ok, hsz, hev⟩ := PEqualNP.Outside.Meta138.upper
    exact ⟨C, ok, by omega, hev⟩
