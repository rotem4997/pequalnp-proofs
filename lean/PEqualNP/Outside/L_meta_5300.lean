import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5300

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def inp (s a b : Bool) : List Bool :=
  [a, s, false, !s, b, false, false, false, false, !a]

def gateVal (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [gateVal g w]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp [step]
    omega

lemma run_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma step_congr_on (P : ℕ → Prop) (g : Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, P i → w1.getD i false = w2.getD i false)
    (hg : gateVal g w1 = gateVal g w2) :
    (step w1 g).length = (step w2 g).length ∧
      ∀ i, P i → (step w1 g).getD i false = (step w2 g).getD i false := by
  refine ⟨by simp [step, hlen], ?_⟩
  intro i hi
  by_cases hlt : i < w1.length
  · have hlt2 : i < w2.length := hlen ▸ hlt
    rw [step, step, List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt2]
    exact hw i hi
  · by_cases heq : i = w1.length
    · subst heq
      have h1 : (w1 ++ [gateVal g w1]).getD w1.length false = gateVal g w1 := by
        simp [List.getD_eq_getElem?_getD]
      have h2 : (w2 ++ [gateVal g w2]).getD w1.length false = gateVal g w2 := by
        rw [hlen]
        simp [List.getD_eq_getElem?_getD]
      rw [step, step, h1, h2, hg]
    · have hgt1 : (w1 ++ [gateVal g w1]).length ≤ i := by simp; omega
      have hgt2 : (w2 ++ [gateVal g w2]).length ≤ i := by simp; omega
      rw [step, step, List.getD_eq_default _ _ hgt1, List.getD_eq_default _ _ hgt2]

lemma run_congr_on (P : ℕ → Prop) (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, P i → w1.getD i false = w2.getD i false)
    (hgs : ∀ g ∈ gs, ∀ i ∈ g.inputs, P i) :
    (run gs w1).length = (run gs w2).length ∧
      ∀ i, P i → (run gs w1).getD i false = (run gs w2).getD i false := by
  induction gs generalizing w1 w2 with
  | nil => exact ⟨hlen, hw⟩
  | cons g gs ih =>
    have hg : gateVal g w1 = gateVal g w2 := by
      unfold gateVal
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hw i (hgs g (List.mem_cons_self ..) i hi)
    obtain ⟨hlen', hw'⟩ := step_congr_on P g w1 w2 hlen hw hg
    exact ih (step w1 g) (step w2 g) hlen' hw' (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))

lemma gateVal_eq_of_no4 (g : Gate) (w1 w2 : List Bool)
    (hno4 : 4 ∉ g.inputs)
    (hw : ∀ i, i ≠ 4 → w1.getD i false = w2.getD i false) :
    gateVal g w1 = gateVal g w2 := by
  unfold gateVal
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hw i (fun h => hno4 (h ▸ hi))

lemma gateVal_with4 (g : Gate) (w : List Bool) (a b : Bool)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (h09 : 0 ∈ g.inputs ∨ 9 ∈ g.inputs)
    (h4 : 4 ∈ g.inputs)
    (hw0 : w.getD 0 false = a)
    (hw4 : w.getD 4 false = b)
    (hw9 : w.getD 9 false = !a) :
    (g.op = GateOp.and ∧ 0 ∈ g.inputs ∧ gateVal g w = (a && b)) ∨
    (g.op = GateOp.and ∧ 9 ∈ g.inputs ∧ gateVal g w = (!a && b)) ∨
    (g.op = GateOp.or ∧ 0 ∈ g.inputs ∧ gateVal g w = (a || b)) ∨
    (g.op = GateOp.or ∧ 9 ∈ g.inputs ∧ gateVal g w = (!a || b)) := by
  rcases hfan with ⟨hop, hlen⟩
  rcases g with ⟨op, ins⟩
  simp only at hop hlen hnot h09 h4 ⊢
  match ins with
  | [] => simp at h4
  | [u] =>
    simp only [List.mem_singleton] at h4 h09
    subst h4
    rcases h09 with h | h <;> omega
  | [u, v] =>
    have hop' : op = GateOp.and ∨ op = GateOp.or := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · have := hnot rfl; simp at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4 h09
    rcases hop' with rfl | rfl
    · rcases h09 with (rfl | rfl) | (rfl | rfl)
      · rcases h4 with h | rfl
        · omega
        · exact Or.inl ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.all, id, hw0, hw4, Bool.and_true]⟩
      · rcases h4 with rfl | h
        · exact Or.inl ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.all, id, hw0, hw4, Bool.and_true, Bool.and_comm]⟩
        · omega
      · rcases h4 with h | rfl
        · omega
        · exact Or.inr (Or.inl ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.all, id, hw9, hw4, Bool.and_true]⟩)
      · rcases h4 with rfl | h
        · exact Or.inr (Or.inl ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.all, id, hw9, hw4, Bool.and_true, Bool.true_and, Bool.and_comm]⟩)
        · omega
    · rcases h09 with (rfl | rfl) | (rfl | rfl)
      · rcases h4 with h | rfl
        · omega
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.any, id, hw0, hw4, Bool.or_false]⟩))
      · rcases h4 with rfl | h
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.any, id, hw0, hw4, Bool.or_false, Bool.or_comm]⟩))
        · omega
      · rcases h4 with h | rfl
        · omega
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.any, id, hw9, hw4, Bool.or_false]⟩))
      · rcases h4 with rfl | h
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, by simp, by simp only [gateVal, GateOp.eval, List.map, List.any, id, hw9, hw4, Bool.or_false, Bool.false_or, Bool.or_comm]⟩))
        · omega
  | _ :: _ :: _ :: _ => simp at hlen

lemma gate_spec4 (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (h09 : 0 ∈ g.inputs ∨ 9 ∈ g.inputs)
    (h4 : 4 ∈ g.inputs) :
    (∀ w a b, w.getD 0 false = a → w.getD 4 false = b → w.getD 9 false = !a → gateVal g w = (a && b)) ∨
    (∀ w a b, w.getD 0 false = a → w.getD 4 false = b → w.getD 9 false = !a → gateVal g w = (!a && b)) ∨
    (∀ w a b, w.getD 0 false = a → w.getD 4 false = b → w.getD 9 false = !a → gateVal g w = (a || b)) ∨
    (∀ w a b, w.getD 0 false = a → w.getD 4 false = b → w.getD 9 false = !a → gateVal g w = (!a || b)) := by
  have hbase := gateVal_with4 g (inp false false false) false false hfan hnot h09 h4 rfl rfl rfl
  rcases hbase with ⟨hop, h0, _⟩ | ⟨hop, h9, _⟩ | ⟨hop, h0, _⟩ | ⟨hop, h9, _⟩
  · left
    intro w a b hw0 hw4 hw9
    rcases gateVal_with4 g w a b hfan hnot h09 h4 hw0 hw4 hw9 with ⟨_, _, h⟩ | ⟨_, h9', _⟩ | ⟨h', _, _⟩ | ⟨h', _, _⟩
    · exact h
    · exfalso
      rcases g with ⟨op, ins⟩
      simp only at hfan h0 h9' h4
      match ins with
      | [u, v] =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9' h4
        omega
      | [] => simp at h4
      | [_] => simp only [List.mem_singleton] at h0 h4; omega
      | _ :: _ :: _ :: _ => simp at hfan
    · rw [hop] at h'; cases h'
    · rw [hop] at h'; cases h'
  · right; left
    intro w a b hw0 hw4 hw9
    rcases gateVal_with4 g w a b hfan hnot h09 h4 hw0 hw4 hw9 with ⟨_, h0', _⟩ | ⟨_, _, h⟩ | ⟨h', _, _⟩ | ⟨h', _, _⟩
    · exfalso
      rcases g with ⟨op, ins⟩
      simp only at hfan h9 h0' h4
      match ins with
      | [u, v] =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h9 h0' h4
        omega
      | [] => simp at h4
      | [_] => simp only [List.mem_singleton] at h9 h4; omega
      | _ :: _ :: _ :: _ => simp at hfan
    · exact h
    · rw [hop] at h'; cases h'
    · rw [hop] at h'; cases h'
  · right; right; left
    intro w a b hw0 hw4 hw9
    rcases gateVal_with4 g w a b hfan hnot h09 h4 hw0 hw4 hw9 with ⟨h', _, _⟩ | ⟨h', _, _⟩ | ⟨_, _, h⟩ | ⟨_, h9', _⟩
    · rw [hop] at h'; cases h'
    · rw [hop] at h'; cases h'
    · exact h
    · exfalso
      rcases g with ⟨op, ins⟩
      simp only at hfan h0 h9' h4
      match ins with
      | [u, v] =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9' h4
        omega
      | [] => simp at h4
      | [_] => simp only [List.mem_singleton] at h0 h4; omega
      | _ :: _ :: _ :: _ => simp at hfan
  · right; right; right
    intro w a b hw0 hw4 hw9
    rcases gateVal_with4 g w a b hfan hnot h09 h4 hw0 hw4 hw9 with ⟨h', _, _⟩ | ⟨h', _, _⟩ | ⟨_, h0', _⟩ | ⟨_, _, h⟩
    · rw [hop] at h'; cases h'
    · rw [hop] at h'; cases h'
    · exfalso
      rcases g with ⟨op, ins⟩
      simp only at hfan h9 h0' h4
      match ins with
      | [u, v] =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h9 h0' h4
        omega
      | [] => simp at h4
      | [_] => simp only [List.mem_singleton] at h9 h4; omega
      | _ :: _ :: _ :: _ => simp at hfan
    · exact h

end PEqualNP.Outside.L_meta_5300

theorem PEqualNP.Outside.L_meta_5300 : ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → (∀ x9 ∈ x7.gates, x9.op = PEqualNP.CircuitLowerBounds.GateOp.not → x9.inputs.length ≤ (1 : ℕ)) → (∀ x10 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x10.inputs ∧ (9 : ℕ) ∉ x10.inputs) → (∀ x11 ∈ [x4, x5], (0 : ℕ) ∈ x11.inputs ∨ (9 : ℕ) ∈ x11.inputs) → (∀ (x12 x13 x14 : Bool), x7.eval [x13, x12, Bool.false, !x12, x14, Bool.false, Bool.false, Bool.false, Bool.false, !x13] = if x12 = Bool.true then x13 else x14) → ∃ x13 ∈ x1 ++ x2 ++ x3, (4 : ℕ) ∈ x13.inputs := by
  intro x1 x2 x3 x4 x5 x6
  dsimp only
  intro hFan hNot hNo09 h45 hEval
  by_contra hNo4
  push_neg at hNo4
  let C : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 }
  have hEvalRun : ∀ s a b, (PEqualNP.Outside.L_meta_5300.run (x1 ++ x4 :: (x2 ++ x5 :: x3)) (PEqualNP.Outside.L_meta_5300.inp s a b)).getD x6 false = if s = true then a else b :=
    fun s a b => hEval s a b
  have hx6_0 : x6 ≠ 0 := by
    intro h0
    have h := hEvalRun false false true
    rw [h0, PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 0 (by simp [PEqualNP.Outside.L_meta_5300.inp])] at h
    simp [PEqualNP.Outside.L_meta_5300.inp] at h
  have hx6_4 : x6 ≠ 4 := by
    intro h4
    have h := hEvalRun true true false
    rw [h4, PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 4 (by simp [PEqualNP.Outside.L_meta_5300.inp])] at h
    simp [PEqualNP.Outside.L_meta_5300.inp] at h
  have hx6_9 : x6 ≠ 9 := by
    intro h9
    have h := hEvalRun true true false
    rw [h9, PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 9 (by simp [PEqualNP.Outside.L_meta_5300.inp])] at h
    simp [PEqualNP.Outside.L_meta_5300.inp] at h
  have h1_clean : ∀ g ∈ x1, ∀ i ∈ g.inputs, i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9 := by
    intro g hg i hi
    have hmem : g ∈ x1 ++ x2 ++ x3 := List.mem_append_left x3 (List.mem_append_left x2 hg)
    have h09 := hNo09 g hmem
    have h4 := hNo4 g hmem
    exact ⟨fun h => h09.1 (h ▸ hi), fun h => h4 (h ▸ hi), fun h => h09.2 (h ▸ hi)⟩
  have h2_clean : ∀ g ∈ x2, ∀ i ∈ g.inputs, i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9 := by
    intro g hg i hi
    have hmem : g ∈ x1 ++ x2 ++ x3 := List.mem_append_left x3 (List.mem_append_right x1 hg)
    have h09 := hNo09 g hmem
    have h4 := hNo4 g hmem
    exact ⟨fun h => h09.1 (h ▸ hi), fun h => h4 (h ▸ hi), fun h => h09.2 (h ▸ hi)⟩
  have h3_clean : ∀ g ∈ x3, ∀ i ∈ g.inputs, i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9 := by
    intro g hg i hi
    have hmem : g ∈ x1 ++ x2 ++ x3 := List.mem_append_right (x1 ++ x2) hg
    have h09 := hNo09 g hmem
    have h4 := hNo4 g hmem
    exact ⟨fun h => h09.1 (h ▸ hi), fun h => h4 (h ▸ hi), fun h => h09.2 (h ▸ hi)⟩
  let w1 := fun s a b => PEqualNP.Outside.L_meta_5300.run x1 (PEqualNP.Outside.L_meta_5300.inp s a b)
  let w2 := fun s a b => PEqualNP.Outside.L_meta_5300.run x2 (PEqualNP.Outside.L_meta_5300.step (w1 s a b) x4)
  have hw1_0 : ∀ s a b, (w1 s a b).getD 0 false = a := fun s a b => by
    rw [PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 0 (by simp [PEqualNP.Outside.L_meta_5300.inp])]; rfl
  have hw1_4 : ∀ s a b, (w1 s a b).getD 4 false = b := fun s a b => by
    rw [PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 4 (by simp [PEqualNP.Outside.L_meta_5300.inp])]; rfl
  have hw1_9 : ∀ s a b, (w1 s a b).getD 9 false = !a := fun s a b => by
    rw [PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 9 (by simp [PEqualNP.Outside.L_meta_5300.inp])]; rfl
  have hw2_0 : ∀ s a b, (w2 s a b).getD 0 false = a := fun s a b => by
    have hlen : 0 < (PEqualNP.Outside.L_meta_5300.step (w1 s a b) x4).length := by
      simp [PEqualNP.Outside.L_meta_5300.step, w1, PEqualNP.Outside.L_meta_5300.run_length, PEqualNP.Outside.L_meta_5300.inp]
    rw [PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 0 hlen]
    have hlen1 : 0 < (w1 s a b).length := by
      simp [w1, PEqualNP.Outside.L_meta_5300.run_length, PEqualNP.Outside.L_meta_5300.inp]
    rw [PEqualNP.Outside.L_meta_5300.step, List.getD_append _ _ _ _ hlen1]
    exact hw1_0 s a b
  have hw2_4 : ∀ s a b, (w2 s a b).getD 4 false = b := fun s a b => by
    have hlen : 4 < (PEqualNP.Outside.L_meta_5300.step (w1 s a b) x4).length := by
      simp [PEqualNP.Outside.L_meta_5300.step, w1, PEqualNP.Outside.L_meta_5300.run_length, PEqualNP.Outside.L_meta_5300.inp]; omega
    rw [PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 4 hlen]
    have hlen1 : 4 < (w1 s a b).length := by
      simp [w1, PEqualNP.Outside.L_meta_5300.run_length, PEqualNP.Outside.L_meta_5300.inp]; omega
    rw [PEqualNP.Outside.L_meta_5300.step, List.getD_append _ _ _ _ hlen1]
    exact hw1_4 s a b
  have hw2_9 : ∀ s a b, (w2 s a b).getD 9 false = !a := fun s a b => by
    have hlen : 9 < (PEqualNP.Outside.L_meta_5300.step (w1 s a b) x4).length := by
      simp [PEqualNP.Outside.L_meta_5300.step, w1, PEqualNP.Outside.L_meta_5300.run_length, PEqualNP.Outside.L_meta_5300.inp]; omega
    rw [PEqualNP.Outside.L_meta_5300.run_getD_lt _ _ 9 hlen]
    have hlen1 : 9 < (w1 s a b).length := by
      simp [w1, PEqualNP.Outside.L_meta_5300.run_length, PEqualNP.Outside.L_meta_5300.inp]; omega
    rw [PEqualNP.Outside.L_meta_5300.step, List.getD_append _ _ _ _ hlen1]
    exact hw1_9 s a b
  have hSameEval : ∀ s a1 b1 a2 b2,
      PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 s a1 b1) = PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 s a2 b2) →
      PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 s a1 b1) = PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 s a2 b2) →
      (if s = true then a1 else b1) = (if s = true then a2 else b2) := by
    intro s a1 b1 a2 b2 hv4 hv5
    have hinp : ∀ i, (i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9) →
        (PEqualNP.Outside.L_meta_5300.inp s a1 b1).getD i false = (PEqualNP.Outside.L_meta_5300.inp s a2 b2).getD i false := by
      intro i ⟨h0, h4, h9⟩
      match i with
      | 0 => exact (h0 rfl).elim
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
      | 4 => exact (h4 rfl).elim
      | 5 => rfl
      | 6 => rfl
      | 7 => rfl
      | 8 => rfl
      | 9 => exact (h9 rfl).elim
      | n + 10 => rfl
    obtain ⟨hl1, hw1eq⟩ := PEqualNP.Outside.L_meta_5300.run_congr_on (fun i => i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9) x1
      (PEqualNP.Outside.L_meta_5300.inp s a1 b1) (PEqualNP.Outside.L_meta_5300.inp s a2 b2) rfl hinp h1_clean
    obtain ⟨hl1', hw1eq'⟩ := PEqualNP.Outside.L_meta_5300.step_congr_on (fun i => i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9) x4 _ _ hl1 hw1eq hv4
    obtain ⟨hl2, hw2eq⟩ := PEqualNP.Outside.L_meta_5300.run_congr_on (fun i => i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9) x2 _ _ hl1' hw1eq' h2_clean
    obtain ⟨hl2', hw2eq'⟩ := PEqualNP.Outside.L_meta_5300.step_congr_on (fun i => i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9) x5 _ _ hl2 hw2eq hv5
    obtain ⟨_, hw3eq⟩ := PEqualNP.Outside.L_meta_5300.run_congr_on (fun i => i ≠ 0 ∧ i ≠ 4 ∧ i ≠ 9) x3 _ _ hl2' hw2eq' h3_clean
    have hfinal := hw3eq x6 ⟨hx6_0, hx6_4, hx6_9⟩
    have hrew : ∀ a b, PEqualNP.Outside.L_meta_5300.run x3 (PEqualNP.Outside.L_meta_5300.step (w2 s a b) x5) =
        PEqualNP.Outside.L_meta_5300.run (x1 ++ x4 :: (x2 ++ x5 :: x3)) (PEqualNP.Outside.L_meta_5300.inp s a b) := by
      intro a b
      rw [PEqualNP.Outside.L_meta_5300.run_append, PEqualNP.Outside.L_meta_5300.run_cons,
          PEqualNP.Outside.L_meta_5300.run_append, PEqualNP.Outside.L_meta_5300.run_cons]
    rw [hrew a1 b1, hrew a2 b2, hEvalRun s a1 b1, hEvalRun s a2 b2] at hfinal
    exact hfinal
  have hSame4_of_a : ∀ s a,
      (w1 s a false).length = (w1 s a true).length ∧
      ∀ i, i ≠ 4 → (w1 s a false).getD i false = (w1 s a true).getD i false := by
    intro s a
    apply PEqualNP.Outside.L_meta_5300.run_congr_on (fun i => i ≠ 4) x1
      (PEqualNP.Outside.L_meta_5300.inp s a false) (PEqualNP.Outside.L_meta_5300.inp s a true) rfl
    · intro i hi
      match i with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
      | 4 => exact (hi rfl).elim
      | 5 => rfl
      | 6 => rfl
      | 7 => rfl
      | 8 => rfl
      | 9 => rfl
      | n + 10 => rfl
    · intro g hg i hi
      exact (h1_clean g hg i hi).2.1
  have hSameW2_of_v4 : ∀ s a,
      PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 s a false) = PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 s a true) →
      ∀ i, i ≠ 4 → (w2 s a false).getD i false = (w2 s a true).getD i false := by
    intro s a hv4
    obtain ⟨hl1, hw1eq⟩ := hSame4_of_a s a
    obtain ⟨hl1', hw1eq'⟩ := PEqualNP.Outside.L_meta_5300.step_congr_on (fun i => i ≠ 4) x4 _ _ hl1 hw1eq hv4
    obtain ⟨_, hw2eq⟩ := PEqualNP.Outside.L_meta_5300.run_congr_on (fun i => i ≠ 4) x2 _ _ hl1' hw1eq' (fun g hg i hi => (h2_clean g hg i hi).2.1)
    exact hw2eq
  have hx4_mem : x4 ∈ C.gates := List.mem_append_right x1 (List.mem_cons_self ..)
  have hx5_mem : x5 ∈ C.gates := List.mem_append_right x1 (List.mem_cons_of_mem x4 (List.mem_append_right x2 (List.mem_cons_self ..)))
  have hFan4 := hFan x4 hx4_mem
  have hFan5 := hFan x5 hx5_mem
  have hNot4 := hNot x4 hx4_mem
  have hNot5 := hNot x5 hx5_mem
  have h09_4 := h45 x4 (by simp)
  have h09_5 := h45 x5 (by simp)
  by_cases h4in4 : 4 ∈ x4.inputs
  · by_cases h4in5 : 4 ∈ x5.inputs
    · have hs4 := PEqualNP.Outside.L_meta_5300.gate_spec4 x4 hFan4 hNot4 h09_4 h4in4
      have hs5 := PEqualNP.Outside.L_meta_5300.gate_spec4 x5 hFan5 hNot5 h09_5 h4in5
      rcases hs4 with f4 | f4 | f4 | f4 <;> rcases hs5 with f5 | f5 | f5 | f5
      · have hc := hSameEval true false false true false
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false false true false
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false true true false
          (by rw [f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval false false false false true
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false false true false
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false false true false
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval false true false true true
          (by rw [f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false false true true
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false true true false
          (by rw [f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval false true false true true
          (by rw [f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false true true true
          (by rw [f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false true true true
          (by rw [f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval false false false false true
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false false true true
          (by rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false true true true
          (by rw [f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
      · have hc := hSameEval true false true true true
          (by rw [f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl)
          (by rw [f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl)
        simp at hc
    · have hs4 := PEqualNP.Outside.L_meta_5300.gate_spec4 x4 hFan4 hNot4 h09_4 h4in4
      rcases hs4 with f4 | f4 | f4 | f4
      · have hv4 : PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false false false) = PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false false true) := by
          rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl
        have hv5 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x5 _ _ h4in5 (hSameW2_of_v4 false false hv4)
        have hc := hSameEval false false false false true hv4 hv5
        simp at hc
      · have hv4 : PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false true false) = PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false true true) := by
          rw [f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl
        have hv5 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x5 _ _ h4in5 (hSameW2_of_v4 false true hv4)
        have hc := hSameEval false true false true true hv4 hv5
        simp at hc
      · have hv4 : PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false true false) = PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false true true) := by
          rw [f4 _ true false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ true true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl
        have hv5 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x5 _ _ h4in5 (hSameW2_of_v4 false true hv4)
        have hc := hSameEval false true false true true hv4 hv5
        simp at hc
      · have hv4 : PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false false false) = PEqualNP.Outside.L_meta_5300.gateVal x4 (w1 false false true) := by
          rw [f4 _ false false (hw1_0 ..) (hw1_4 ..) (hw1_9 ..), f4 _ false true (hw1_0 ..) (hw1_4 ..) (hw1_9 ..)]; rfl
        have hv5 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x5 _ _ h4in5 (hSameW2_of_v4 false false hv4)
        have hc := hSameEval false false false false true hv4 hv5
        simp at hc
  · by_cases h4in5 : 4 ∈ x5.inputs
    · have hs5 := PEqualNP.Outside.L_meta_5300.gate_spec4 x5 hFan5 hNot5 h09_5 h4in5
      rcases hs5 with f5 | f5 | f5 | f5
      · have hv4 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x4 _ _ h4in4 (hSame4_of_a false false).2
        have hv5 : PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false false false) = PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false false true) := by
          rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl
        have hc := hSameEval false false false false true hv4 hv5
        simp at hc
      · have hv4 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x4 _ _ h4in4 (hSame4_of_a false true).2
        have hv5 : PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false true false) = PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false true true) := by
          rw [f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl
        have hc := hSameEval false true false true true hv4 hv5
        simp at hc
      · have hv4 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x4 _ _ h4in4 (hSame4_of_a false true).2
        have hv5 : PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false true false) = PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false true true) := by
          rw [f5 _ true false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ true true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl
        have hc := hSameEval false true false true true hv4 hv5
        simp at hc
      · have hv4 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x4 _ _ h4in4 (hSame4_of_a false false).2
        have hv5 : PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false false false) = PEqualNP.Outside.L_meta_5300.gateVal x5 (w2 false false true) := by
          rw [f5 _ false false (hw2_0 ..) (hw2_4 ..) (hw2_9 ..), f5 _ false true (hw2_0 ..) (hw2_4 ..) (hw2_9 ..)]; rfl
        have hc := hSameEval false false false false true hv4 hv5
        simp at hc
    · have hv4 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x4 _ _ h4in4 (hSame4_of_a false false).2
      have hv5 := PEqualNP.Outside.L_meta_5300.gateVal_eq_of_no4 x5 _ _ h4in5 (hSameW2_of_v4 false false hv4)
      have hc := hSameEval false false false false true hv4 hv5
      simp at hc
