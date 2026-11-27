import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6050

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6050

theorem PEqualNP.Outside.L_meta_6050 : ∀ (x1 : ℕ) (x2 : List (BitVec x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x3 →     have x5 : List (BitVec x1) → List ℕ → BitVec x1 := fun (x5 : List (BitVec x1)) (x6 : List ℕ) => List.foldr (fun (x7 : ℕ) (x8 : BitVec x1) => x5.getD x7 (0 : BitVec x1) &&& x8) (~~~(0 : BitVec x1)) x6;     ∃ (x6 : List (BitVec x1)),       x6.length = List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.false Bool.true Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false) x3.gates ∧         (∀ (x7 : Fin x6.length),             have x8 : List (BitVec x1) := (0 : BitVec x1) :: x2 ++ List.take (↑x7) x6;             ∃ (x9 : List ℕ) (x10 : List ℕ), (∀ x11 ∈ x9 ++ x10, x11 < x8.length) ∧ x6.get x7 = x5 x8 x9 ||| x5 x8 x10) ∧           ∃ (x7 : List ℕ), (∀ x8 ∈ x7, x8 < ((0 : BitVec x1) :: x2 ++ x6).length) ∧ ∀ (x8 : Fin x1), (x5 ((0 : BitVec x1) :: x2 ++ x6) x7).getLsbD ↑x8 = x3.eval (List.map (fun (x9 : BitVec x1) => x9.getLsbD ↑x8) x2) := by
  intro m X C hC A
  classical
  have Abit : ∀ (l : List (BitVec m)) (ix : List ℕ) (b : ℕ), b < m → (A l ix).getLsbD b = ix.all fun i => (l.getD i 0).getLsbD b := by
    intro l ix b hb
    induction ix with
    | nil => simp [A, hb]
    | cons i ix ih =>
      simp only [A, List.foldr_cons, List.all_cons] at ih ⊢
      rw [BitVec.getLsbD_and, ih]
  let bx : ℕ → List Bool := fun b => X.map fun v => v.getLsbD b
  have hbx : ∀ b, (bx b).length = X.length := by intro b; simp [bx]
  let base := (0 : BitVec m) :: X
  let isOr : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn g.op false true false (fun _ => false) false
  have gext : ∀ (l l' : List (BitVec m)) (i : ℕ), i < l.length → (l ++ l').getD i 0 = l.getD i 0 := by
    intro l l' i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have Aext : ∀ (l l' : List (BitVec m)) (ix : List ℕ), (∀ i ∈ ix, i < l.length) → A (l ++ l') ix = A l ix := by
    intro l l' ix h
    induction ix with
    | nil => rfl
    | cons i ix ih =>
      simp only [A, List.foldr_cons] at ih ⊢
      rw [gext l l' i (h i List.mem_cons_self), ih fun j hj => h j (List.mem_cons_of_mem _ hj)]
  have key : ∀ k ≤ C.gates.length, ∃ (xs : List (BitVec m)) (L : ℕ → List ℕ), xs.length = List.countP isOr (C.gates.take k) ∧
      (∀ i : Fin xs.length, ∃ p q : List ℕ, (∀ j ∈ p ++ q, j < (base ++ xs.take i).length) ∧ xs.get i = A (base ++ xs.take i) p ||| A (base ++ xs.take i) q) ∧
      (∀ w, w < X.length + k → ∀ j ∈ L w, j < (base ++ xs).length) ∧
      ∀ b < m, ∀ w < X.length + k, (A (base ++ xs) (L w)).getLsbD b = (PEqualNP.Outside.L_meta_6050.run C.gates (bx b)).getD w false := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => [w + 1], by simp, fun i => i.elim0, ?_, ?_⟩
      · intro w hw j hj
        simp only [List.mem_singleton] at hj
        simp [base]; omega
      · intro b hb w hw
        have hw' : w < X.length := by omega
        rw [Abit _ _ _ hb, PEqualNP.Outside.L_meta_6050.run_input _ _ _ (by rw [hbx]; exact hw')]
        simp [base, bx, List.getD_eq_getElem?_getD, hw']
    | succ k ih =>
      intro hk
      obtain ⟨xs, L, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hk')
      have hop' : C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[k].op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hop
      have rg := fun b => PEqualNP.Outside.L_meta_6050.run_gate C.gates (bx b) k hk'
      simp only [hbx] at rg
      -- index lists for reads
      let rd : ℕ → List ℕ := fun i => if i < X.length + k then L i else [0]
      have rd1 : ∀ i, ∀ j ∈ rd i, j < (base ++ xs).length := by
        intro i j hj
        simp only [rd] at hj
        split_ifs at hj with h
        · exact h3 i h j hj
        · simp only [List.mem_singleton] at hj
          subst hj; simp [base]
      have rd2 : ∀ b < m, ∀ i, (A (base ++ xs) (rd i)).getLsbD b = if i < X.length + k then (PEqualNP.Outside.L_meta_6050.run C.gates (bx b)).getD i false else false := by
        intro b hb i
        simp only [rd]
        split_ifs with h
        · exact h4 b hb i h
        · rw [Abit _ _ _ hb]
          simp [base]
      rcases hop' with ho | ho
      · have hcount : List.countP isOr (C.gates.take (k + 1)) = List.countP isOr (C.gates.take k) := by
          rw [List.take_succ_eq_append_getElem hk', List.countP_append]
          have : isOr C.gates[k] = false := by simp only [isOr]; rw [ho]
          simp [this]
        refine ⟨xs, Function.update L (X.length + k) (C.gates[k].inputs.flatMap rd), by rw [hcount]; exact h1, h2, ?_, ?_⟩
        · intro w hw j hj
          by_cases hwk : w = X.length + k
          · subst hwk
            rw [Function.update_self, List.mem_flatMap] at hj
            obtain ⟨i, _, hj⟩ := hj
            exact rd1 i j hj
          · rw [Function.update_of_ne hwk] at hj
            exact h3 w (by omega) j hj
        · intro b hb w hw
          by_cases hwk : w = X.length + k
          · subst hwk
            rw [Function.update_self, rg b, ho, Abit _ _ _ hb, List.all_flatMap]
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_map]
            congr 1
            funext i
            rw [← Abit _ _ _ hb, rd2 b hb i]
            rfl
          · rw [Function.update_of_ne hwk]
            exact h4 b hb w (by omega)
      · have hcount : List.countP isOr (C.gates.take (k + 1)) = List.countP isOr (C.gates.take k) + 1 := by
          rw [List.take_succ_eq_append_getElem hk', List.countP_append]
          have : isOr C.gates[k] = true := by simp only [isOr]; rw [ho]
          simp [this]
        have two : ∃ p q : List ℕ, (∀ j ∈ p ++ q, j < (base ++ xs).length) ∧ ∀ b < m, ((A (base ++ xs) p).getLsbD b || (A (base ++ xs) q).getLsbD b) = (PEqualNP.Outside.L_meta_6050.run C.gates (bx b)).getD (X.length + k) false := by
          have z0 : ∀ b < m, (A (base ++ xs) [0]).getLsbD b = false := by
            intro b hb
            rw [Abit _ _ _ hb]; simp [base]
          have z1 : ∀ j ∈ [0], j < (base ++ xs).length := by
            intro j hj
            simp only [List.mem_singleton] at hj
            subst hj; simp [base]
          have jn : ∀ p q : List ℕ, (∀ j ∈ p, j < (base ++ xs).length) → (∀ j ∈ q, j < (base ++ xs).length) → ∀ j ∈ p ++ q, j < (base ++ xs).length := fun p q hp hq j hj => (List.mem_append.1 hj).elim (hp j) (hq j)
          generalize hl : C.gates[k].inputs = l at hlen
          rcases l with _ | ⟨i, _ | ⟨i', _ | ⟨i'', l⟩⟩⟩
          · refine ⟨[0], [0], jn _ _ z1 z1, fun b hb => ?_⟩
            rw [z0 b hb, rg b, ho, hl]; rfl
          · refine ⟨rd i, [0], jn _ _ (rd1 i) z1, fun b hb => ?_⟩
            rw [z0 b hb, rd2 b hb i, rg b, ho, hl]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          · refine ⟨rd i, rd i', jn _ _ (rd1 i) (rd1 i'), fun b hb => ?_⟩
            rw [rd2 b hb i, rd2 b hb i', rg b, ho, hl]
            simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          · simp at hlen
        obtain ⟨p, q, hpq, hval⟩ := two
        let Z := A (base ++ xs) p ||| A (base ++ xs) q
        refine ⟨xs ++ [Z], Function.update L (X.length + k) [(base ++ xs).length], by rw [hcount]; simp [h1], ?_, ?_, ?_⟩
        · intro i
          have hi : (i : ℕ) < (xs ++ [Z]).length := i.isLt
          simp only [List.length_append, List.length_singleton] at hi
          rcases Nat.lt_or_ge i xs.length with h | h
          · have := h2 ⟨i, h⟩
            simp only [List.get_eq_getElem] at this ⊢
            rw [List.take_append_of_le_length (by omega), List.getElem_append_left h]
            exact this
          · have hh : (i : ℕ) = xs.length := by omega
            simp only [List.get_eq_getElem]
            have e1 : (xs ++ [Z])[(i : ℕ)]'i.isLt = Z := by
              rw [List.getElem_append_right (by omega)]; simp
            rw [e1, List.take_append_of_le_length (by omega), hh, List.take_length]
            exact ⟨p, q, hpq, rfl⟩
        · intro w hw j hj
          by_cases hwk : w = X.length + k
          · subst hwk
            rw [Function.update_self, List.mem_singleton] at hj
            subst hj; simp [base]
          · rw [Function.update_of_ne hwk] at hj
            have := h3 w (by omega) j hj
            rw [← List.append_assoc, List.length_append]; omega
        · intro b hb w hw
          by_cases hwk : w = X.length + k
          · subst hwk
            rw [Function.update_self, Abit _ _ _ hb, ← hval b hb, ← List.append_assoc]
            have : ((base ++ xs) ++ [Z]).getD (base ++ xs).length 0 = Z := by simp [List.getD_eq_getElem?_getD]
            simp only [List.all_cons, List.all_nil, Bool.and_true, this, Z, BitVec.getLsbD_or]
          · rw [Function.update_of_ne hwk, ← List.append_assoc, Aext _ _ _ (h3 w (by omega))]
            exact h4 b hb w (by omega)
  obtain ⟨xs, L, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  rw [List.take_length] at h1
  refine ⟨xs, h1, h2, if C.output < X.length + C.gates.length then L C.output else [0], ?_, fun b => ?_⟩
  · intro j hj
    split_ifs at hj with h
    · exact h3 _ h j hj
    · simp only [List.mem_singleton] at hj
      subst hj; simp
  · change _ = (PEqualNP.Outside.L_meta_6050.run C.gates (bx b)).getD C.output false
    split_ifs with h
    · exact h4 b b.isLt _ h
    · rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6050.run_length, hbx]; omega), Abit _ _ _ b.isLt]
      simp
