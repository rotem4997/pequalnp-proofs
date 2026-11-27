import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2116_1
    (hMono : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8),
          (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) →
      (∀ i : Fin C.size, (∀ w ∈ (C.gates.get i).inputs, w < 9 + (i : ℕ)) ∧
        (C.gates.get i).inputs.Nodup ∧
        ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (C.gates.get i).inputs.length = 1 ∨
          (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (C.gates.get i).inputs.length = 2)) →
      (∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) → ∃ i : Fin C.size,
        (∀ j : Fin C.size, (v : ℕ) ∈ (C.gates.get j).inputs ↔ j = i) ∧
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ i : Fin C.size, ∀ a ∈ (C.gates.get i).inputs, ∀ b ∈ (C.gates.get i).inputs,
        a ∈ ([4, 6, 7] : List ℕ) → b ∈ ([4, 6, 7] : List ℕ) → a = b) →
      (∀ i : Fin C.size, (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → False)
    (hNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8),
          (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) →
      (∀ i : Fin C.size, (∀ w ∈ (C.gates.get i).inputs, w < 9 + (i : ℕ)) ∧
        (C.gates.get i).inputs.Nodup ∧
        ((C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (C.gates.get i).inputs.length = 1 ∨
          (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧
            (C.gates.get i).inputs.length = 2)) →
      (∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) → ∃ i : Fin C.size,
        (∀ j : Fin C.size, (v : ℕ) ∈ (C.gates.get j).inputs ↔ j = i) ∧
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∀ i : Fin C.size, ∀ a ∈ (C.gates.get i).inputs, ∀ b ∈ (C.gates.get i).inputs,
        a ∈ ([4, 6, 7] : List ℕ) → b ∈ ([4, 6, 7] : List ℕ) → a = b) →
      (∃ i : Fin C.size, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C hP hS
  obtain ⟨hmin, hsize, hfun, hnorm, -⟩ := hP
  have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8),
        (8, 5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2) := by
    rw [hfun]; funext x
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  have hR : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) → ∃ i : Fin C.size,
      (∀ j : Fin C.size, (v : ℕ) ∈ (C.gates.get j).inputs ↔ j = i) ∧
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro v hv
    obtain ⟨hc, hor⟩ := hS v hv
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, fun j => ?_, hor i (by rw [hi]; exact Finset.mem_singleton_self i)⟩
    have := Finset.ext_iff.mp hi j
    simpa using this
  by_cases hdist : ∀ i : Fin C.size, ∀ a ∈ (C.gates.get i).inputs, ∀ b ∈ (C.gates.get i).inputs,
      a ∈ ([4, 6, 7] : List ℕ) → b ∈ ([4, 6, 7] : List ℕ) → a = b
  · by_cases hn : ∀ i : Fin C.size, (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not
    · exact hMono C hmin hsize hfun' hnorm hR hdist hn
    · push Not at hn
      exact hNot C hmin hsize hfun' hnorm hR hdist hn
  -- two of the inputs 4, 6, 7 share their only reader, an OR gate: they are interchangeable
  push Not at hdist
  obtain ⟨i, a, ha, b, hb, haL, hbL, hab⟩ := hdist
  -- helpers on lists
  have getD_snoc_lt : ∀ (l : List Bool) (z : Bool) (j : ℕ), j < l.length →
      (l ++ [z]).getD j false = l.getD j false := by
    intro l z j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have getD_snoc_eq : ∀ (l : List Bool) (z : Bool), (l ++ [z]).getD l.length false = z := by
    intro l z
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length)]
    simp
  have getD_ge : ∀ (l : List Bool) (j : ℕ), l.length ≤ j → l.getD j false = false := by
    intro l j hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj, Option.getD_none]
  have two_list : ∀ l : List ℕ, l.length = 2 → a ∈ l → b ∈ l → l = [a, b] ∨ l = [b, a] := by
    intro l hl hal hbl
    rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r, t⟩⟩⟩
    · simp at hl
    · simp at hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hal hbl
      rcases hal with rfl | rfl <;> rcases hbl with rfl | rfl
      · exact absurd rfl hab
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hab
    · simp at hl
  have ha9 : a < 9 := by simp at haL; omega
  have hb9 : b < 9 := by simp at hbL; omega
  -- the only reader of a and of b is gate i
  have huniq : ∀ c : ℕ, c ∈ ([4, 6, 7] : List ℕ) → c ∈ (C.gates.get i).inputs →
      ∀ j : Fin C.size, c ∈ (C.gates.get j).inputs → j = i := by
    intro c hcL hci j hcj
    have hc9 : c < 9 := by simp at hcL; omega
    obtain ⟨i0, hi0, -⟩ := hR ⟨c, hc9⟩ (by simp at hcL ⊢; rcases hcL with h | h | h <;> simp [h])
    have e1 := (hi0 j).mp hcj
    have e2 := (hi0 i).mp hci
    rw [e1, e2]
  have hiOr : (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    obtain ⟨i0, hi0, hor⟩ := hR ⟨a, ha9⟩ (by simp at haL ⊢; rcases haL with h | h | h <;> simp [h])
    rw [(hi0 i).mp ha]; exact hor
  have hiIn : (C.gates.get i).inputs = [a, b] ∨ (C.gates.get i).inputs = [b, a] := by
    have hlen : (C.gates.get i).inputs.length = 2 := by
      rcases (hnorm i).2.2 with h | h
      · rw [hiOr] at h; cases h.1
      · exact h.2
    exact two_list _ hlen ha hb
  -- the wires, gate by gate
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have hwires : ∀ x : List Bool, C.wires x = C.gates.foldl step x := fun _ => rfl
  have core : ∀ x x' : List Bool, x.length = 9 → x'.length = 9 →
      (∀ j < 9, j ≠ a → j ≠ b → x.getD j false = x'.getD j false) →
      (x.getD a false || x.getD b false) = true → (x'.getD a false || x'.getD b false) = true →
      ∀ k, k ≤ C.gates.length →
        ((C.gates.take k).foldl step x).length = 9 + k ∧
        ((C.gates.take k).foldl step x').length = 9 + k ∧
        (∀ j < 9, ((C.gates.take k).foldl step x).getD j false = x.getD j false) ∧
        (∀ j < 9, ((C.gates.take k).foldl step x').getD j false = x'.getD j false) ∧
        (∀ j, j ≠ a → j ≠ b →
          ((C.gates.take k).foldl step x).getD j false =
            ((C.gates.take k).foldl step x').getD j false) := by
    intro x x' hx hx' hagree hor1 hor2 k
    induction k with
    | zero =>
      intro _
      have e0 : ∀ z : List Bool, (C.gates.take 0).foldl step z = z := fun z => by simp
      rw [e0 x, e0 x']
      refine ⟨by omega, by omega, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
      intro j hja hjb
      rcases lt_or_ge j 9 with h | h
      · exact hagree j h hja hjb
      · rw [getD_ge x j (by omega), getD_ge x' j (by omega)]
    | succ k ih =>
      intro hk
      have hk' : k < C.gates.length := by omega
      have hkS : k < C.size := hk'
      obtain ⟨l1, l2, p1, p2, ag⟩ := ih (by omega)
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk']; rfl
      rw [htake, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, step]
      set L := (C.gates.take k).foldl step x with hL
      set L' := (C.gates.take k).foldl step x' with hL'
      set g := C.gates[k] with hg
      have hval : g.op.eval (g.inputs.map fun j => L.getD j false) =
          g.op.eval (g.inputs.map fun j => L'.getD j false) := by
        by_cases hrd : a ∈ g.inputs ∨ b ∈ g.inputs
        · have hki : (⟨k, hkS⟩ : Fin C.size) = i := by
            rcases hrd with h | h
            · exact huniq a haL ha ⟨k, hkS⟩ (by rw [hg] at h; exact h)
            · exact huniq b hbL hb ⟨k, hkS⟩ (by rw [hg] at h; exact h)
          have hgi : g = C.gates.get i := by rw [← hki, hg]; rfl
          rw [hgi, hiOr]
          have e1 : L.getD a false = x.getD a false := p1 a ha9
          have e2 : L.getD b false = x.getD b false := p1 b hb9
          have e3 : L'.getD a false = x'.getD a false := p2 a ha9
          have e4 : L'.getD b false = x'.getD b false := p2 b hb9
          have eval_or : ∀ l : List Bool,
              PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
          rcases hiIn with h | h <;> rw [h, eval_or, eval_or] <;>
            simp only [List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id, Bool.or_false, e1, e2, e3, e4]
          · rw [hor1, hor2]
          · rw [Bool.or_comm, hor1, Bool.or_comm, hor2]
        · push Not at hrd
          congr 1
          apply List.map_congr_left
          intro j hj
          exact ag j (fun e => hrd.1 (e ▸ hj)) (fun e => hrd.2 (e ▸ hj))
      refine ⟨by simp only [List.length_append, List.length_singleton, l1]; omega,
        by simp only [List.length_append, List.length_singleton, l2]; omega, ?_, ?_, ?_⟩
      · intro j hj; rw [getD_snoc_lt L _ j (by omega)]; exact p1 j hj
      · intro j hj; rw [getD_snoc_lt L' _ j (by omega)]; exact p2 j hj
      · intro j hja hjb
        rcases lt_trichotomy j (9 + k) with h | h | h
        · rw [getD_snoc_lt L _ j (by omega), getD_snoc_lt L' _ j (by omega)]
          exact ag j hja hjb
        · subst h
          have e5 := getD_snoc_eq L (g.op.eval (g.inputs.map fun j => L.getD j false))
          have e6 := getD_snoc_eq L' (g.op.eval (g.inputs.map fun j => L'.getD j false))
          rw [l1] at e5; rw [l2] at e6
          rw [e5, e6, hval]
        · rw [getD_ge _ j (by simp only [List.length_append, List.length_singleton, l1]; omega),
            getD_ge _ j (by simp only [List.length_append, List.length_singleton, l2]; omega)]
  have full : ∀ x x' : List Bool, x.length = 9 → x'.length = 9 →
      (∀ j < 9, j ≠ a → j ≠ b → x.getD j false = x'.getD j false) →
      (x.getD a false || x.getD b false) = true → (x'.getD a false || x'.getD b false) = true →
      (∀ j < 9, (C.wires x).getD j false = x.getD j false) ∧
      (∀ j, j ≠ a → j ≠ b → (C.wires x).getD j false = (C.wires x').getD j false) := by
    intro x x' hx hx' h1 h2 h3
    obtain ⟨-, -, p1, -, ag⟩ := core x x' hx hx' h1 h2 h3 C.gates.length le_rfl
    rw [List.take_length] at p1 ag
    exact ⟨fun j hj => by rw [hwires]; exact p1 j hj, fun j hja hjb => by
      rw [hwires, hwires]; exact ag j hja hjb⟩
  have hev : ∀ y : Fin 9 → Bool, C.eval (List.ofFn y) =
      PEqualNP.MetaComplexity.circuitFun 9 C y := fun _ => rfl
  -- the contradiction, from four inputs chosen for the pair a, b
  have finish : ∀ y y' z z' : Fin 9 → Bool,
      (∀ j < 9, j ≠ a → j ≠ b → (List.ofFn y).getD j false = (List.ofFn y').getD j false) →
      ((List.ofFn y).getD a false || (List.ofFn y).getD b false) = true →
      ((List.ofFn y').getD a false || (List.ofFn y').getD b false) = true →
      PEqualNP.MetaComplexity.circuitFun 9 C y = true →
      PEqualNP.MetaComplexity.circuitFun 9 C y' = false →
      (List.ofFn z).getD a false = true → PEqualNP.MetaComplexity.circuitFun 9 C z = false →
      (List.ofFn z').getD b false = true → PEqualNP.MetaComplexity.circuitFun 9 C z' = false →
      False := by
    intro y y' z z' hyy hy hy' fy fy' hz fz hz' fz'
    obtain ⟨-, ag⟩ := full _ _ (by simp) (by simp) hyy hy hy'
    by_cases hoa : C.output = a
    · obtain ⟨pz, -⟩ := full (List.ofFn z) (List.ofFn z) (by simp) (by simp) (fun _ _ _ _ => rfl)
        (by rw [hz]; rfl) (by rw [hz]; rfl)
      have : C.eval (List.ofFn z) = true := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval; rw [hoa, pz a ha9]; exact hz
      rw [hev] at this; rw [this] at fz; exact absurd fz (by decide)
    by_cases hob : C.output = b
    · obtain ⟨pz, -⟩ := full (List.ofFn z') (List.ofFn z') (by simp) (by simp) (fun _ _ _ _ => rfl)
        (by rw [hz', Bool.or_true]) (by rw [hz', Bool.or_true])
      have : C.eval (List.ofFn z') = true := by
        unfold PEqualNP.CircuitLowerBounds.Circuit.eval; rw [hob, pz b hb9]; exact hz'
      rw [hev] at this; rw [this] at fz'; exact absurd fz' (by decide)
    have : C.eval (List.ofFn y) = C.eval (List.ofFn y') := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval; exact ag _ hoa hob
    rw [hev, hev, fy, fy'] at this; exact absurd this (by decide)
  have hF : ∀ y : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 C y =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) ||
        (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) ||
        (y 6 && y 8) || (y 8 && y 5)) := fun y => by rw [hfun]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at haL hbL
  rcases haL with rfl | rfl | rfl <;> rcases hbL with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | skip
  -- a = 4, b = 6: neighbour 0 of 4 is not a neighbour of 6
  · exact finish (fun j => decide (j = 0 ∨ j = 4)) (fun j => decide (j = 0 ∨ j = 6))
      (fun j => decide (j = 4)) (fun j => decide (j = 6)) (by decide) (by decide) (by decide)
      (by rw [hF]; decide) (by rw [hF]; decide) (by decide) (by rw [hF]; decide)
      (by decide) (by rw [hF]; decide)
  · exact finish (fun j => decide (j = 0 ∨ j = 4)) (fun j => decide (j = 0 ∨ j = 7))
      (fun j => decide (j = 4)) (fun j => decide (j = 7)) (by decide) (by decide) (by decide)
      (by rw [hF]; decide) (by rw [hF]; decide) (by decide) (by rw [hF]; decide)
      (by decide) (by rw [hF]; decide)
  · exact finish (fun j => decide (j = 1 ∨ j = 6)) (fun j => decide (j = 1 ∨ j = 4))
      (fun j => decide (j = 6)) (fun j => decide (j = 4)) (by decide) (by decide) (by decide)
      (by rw [hF]; decide) (by rw [hF]; decide) (by decide) (by rw [hF]; decide)
      (by decide) (by rw [hF]; decide)
  · exact finish (fun j => decide (j = 1 ∨ j = 6)) (fun j => decide (j = 1 ∨ j = 7))
      (fun j => decide (j = 6)) (fun j => decide (j = 7)) (by decide) (by decide) (by decide)
      (by rw [hF]; decide) (by rw [hF]; decide) (by decide) (by rw [hF]; decide)
      (by decide) (by rw [hF]; decide)
  · exact finish (fun j => decide (j = 2 ∨ j = 7)) (fun j => decide (j = 2 ∨ j = 4))
      (fun j => decide (j = 7)) (fun j => decide (j = 4)) (by decide) (by decide) (by decide)
      (by rw [hF]; decide) (by rw [hF]; decide) (by decide) (by rw [hF]; decide)
      (by decide) (by rw [hF]; decide)
  · exact finish (fun j => decide (j = 2 ∨ j = 7)) (fun j => decide (j = 2 ∨ j = 6))
      (fun j => decide (j = 7)) (fun j => decide (j = 6)) (by decide) (by decide) (by decide)
      (by rw [hF]; decide) (by rw [hF]; decide) (by decide) (by rw [hF]; decide)
      (by decide) (by rw [hF]; decide)
