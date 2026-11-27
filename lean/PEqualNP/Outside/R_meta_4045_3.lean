import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Count all gates with an operand forced to zero by a false input, including propagated zeros.
-- The local wire equation follows R_meta_4045_2; the new residual case bounds this larger set.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_4045_3
    (monotoneWires : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      ∀ (x y : Fin n → Bool), (∀ i, x i = true → y i = true) →
      ∀ w, (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true)
    (fewZeros : ∀ C : Circuit,
      (∀ j (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) →
      C.size ≤ 62 →
      (∀ x : Fin 26 → Bool, circuitFun 26 C x = true ↔
        ∃ p l : Fin 13, (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
      (∀ v : Fin 26, ((Finset.range C.size).filter fun j =>
        ∃ w ∈ (gateAt C j).inputs,
          PEqualNP.ReadTwo.wval C (fun i : Fin 26 => decide (i ≠ v)) w = false).card ≤ 4) →
      ∃ (v : Fin 26) (S : Finset ℕ), 5 ≤ S.card ∧ ∀ j ∈ S,
        j < C.size ∧ ∃ w < 26+j, ∀ x : Fin 26 → Bool, x v = false →
          PEqualNP.ReadTwo.wval C x (26+j) = PEqualNP.ReadTwo.wval C x w) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) → x1.size ≤ (62 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool) (x6 : ℕ), x2 x5 x6 = (x1.wires (List.ofFn x5)).getD x6 Bool.false) → (∀ (x6 : Fin (26 : ℕ) → Bool), x2 x6 x1.output = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) → ∃ (x7 : Fin (26 : ℕ)) (x8 : Finset ℕ), (5 : ℕ) ≤ x8.card ∧ ∀ x9 ∈ x8, x9 < x1.size ∧ ∃ (x11 : Bool) (x12 : Bool), ∃ x13 < (26 : ℕ) + x9, ∀ (x14 : Fin (26 : ℕ) → Bool), x14 x7 = Bool.false → x2 x14 ((26 : ℕ) + x9) = (x11 && x2 x14 x13 || x12) := by
  classical
  intro C W hlegal hsz hval hcomp
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨j, hj, eq⟩ := List.getElem_of_mem hg
    obtain ⟨op,a,b,ab,-,-,-⟩ := hlegal j g (by simpa [eq] using List.getElem?_eq_getElem hj)
    refine ⟨?_, by simp [ab]⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using op
  have forced (v : Fin 26) (w : ℕ)
      (off : PEqualNP.ReadTwo.wval C (fun i : Fin 26 => decide (i ≠ v)) w = false)
      (x : Fin 26 → Bool) (hx : x v = false) : W x w = false := by
    cases hw : W x w with
    | false => rfl
    | true =>
      have up := monotoneWires 26 C hm x (fun i => decide (i ≠ v))
        (by intro i hi; apply decide_eq_true; intro eq; subst i; simp [hx] at hi)
        w (by rw [← hval]; exact hw)
      change PEqualNP.ReadTwo.wval C (fun i : Fin 26 => decide (i ≠ v)) w = true at up
      rw [off] at up
      contradiction
  have hwires_append : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      ∃ ext : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init = init ++ ext ∧ ext.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro init; exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      intro init
      simp only [List.foldl_cons]
      obtain ⟨ext, heq, hlen⟩ := ih (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)])
      exact ⟨[g.op.eval (g.inputs.map fun i => init.getD i false)] ++ ext, by rw [heq, List.append_assoc], by simp [hlen]⟩

  have hval_gate : ∀ (x : Fin 26 → Bool) (j : ℕ) (hj : j < C.gates.length)
      (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
      (∀ i ∈ g.inputs, i < 26 + j) →
      W x (26 + j) = g.op.eval (g.inputs.map (W x)) := by
    intro x j hj g hgj hlt
    rw [hval]
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j C.gates
      rw [List.drop_eq_getElem_cons hj] at h1
      exact h1.symm
    set w_j := (C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
    have hfold : C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) =
        (C.gates.drop (j + 1)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (w_j ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w_j.getD i false)]) := by
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    obtain ⟨ext, heq, _⟩ := hwires_append (C.gates.drop (j + 1)) (w_j ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w_j.getD i false)])
    obtain ⟨ext', heq', hlen'⟩ := hwires_append (C.gates.take j) (List.ofFn x)
    have hwj_len : w_j.length = 26 + j := by
      change w_j = List.ofFn x ++ ext' at heq'
      rw [heq', List.length_append, List.length_ofFn, hlen', List.length_take, Nat.min_eq_left hj.le]
    have hge_eq : C.gates[j] = g := by
      rw [List.getElem?_eq_getElem hj] at hgj
      exact Option.some.inj hgj
    rw [hfold, heq, List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega)]
    rw [hwj_len, Nat.sub_self]
    simp only [List.cons_append, List.getElem?_cons_zero, Option.getD_some, hge_eq]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi_lt : i < 26 + j := hlt i (hge_eq ▸ hi)
    rw [hval]
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [hfold, heq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
      List.getElem?_append_left (by omega)]
  let Z (v : Fin 26) := (Finset.range C.size).filter fun j =>
    ∃ w ∈ (gateAt C j).inputs,
      PEqualNP.ReadTwo.wval C (fun i : Fin 26 => decide (i ≠ v)) w = false
  by_cases hz : ∃ v : Fin 26, 5 ≤ (Z v).card
  · obtain ⟨v,hv⟩ := hz
    refine ⟨v,Z v,hv,?_⟩
    intro j hj
    obtain ⟨hj,u,hu,off⟩ := Finset.mem_filter.mp hj
    have jlt : j < C.gates.length := Finset.mem_range.mp hj
    let g := gateAt C j
    have gj : C.gates[j]? = some g := by
      change C.gates[j]? = some (C.gates.getD j {op := .or, inputs := []})
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem jlt,Option.getD_some]
    obtain ⟨op,a,b,ab,ne,al,bl⟩ := hlegal j g gj
    have all : ∀ w ∈ g.inputs, w < 26+j := by
      simpa [ab] using (show a < 26+j ∧ b < 26+j from ⟨al,bl⟩)
    have uv : u=a ∨ u=b := by simpa [g,ab] using hu
    refine ⟨jlt,?_⟩
    rcases uv with rfl | rfl
    · rcases op with op | op
      · refine ⟨false,false,b,bl,?_⟩
        intro x hx
        rw [hval_gate x j jlt g gj all,op,ab]
        dsimp only [GateOp.eval]
        simp [forced v u off x hx]
      · refine ⟨true,false,b,bl,?_⟩
        intro x hx
        rw [hval_gate x j jlt g gj all,op,ab]
        dsimp only [GateOp.eval]
        simp [forced v u off x hx]
    · rcases op with op | op
      · refine ⟨false,false,a,al,?_⟩
        intro x hx
        rw [hval_gate x j jlt g gj all,op,ab]
        dsimp only [GateOp.eval]
        simp [forced v u off x hx]
      · refine ⟨true,false,a,al,?_⟩
        intro x hx
        rw [hval_gate x j jlt g gj all,op,ab]
        dsimp only [GateOp.eval]
        simp [forced v u off x hx]
  · have few : ∀ v, (Z v).card ≤ 4 := by
      intro v
      by_contra h
      exact hz ⟨v,by omega⟩
    obtain ⟨v,S,sz,good⟩ := fewZeros C hlegal hsz
      (by intro x; change (C.wires (List.ofFn x)).getD C.output false = true ↔ _; rw [← hval]; exact hcomp x) few
    refine ⟨v,S,sz,?_⟩
    intro j hj
    obtain ⟨jlt,w,wl,e⟩ := good j hj
    refine ⟨jlt,true,false,w,wl,?_⟩
    intro x hx
    have eq := e x hx
    change (C.wires (List.ofFn x)).getD (26+j) false = (C.wires (List.ofFn x)).getD w false at eq
    simpa only [Bool.true_and,Bool.or_false,hval] using eq
