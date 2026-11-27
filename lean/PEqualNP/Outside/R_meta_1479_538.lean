import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- At a marked pair, addition counts reads through an AND and minimum bounds reads through an OR.
-- A cost of two excludes every linear contribution in that direction.
theorem PEqualNP.Outside.R_meta_1479_538
  (synth : (∃ C : Circuit, C.size ≤ 27 ∧ (∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
    (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7,
      (p = l ∨ p = l+1 ∨ p = l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
    ∀ s : Bool, ∃ d : ℕ → ℕ, d (if s then 0 else 7) = 0 ∧
      d (if s then 7 else 0) ≤ 1 ∧ 2 ≤ d C.output ∧ (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (14+j) ≤ d a + d b) ∧
        (g.op = .or → d (14+j) ≤ min (d a) (d b)))))
  (interpret : (∀ (N : ℕ) (C : Circuit), (∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < N+j ∧ b < N+j) →
    ∀ (base seed : Fin N → Bool) (d : ℕ → ℕ),
    (∀ i, base i = true → d i.val = 0) → (∀ i, seed i = true → d i.val ≤ 1) →
    (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (N+j) ≤ d a + d b) ∧
        (g.op = .or → d (N+j) ≤ min (d a) (d b))) →
    ∃ v : ℕ → Bool, (∀ i : Fin N, v i.val = seed i) ∧
      (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        let w := C.wires (List.ofFn base)
        (g.op = .and → v (N+j) = ((w.getD a false && v b) || (v a && w.getD b false))) ∧
        (g.op = .or → v (N+j) = (v a || v b))) ∧
      ∀ k, v k = true → d k ≤ 1)) :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  obtain ⟨C, size, normal, computes, costs⟩ := synth
  let p : Fin 7 := 0
  let l : Fin 7 := 0
  let pt := Fin.castAdd 7 p
  let ln := Fin.natAdd 7 l
  have lift (s t : Fin 14) (d : ℕ → ℕ) (hs : d s.val = 0) (ht : d t.val ≤ 1)
      (ho : 2 ≤ d C.output) (hr : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (14+j) ≤ d a + d b) ∧
        (g.op = .or → d (14+j) ≤ min (d a) (d b))) :
      ∃ v : ℕ → Bool, (∀ i : Fin 14, v i.val = decide (i=t)) ∧
        (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
          let w := C.wires (List.ofFn fun i : Fin 14 => decide (i=s))
          (g.op = .and → v (14+j) = ((w.getD a false && v b) || (v a && w.getD b false))) ∧
          (g.op = .or → v (14+j) = (v a || v b))) ∧ v C.output = false := by
    obtain ⟨v, hi, hg, sound⟩ := interpret 14 C normal
      (fun i => decide (i=s)) (fun i => decide (i=t)) d
      (fun i h => of_decide_eq_true h ▸ hs) (fun i h => of_decide_eq_true h ▸ ht) hr
    refine ⟨v,hi,hg,?_⟩
    cases h : v C.output with
    | false => rfl
    | true => have := sound _ h; omega
  obtain ⟨d,ha,hb,hc,hd⟩ := costs true
  obtain ⟨e,he,hf,hg,hh⟩ := costs false
  obtain ⟨v,vi,vr,vo⟩ := lift pt ln d ha hb hc hd
  obtain ⟨w,wi,wr,wo⟩ := lift ln pt e he hf hg hh
  refine ⟨C,size,normal,computes,p,l,Or.inl rfl,⟨v,?_,vr,vo⟩,w,?_,wr,wo⟩
  · intro m
    exact ⟨(vi (Fin.castAdd 7 m)).trans (by fin_cases m <;> rfl),
      (vi (Fin.natAdd 7 m)).trans (by fin_cases m <;> rfl)⟩
  · intro m
    exact ⟨(wi (Fin.castAdd 7 m)).trans (by fin_cases m <;> rfl),
      (wi (Fin.natAdd 7 m)).trans (by fin_cases m <;> rfl)⟩
