import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate PEqualNP.TopForm

-- TearGosling suggested giving the two signals different jobs. Both accept every incident
-- pair. Only the operand named by the line-zero bit must reject a given maximal negative.
theorem PEqualNP.Outside.R_meta_1481_37
    (hwires : ∀ (C : Circuit) (n : ℕ), IsAO2 n C →
      (∀ w, Monotone (fun x : Fin n → Bool => wireValue C n x w)) ∧
      ∀ j a b, C.gates[j]? = some ⟨GateOp.and, [a,b]⟩ → ∀ x : Fin n → Bool,
        wireValue C n x (n+j) = (wireValue C n x a && wireValue C n x b))
    (hsearch :
      let E (p l : Fin 13) := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let hit (x : Fin 26 → Bool) := ∃ p l, E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ (C : Circuit) (j a b : ℕ), C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        C.output = 26+j ∧ C.gates[j]? = some ⟨GateOp.and, [a,b]⟩ ∧
        (∀ p l, E p l →
          let x (i : Fin 26) := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
          wireValue C 26 x a = true ∧ wireValue C 26 x b = true) ∧
        ∀ z, Maximal (fun x => ¬hit x) z → wireValue C 26 z (if z 13 then a else b) = false) :
    ∃ C : Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧
      ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
        (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧
          (∀ (ky : ℕ) (hy : Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] →
            (hy.op = GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧
            (hy.op = GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧
        (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧
          (∀ (kx : ℕ) (hx : Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] →
            (hx.op = GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧
            (hx.op = GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  let E (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let hit (x : Fin 26 → Bool) := ∃ p l, E p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  obtain ⟨C,j,a,b,hs,hao,hdist,hout,hj,hedge,hneg⟩ := hsearch
  obtain ⟨hmono, hand⟩ := hwires C 26 hao
  have legal (k : ℕ) (g : Gate) (hk : C.gates[k]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ u v, g.inputs = [u,v] ∧ u ≠ v ∧ u < 26+k ∧ v < 26+k := by
    have hg := List.mem_iff_getElem?.2 ⟨k,hk⟩
    obtain ⟨u,v,huv⟩ := List.length_eq_two.mp (hao.2.2 g hg)
    have he : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
      change C.gates.getD k _ = g
      simp [List.getD_eq_getElem?_getD, hk]
    have hback := hao.2.1 k (List.getElem?_eq_some_iff.1 hk).1
    rw [he, huv] at hback
    exact ⟨hao.1 g hg,u,v,huv,by simpa [huv] using hdist g hg,hback u (by simp),hback v (by simp)⟩
  have root (x : Fin 26 → Bool) : C.eval (List.ofFn x) = (wireValue C 26 x a && wireValue C 26 x b) := by
    change wireValue C 26 x C.output = _
    rw [hout, hand j a b hj]
  have fall {x y : Fin 26 → Bool} (w : ℕ) (hle : x ≤ y) (hy : wireValue C 26 y w = false) :
      wireValue C 26 x w = false := le_antisymm (hy ▸ hmono w hle) (Bool.false_le _)
  have calcF (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔ hit x := by
    rw [root, Bool.and_eq_true]
    constructor
    · rintro ⟨ha,hb⟩
      by_contra hn
      obtain ⟨z,hxz,hz⟩ := Finite.exists_le_maximal (p := fun t => ¬hit t) hn
      have h := hneg z hz
      cases hline : z 13 <;> simp only [hline, Bool.false_eq_true, ite_false, ite_true] at h
      · rw [fall b hxz h] at hb
        contradiction
      · rw [fall a hxz h] at ha
        contradiction
    · rintro ⟨p,l,hpl,hp,hl⟩
      let z (i : Fin 26) := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      have hle : z ≤ x := by
        intro i
        by_cases h : i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l
        · rcases h with rfl | rfl
          · simp only [hp, Bool.le_true]
          · simp only [hl, Bool.le_true]
        · simp only [z, h, decide_false, Bool.false_le]
      obtain ⟨ha,hb⟩ := hedge p l hpl
      exact ⟨Bool.eq_true_of_true_le (ha ▸ hmono a hle), Bool.eq_true_of_true_le (hb ▸ hmono b hle)⟩
  let single (k : Fin 26) (i : Fin 26) := decide (i = k)
  let pair (s t i : Fin 26) := decide (i = s ∨ i = t)
  have dark (x r s : Fin 26 → Bool) (hr : x ≤ r) (hs' : x ≤ s) (nr : ¬hit r) (ns : ¬hit s)
      (yr : r 13 = true) (ps : s 0 = true) : wireValue C 26 x a = false ∧ wireValue C 26 x b = false := by
    obtain ⟨R, hR, mR⟩ := Finite.exists_le_maximal (p := fun t => ¬hit t) nr
    obtain ⟨S, hS, mS⟩ := Finite.exists_le_maximal (p := fun t => ¬hit t) ns
    have h1 : R 13 = true := Bool.eq_true_of_true_le (yr ▸ hR 13)
    have h0 : S 0 = true := Bool.eq_true_of_true_le (ps ▸ hS 0)
    have h2 : S 13 = false := by
      apply Bool.eq_false_iff.mpr
      intro v
      exact mS.1 ⟨0,0,Or.inl rfl,h0,v⟩
    exact ⟨fall a (hr.trans hR) (by simpa [h1] using hneg R mR),
           fall b (hs'.trans hS) (by simpa [h2] using hneg S mS)⟩
  have dp := dark (single 2) (pair 2 13) (pair 2 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have dl := dark (single 15) (pair 15 13) (pair 15 0) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have blocked (base seed : Fin 26 → Bool) (darks : wireValue C 26 base a = false ∧ wireValue C 26 base b = false) :
      ∃ d : ℕ → Bool, (∀ i : Fin 26, d i.val = seed i) ∧ (∀ k (g : Gate) u v, C.gates[k]? = some g → g.inputs = [u,v] →
        (g.op = .and → d (26+k) = ((wireValue C 26 base u && d v) || (d u && wireValue C 26 base v))) ∧
        (g.op = .or → d (26+k) = (d u || d v))) ∧ d C.output = false := by
    let step (n : ℕ) (prev : (i : ℕ) → i < n → Bool) : Bool :=
      if h : n < 26 then seed ⟨n,h⟩ else
      let g := C.gates[n-26]?.getD ⟨GateOp.or,[]⟩
      let u := g.inputs[0]?.getD 0
      let v := g.inputs[1]?.getD 0
      if hu : u < n then if hv : v < n then
        if g.op = GateOp.and then (wireValue C 26 base u && prev v hv) || (prev u hu && wireValue C 26 base v)
        else prev u hu || prev v hv
      else false else false
    let d (n : ℕ) : Bool := Nat.strongRecOn n step
    have unfoldD (n : ℕ) : d n = step n (fun i _ => d i) := Nat.strongRecOn_eq step n
    have inputs (i : Fin 26) : d i.val = seed i := by rw [unfoldD]; simp [step,i.isLt]
    have gates (k : ℕ) (g : Gate) (u v : ℕ) (hk : C.gates[k]? = some g) (hg : g.inputs = [u,v]) :
        (g.op = .and → d (26+k) = ((wireValue C 26 base u && d v) || (d u && wireValue C 26 base v))) ∧
        (g.op = .or → d (26+k) = (d u || d v)) := by
      obtain ⟨_,s,t,hst,_,hs',ht⟩ := legal k g hk
      rw [hg] at hst
      simp only [List.cons.injEq, and_true] at hst
      obtain ⟨rfl,rfl⟩ := hst
      have big : ¬26+k < 26 := by omega
      have eqk : 26+k-26 = k := by omega
      constructor <;> intro hop <;> rw [unfoldD] <;> simp [step,big,eqk,hk,hg,hs',ht,hop]
    refine ⟨d,inputs,gates,?_⟩
    rw [hout,(gates j _ a b hj rfl).1 rfl,darks.1,darks.2]
    simp
  refine ⟨C,hs,legal,calcF,2,2,Or.inl rfl,?_,?_⟩
  · obtain ⟨d,hi,hg,hz⟩ := blocked (single 2) (single 15) dp
    refine ⟨d,?_,hg,hz⟩
    intro i
    exact ⟨(hi (Fin.castAdd 13 i)).trans (by fin_cases i <;> decide),
           (hi (Fin.natAdd 13 i)).trans (by fin_cases i <;> decide)⟩
  · obtain ⟨d,hi,hg,hz⟩ := blocked (single 15) (single 2) dl
    refine ⟨d,?_,hg,hz⟩
    intro i
    exact ⟨(hi (Fin.castAdd 13 i)).trans (by fin_cases i <;> decide),
           (hi (Fin.natAdd 13 i)).trans (by fin_cases i <;> decide)⟩
