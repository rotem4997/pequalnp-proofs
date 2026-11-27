import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.BlindGate PEqualNP.TopForm

-- Adapt the boundary-row and derivative arguments of R_meta_1481_37 to the Fano plane.
-- The two output operands can split the negative rows in any way.
theorem PEqualNP.Outside.R_meta_1479_312
    (hmono : ∀ C : Circuit, IsAO2 14 C →
      Monotone (fun x : Fin 14 → Bool => C.eval (List.ofFn x)))
    (hcert :
      let E (p l : Fin 7) := p = l ∨ p = l + 1 ∨ p = l + 3
      let hit (x : Fin 14 → Bool) :=
        ∃ p l, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
      ∃ (C : Circuit) (j a b : ℕ), C.size ≤ 27 ∧ IsAO2 14 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output = 14 + j ∧
        C.gates[j]? = some ⟨GateOp.and, [a,b]⟩ ∧
        (∀ p l, E p l →
          C.eval (List.ofFn (fun i : Fin 14 => decide
            (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l))) = true) ∧
        (∀ z, Maximal (fun x => ¬ hit x) z → C.eval (List.ofFn z) = false) ∧
        ∀ s ∈ ([0,7] : List (Fin 14)),
          let x (i : Fin 14) := decide (i = s)
          wireValue C 14 x a = false ∧ wireValue C 14 x b = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  classical
  let E (p l : Fin 7) := p = l ∨ p = l+1 ∨ p = l+3
  let hit (x : Fin 14 → Bool) := ∃ p l, E p l ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
  obtain ⟨C,j,a,b,hs,hao,hdist,hout,hj,hedge,hneg,hquiet⟩ := hcert
  have mon := hmono C hao
  have legal (k : ℕ) (g : Gate) (hk : C.gates[k]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ u v, g.inputs = [u,v] ∧ u ≠ v ∧ u < 14+k ∧ v < 14+k := by
    have hg := List.mem_iff_getElem?.2 ⟨k,hk⟩
    obtain ⟨u,v,huv⟩ := List.length_eq_two.mp (hao.2.2 g hg)
    have he : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
      change C.gates.getD k _ = g
      simp [List.getD_eq_getElem?_getD, hk]
    have hback := hao.2.1 k (List.getElem?_eq_some_iff.1 hk).1
    rw [he, huv] at hback
    exact ⟨hao.1 g hg,u,v,huv,by simpa [huv] using hdist g hg,hback u (by simp),hback v (by simp)⟩
  have calcF (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ hit x := by
    constructor
    · intro yes
      by_contra absent
      obtain ⟨z,hxz,hz⟩ := Finite.exists_le_maximal (p := fun t => ¬ hit t) absent
      have below := mon hxz
      change C.eval (List.ofFn x) ≤ C.eval (List.ofFn z) at below
      rw [yes, hneg z hz] at below
      exact (by decide : ¬ true ≤ false) below
    · rintro ⟨p,l,hpl,hp,hl⟩
      let z (i : Fin 14) := decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l)
      have hle : z ≤ x := by
        intro i
        by_cases h : i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l
        · rcases h with rfl | rfl
          · simp only [hp, Bool.le_true]
          · simp only [hl, Bool.le_true]
        · simp only [z, h, decide_false, Bool.false_le]
      have below := mon hle
      change C.eval (List.ofFn z) ≤ C.eval (List.ofFn x) at below
      rw [hedge p l hpl] at below
      exact Bool.eq_true_of_true_le below
  let single (k : Fin 14) (i : Fin 14) := decide (i = k)
  have blocked (base seed : Fin 14 → Bool) (quiet : wireValue C 14 base a = false ∧ wireValue C 14 base b = false) :
      ∃ d : ℕ → Bool, (∀ i : Fin 14, d i.val = seed i) ∧ (∀ k (g : Gate) u v, C.gates[k]? = some g → g.inputs = [u,v] →
        (g.op = .and → d (14+k) = ((wireValue C 14 base u && d v) || (d u && wireValue C 14 base v))) ∧
        (g.op = .or → d (14+k) = (d u || d v))) ∧ d C.output = false := by
    let step (n : ℕ) (prev : (i : ℕ) → i < n → Bool) : Bool :=
      if h : n < 14 then seed ⟨n,h⟩ else
      let g := C.gates[n-14]?.getD ⟨GateOp.or,[]⟩
      let u := g.inputs[0]?.getD 0
      let v := g.inputs[1]?.getD 0
      if hu : u < n then if hv : v < n then
        if g.op = GateOp.and then (wireValue C 14 base u && prev v hv) || (prev u hu && wireValue C 14 base v)
        else prev u hu || prev v hv
      else false else false
    let d (n : ℕ) : Bool := Nat.strongRecOn n step
    have unfoldD (n : ℕ) : d n = step n (fun i _ => d i) := Nat.strongRecOn_eq step n
    have inputs (i : Fin 14) : d i.val = seed i := by rw [unfoldD]; simp [step,i.isLt]
    have gates (k : ℕ) (g : Gate) (u v : ℕ) (hk : C.gates[k]? = some g) (hg : g.inputs = [u,v]) :
        (g.op = .and → d (14+k) = ((wireValue C 14 base u && d v) || (d u && wireValue C 14 base v))) ∧
        (g.op = .or → d (14+k) = (d u || d v)) := by
      obtain ⟨_,s,t,hst,_,hs',ht⟩ := legal k g hk
      rw [hg] at hst
      simp only [List.cons.injEq, and_true] at hst
      obtain ⟨rfl,rfl⟩ := hst
      have big : ¬14+k < 14 := by omega
      have eqk : 14+k-14 = k := by omega
      constructor <;> intro hop <;> rw [unfoldD] <;> simp [step,big,eqk,hk,hg,hs',ht,hop]
    refine ⟨d,inputs,gates,?_⟩
    rw [hout,(gates j _ a b hj rfl).1 rfl,quiet.1,quiet.2]
    simp
  refine ⟨C,hs,legal,calcF,0,0,Or.inl rfl,?_,?_⟩
  · obtain ⟨d,hi,hg,hz⟩ := blocked (single 0) (single 7) (hquiet 0 (by simp))
    refine ⟨d,?_,hg,hz⟩
    intro i
    exact ⟨(hi (Fin.castAdd 7 i)).trans (by fin_cases i <;> decide),
           (hi (Fin.natAdd 7 i)).trans (by fin_cases i <;> decide)⟩
  · obtain ⟨d,hi,hg,hz⟩ := blocked (single 7) (single 0) (hquiet 7 (by simp))
    refine ⟨d,?_,hg,hz⟩
    intro i
    exact ⟨(hi (Fin.castAdd 7 i)).trans (by fin_cases i <;> decide),
           (hi (Fin.natAdd 7 i)).trans (by fin_cases i <;> decide)⟩
