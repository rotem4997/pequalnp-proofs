import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The smaller circuit already joins two of the points on the omitted line.
-- The final calculation follows the omitted-line construction in pull request 3937.
theorem PEqualNP.Outside.R_meta_1481_7
    (seeded : ∃ (H : Circuit) (wire : ℕ), H.size ≤ 59 ∧ 26 ≤ H.output ∧ H.output < 26 + H.size ∧
      26 ≤ wire ∧ wire < 26 + H.size ∧ (∀ (j : ℕ) (g : Gate), H.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) ∧
      (∀ x : Fin 26 → Bool, (H.wires (List.ofFn x)).getD wire false = (x 1 || x 2)) ∧
      (∀ x : Fin 26 → Bool, H.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, l ≠ 1 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true))
    (extendPair : ∀ (H : Circuit) (wire : ℕ), 26 ≤ H.output → H.output < 26 + H.size →
      26 ≤ wire → wire < 26 + H.size → (∀ (j : ℕ) (g : Gate), H.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) →
      (∀ x : Fin 26 → Bool, (H.wires (List.ofFn x)).getD wire false = (x 1 || x 2)) →
      ∃ (C : Circuit) (j a b : ℕ), C.size ≤ H.size + 5 ∧ (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) ∧
        C.output = 26 + j ∧ C.gates[j]? = some ⟨.and, [a,b]⟩ ∧
        (∀ x : Fin 26 → Bool, let W := C.wires (List.ofFn x); let h := H.eval (List.ofFn x)
          W.getD a false = (h || x 14) ∧ W.getD b false = (h || x 1 || x 2 || x 4 || x 10) ∧
            C.eval (List.ofFn x) = (W.getD a false && W.getD b false))) :

  ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  have propagate : ∀ (C : Circuit), (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ,
          g.inputs = [a,b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
      ∀ (base seed : Fin 26 → Bool), ∃ d : ℕ → Bool,
        (∀ i : Fin 26, d i.val = seed i) ∧
        ∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a,b] →
          (g.op = GateOp.and → d (26+k) =
            (((C.wires (List.ofFn base)).getD a false && d b) ||
             (d a && (C.wires (List.ofFn base)).getD b false))) ∧
          (g.op = GateOp.or → d (26+k) = (d a || d b)) := by
    intro C hC base seed
    classical
    let step := fun (n : ℕ) (get : (i : ℕ) → i < n → Bool) =>
      if hi : n < 26 then seed ⟨n,hi⟩ else
        let g := C.gates[n-26]?.getD ⟨GateOp.and, []⟩
        let a := g.inputs[0]?.getD 0
        let b := g.inputs[1]?.getD 0
        if ha : a < n then
          if hb : b < n then
            if g.op = GateOp.and then
              ((C.wires (List.ofFn base)).getD a false && get b hb) ||
              (get a ha && (C.wires (List.ofFn base)).getD b false)
            else get a ha || get b hb
          else false
        else false
    let d (n : ℕ) : Bool := Nat.strongRecOn n step
    have unfoldD (n : ℕ) : d n = step n (fun i _ => d i) :=
      Nat.strongRecOn_eq step n
    refine ⟨d, ?_, ?_⟩
    · intro i
      rw [unfoldD]
      simp [step, i.isLt]
    · intro k g a b hg hin
      obtain ⟨_, c, e, he, _, hc, hd⟩ := hC k g hg
      rw [hin] at he
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨rfl,rfl⟩ := he
      have hh : ¬ 26 + k < 26 := by omega
      have hs : 26 + k - 26 = k := by omega
      constructor <;> intro hop <;> rw [unfoldD] <;>
        simp [step, hh, hs, hg, hin, hc, hd, hop]
  obtain ⟨H, wire, hsize, hlow, hhigh, hwlow, hwhigh, hH, hw, hfun⟩ := seeded
  obtain ⟨C, j, a, b, hc, hC, hout, hgate, hval⟩ := extendPair H wire hlow hhigh hwlow hwhigh hH hw
  refine ⟨C, by omega, hC, ?_, (0 : Fin 13), (0 : Fin 13), Or.inl rfl, ?_, ?_⟩
  · intro x
    obtain ⟨ha, hb, ho⟩ := hval x
    rw [ho, ha, hb]
    simp only [Bool.and_eq_true, Bool.or_eq_true, hfun x]
    constructor
    · rintro ⟨h, hits⟩
      rcases h with ⟨u,t,_,hi,hp,hl⟩ | hl
      · exact ⟨u,t,hi,hp,hl⟩
      rcases hits with (((⟨u,t,_,hi,hp,hl'⟩ | hp) | hp) | hp) | hp
      · exact ⟨u,t,hi,hp,hl'⟩
      · exact ⟨1,1,Or.inl rfl,hp,hl⟩
      · exact ⟨2,1,Or.inr (Or.inl rfl),hp,hl⟩
      · exact ⟨4,1,Or.inr (Or.inr (Or.inl rfl)),hp,hl⟩
      · exact ⟨10,1,Or.inr (Or.inr (Or.inr rfl)),hp,hl⟩
    · rintro ⟨u,t,hi,hp,hl⟩
      by_cases ht : t = 1
      · subst t
        refine ⟨Or.inr hl, ?_⟩
        rcases hi with h | h | h | h <;> subst u
        · exact Or.inl (Or.inl (Or.inl (Or.inr hp)))
        · exact Or.inl (Or.inl (Or.inr hp))
        · exact Or.inl (Or.inr hp)
        · exact Or.inr hp
      · have hex : ∃ u t : Fin 13, t ≠ 1 ∧ (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true := ⟨u,t,ht,hi,hp,hl⟩
        exact ⟨Or.inl hex, Or.inl (Or.inl (Or.inl (Or.inl hex)))⟩
  · let base : Fin 26 → Bool := fun i => decide (i = 0)
    let seed : Fin 26 → Bool := fun i => decide (i = 13)
    obtain ⟨d, hd, hr⟩ := propagate C hC base seed
    have hh : H.eval (List.ofFn base) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨u,t,_,_,hp,hl⟩ := (hfun base).mp ht
      have hn : base (Fin.natAdd 13 t) = false := by fin_cases t <;> decide
      rw [hn] at hl
      contradiction
    obtain ⟨ha,hb,_⟩ := hval base
    rw [hh] at ha hb
    have za : (C.wires (List.ofFn base)).getD a false = false := ha
    have zb : (C.wires (List.ofFn base)).getD b false = false := hb
    refine ⟨d, ?_, hr, ?_⟩
    · intro i
      have hp := hd (Fin.castAdd 13 i)
      have hl := hd (Fin.natAdd 13 i)
      exact ⟨hp.trans (by fin_cases i <;> decide), hl.trans (by fin_cases i <;> decide)⟩
    · rw [hout, (hr j _ a b hgate rfl).1 rfl, za, zb]
      simp
  · let base : Fin 26 → Bool := fun i => decide (i = 13)
    let seed : Fin 26 → Bool := fun i => decide (i = 0)
    obtain ⟨d, hd, hr⟩ := propagate C hC base seed
    have hh : H.eval (List.ofFn base) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨u,t,_,_,hp,hl⟩ := (hfun base).mp ht
      have hn : base (Fin.castAdd 13 u) = false := by fin_cases u <;> decide
      rw [hn] at hp
      contradiction
    obtain ⟨ha,hb,_⟩ := hval base
    rw [hh] at ha hb
    have za : (C.wires (List.ofFn base)).getD a false = false := ha
    have zb : (C.wires (List.ofFn base)).getD b false = false := hb
    refine ⟨d, ?_, hr, ?_⟩
    · intro i
      have hp := hd (Fin.castAdd 13 i)
      have hl := hd (Fin.natAdd 13 i)
      exact ⟨hp.trans (by fin_cases i <;> decide), hl.trans (by fin_cases i <;> decide)⟩
    · rw [hout, (hr j _ a b hgate rfl).1 rfl, za, zb]
      simp
