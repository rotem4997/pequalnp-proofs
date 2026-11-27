import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2766_2
    (project : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), C.gates.length = 15 → C.output = 23 →
      C.gates[0]? = some ⟨.or,[0,3]⟩ → PEqualNP.MetaComplexity.Monotone2 C →
      (∀ (j : ℕ) (p : j < C.gates.length) (a : ℕ), a ∈ C.gates[j].inputs → a < 9+j ∨ a = 24) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x =>
        ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 (k % 9)))) →
      ∃ w : List (BitVec 24), w.length = 24 ∧
      w.take 10 = [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661] ∧
      w.getD 23 0 = 4095 ∧ (0 :: w).Nodup ∧
      ∀ j : ℕ, 0 < j → j < 15 →
        let t := w.getD (9+j) 0
        t = 16777215 ∨ ∃ u v : BitVec 24, u ∈ w.take (9+j) ∧ v ∈ w.take (9+j) ∧
          (t = u &&& v ∨ t = u ||| v))
    (exclude : ¬ ∃ w : List (BitVec 24), w.length = 24 ∧
      w.take 10 = [5521457,8532035,3227782,430348,11083800,113184,902208,13501056,15731968,5689661] ∧
      w.getD 23 0 = 4095 ∧ (0 :: w).Nodup ∧
      ∀ j : ℕ, 0 < j → j < 15 →
        let t := w.getD (9+j) 0
        t = 16777215 ∨ ∃ u v : BitVec 24, u ∈ w.take (9+j) ∧ v ∈ w.take (9+j) ∧
          (t = u &&& v ∨ t = u ||| v)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates = (0 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  intro C h nz same
  obtain ⟨len,output,first,form⟩ := h
  have mono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    obtain ⟨j,p,eq⟩ := List.mem_iff_getElem.mp hg
    obtain zero | ⟨a,ha,neq⟩ | ⟨a,b,ha,hb,rk,closed⟩ := form j p
    · rw [← eq,zero]
      simp
    · have no := List.countP_eq_zero.mp nz g hg
      rw [← eq,neq] at no
      exact (no rfl).elim
    · rw [← eq]
      rcases closed with e | e <;> rw [e] <;> simp
  have reads (j : ℕ) (p : j < C.gates.length) (a : ℕ) (ha : a ∈ C.gates[j].inputs) :
      a < 9+j ∨ a = 24 := by
    obtain empty | ⟨b,hb,e⟩ | ⟨b,c,hb,hc,_,eq⟩ := form j p
    · simp [empty] at ha
    · simp [e] at ha
      simpa [ha] using hb
    · have mem : a ∈ [b,c] := by
        rcases eq with e | e <;> simpa [e] using ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl | rfl
      · exact hb
      · exact hc
  have graph (x : Fin 9 → Bool) : ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 9)) && x (Fin.ofNat 9 (k % 9))) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    simp only [List.any_cons,List.any_nil]
    change (x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 ||
      (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 ||
        (x 3 && x 8 || (x 5 && x 7 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))) = _
    simp only [Bool.or_false,Bool.or_assoc]
  apply exclude (project C len output first mono reads ?_)
  funext x
  exact (congrFun same x).trans (graph x).symm
