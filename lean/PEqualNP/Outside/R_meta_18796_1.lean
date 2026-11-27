import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.HeptadCover

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_18796_1
  (normalize :
    let good := fun (D : Circuit) => ∀ x : Fin 25 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ (p : Fin 12) (l : Fin 13), p.succ ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let marked := fun (D : Circuit) => ∃ (j : Fin D.gates.length) (t : ℕ), t ∈ [1,2,14,16,313,316,339] ∧
      (D.gates.get j).op = .and ∧ 25+j.val ≠ D.output ∧
      (D.wires (List.ofFn fun i : Fin 25 => decide (i.val = t/25 ∨ i.val = t%25))).getD (25+j.val) false = true
    (∃ C, Monotone2 C ∧ good C ∧ C.size < 59) →
      ∃ D, Monotone2 D ∧ good D ∧ D.size < 59 ∧ marked D)
  (lower :
    let good := fun (D : Circuit) => ∀ x : Fin 25 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ (p : Fin 12) (l : Fin 13), p.succ ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true
    let marked := fun (D : Circuit) => ∃ (j : Fin D.gates.length) (t : ℕ), t ∈ [1,2,14,16,313,316,339] ∧
      (D.gates.get j).op = .and ∧ 25+j.val ≠ D.output ∧
      (D.wires (List.ofFn fun i : Fin 25 => decide (i.val = t/25 ∨ i.val = t%25))).getD (25+j.val) false = true
    ∀ D, Monotone2 D → good D → marked D → 59 ≤ D.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false → (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) → (59 : ℕ) ≤ x1.size := by
  intro C ao computes
  by_contra! small
  let rename : ℕ → ℕ := fun i => if i = 0 then 25+C.size else i-1
  let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map rename⟩
  let D : Circuit := ⟨C.gates.map gate,rename C.output⟩
  have size : D.size = C.size := List.length_map _
  have mono : Monotone2 D := by
    intro g mem
    obtain ⟨h,hm,rfl⟩ := List.mem_map.mp mem
    exact ⟨ao.1 h hm,by simpa [gate] using (ao.2.2 h hm).le⟩
  let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have read (xs : List Bool) (bound : xs.length ≤ 25+C.size) (i : ℕ) :
      xs.getD (rename i) false = (false::xs).getD i false := by
    cases i with
    | zero => simpa [rename] using List.getD_eq_default xs false bound
    | succ i => simp [rename]
  have sim (gs : List Gate) (xs : List Bool) (bound : xs.length + gs.length ≤ 25+C.size) :
      (gs.foldl step (false::xs)) = false :: ((gs.map gate).foldl step xs) := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      have rb : xs.length ≤ 25+C.size := by simp only [List.length_cons] at bound; omega
      have same : step (false::xs) g = false::step xs (gate g) := by
        simp only [step,gate,List.cons_append,List.map_map]
        congr 3
        exact congrArg g.op.eval (List.map_congr_left fun i _ => (read xs rb i).symm)
      rw [same]
      exact ih _ (by simp [step] at *; omega)
  have len (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih => simpa [step,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step xs g)
  have correct (x : Fin 25 → Bool) : D.eval (List.ofFn x) = true ↔
      ∃ (p : Fin 12) (l : Fin 13), p.succ ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true := by
    let y : Fin 26 → Bool := Fin.cases false x
    have inputs : List.ofFn y = false :: List.ofFn x := by rw [List.ofFn_succ]; rfl
    have ev : D.eval (List.ofFn x) = C.eval (List.ofFn y) := by
      change ((C.gates.map gate).foldl step (List.ofFn x)).getD (rename C.output) false =
        (C.gates.foldl step (List.ofFn y)).getD C.output false
      rw [inputs,sim _ _ (by rw [List.length_ofFn]; exact Nat.le_refl _)]
      apply read
      rw [len,List.length_ofFn,List.length_map]
      exact Nat.le_refl _
    rw [ev, computes y rfl]
    have hp (p : Fin 12) : y (Fin.castAdd 13 p.succ) = x (Fin.castAdd 13 p) := rfl
    have hl (l : Fin 13) : y (Fin.natAdd 13 l) = x (Fin.natAdd 12 l) := by
      have eq : Fin.natAdd 13 l = (Fin.natAdd 12 l).succ := Fin.ext (by simp [Fin.natAdd]; omega)
      rw [eq]; rfl
    constructor
    · rintro ⟨p,l,h,xp,xl⟩
      have edge : ∀ q : Fin 13, q ∈ singerLines3 l → y (Fin.castAdd 13 q) = true →
          ∃ i : Fin 12, i.succ ∈ singerLines3 l ∧ x (Fin.castAdd 13 i) = true := by
        intro q
        refine Fin.cases ?_ (fun i e v => ⟨i,e,(hp i) ▸ v⟩) q
        intro _ v
        exact Bool.noConfusion v
      obtain ⟨i,e,v⟩ := edge p h xp
      exact ⟨i,l,e,v,(hl l) ▸ xl⟩
    · rintro ⟨i,l,e,v,w⟩
      exact ⟨i.succ,l,e,(hp i).symm ▸ v,(hl l).symm ▸ w⟩
  obtain ⟨T,mt,ct,st,hit⟩ := normalize ⟨D,mono,correct,size ▸ small⟩
  exact (Nat.not_le_of_gt st) (lower T mt ct hit)
