import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2504_1
    (case_and :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let z : (Fin 8 → Bool) → Bool := fun x =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
      ∀ (pre post : List Gate) (g : Gate) (out : ℕ),
        let D : Circuit := ⟨pre ++ g :: post, out⟩
        FanInTwo D → pre.length + post.length ≤ 13 →
        (∀ h ∈ pre ++ post, read h = false) → read g = true → g.op = .and →
        (let x : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
         let value := fun b => g.op.eval (g.inputs.map fun i =>
           ((Circuit.mk pre 0).wires (input b x)).getD i false)
         value true ≠ value false) →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = z x) →
        ∃ x : Fin 8 → Bool, D.eval (input true x) ≠ (z x || x 0 || x 3))
    (case_or :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let z : (Fin 8 → Bool) → Bool := fun x =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
      ∀ (pre post : List Gate) (g : Gate) (out : ℕ),
        let D : Circuit := ⟨pre ++ g :: post, out⟩
        FanInTwo D → pre.length + post.length ≤ 13 →
        (∀ h ∈ pre ++ post, read h = false) → read g = true → g.op = .or →
        (let x : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
         let value := fun b => g.op.eval (g.inputs.map fun i =>
           ((Circuit.mk pre 0).wires (input b x)).getD i false)
         value true ≠ value false) →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = z x) →
        ∃ x : Fin 8 → Bool, D.eval (input true x) ≠ (z x || x 0 || x 3))
    (case_not :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let z : (Fin 8 → Bool) → Bool := fun x =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
      ∀ (pre post : List Gate) (g : Gate) (out : ℕ),
        let D : Circuit := ⟨pre ++ g :: post, out⟩
        FanInTwo D → pre.length + post.length ≤ 13 →
        (∀ h ∈ pre ++ post, read h = false) → read g = true → g.op = .not →
        (let x : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
         let value := fun b => g.op.eval (g.inputs.map fun i =>
           ((Circuit.mk pre 0).wires (input b x)).getD i false)
         value true ≠ value false) →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = z x) →
        ∃ x : Fin 8 → Bool, D.eval (input true x) ≠ (z x || x 0 || x 3)) :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      let z : (Fin 8 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
        (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 14 →
        D.gates.countP read ≤ 1 →
        (∀ x : Fin 8 → Bool, D.eval (input false x) = z x) →
        ∃ x : Fin 8 → Bool, D.eval (input true x) ≠ (z x || x 0 || x 3) := by
  intro read input z D fan size count correct
  let packed : (Fin 8 → Bool) → Bool := fun x =>
        let k := tableIndex x
        (([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (k / 64) 0).testBit (k % 64)
  have unpack : ∀ x, packed x = z x := by
    dsimp only [packed,z]
    decide +kernel
  have noReadGate (g : Gate) (basis : g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (skip : read g = false) (w w' : List Bool)
      (agree : ∀ i, i ≠ 6 → w.getD i false = w'.getD i false) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
    obtain ⟨op,pins⟩ := g
    rcases basis with h|h|h <;> change op = _ at h <;> subst op
    · apply congrArg GateOp.and.eval
      apply List.map_congr_left
      intro i hi
      apply agree
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · apply congrArg GateOp.or.eval
      apply List.map_congr_left
      intro i hi
      apply agree
      rintro rfl
      change (pins.any (fun j => decide (j = 6))) = false at skip
      have exclude : ∀ x ∈ pins, x ≠ 6 := by simpa using skip
      exact exclude 6 hi rfl
    · cases pins with
      | nil => rfl
      | cons i rest =>
        change (decide (i = 6) || false) = false at skip
        have ne : i ≠ 6 := by simpa using skip
        exact congrArg Bool.not (agree i ne)
  let stepSix (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have noReadSuffix (gs : List Gate)
      (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ read g = false)
      (w w' : List Bool) (len : w.length = w'.length)
      (agree : ∀ i, i ≠ 6 → w.getD i false = w'.getD i false) :
      ∀ i, i ≠ 6 → (gs.foldl stepSix w).getD i false = (gs.foldl stepSix w').getD i false := by
    induction gs generalizing w w' with
    | nil => exact agree
    | cons g gs ih =>
      obtain ⟨basis,skip⟩ := ok g (by simp)
      apply ih (fun h hh => ok h (List.mem_cons_of_mem g hh)) (stepSix w g) (stepSix w' g)
      · simp [stepSix,len]
      · intro i ne
        by_cases h : i < w.length
        · simpa only [stepSix,List.getD_append _ _ false i h,List.getD_append _ _ false i (len ▸ h)] using agree i ne
        · have he := noReadGate g basis skip w w' agree
          simp only [stepSix,List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),
            List.getD_append_right _ _ _ _ (by omega : w'.length ≤ i),len,he]
  have split (gs : List Gate) (one : gs.countP read = 1) :
      ∃ pre g post, gs = pre ++ g :: post ∧ read g = true ∧
        ∀ h ∈ pre ++ post, read h = false := by
    induction gs with
    | nil => simp at one
    | cons g gs ih =>
      cases r : read g with
      | true =>
        have empty : gs.countP read = 0 := by simpa [List.countP_cons,r] using one
        exact ⟨[],g,gs,rfl,r,by simpa using List.countP_eq_zero.mp empty⟩
      | false =>
        obtain ⟨pre,k,post,eqn,rk,rest⟩ := ih (by simpa [List.countP_cons,r] using one)
        refine ⟨g::pre,k,post,by simp [eqn],rk,?_⟩
        intro h mem
        rcases List.mem_cons.mp mem with rfl | mem
        · exact r
        · exact rest h mem
  by_cases outputSix : D.output = 6
  · let x : Fin 8 → Bool := fun _ => false
    refine ⟨x, ?_⟩
    have preserved (gs : List Gate) (w : List Bool) (hw : 6 < w.length) :
        (gs.foldl stepSix w).getD 6 false = w.getD 6 false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons,ih (stepSix w g) (by simp [stepSix]; omega)]
        exact List.getD_append _ _ false 6 hw
    change (D.gates.foldl stepSix (input true x)).getD D.output false ≠ _
    rw [outputSix,preserved _ _ (by decide)]
    decide
  let probe : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
  have agreement (i : ℕ) (ne : i ≠ 6) :
      (input true probe).getD i false = (input false probe).getD i false := by
    by_cases h : i < 10
    · interval_cases i <;> first | rfl | contradiction
    · rw [List.getD_eq_default _ false (by change i ≥ 10; omega),
        List.getD_eq_default _ false (by change i ≥ 10; omega)]
  have finish (same : D.eval (input true probe) = D.eval (input false probe)) :
      ∃ x, D.eval (input true x) ≠ (z x || x 0 || x 3) := by
    refine ⟨probe, ?_⟩
    rw [same,correct probe]
    decide
  by_cases one : D.gates.countP read = 1
  · obtain ⟨gs,out⟩ := D
    obtain ⟨pre,g,post,eqn,rg,rest⟩ := split gs one
    subst gs
    have lengths : pre.length + post.length ≤ 13 := by
      change (pre ++ g :: post).length ≤ 14 at size
      simp only [List.length_append,List.length_cons] at size
      omega
    let w (b : Bool) := pre.foldl stepSix (input b probe)
    let value (b : Bool) := g.op.eval (g.inputs.map fun i => (w b).getD i false)
    by_cases test : value true = value false
    · have okPart (part : List Gate) (sub : ∀ h ∈ part, h ∈ pre ++ post) :
          ∀ h ∈ part, (h.op = .and ∨ h.op = .or ∨ h.op = .not) ∧ read h = false := by
        intro h mem
        have hp := sub h mem
        have hc : h ∈ pre ++ g :: post := by
          rcases List.mem_append.mp hp with hp|hp <;> simp [hp]
        exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan h hc).1,rest h hp⟩
      have earlier := noReadSuffix pre (okPart pre (fun _ h => List.mem_append_left _ h))
        (input true probe) (input false probe) rfl agreement
      have lengthRun (gs : List Gate) (v : List Bool) :
          (gs.foldl stepSix v).length = v.length + gs.length := by
        induction gs generalizing v with
        | nil => simp
        | cons h gs ih =>
          rw [List.foldl_cons,ih]
          simp only [stepSix,List.length_append,List.length_cons,List.length_nil]
          omega
      have lengthsEq : (w true).length = (w false).length := by simp only [w,lengthRun]; rfl
      have next (i : ℕ) (ne : i ≠ 6) :
          (stepSix (w true) g).getD i false = (stepSix (w false) g).getD i false := by
        change (w true ++ [value true]).getD i false = (w false ++ [value false]).getD i false
        by_cases h : i < (w true).length
        · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (lengthsEq ▸ h)]
          exact earlier i ne
        · simp only [List.getD_append_right _ _ _ _ (by omega : (w true).length ≤ i),
            List.getD_append_right _ _ _ _ (by omega : (w false).length ≤ i), lengthsEq,test]
      apply finish
      have same := noReadSuffix post (okPart post (fun _ h => List.mem_append_right _ h))
        _ _ (by simp only [stepSix,List.length_append,List.length_cons,List.length_nil,lengthsEq]) next out outputSix
      change ((pre ++ g :: post).foldl stepSix _).getD out false = ((pre ++ g :: post).foldl stepSix _).getD out false
      rw [List.foldl_append,List.foldl_append,List.foldl_cons,List.foldl_cons]
      exact same
    have allowed := (fan g (by simp)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at allowed
    have packedCorrect : ∀ x, (Circuit.mk (pre ++ g :: post) out).eval (input false x) = packed x :=
      fun x => (correct x).trans (unpack x).symm
    have result : ∃ x, (Circuit.mk (pre ++ g :: post) out).eval (input true x) ≠ (packed x || x 0 || x 3) := by
      rcases allowed with h|h|h
      · exact case_and pre post g out fan lengths rest rg h test packedCorrect
      · exact case_or pre post g out fan lengths rest rg h test packedCorrect
      · exact case_not pre post g out fan lengths rest rg h test packedCorrect
    simpa only [unpack] using result
  · have empty : D.gates.countP read = 0 := by omega
    have ok (g : Gate) (hg : g ∈ D.gates) :
        (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ read g = false := by
      exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (fan g hg).1,
        by simpa using List.countP_eq_zero.mp empty g hg⟩
    have same := noReadSuffix D.gates ok (input true probe) (input false probe) rfl agreement D.output outputSix
    exact finish same
