import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.L_meta_10299

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def maskA : ℕ := 24151086

def matA (u v : Fin 5) : Bool := maskA.testBit (5 * u.val + v.val)

def targetVal : ℕ := 206

def ptU (p : Fin 9) : Fin 5 :=
  match p.val / 3 with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨1, by omega⟩
  | _ => ⟨4, by omega⟩

def ptV (p : Fin 9) : Fin 5 :=
  match p.val % 3 with
  | 0 => ⟨0, by omega⟩
  | 1 => ⟨1, by omega⟩
  | _ => ⟨3, by omega⟩

def initVals : List ℕ := [7, 56, 0, 0, 448, 73, 146, 0, 292, 0]

def coreList : List ℕ := [7, 56, 448, 73, 146, 292]

def coreSet : Finset ℕ := coreList.toFinset

def gtVal (op : GateOp) (vals : List ℕ) : ℕ :=
  match op with
  | GateOp.and => vals.foldr (· &&& ·) 511
  | GateOp.or => vals.foldr (· ||| ·) 0
  | _ => 0

def stepTabs (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [gtVal g.op (g.inputs.map fun i => w.getD i 0)]

def evalTabs (gs : List Gate) : List ℕ :=
  gs.foldl stepTabs initVals

theorem and_full (v : ℕ) (hv : v < 2 ^ 9) : v &&& 511 = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 9
  · have hfull : (511 : ℕ).testBit i = true := by
      have hfin : (511 : ℕ).testBit (⟨i, hi⟩ : Fin 9).val = true := by
        generalize (⟨i, hi⟩ : Fin 9) = p
        fin_cases p <;> decide
      exact hfin
    rw [hfull, Bool.and_true]
  · have hlt : v < 2 ^ i := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt, Bool.false_and]

theorem or_full (v : ℕ) (hv : v < 2 ^ 9) : v ||| 511 = 511 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases hi : i < 9
  · have hfull : (511 : ℕ).testBit i = true := by
      have hfin : (511 : ℕ).testBit (⟨i, hi⟩ : Fin 9).val = true := by
        generalize (⟨i, hi⟩ : Fin 9) = p
        fin_cases p <;> decide
      exact hfin
    rw [hfull, Bool.or_true]
  · have hlt1 : v < 2 ^ i := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega))
    have hlt2 : 511 < 2 ^ i := lt_of_lt_of_le (show 511 < 2 ^ 9 by omega)
      (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2, Bool.false_or]

theorem foldl_stepTabs_length (w : List ℕ) (gs : List Gate) :
    (gs.foldl stepTabs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepTabs, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem foldl_stepTabs_getD_lt (w : List ℕ) (gs : List Gate) {i : ℕ} (hi : i < w.length) :
    (gs.foldl stepTabs w).getD i 0 = w.getD i 0 := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepTabs w g).length := by
      simp only [stepTabs, List.length_append, List.length_singleton]; omega
    rw [ih (stepTabs w g) hi']
    simp only [stepTabs, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_wires_length (w : List Bool) (gs : List Gate) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem gtVal_bit (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p : Fin 9)
    (l : List ℕ) (wN : List ℕ) (wB : List Bool)
    (hbit : ∀ i, (wN.getD i 0).testBit p.val = wB.getD i false) :
    (gtVal op (l.map fun i => wN.getD i 0)).testBit p.val =
      op.eval (l.map fun i => wB.getD i false) := by
  rcases hop with rfl | rfl
  · simp only [gtVal, GateOp.eval]
    induction l with
    | nil =>
      have hp : (511 : ℕ).testBit p.val = true := by fin_cases p <;> decide
      simpa using hp
    | cons i tl ih =>
      simp only [List.map_cons, List.foldr_cons, Nat.testBit_and, List.all_cons, id_eq]
      rw [hbit i, ih]
  · simp only [gtVal, GateOp.eval]
    induction l with
    | nil => simp
    | cons i tl ih =>
      simp only [List.map_cons, List.foldr_cons, Nat.testBit_or, List.any_cons, id_eq]
      rw [hbit i, ih]

theorem foldl_bit (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (p : Fin 9) (wN : List ℕ) (wB : List Bool)
    (hlen : wN.length = wB.length)
    (hbit : ∀ i, (wN.getD i 0).testBit p.val = wB.getD i false) :
    ∀ i, ((gs.foldl stepTabs wN).getD i 0).testBit p.val =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wB).getD i false := by
  induction gs generalizing wN wB with
  | nil => exact hbit
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hm g List.mem_cons_self
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    · simp only [stepTabs, List.length_append, List.length_singleton, hlen]
    · intro i
      simp only [stepTabs, List.getD_eq_getElem?_getD]
      by_cases hlt : i < wN.length
      · have hltB : i < wB.length := by omega
        rw [List.getElem?_append_left hlt, List.getElem?_append_left hltB]
        simpa [List.getD_eq_getElem?_getD] using hbit i
      · by_cases heq : i = wN.length
        · subst heq
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self,
            hlen, List.getElem?_append_right (le_refl _), Nat.sub_self]
          simp only [List.getElem?_cons_zero, Option.getD_some]
          exact gtVal_bit g.op hop p g.inputs wN wB hbit
        · have hgt : wN.length + 1 ≤ i := by omega
          have hgtB : wB.length + 1 ≤ i := by omega
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
          simp

theorem initVals_bit_fin (p : Fin 9) (i : Fin 10) :
    (initVals.getD i.val 0).testBit p.val = (oneEach (ptU p) (ptV p)).getD i.val false := by
  fin_cases p <;> fin_cases i <;> decide

theorem initVals_bit (p : Fin 9) (i : ℕ) :
    (initVals.getD i 0).testBit p.val = (oneEach (ptU p) (ptV p)).getD i false := by
  by_cases hi : i < 10
  · exact initVals_bit_fin p ⟨i, hi⟩
  · have h1 : initVals.length ≤ i := by simp [initVals]; omega
    have h2 : (oneEach (ptU p) (ptV p)).length ≤ i := by simp [oneEach]; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2,
      Option.getD_none, Nat.zero_testBit]

theorem evalTabs_bit (C : Circuit) (hm : Monotone2 C) (p : Fin 9) (i : ℕ) :
    ((evalTabs C.gates).getD i 0).testBit p.val =
      (C.wires (oneEach (ptU p) (ptV p))).getD i false :=
  foldl_bit C.gates hm p initVals (oneEach (ptU p) (ptV p)) (by simp [initVals, oneEach])
    (initVals_bit p) i

theorem gtVal_lt (op : GateOp) (vals : List ℕ) (hv : ∀ x ∈ vals, x < 2 ^ 9) :
    gtVal op vals < 2 ^ 9 := by
  cases op with
  | and =>
    simp only [gtVal]
    induction vals with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldr_cons]
      exact Nat.and_lt_two_pow x (ih (fun y hy => hv y (List.mem_cons_of_mem _ hy)))
  | or =>
    simp only [gtVal]
    induction vals with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldr_cons]
      exact Nat.or_lt_two_pow (hv x List.mem_cons_self)
        (ih (fun y hy => hv y (List.mem_cons_of_mem _ hy)))
  | not => simp [gtVal]
  | mod _ => simp [gtVal]
  | maj => simp [gtVal]

theorem foldl_stepTabs_lt (gs : List Gate) (w : List ℕ) (hw : ∀ x ∈ w, x < 2 ^ 9) :
    ∀ x ∈ gs.foldl stepTabs w, x < 2 ^ 9 := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    intro x hx
    simp only [stepTabs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · apply gtVal_lt
      intro y hy
      rcases List.mem_map.mp hy with ⟨i, _, rfl⟩
      by_cases hi : i < w.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hw _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; omega

theorem evalTabs_getD_lt (C : Circuit) (i : ℕ) : (evalTabs C.gates).getD i 0 < 2 ^ 9 := by
  by_cases hi : i < (evalTabs C.gates).length
  · rw [List.getD_eq_getElem _ _ hi]
    exact foldl_stepTabs_lt C.gates initVals (by decide) _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]; omega

theorem target_bit_match (p : Fin 9) : matA (ptU p) (ptV p) = targetVal.testBit p.val := by
  fin_cases p <;> decide

theorem evalTabs_output (C : Circuit) (hm : Monotone2 C) (hrep : Represents matA C) :
    (evalTabs C.gates).getD C.output 0 = targetVal := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 9
  · rw [evalTabs_bit C hm ⟨k, hk⟩ C.output]
    change C.eval (oneEach (ptU ⟨k, hk⟩) (ptV ⟨k, hk⟩)) = targetVal.testBit k
    rw [hrep (ptU ⟨k, hk⟩) (ptV ⟨k, hk⟩), target_bit_match ⟨k, hk⟩]
  · have hkN : 9 ≤ k := by omega
    have h1 : (evalTabs C.gates).getD C.output 0 < 2 ^ k :=
      lt_of_lt_of_le (evalTabs_getD_lt C C.output) (Nat.pow_le_pow_right (by omega) hkN)
    have h2 : targetVal < 2 ^ k :=
      lt_of_lt_of_le (show targetVal < 2 ^ 9 by decide) (Nat.pow_le_pow_right (by omega) hkN)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

def listLe (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (w1 w2 : List Bool) (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    op.eval (l.map fun i => w1.getD i false) = true →
      op.eval (l.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h (w1.getD i false) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h1⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle i h1⟩

theorem wires_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w1 w2 : List Bool) (hle : listLe w1 w2) :
    listLe (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hm g List.mem_cons_self
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp [hle.1], fun i hi => ?_⟩
    simp only [List.getD_eq_getElem?_getD] at hi ⊢
    by_cases hlt : i < w1.length
    · have hlt2 : i < w2.length := by rw [← hle.1]; exact hlt
      rw [List.getElem?_append_left hlt] at hi
      rw [List.getElem?_append_left hlt2]
      exact hle.2 i (by simpa [List.getD_eq_getElem?_getD] using hi)
    · by_cases heq : i = w1.length
      · subst heq
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
        rw [hle.1, List.getElem?_append_right (le_refl _), Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some] at hi ⊢
        exact gate_mono g.op hop g.inputs w1 w2 hle.2 hi
      · rw [List.getElem?_eq_none (by simp; omega)] at hi
        simp at hi

def effInputs (gs : List Gate) (k : ℕ) : List ℕ :=
  (gs.getD k ⟨GateOp.or, []⟩).inputs.filter (· < 10 + k)

def reachStep (gs : List Gate) : ℕ → Finset ℕ → Finset ℕ
  | 0, R => R
  | k + 1, R =>
    let R' := if 10 + k ∈ R then R ∪ (effInputs gs k).toFinset else R
    reachStep gs k R'

theorem reachStep_sub (gs : List Gate) (m : ℕ) (R : Finset ℕ) : R ⊆ reachStep gs m R := by
  induction m generalizing R with
  | zero => exact Finset.Subset.refl R
  | succ k ih =>
    simp only [reachStep]
    split_ifs
    · exact Finset.Subset.trans Finset.subset_union_left (ih _)
    · exact ih R

theorem reachStep_ge_iff (gs : List Gate) (m : ℕ) (R : Finset ℕ) (w : ℕ) (hw : 10 + m ≤ w) :
    w ∈ reachStep gs m R ↔ w ∈ R := by
  induction m generalizing R with
  | zero => rfl
  | succ k ih =>
    simp only [reachStep]
    rw [ih _ (by omega)]
    split_ifs with h
    · simp only [Finset.mem_union, List.mem_toFinset, effInputs, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro (hR | ⟨_, hlt⟩)
        · exact hR
        · omega
      · exact Or.inl
    · rfl

theorem reachStep_closed (gs : List Gate) (m : ℕ) (R : Finset ℕ) {k : ℕ} (hk : k < m)
    (hmem : 10 + k ∈ reachStep gs m R) :
    (effInputs gs k).toFinset ⊆ reachStep gs m R := by
  induction m generalizing R with
  | zero => omega
  | succ j ih =>
    simp only [reachStep] at hmem ⊢
    by_cases hkj : k = j
    · subst hkj
      have h1 : 10 + k ∈ (if 10 + k ∈ R then R ∪ (effInputs gs k).toFinset else R) :=
        (reachStep_ge_iff gs k _ (10 + k) (le_refl _)).mp hmem
      have h2 : 10 + k ∈ R := by
        split_ifs at h1 with hR
        · exact hR
        · exact h1
      simp only [h2, ↓reduceIte]
      exact Finset.Subset.trans Finset.subset_union_right (reachStep_sub gs k _)
    · exact ih _ (by omega) hmem

theorem reachStep_parent (gs : List Gate) (m : ℕ) (R : Finset ℕ) {w : ℕ}
    (hw : w ∈ reachStep gs m R) (hn : w ∉ R) :
    ∃ k < m, 10 + k ∈ reachStep gs m R ∧ w ∈ effInputs gs k := by
  induction m generalizing R with
  | zero => exact absurd hw hn
  | succ k ih =>
    simp only [reachStep] at hw ⊢
    by_cases hR' : w ∈ (if 10 + k ∈ R then R ∪ (effInputs gs k).toFinset else R)
    · split_ifs at hR' with hk
      · rcases Finset.mem_union.mp hR' with h1 | h2
        · exact absurd h1 hn
        · refine ⟨k, by omega, ?_, List.mem_toFinset.mp h2⟩
          simp only [hk, ↓reduceIte]
          exact reachStep_sub gs k _ (Finset.mem_union_left _ hk)
      · exact absurd hR' hn
    · obtain ⟨j, hj, h1, h2⟩ := ih _ hw hR'
      exact ⟨j, by omega, h1, h2⟩

theorem wires_eq_on_reach (gs : List Gate) (R : Finset ℕ)
    (hclosed : ∀ k < gs.length, 10 + k ∈ R → (effInputs gs k).toFinset ⊆ R)
    (x y : List Bool) (hx : x.length = 10) (hy : y.length = 10)
    (hxy : ∀ i < 10, i ∈ R → x.getD i false = y.getD i false) :
    ∀ m ≤ gs.length, ∀ w < 10 + m, w ∈ R →
      ((gs.take m).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD w false =
      ((gs.take m).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD w false := by
  intro m hm
  induction m with
  | zero =>
    intro w hw hR
    simpa using hxy w hw hR
  | succ k ih =>
    have hlt : k < gs.length := by omega
    have htake : gs.take (k + 1) = gs.take k ++ [gs[k]] := List.take_succ_eq_append_getElem hlt
    intro w hw hR
    rw [htake, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    set wx := (gs.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
    set wy := (gs.take k).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y
    have hwx : wx.length = 10 + k := by
      rw [foldl_wires_length, hx, List.length_take, Nat.min_eq_left (by omega : k ≤ gs.length)]
    have hwy : wy.length = 10 + k := by
      rw [foldl_wires_length, hy, List.length_take, Nat.min_eq_left (by omega : k ≤ gs.length)]
    by_cases hwk : w < 10 + k
    · have hwx_lt : w < wx.length := by omega
      have hwy_lt : w < wy.length := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwx_lt,
        List.getElem?_append_left hwy_lt]
      simpa only [List.getD_eq_getElem?_getD] using ih (by omega) w hwk hR
    · have hweq : w = 10 + k := by omega
      subst hweq
      simp only [List.getD_eq_getElem?_getD]
      have hx_eq : 10 + k = wx.length := by omega
      have hy_eq : 10 + k = wy.length := by omega
      rw [hx_eq, List.getElem?_append_right (le_refl _), Nat.sub_self,
        ← hx_eq, hy_eq, List.getElem?_append_right (le_refl _), Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases hik : i < 10 + k
      · have hiR : i ∈ R := by
          apply hclosed k hlt hR
          rw [List.mem_toFinset, effInputs, List.mem_filter, List.getD_eq_getElem _ _ hlt]
          exact ⟨hi, by simpa using hik⟩
        exact ih (by omega) i hik hiR
      · have hwx_ge : wx.length ≤ i := by omega
        have hwy_ge : wy.length ≤ i := by omega
        rw [List.getElem?_eq_none hwx_ge, List.getElem?_eq_none hwy_ge]

theorem essential_in_reach (C : Circuit) (hm : Monotone2 C) (hrep : Represents matA C)
    (z : ℕ) (hz : z < 10) (u1 v1 u2 v2 : Fin 5)
    (h1 : matA u1 v1 = true) (h2 : matA u2 v2 = false)
    (hle : ∀ i < 10, i ≠ z → (oneEach u1 v1).getD i false = true → (oneEach u2 v2).getD i false = true) :
    z ∈ reachStep C.gates C.gates.length {C.output} := by
  set R := reachStep C.gates C.gates.length {C.output}
  by_contra hnot
  let x := oneEach u1 v1
  let y := x.set z false
  have hx : x.length = 10 := by simp [x, oneEach]
  have hy : y.length = 10 := by simp [y, hx]
  have heq : C.eval x = C.eval y := by
    unfold Circuit.eval Circuit.wires
    by_cases hout : C.output < 10 + C.gates.length
    · have h := wires_eq_on_reach C.gates R
        (fun k hk hR => reachStep_closed C.gates C.gates.length {C.output} hk hR)
        x y hx hy (fun i _ hiR => by
          have hzi : z ≠ i := fun e => hnot (e ▸ hiR)
          simp only [y, List.getD_eq_getElem?_getD, List.getElem?_set_ne hzi])
        C.gates.length (le_refl _) C.output hout
        (reachStep_sub C.gates C.gates.length {C.output} (Finset.mem_singleton_self _))
      simpa [List.take_length] using h
    · have hlx : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length ≤ C.output := by
        rw [foldl_wires_length, hx]; omega
      have hly : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).length ≤ C.output := by
        rw [foldl_wires_length, hy]; omega
      rw [List.getD_eq_default _ _ hlx, List.getD_eq_default _ _ hly]
  have hle_y : listLe y (oneEach u2 v2) := by
    refine ⟨by simp [hy, oneEach], fun i hi => ?_⟩
    by_cases hi10 : i < 10
    · by_cases hiz : i = z
      · subst hiz
        have : y.getD i false = false := by
          simp only [y, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega : i < x.length),
            Option.getD_some]
        rw [this] at hi; cases hi
      · have hxi : x.getD i false = true := by
          rw [List.getD_eq_getElem?_getD]
          rw [List.getD_eq_getElem?_getD] at hi
          simpa only [y, List.getElem?_set_ne (Ne.symm hiz)] using hi
        exact hle i hi10 hiz hxi
    · rw [List.getD_eq_default _ _ (by omega)] at hi; cases hi
  have hwm := wires_mono C.gates hm y (oneEach u2 v2) hle_y
  have hc1 : C.eval y = true := by rw [← heq, hrep u1 v1, h1]
  have hc2 : C.eval (oneEach u2 v2) = true := hwm.2 C.output hc1
  rw [hrep u2 v2, h2] at hc2
  cases hc2

def isTriv (gs : List Gate) (k : ℕ) : Bool :=
  ((evalTabs gs).getD (10 + k) 0 == 0) ||
    (effInputs gs k).any (fun w => (evalTabs gs).getD w 0 == 0)

theorem evalTabs_gate_eq_pre (gs : List Gate) {k : ℕ} (hk : k < gs.length) :
    (evalTabs gs).getD (10 + k) 0 =
      gtVal gs[k].op (gs[k].inputs.map fun i => if i < 10 + k then (evalTabs gs).getD i 0 else 0) := by
  have hsplit : gs = gs.take k ++ [gs[k]] ++ gs.drop (k + 1) := by
    have h1 := (List.take_append_drop (k + 1) gs).symm
    have h2 := List.take_succ_eq_append_getElem hk
    rw [h2] at h1
    exact h1
  set w0 := (gs.take k).foldl stepTabs initVals
  have hw0 : w0.length = 10 + k := by
    rw [foldl_stepTabs_length, List.length_take, Nat.min_eq_left (by omega : k ≤ gs.length)]
    simp [initVals]
  have hpre : ∀ i < 10 + k, (evalTabs gs).getD i 0 = w0.getD i 0 := by
    intro i hi
    have hi_st : i < (stepTabs w0 gs[k]).length := by
      simp only [stepTabs, List.length_append, List.length_singleton]; omega
    conv_lhs => rw [evalTabs, hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [foldl_stepTabs_getD_lt _ _ hi_st]
    simp only [stepTabs, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega : i < w0.length)]
  have hlt_st : 10 + k < (stepTabs w0 gs[k]).length := by
    simp only [stepTabs, List.length_append, List.length_singleton]; omega
  conv_lhs => rw [evalTabs, hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_stepTabs_getD_lt _ _ hlt_st]
  have hget : (stepTabs w0 gs[k]).getD (10 + k) 0 =
      gtVal gs[k].op (gs[k].inputs.map fun i => w0.getD i 0) := by
    simp only [stepTabs, List.getD_eq_getElem?_getD]
    rw [← hw0, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 10 + k
  · simp only [hi, ↓reduceIte]; exact (hpre i hi).symm
  · simp only [hi, ↓reduceIte]; exact List.getD_eq_default w0 0 (by omega)

theorem triv_count_ge (C : Circuit) (hm : Monotone2 C) (hrep : Represents matA C) :
    4 ≤ ((Finset.range C.gates.length).filter (fun k => isTriv C.gates k = true)).card := by
  set R := reachStep C.gates C.gates.length {C.output}
  set tabs := evalTabs C.gates
  set S := R.filter (fun w => tabs.getD w 0 = 0)
  set Z : Finset ℕ := {2, 3, 7, 9}
  have hZR : Z ⊆ R := by
    intro z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact essential_in_reach C hm hrep 2 (by omega) ⟨2, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
        (by decide) (by decide) (by intro i hi hne h1; revert hi hne h1; revert i; decide)
    · exact essential_in_reach C hm hrep 3 (by omega) ⟨3, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
        (by decide) (by decide) (by intro i hi hne h1; revert hi hne h1; revert i; decide)
    · exact essential_in_reach C hm hrep 7 (by omega) ⟨0, by omega⟩ ⟨2, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
        (by decide) (by decide) (by intro i hi hne h1; revert hi hne h1; revert i; decide)
    · exact essential_in_reach C hm hrep 9 (by omega) ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨4, by omega⟩ ⟨3, by omega⟩
        (by decide) (by decide) (by intro i hi hne h1; revert hi hne h1; revert i; decide)
  have hZS : Z ⊆ S := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨hZR hz, ?_⟩
    have hz10 : z < 10 := by
      simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz; omega
    have hget : tabs.getD z 0 = initVals.getD z 0 :=
      foldl_stepTabs_getD_lt initVals C.gates (by simp [initVals]; omega)
    rw [hget]
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> decide
  set G := (Finset.range C.gates.length).filter (fun k => 10 + k ∈ R)
  set G0 := G.filter (fun k => tabs.getD (10 + k) 0 = 0)
  set G1 := G.filter (fun k => tabs.getD (10 + k) 0 ≠ 0 ∧ ∃ w ∈ effInputs C.gates k, tabs.getD w 0 = 0)
  have hdisj_G : Disjoint G0 G1 := by
    rw [Finset.disjoint_left]
    intro k hk0 hk1
    exact (Finset.mem_filter.mp hk1).2.1 (Finset.mem_filter.mp hk0).2
  have hGsub : G0 ∪ G1 ⊆ (Finset.range C.gates.length).filter (fun k => isTriv C.gates k = true) := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk0 | hk1
    · have h0 := Finset.mem_filter.mp hk0
      have hG := Finset.mem_filter.mp h0.1
      refine Finset.mem_filter.mpr ⟨hG.1, ?_⟩
      simp only [isTriv, Bool.or_eq_true, beq_iff_eq]
      exact Or.inl h0.2
    · have h1 := Finset.mem_filter.mp hk1
      have hG := Finset.mem_filter.mp h1.1
      refine Finset.mem_filter.mpr ⟨hG.1, ?_⟩
      simp only [isTriv, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
      right
      obtain ⟨w, hw, hzw⟩ := h1.2.2
      exact ⟨w, hw, hzw⟩
  have hG0_img : G0.image (fun k => 10 + k) ⊆ S := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨k, hk, rfl⟩
    have h0 := Finset.mem_filter.mp hk
    have hG := Finset.mem_filter.mp h0.1
    exact Finset.mem_filter.mpr ⟨hG.2, h0.2⟩
  have hdisj_ZS : Disjoint Z (G0.image (fun k => 10 + k)) := by
    rw [Finset.disjoint_left]
    intro w hwZ hwG
    rcases Finset.mem_image.mp hwG with ⟨k, _, rfl⟩
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hwZ
    omega
  have hS_lo : 4 + G0.card ≤ S.card := by
    have h1 : (Z ∪ G0.image (fun k => 10 + k)).card ≤ S.card :=
      Finset.card_le_card (Finset.union_subset hZS hG0_img)
    rw [Finset.card_union_of_disjoint hdisj_ZS, Finset.card_image_of_injective _ (fun a b h => by omega)] at h1
    have hZcard : Z.card = 4 := by decide
    omega
  have hS_cov : S ⊆ (G0 ∪ G1).biUnion (fun k => (effInputs C.gates k).toFinset ∩ S) := by
    intro w hw
    have hwR : w ∈ R := (Finset.mem_filter.mp hw).1
    have hw0 : tabs.getD w 0 = 0 := (Finset.mem_filter.mp hw).2
    have hne_out : w ≠ C.output := by
      rintro rfl
      have hout := evalTabs_output C hm hrep
      change tabs.getD C.output 0 = targetVal at hout
      rw [hw0] at hout
      simp [targetVal] at hout
    obtain ⟨k, hk, hkR, hweff⟩ :=
      reachStep_parent C.gates C.gates.length {C.output} hwR (by simpa using hne_out)
    refine Finset.mem_biUnion.mpr ⟨k, ?_, Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hweff, hw⟩⟩
    have hkG : k ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkR⟩
    by_cases hkz : tabs.getD (10 + k) 0 = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hkG, hkz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hkG, hkz, w, hweff, hw0⟩)
  have hG0_deg : ∀ k ∈ G0, ((effInputs C.gates k).toFinset ∩ S).card ≤ 2 := by
    intro k hk
    have hlt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
    have hlen : (C.gates[k]).inputs.length ≤ 2 := (hm _ (List.getElem_mem hlt)).2
    have hgetD : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hlt
    calc ((effInputs C.gates k).toFinset ∩ S).card
        ≤ (effInputs C.gates k).toFinset.card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ (effInputs C.gates k).length := List.toFinset_card_le _
      _ ≤ (C.gates.getD k ⟨GateOp.or, []⟩).inputs.length := List.length_filter_le _ _
      _ = C.gates[k].inputs.length := by rw [hgetD]
      _ ≤ 2 := hlen
  have hG1_deg : ∀ k ∈ G1, ((effInputs C.gates k).toFinset ∩ S).card ≤ 1 := by
    intro k hk
    have h1 := Finset.mem_filter.mp hk
    have hlt : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp h1.1).1
    have hnz : tabs.getD (10 + k) 0 ≠ 0 := h1.2.1
    have hgm := hm _ (List.getElem_mem hlt)
    have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgm.1
    have hgetD : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hlt
    by_contra hgt1
    have hgt1' : 1 < ((effInputs C.gates k).toFinset ∩ S).card := Nat.lt_of_not_le hgt1
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hgt1'
    have haE := List.mem_filter.mp (List.mem_toFinset.mp (Finset.mem_inter.mp ha).1)
    have hbE := List.mem_filter.mp (List.mem_toFinset.mp (Finset.mem_inter.mp hb).1)
    have ha0 : tabs.getD a 0 = 0 := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
    have hb0 : tabs.getD b 0 = 0 := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2
    have haIn : a ∈ C.gates[k].inputs := by rw [← hgetD]; exact haE.1
    have hbIn : b ∈ C.gates[k].inputs := by rw [← hgetD]; exact hbE.1
    have hvals0 : ∀ i ∈ C.gates[k].inputs, (if i < 10 + k then tabs.getD i 0 else 0) = 0 := by
      have hlen2 : C.gates[k].inputs.length ≤ 2 := hgm.2
      rcases hL : C.gates[k].inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, tl⟩⟩⟩
      · simp [hL] at haIn
      · simp [hL] at haIn hbIn; exact absurd (haIn.trans hbIn.symm) hab
      · intro i hi
        simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at haIn hbIn hi
        rcases haIn with rfl | rfl <;> rcases hbIn with rfl | rfl
        · exact absurd rfl hab
        · rcases hi with rfl | rfl
          · split_ifs; exact ha0; rfl
          · split_ifs; exact hb0; rfl
        · rcases hi with rfl | rfl
          · split_ifs; exact hb0; rfl
          · split_ifs; exact ha0; rfl
        · exact absurd rfl hab
      · simp [hL] at hlen2
    have hgk := evalTabs_gate_eq_pre C.gates hlt
    have hmap : C.gates[k].inputs.map (fun i => if i < 10 + k then tabs.getD i 0 else 0) =
        C.gates[k].inputs.map (fun _ => 0) :=
      List.map_congr_left hvals0
    change tabs.getD (10 + k) 0 = _ at hgk
    rw [hgk, hmap] at hnz
    have hlen2 : C.gates[k].inputs.length ≤ 2 := hgm.2
    rcases hL : C.gates[k].inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, tl⟩⟩⟩
    · simp [hL] at haIn
    · rw [hL] at hnz
      rcases hop with h | h <;> simp [h, gtVal] at hnz
    · rw [hL] at hnz
      rcases hop with h | h <;> simp [h, gtVal] at hnz
    · simp [hL] at hlen2
  have hS_hi : S.card ≤ 2 * G0.card + G1.card := by
    calc S.card
        ≤ ((G0 ∪ G1).biUnion (fun k => (effInputs C.gates k).toFinset ∩ S)).card :=
          Finset.card_le_card hS_cov
      _ ≤ ∑ k ∈ G0 ∪ G1, ((effInputs C.gates k).toFinset ∩ S).card := Finset.card_biUnion_le
      _ = (∑ k ∈ G0, ((effInputs C.gates k).toFinset ∩ S).card) +
          (∑ k ∈ G1, ((effInputs C.gates k).toFinset ∩ S).card) :=
          Finset.sum_union hdisj_G
      _ ≤ (∑ _k ∈ G0, 2) + (∑ _k ∈ G1, 1) :=
          Nat.add_le_add (Finset.sum_le_sum hG0_deg) (Finset.sum_le_sum hG1_deg)
      _ = 2 * G0.card + G1.card := by simp [Nat.mul_comm]
  have hcardU : (G0 ∪ G1).card ≤
      ((Finset.range C.gates.length).filter (fun k => isTriv C.gates k = true)).card :=
    Finset.card_le_card hGsub
  rw [Finset.card_union_of_disjoint hdisj_G] at hcardU
  omega

def freeVal (S : Finset ℕ) (v : ℕ) : Prop := v = 0 ∨ v = 511 ∨ v ∈ S

def ops (a b : ℕ) : Finset ℕ :=
  ({a &&& b, a ||| b} : Finset ℕ).filter (fun z => z ≠ 0 ∧ z ≠ 511)

def build (goal : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => goal ∈ S
  | k + 1, S => build goal k S ∨
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ z ∈ ops a b, build goal k (insert z S)

def live (goal : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => s = {goal}
  | k + 1, s => live goal k s ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
        ∃ rest : Finset ℕ, s = insert a (insert b rest) ∧ live goal k (insert z rest)

theorem build_mono_k {goal k k' : ℕ} {S : Finset ℕ} (hk : k ≤ k') (h : build goal k S) :
    build goal k' S := by
  induction hk with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem compress {goal k : ℕ} {S : Finset ℕ} (h : build goal k S) :
    ∃ s ⊆ S, live goal k s := by
  induction k generalizing S with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, hk⟩
    · obtain ⟨s, hs, hl⟩ := ih h
      exact ⟨s, hs, Or.inl hl⟩
    · obtain ⟨t, ht, hl⟩ := ih hk
      by_cases hsub : t ⊆ S
      · exact ⟨t, hsub, Or.inl hl⟩
      · have hzt : z ∈ t := by
          by_contra hnz
          apply hsub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | hS
          · exact absurd hu hnz
          · exact hS
        have hzS : z ∉ S := fun hz' => hsub (by simpa [Finset.insert_eq_of_mem hz'] using ht)
        let rest := t.erase z
        have hrest : rest ⊆ S := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ S := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        have hzs : z ∉ s := fun h => hzS (hs h)
        have htr : insert z rest = t := Finset.insert_erase hzt
        refine ⟨s, hs, Or.inr ⟨a, Finset.mem_insert_self _ _, b,
          Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hab, z, hz, hzs, rest, rfl, ?_⟩⟩
        rw [htr]; exact hl

theorem build_from_circuit (C : Circuit) (hm : Monotone2 C) (hrep : Represents matA C)
    (hsize : C.size ≤ 10) : build targetVal 6 coreSet := by
  set tabs := evalTabs C.gates
  have htriv := triv_count_ge C hm hrep
  have hstep : ∀ (m : ℕ), m ≤ C.gates.length →
      ∃ S : Finset ℕ, (∀ i < 10 + m, freeVal S (tabs.getD i 0)) ∧
        (∀ b : ℕ, build targetVal b S →
          build targetVal (b + ((Finset.range m).filter (fun k => isTriv C.gates k = false)).card) coreSet) := by
    intro m hm_le
    induction m with
    | zero =>
      refine ⟨coreSet, ?_, fun b hb => by simpa using hb⟩
      intro i hi
      have hget : tabs.getD i 0 = initVals.getD i 0 :=
        foldl_stepTabs_getD_lt initVals C.gates (by simp [initVals]; omega)
      rw [hget]
      have : i ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) := by simp; omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [initVals, freeVal, coreSet, coreList]
    | succ k ih =>
      obtain ⟨S, hS, hbuild⟩ := ih (by omega)
      have hlt : k < C.gates.length := by omega
      have hgm := hm _ (List.getElem_mem hlt)
      have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgm.1
      have hval_k := evalTabs_gate_eq_pre C.gates hlt
      change tabs.getD (10 + k) 0 = _ at hval_k
      have hgetD : C.gates.getD k ⟨GateOp.or, []⟩ = C.gates[k] := List.getD_eq_getElem _ _ hlt
      have hcard_eq :
          ((Finset.range (k + 1)).filter (fun j => isTriv C.gates j = false)).card =
          ((Finset.range k).filter (fun j => isTriv C.gates j = false)).card +
            if isTriv C.gates k = false then 1 else 0 := by
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp)]
        · omega
      have hfree_or_step : freeVal S (tabs.getD (10 + k) 0) ∨
          (isTriv C.gates k = false ∧ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
            tabs.getD (10 + k) 0 ∈ ops a b) := by
        by_cases htk : isTriv C.gates k = true
        · left
          simp only [isTriv, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at htk
          rcases htk with h0 | ⟨w, hweff, hw0⟩
          · exact Or.inl h0
          · have hwE := List.mem_filter.mp hweff
            have hwIn : w ∈ C.gates[k].inputs := by rw [← hgetD]; exact hwE.1
            have hwLt : w < 10 + k := by simpa using hwE.2
            have hlen2 : C.gates[k].inputs.length ≤ 2 := hgm.2
            rcases hL : C.gates[k].inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, tl⟩⟩⟩
            · simp [hL] at hwIn
            · rw [hL] at hval_k hwIn
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwIn
              subst hwIn
              simp only [List.map_cons, List.map_nil, hwLt, ↓reduceIte] at hval_k
              change tabs.getD (10 + k) 0 = gtVal C.gates[k].op [tabs.getD w 0] at hval_k
              rw [hw0] at hval_k
              rcases hop with h | h <;> (rw [h] at hval_k; simp [gtVal] at hval_k; exact Or.inl hval_k)
            · rw [hL] at hval_k hwIn
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hwIn
              set vx := if x < 10 + k then tabs.getD x 0 else 0
              set vy := if y < 10 + k then tabs.getD y 0 else 0
              have hfx : freeVal S vx := by dsimp [vx]; split_ifs with h; exact hS x h; exact Or.inl rfl
              have hfy : freeVal S vy := by dsimp [vy]; split_ifs with h; exact hS y h; exact Or.inl rfl
              change tabs.getD (10 + k) 0 = gtVal C.gates[k].op [vx, vy] at hval_k
              rcases hwIn with rfl | rfl
              · have hvx0 : vx = 0 := by dsimp [vx]; simp only [hwLt, ↓reduceIte]; exact hw0
                rw [hvx0] at hval_k
                rcases hop with h | h
                · rw [h] at hval_k; simp only [gtVal, List.foldr_cons, List.foldr_nil, Nat.zero_and] at hval_k
                  exact Or.inl hval_k
                · rw [h] at hval_k; simp only [gtVal, List.foldr_cons, List.foldr_nil, Nat.zero_or, Nat.or_zero] at hval_k
                  rw [hval_k]; exact hfy
              · have hvy0 : vy = 0 := by dsimp [vy]; simp only [hwLt, ↓reduceIte]; exact hw0
                rw [hvy0] at hval_k
                rcases hop with h | h
                · rw [h] at hval_k; simp only [gtVal, List.foldr_cons, List.foldr_nil, Nat.zero_and, Nat.and_zero] at hval_k
                  exact Or.inl hval_k
                · rw [h] at hval_k; simp only [gtVal, List.foldr_cons, List.foldr_nil, Nat.or_zero] at hval_k
                  rw [hval_k]; exact hfx
            · simp [hL] at hlen2
        · have htkf : isTriv C.gates k = false := by cases h : isTriv C.gates k <;> simp_all
          have hlen2 : C.gates[k].inputs.length ≤ 2 := hgm.2
          rcases hL : C.gates[k].inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, tl⟩⟩⟩
          · left; rw [hL] at hval_k
            rcases hop with h | h
            · rw [h] at hval_k; simp only [List.map_nil, gtVal, List.foldr_nil] at hval_k
              exact Or.inr (Or.inl hval_k)
            · rw [h] at hval_k; simp only [List.map_nil, gtVal, List.foldr_nil] at hval_k
              exact Or.inl hval_k
          · left; rw [hL] at hval_k
            set vx := if x < 10 + k then tabs.getD x 0 else 0
            have hfx : freeVal S vx := by dsimp [vx]; split_ifs with h; exact hS x h; exact Or.inl rfl
            have hlx : vx < 2 ^ 9 := by dsimp [vx]; split_ifs; exact evalTabs_getD_lt C x; omega
            change tabs.getD (10 + k) 0 = gtVal C.gates[k].op [vx] at hval_k
            rcases hop with h | h
            · rw [h] at hval_k
              simp only [gtVal, List.foldr_cons, List.foldr_nil, and_full vx hlx] at hval_k
              rw [hval_k]; exact hfx
            · rw [h] at hval_k
              simp only [gtVal, List.foldr_cons, List.foldr_nil, Nat.or_zero] at hval_k
              rw [hval_k]; exact hfx
          · rw [hL] at hval_k
            set vx := if x < 10 + k then tabs.getD x 0 else 0
            set vy := if y < 10 + k then tabs.getD y 0 else 0
            have hfx : freeVal S vx := by dsimp [vx]; split_ifs with h; exact hS x h; exact Or.inl rfl
            have hfy : freeVal S vy := by dsimp [vy]; split_ifs with h; exact hS y h; exact Or.inl rfl
            have hlx : vx < 2 ^ 9 := by dsimp [vx]; split_ifs; exact evalTabs_getD_lt C x; omega
            have hly : vy < 2 ^ 9 := by dsimp [vy]; split_ifs; exact evalTabs_getD_lt C y; omega
            change tabs.getD (10 + k) 0 = gtVal C.gates[k].op [vx, vy] at hval_k
            have hval_simp : tabs.getD (10 + k) 0 = vx &&& vy ∨ tabs.getD (10 + k) 0 = vx ||| vy := by
              rcases hop with h | h
              · left; rw [h] at hval_k
                simp only [gtVal, List.foldr_cons, List.foldr_nil, and_full vy hly] at hval_k
                exact hval_k
              · right; rw [h] at hval_k
                simp only [gtVal, List.foldr_cons, List.foldr_nil, Nat.or_zero] at hval_k
                exact hval_k
            by_cases hv0 : tabs.getD (10 + k) 0 = 0 ∨ tabs.getD (10 + k) 0 = 511
            · left; rcases hv0 with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
            · have hv0' : tabs.getD (10 + k) 0 ≠ 0 ∧ tabs.getD (10 + k) 0 ≠ 511 :=
                ⟨fun h => hv0 (Or.inl h), fun h => hv0 (Or.inr h)⟩
              rcases hfx with hx0 | hx1 | hxS
              · left; rcases hval_simp with h | h
                · rw [hx0, Nat.zero_and] at h; exact Or.inl h
                · rw [hx0, Nat.zero_or] at h; rw [h]; exact hfy
              · left; rcases hval_simp with h | h
                · rw [hx1, Nat.land_comm, and_full vy hly] at h; rw [h]; exact hfy
                · rw [hx1, Nat.lor_comm, or_full vy hly] at h; exact Or.inr (Or.inl h)
              · rcases hfy with hy0 | hy1 | hyS
                · left; rcases hval_simp with h | h
                  · rw [hy0, Nat.and_zero] at h; exact Or.inl h
                  · rw [hy0, Nat.or_zero] at h; rw [h]; exact Or.inr (Or.inr hxS)
                · left; rcases hval_simp with h | h
                  · rw [hy1, and_full vx hlx] at h; rw [h]; exact Or.inr (Or.inr hxS)
                  · rw [hy1, or_full vx hlx] at h; exact Or.inr (Or.inl h)
                · by_cases hxy : vx = vy
                  · left
                    rcases hval_simp with h | h
                    · rw [hxy, Nat.and_self] at h; rw [h]; exact Or.inr (Or.inr hyS)
                    · rw [hxy, Nat.or_self] at h; rw [h]; exact Or.inr (Or.inr hyS)
                  · right
                    refine ⟨htkf, vx, hxS, vy, hyS, hxy, ?_⟩
                    simp only [ops, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨hval_simp, hv0'.1, hv0'.2⟩
          · simp [hL] at hlen2
      rcases hfree_or_step with hfree | ⟨htkf, a, ha, b, hb, hab, hops⟩
      · refine ⟨S, fun i hi => ?_, fun r hr => ?_⟩
        · by_cases hik : i < 10 + k
          · exact hS i hik
          · have : i = 10 + k := by omega
            subst this; exact hfree
        · rw [hcard_eq]
          exact build_mono_k (by omega) (hbuild r hr)
      · refine ⟨insert (tabs.getD (10 + k) 0) S, fun i hi => ?_, fun r hr => ?_⟩
        · by_cases hik : i < 10 + k
          · rcases hS i hik with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
          · have : i = 10 + k := by omega
            subst this; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
        · rw [hcard_eq]; simp only [htkf, ↓reduceIte]
          have h1 : build targetVal (r + 1) S := Or.inr ⟨a, ha, b, hb, hab, _, hops, hr⟩
          have h2 := hbuild (r + 1) h1
          exact build_mono_k (by omega) h2
  obtain ⟨S, hS, hbuild⟩ := hstep C.gates.length (le_refl _)
  have hout := evalTabs_output C hm hrep
  change tabs.getD C.output 0 = targetVal at hout
  have hmem : targetVal ∈ S := by
    by_cases hlt : C.output < 10 + C.gates.length
    · rcases hS C.output hlt with h | h | h
      · rw [hout] at h; simp [targetVal] at h
      · rw [hout] at h; simp [targetVal] at h
      · rw [hout] at h; exact h
    · have hlen : tabs.length = 10 + C.gates.length := by
        rw [show tabs = evalTabs C.gates from rfl, evalTabs, foldl_stepTabs_length]; simp [initVals]
      rw [List.getD_eq_default _ _ (by omega)] at hout
      simp [targetVal] at hout
  have hpart : ((Finset.range C.gates.length).filter (fun k => isTriv C.gates k = true)).card +
      ((Finset.range C.gates.length).filter (fun k => isTriv C.gates k = false)).card =
      C.gates.length := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.range C.gates.length)
      (p := fun k => isTriv C.gates k = true)
    simp only [Bool.not_eq_true, Finset.card_range] at h
    exact h
  have h0 : build targetVal 0 S := hmem
  have hb := hbuild 0 h0
  change C.gates.length ≤ 10 at hsize
  exact build_mono_k (by omega) hb

def sepList (l : List ℕ) : Bool :=
  [0, 4, 5, 8].all fun b =>
    ((l.foldl (fun acc w => if w.testBit b then acc else acc ||| w) 0) &&& targetVal) == targetVal

def separates (s : Finset ℕ) : Prop :=
  ∀ b ∈ ({0, 4, 5, 8} : Finset ℕ), ∀ a ∈ ({1, 2, 3, 6, 7} : Finset ℕ),
    ∃ w ∈ s, w.testBit a = true ∧ w.testBit b = false

theorem live_separates {k : ℕ} {s : Finset ℕ} (h : live targetVal k s) : separates s := by
  induction k generalizing s with
  | zero =>
    rw [live] at h; subst h
    intro b hb a ha
    refine ⟨targetVal, Finset.mem_singleton_self _, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> decide
  | succ k ih =>
    rcases h with h | ⟨x, hx, y, hy, _, z, hz, _, rest, hseq, hnext⟩
    · exact ih h
    · intro b hb a ha
      obtain ⟨w, hw, hwa, hwb⟩ := ih hnext b hb a ha
      rcases Finset.mem_insert.mp hw with rfl | hwr
      · simp only [ops, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz.1 with rfl | rfl
        · rw [Nat.testBit_and, Bool.and_eq_true] at hwa
          rw [Nat.testBit_and, Bool.and_eq_false_iff] at hwb
          rcases hwb with hxb | hyb
          · exact ⟨x, hx, hwa.1, hxb⟩
          · exact ⟨y, hy, hwa.2, hyb⟩
        · rw [Nat.testBit_or, Bool.or_eq_true] at hwa
          rw [Nat.testBit_or, Bool.or_eq_false_iff] at hwb
          rcases hwa with hxa | hya
          · exact ⟨x, hx, hxa, hwb.1⟩
          · exact ⟨y, hy, hya, hwb.2⟩
      · exact ⟨w, hseq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwr), hwa, hwb⟩

theorem sep_subset_core_eq {s : Finset ℕ} (hsub : s ⊆ coreSet) (hsep : separates s) :
    s = coreSet := by
  apply Finset.Subset.antisymm hsub
  intro w hw
  have hmem : ∀ (a b : ℕ), a ∈ ({1, 2, 3, 6, 7} : Finset ℕ) → b ∈ ({0, 4, 5, 8} : Finset ℕ) →
      (∀ u ∈ coreSet, u ≠ w → (u.testBit a = true → u.testBit b = true)) → w ∈ s := by
    intro a b ha hb huniq
    obtain ⟨u, hus, hua, hub⟩ := hsep b hb a ha
    by_cases huw : u = w
    · exact huw ▸ hus
    · exact absurd (huniq u (hsub hus) huw hua) (by rw [hub]; decide)
  have hwL : w ∈ coreList := List.mem_toFinset.mp hw
  simp only [coreList, List.mem_cons, List.not_mem_nil, or_false] at hwL
  rcases hwL with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hmem 1 4 (by decide) (by decide) (by decide)
  · exact hmem 3 0 (by decide) (by decide) (by decide)
  · exact hmem 6 0 (by decide) (by decide) (by decide)
  · exact hmem 3 4 (by decide) (by decide) (by decide)
  · exact hmem 1 0 (by decide) (by decide) (by decide)
  · exact hmem 2 0 (by decide) (by decide) (by decide)

theorem foldl_or_bit (l : List ℕ) (b a acc : ℕ) :
    (l.foldl (fun acc w => if w.testBit b then acc else acc ||| w) acc).testBit a = true ↔
      acc.testBit a = true ∨ ∃ w ∈ l, w.testBit b = false ∧ w.testBit a = true := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    cases hxb : x.testBit b
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
      constructor
      · rintro ((h1 | h2) | ⟨w, hw, hb, ha⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨x, Or.inl rfl, hxb, h2⟩
        · exact Or.inr ⟨w, Or.inr hw, hb, ha⟩
      · rintro (h1 | ⟨w, rfl | hw, hb, ha⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr ha)
        · exact Or.inr ⟨w, hw, hb, ha⟩
    · simp only [↓reduceIte]
      constructor
      · rintro (h1 | ⟨w, hw, hb, ha⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨w, Or.inr hw, hb, ha⟩
      · rintro (h1 | ⟨w, rfl | hw, hb, ha⟩)
        · exact Or.inl h1
        · rw [hxb] at hb; cases hb
        · exact Or.inr ⟨w, hw, hb, ha⟩

theorem sepList_of_separates {l : List ℕ} (h : separates l.toFinset) : sepList l = true := by
  simp only [sepList, List.all_eq_true, beq_iff_eq]
  intro b hb
  apply Nat.eq_of_testBit_eq
  intro a
  rw [Nat.testBit_and]
  cases ht : targetVal.testBit a
  · simp
  · simp only [Bool.and_true]
    have ha : a ∈ ({1, 2, 3, 6, 7} : Finset ℕ) := by
      have haN : a < 9 := by
        by_contra hge
        have hlt : targetVal < 2 ^ a :=
          lt_of_lt_of_le (show targetVal < 2 ^ 9 by decide)
            (Nat.pow_le_pow_right (by omega) (by omega))
        rw [Nat.testBit_lt_two_pow hlt] at ht; cases ht
      have hfin : (⟨a, haN⟩ : Fin 9).val ∈ ({1, 2, 3, 6, 7} : Finset ℕ) := by
        have ht' : targetVal.testBit (⟨a, haN⟩ : Fin 9).val = true := ht
        generalize (⟨a, haN⟩ : Fin 9) = p at ht' ⊢
        fin_cases p <;> revert ht' <;> decide
      exact hfin
    have hbF : b ∈ ({0, 4, 5, 8} : Finset ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> decide
    obtain ⟨w, hw, hwa, hwb⟩ := h b hbF a ha
    exact (foldl_or_bit l b a 0).mpr (Or.inr ⟨w, List.mem_toFinset.mp hw, hwb, hwa⟩)

theorem live_card_le {k : ℕ} {s : Finset ℕ} (h : live targetVal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => rw [live] at h; subst h; simp
  | succ k ih =>
    rcases h with h | ⟨a, _, b, _, _, z, _, hzs, rest, rfl, hnext⟩
    · have := ih h; omega
    · have h1 := ih hnext
      have h2 : (insert a (insert b rest)).card ≤ rest.card + 2 := by
        calc (insert a (insert b rest)).card ≤ (insert b rest).card + 1 := Finset.card_insert_le _ _
          _ ≤ rest.card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      have hzr : z ∉ rest := fun h => hzs (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      rw [Finset.card_insert_of_notMem hzr] at h1
      omega

theorem live_nonempty {k : ℕ} {s : Finset ℕ} (h : live targetVal k s) : s.Nonempty := by
  induction k generalizing s with
  | zero => rw [live] at h; subst h; exact Finset.singleton_nonempty _
  | succ k ih =>
    rcases h with h | ⟨a, ha, _, _, _, _, _, _, _, _, _⟩
    · exact ih h
    · exact ⟨a, ha⟩

theorem live_singleton_eq {k x : ℕ} (h : live targetVal k {x}) : x = targetVal := by
  induction k with
  | zero =>
    rw [live] at h
    exact Finset.singleton_injective h
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, _, _, _, _, _, _⟩
    · exact ih h
    · rw [Finset.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab

theorem eraseIdx_toFinset_of_nodup {s : List ℕ} (hnd : s.Nodup) {i : ℕ} (hi : i < s.length) :
    (s.eraseIdx i).toFinset = s.toFinset.erase s[i] := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  constructor
  · intro hx
    have hmem : x ∈ s := List.mem_of_mem_eraseIdx hx
    refine ⟨?_, hmem⟩
    rintro rfl
    obtain ⟨m, hm, hxm⟩ := List.getElem_of_mem hx
    rw [List.getElem_eraseIdx] at hxm
    split_ifs at hxm with hlt
    · have := (List.Nodup.getElem_inj_iff hnd).mp hxm; omega
    · have := (List.Nodup.getElem_inj_iff hnd).mp hxm; omega
  · rintro ⟨hne, hx⟩
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    have hmi : m ≠ i := fun e => hne (by subst e; rfl)
    by_cases hlt : m < i
    · have hm' : m < (s.eraseIdx i).length := by rw [List.length_eraseIdx_of_lt hi]; omega
      have heq : (s.eraseIdx i)[m] = s[m] := by rw [List.getElem_eraseIdx]; simp only [hlt, ↓reduceDIte]
      rw [← heq]
      exact List.getElem_mem hm'
    · have hgt : i < m := by omega
      have hm' : m - 1 < (s.eraseIdx i).length := by rw [List.length_eraseIdx_of_lt hi]; omega
      have heq : (s.eraseIdx i)[m - 1] = s[m] := by
        rw [List.getElem_eraseIdx]
        have hnot : ¬ m - 1 < i := by omega
        simp only [hnot, ↓reduceDIte]
        congr 1; omega
      rw [← heq]
      exact List.getElem_mem hm'

def tryZ (go : List ℕ → Bool) (n k : ℕ) (s : List ℕ) (i j z : ℕ) : Bool :=
  if z == 0 || z == 511 || s.contains z then false
  else
    let sDrop := z :: ((s.eraseIdx j).eraseIdx i)
    if go sDrop then true
    else if n ≤ k then
      let sA := z :: (s.eraseIdx j)
      if go sA then true
      else
        let sB := z :: (s.eraseIdx i)
        if go sB then true
        else if n + 1 ≤ k then go (z :: s)
        else false
    else false

def loopJ (go : List ℕ → Bool) (n k : ℕ) (s : List ℕ) (i a : ℕ) : ℕ → List ℕ → Bool
  | _, [] => false
  | j, b :: bs =>
    if tryZ go n k s i j (a &&& b) then true
    else if tryZ go n k s i j (a ||| b) then true
    else loopJ go n k s i a (j + 1) bs

def loopI (go : List ℕ → Bool) (n k : ℕ) (s : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => false
  | i, a :: rest =>
    if loopJ go n k s i a (i + 1) rest then true
    else loopI go n k s (i + 1) rest

def search : ℕ → List ℕ → Bool
  | 0, s =>
    match s with
    | [x] => x == targetVal
    | _ => false
  | k + 1, s =>
    let n := s.length
    if n == 1 then
      match s with
      | [x] => x == targetVal
      | _ => false
    else if n > k + 2 then false
    else if !sepList s then false
    else if k == 0 then
      match s with
      | [a, b] => ((a &&& b) == targetVal) || ((a ||| b) == targetVal)
      | _ => false
    else
      if n ≤ k + 1 && search k s then true
      else loopI (search k) n (k + 1) s 0 s

theorem tryZ_sound {go : List ℕ → Bool} {k : ℕ}
    (hgo : ∀ l : List ℕ, l.Nodup → live targetVal k l.toFinset → go l = true)
    {s : List ℕ} (hnd : s.Nodup) {i j : ℕ} (hij : i < j) (hj : j < s.length)
    {z : ℕ} (hz0 : z ≠ 0) (hzFull : z ≠ 511) (hzs : z ∉ s.toFinset)
    {rest : Finset ℕ} (hseq : s.toFinset = insert s[i] (insert s[j] rest))
    (hnext : live targetVal k (insert z rest)) :
    tryZ go s.length (k + 1) s i j z = true := by
  have hi : i < s.length := lt_trans hij hj
  have hcz : s.contains z = false := by
    cases h : s.contains z
    · rfl
    · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) hzs
  have hcond : (z == 0 || z == 511 || s.contains z) = false := by
    simp only [hcz, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨hz0, hzFull⟩
  unfold tryZ
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hsub_rest : rest ⊆ s.toFinset := fun x hx =>
    hseq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hcard_s : s.toFinset.card = s.length := List.toFinset_card_of_nodup hnd
  have hcard_next : (insert z rest).card ≤ k + 1 := live_card_le hnext
  have hzr : z ∉ rest := fun h => hzs (hsub_rest h)
  have hnd_ej : (s.eraseIdx j).Nodup := hnd.eraseIdx j
  have hnd_eji : ((s.eraseIdx j).eraseIdx i).Nodup := hnd_ej.eraseIdx i
  have hlen_ej : (s.eraseIdx j).length = s.length - 1 := List.length_eraseIdx_of_lt hj
  have hi_ej : i < (s.eraseIdx j).length := by omega
  have hget_ej : (s.eraseIdx j)[i] = s[i] := by rw [List.getElem_eraseIdx]; simp only [hij, ↓reduceDIte]
  have hej_set : (s.eraseIdx j).toFinset = s.toFinset.erase s[j] :=
    eraseIdx_toFinset_of_nodup hnd hj
  have hei_set : (s.eraseIdx i).toFinset = s.toFinset.erase s[i] :=
    eraseIdx_toFinset_of_nodup hnd hi
  have heji_set : ((s.eraseIdx j).eraseIdx i).toFinset = (s.toFinset.erase s[j]).erase s[i] := by
    rw [eraseIdx_toFinset_of_nodup hnd_ej hi_ej, hget_ej, hej_set]
  by_cases ha : s[i] ∈ rest <;> by_cases hb : s[j] ∈ rest
  · have hr_eq : rest = s.toFinset := by
      rw [hseq, Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
    have hle1 : s.length + 1 ≤ k + 1 := by
      rw [Finset.card_insert_of_notMem hzr, hr_eq, hcard_s] at hcard_next
      exact hcard_next
    have hle0 : s.length ≤ k + 1 := by omega
    have hnd_z : (z :: s).Nodup := List.nodup_cons.mpr ⟨fun h => hzs (List.mem_toFinset.mpr h), hnd⟩
    have hgo_z : go (z :: s) = true := by
      apply hgo (z :: s) hnd_z
      rw [List.toFinset_cons, ← hr_eq]; exact hnext
    by_cases h1 : go (z :: (s.eraseIdx j).eraseIdx i) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, hle0]
      by_cases h2 : go (z :: s.eraseIdx j) = true
      · simp [h2]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : go (z :: s.eraseIdx i) = true
        · simp [h3]
        · simp [h3, hle1, hgo_z]
  · have hr_eq : rest = s.toFinset.erase s[j] := by
      ext x
      rw [hseq, Finset.mem_erase, Finset.mem_insert, Finset.mem_insert]
      constructor
      · intro hx; exact ⟨fun e => hb (e ▸ hx), Or.inr (Or.inr hx)⟩
      · rintro ⟨hxb, rfl | rfl | hx⟩
        · exact ha
        · exact absurd rfl hxb
        · exact hx
    have hle0 : s.length ≤ k + 1 := by
      rw [Finset.card_insert_of_notMem hzr, hr_eq,
        Finset.card_erase_of_mem (List.mem_toFinset.mpr (List.getElem_mem hj)), hcard_s] at hcard_next
      omega
    have hnd_z : (z :: s.eraseIdx j).Nodup := List.nodup_cons.mpr
      ⟨fun h => hzs (List.mem_toFinset.mpr (List.mem_of_mem_eraseIdx h)), hnd_ej⟩
    have hgo_z : go (z :: s.eraseIdx j) = true := by
      apply hgo _ hnd_z
      rw [List.toFinset_cons, hej_set, ← hr_eq]; exact hnext
    by_cases h1 : go (z :: (s.eraseIdx j).eraseIdx i) = true
    · simp [h1]
    · simp [h1, hle0, hgo_z]
  · have hr_eq : rest = s.toFinset.erase s[i] := by
      ext x
      rw [hseq, Finset.mem_erase, Finset.mem_insert, Finset.mem_insert]
      constructor
      · intro hx; exact ⟨fun e => ha (e ▸ hx), Or.inr (Or.inr hx)⟩
      · rintro ⟨hxa, rfl | rfl | hx⟩
        · exact absurd rfl hxa
        · exact hb
        · exact hx
    have hle0 : s.length ≤ k + 1 := by
      rw [Finset.card_insert_of_notMem hzr, hr_eq,
        Finset.card_erase_of_mem (List.mem_toFinset.mpr (List.getElem_mem hi)), hcard_s] at hcard_next
      omega
    have hnd_z : (z :: s.eraseIdx i).Nodup := List.nodup_cons.mpr
      ⟨fun h => hzs (List.mem_toFinset.mpr (List.mem_of_mem_eraseIdx h)), hnd.eraseIdx i⟩
    have hgo_z : go (z :: s.eraseIdx i) = true := by
      apply hgo _ hnd_z
      rw [List.toFinset_cons, hei_set, ← hr_eq]; exact hnext
    by_cases h1 : go (z :: (s.eraseIdx j).eraseIdx i) = true
    · simp [h1]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, hle0]
      by_cases h2 : go (z :: s.eraseIdx j) = true
      · simp [h2]
      · simp [h2, hgo_z]
  · have hr_eq : rest = (s.toFinset.erase s[j]).erase s[i] := by
      ext x
      rw [hseq, Finset.mem_erase, Finset.mem_erase, Finset.mem_insert, Finset.mem_insert]
      constructor
      · intro hx; exact ⟨fun e => ha (e ▸ hx), fun e => hb (e ▸ hx), Or.inr (Or.inr hx)⟩
      · rintro ⟨hxa, hxb, rfl | rfl | hx⟩
        · exact absurd rfl hxa
        · exact absurd rfl hxb
        · exact hx
    have hnd_z : (z :: (s.eraseIdx j).eraseIdx i).Nodup := List.nodup_cons.mpr
      ⟨fun h => hzs (List.mem_toFinset.mpr (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx h))), hnd_eji⟩
    have hgo_z : go (z :: (s.eraseIdx j).eraseIdx i) = true := by
      apply hgo _ hnd_z
      rw [List.toFinset_cons, heji_set, ← hr_eq]; exact hnext
    rw [hgo_z]; rfl

theorem loopJ_sound {go : List ℕ → Bool} {n k : ℕ} {s : List ℕ} {i a : ℕ} :
    ∀ (j : ℕ) (l : List ℕ) (d : ℕ) (hd : d < l.length),
      (tryZ go n k s i (j + d) (a &&& l[d]) = true ∨
        tryZ go n k s i (j + d) (a ||| l[d]) = true) →
      loopJ go n k s i a j l = true
  | _, [], _, hd, _ => by simp at hd
  | j, b :: bs, 0, _, h => by
    simp only [loopJ, Nat.add_zero, List.getElem_cons_zero] at h ⊢
    rcases h with h | h <;> simp [h]
  | j, b :: bs, d + 1, hd, h => by
    simp only [loopJ]
    have hd' : d < bs.length := by simp at hd; omega
    have h' : tryZ go n k s i ((j + 1) + d) (a &&& bs[d]'hd') = true ∨
        tryZ go n k s i ((j + 1) + d) (a ||| bs[d]'hd') = true := by
      have hadd : j + (d + 1) = (j + 1) + d := by omega
      simpa [hadd] using h
    have ih := loopJ_sound (j + 1) bs d hd' h'
    split_ifs <;> simp [ih]

theorem loopI_sound {go : List ℕ → Bool} {n k : ℕ} {s : List ℕ} :
    ∀ (i : ℕ) (l : List ℕ) (d1 d2 : ℕ) (h12 : d1 < d2) (hd2 : d2 < l.length),
      (tryZ go n k s (i + d1) (i + d2) (l[d1] &&& l[d2]) = true ∨
        tryZ go n k s (i + d1) (i + d2) (l[d1] ||| l[d2]) = true) →
      loopI go n k s i l = true
  | _, [], _, _, _, hd2, _ => by simp at hd2
  | i, a :: rest, 0, d2 + 1, _, hd2, h => by
    simp only [loopI]
    have hd2' : d2 < rest.length := by simp at hd2; omega
    have h' : tryZ go n k s i ((i + 1) + d2) (a &&& rest[d2]'hd2') = true ∨
        tryZ go n k s i ((i + 1) + d2) (a ||| rest[d2]'hd2') = true := by
      have hadd : i + (d2 + 1) = (i + 1) + d2 := by omega
      simpa [hadd] using h
    have hj := loopJ_sound (i + 1) rest d2 hd2' h'
    rw [hj]; rfl
  | i, a :: rest, d1 + 1, d2 + 1, h12, hd2, h => by
    simp only [loopI]
    have hd2' : d2 < rest.length := by simp at hd2; omega
    have hd1' : d1 < rest.length := by omega
    have h' : tryZ go n k s ((i + 1) + d1) ((i + 1) + d2) (rest[d1]'hd1' &&& rest[d2]'hd2') = true ∨
        tryZ go n k s ((i + 1) + d1) ((i + 1) + d2) (rest[d1]'hd1' ||| rest[d2]'hd2') = true := by
      have hadd1 : i + (d1 + 1) = (i + 1) + d1 := by omega
      have hadd2 : i + (d2 + 1) = (i + 1) + d2 := by omega
      simpa [hadd1, hadd2] using h
    have ih := loopI_sound (i + 1) rest d1 d2 (by omega) hd2' h'
    split_ifs <;> simp [ih]

theorem search_sound : ∀ (k : ℕ) (s : List ℕ), s.Nodup → live targetVal k s.toFinset → search k s = true
  | 0, s, hnd, hlive => by
    rw [live] at hlive
    have hlen : s.length = 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hlive]; simp
    rcases s with _ | ⟨x, _ | ⟨y, tl⟩⟩
    · simp at hlen
    · have hx : x = targetVal := Finset.singleton_injective (by simpa using hlive)
      simp [search, hx]
    · simp at hlen
  | k + 1, s, hnd, hlive => by
    have hcard_s : s.toFinset.card = s.length := List.toFinset_card_of_nodup hnd
    have hle : s.length ≤ k + 2 := by rw [← hcard_s]; exact live_card_le hlive
    have hsep : sepList s = true := sepList_of_separates (live_separates hlive)
    have hne0 : s.length ≠ 0 := by
      intro h0
      have hemp : s = [] := List.eq_nil_of_length_eq_zero h0
      subst hemp
      obtain ⟨x, hx⟩ := live_nonempty hlive
      simp at hx
    unfold search
    dsimp only
    by_cases h1 : s.length = 1
    · have hb1 : (s.length == 1) = true := beq_iff_eq.mpr h1
      simp only [hb1, ↓reduceIte]
      rcases s with _ | ⟨x, _ | ⟨y, tl⟩⟩
      · simp at h1
      · have hx : x = targetVal := live_singleton_eq (by simpa using hlive)
        simp [hx]
      · simp at h1
    · have hb1 : (s.length == 1) = false := beq_eq_false_iff_ne.mpr h1
      have hgt : ¬ s.length > k + 2 := by omega
      simp only [hb1, Bool.false_eq_true, ↓reduceIte, hgt, hsep, Bool.not_true]
      by_cases hk0 : k = 0
      · subst hk0
        simp only [beq_self_eq_true, ↓reduceIte]
        have h2 : s.length = 2 := by omega
        rcases s with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp at h2
        · simp at h2
        · rcases hlive with h0 | ⟨x, hx, y, hy, hxy, z, hz, _, rest, _, hnext⟩
          · rw [live] at h0
            have : ({a, b} : Finset ℕ).card = 1 := by simpa using congrArg Finset.card h0
            have hab : a ≠ b := by simp at hnd; exact hnd
            rw [Finset.card_pair hab] at this; omega
          · rw [live] at hnext
            have hzt : z = targetVal := by
              have : z ∈ ({targetVal} : Finset ℕ) := hnext ▸ Finset.mem_insert_self _ _
              exact Finset.mem_singleton.mp this
            subst hzt
            simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
              Finset.notMem_empty, or_false] at hx hy
            simp only [ops, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact absurd rfl hxy
            · rcases hz.1 with h | h <;> simp [h.symm]
            · rcases hz.1 with h | h
              · rw [Nat.land_comm] at h; simp [h.symm]
              · rw [Nat.lor_comm] at h; simp [h.symm]
            · exact absurd rfl hxy
        · simp at h2
      · have hbk0 : (k == 0) = false := beq_eq_false_iff_ne.mpr hk0
        simp only [hbk0, Bool.false_eq_true, ↓reduceIte]
        rcases hlive with hskip | ⟨a, ha, b, hb, hab, z, hz, hzs, rest, hseq, hnext⟩
        · have hle_skip : s.length ≤ k + 1 := by rw [← hcard_s]; exact live_card_le hskip
          have hih := search_sound k s hnd hskip
          simp [hle_skip, hih]
        · by_cases hsk : (decide (s.length ≤ k + 1) && search k s) = true
          · simp [hsk]
          · simp only [hsk, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp ha)
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hb)
            have hij_ne : i ≠ j := fun e => hab (by subst e; rfl)
            simp only [ops, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hz
            have hgo := fun l hl hlv => search_sound k l hl hlv
            rcases Nat.lt_or_gt_of_ne hij_ne with hij | hji
            · have htz := tryZ_sound hgo hnd hij hj hz.2.1 hz.2.2 hzs hseq hnext
              apply loopI_sound 0 s i j hij hj
              rcases hz.1 with rfl | rfl
              · left; simpa using htz
              · right; simpa using htz
            · have hseq' : s.toFinset = insert s[j] (insert s[i] rest) := by
                rw [hseq, Finset.insert_comm]
              have htz := tryZ_sound hgo hnd hji hi hz.2.1 hz.2.2 hzs hseq' hnext
              apply loopI_sound 0 s j i hji hi
              rcases hz.1 with rfl | rfl
              · left; rw [Nat.land_comm] at htz; simpa using htz
              · right; rw [Nat.lor_comm] at htz; simpa using htz

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem search_false : search 6 coreList = false := by decide +kernel

theorem lower : ¬ RepSizeAtMost matA 10 := by
  rintro ⟨C, hm, hsize, hrep⟩
  have hb := build_from_circuit C hm hrep hsize
  obtain ⟨s, hsub, hlive⟩ := compress hb
  have heq : s = coreSet := sep_subset_core_eq hsub (live_separates hlive)
  subst heq
  have hnd : coreList.Nodup := by decide
  have ht := search_sound 6 coreList hnd hlive
  rw [search_false] at ht
  cases ht

end PEqualNP.Outside.L_meta_10299

theorem PEqualNP.Outside.L_meta_10299 :
    ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (24151086 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_10299.lower
