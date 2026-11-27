import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4827
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def rgp (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem pkey (n : ℕ) (r : ℕ → ℕ) (hlt : ∀ v, v < n → r v < n) (hge : ∀ v, n ≤ v → r v = v) :
    ∀ (gs : List Gate) (U U' : List Bool), U.length = U'.length → n ≤ U.length →
      (∀ v, U'.getD v false = U.getD (r v) false) →
      ∀ v, (wf gs U').getD v false = (wf (gs.map (rgp r)) U).getD (r v) false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ h v; exact h v
  | cons g gs ih =>
    intro U U' hlen hn h v
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U'.getD i false)
        = (rgp r g).op.eval ((rgp r g).inputs.map fun i => U.getD i false) := by
      show _ = g.op.eval ((g.inputs.map r).map fun i => U.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [← hv]
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ v
    intro t
    rcases Nat.lt_trichotomy t U'.length with ht | ht | ht
    · have h1 : r t < U.length := by
        by_cases htn : t < n
        · have := hlt t htn; omega
        · rw [hge t (by omega)]; omega
      rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ h1]
      exact h t
    · subst ht
      rw [hge _ (by omega), getD_snoc_eq, ← hlen, getD_snoc_eq]
    · rw [hge _ (by omega), getD_snoc_gt _ _ _ ht, getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_4827

open PEqualNP.Outside.L_meta_4827 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4827 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x3 : Fin (9 : ℕ)) (x4 : Fin x1.size), (∀ (x5 : Fin (9 : ℕ)), x2 (x2 x5) = x5) → PEqualNP.MetaComplexity.FanInTwo x1 → (x1.gates.get x4).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or → (∀ (x8 : Fin x1.size), ↑x3 ∈ (x1.gates.get x8).inputs ↔ x8 = x4) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin x9.size), PEqualNP.MetaComplexity.FanInTwo x9 ∧ x9.size = x1.size ∧ (∀ (x11 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x9 x11 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => x11 (x2 x12)) ∧ (x9.gates.get x10).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ (x11 : Fin x9.size), ↑(x2 x3) ∈ (x9.gates.get x11).inputs ↔ x11 = x10 := by
  intro C σ a k hinv hF hop hread
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, r = fun i => if h : i < 9 then ((σ ⟨i, h⟩ : Fin 9) : ℕ) else i := ⟨_, rfl⟩
  have hlt : ∀ v (h : v < 9), r v = ((σ ⟨v, h⟩ : Fin 9) : ℕ) := by
    intro v h; rw [hr]; simp [h]
  have hge : ∀ v, 9 ≤ v → r v = v := by
    intro v h; rw [hr]; simp [Nat.not_lt.mpr h]
  have hlt' : ∀ v, v < 9 → r v < 9 := by
    intro v h; rw [hlt v h]; exact (σ ⟨v, h⟩).isLt
  have hsz : (C.gates.map (rgp r)).length = C.gates.length := List.length_map _
  have hk : k.1 < C.gates.length := k.2
  have hmemr : ∀ (ins : List ℕ) (b : Fin 9), (σ b).1 ∈ ins.map r ↔ b.1 ∈ ins := by
    intro ins b
    rw [List.mem_map]
    constructor
    · rintro ⟨i, hi, hri⟩
      by_cases h9 : i < 9
      · rw [hlt i h9] at hri
        have h2 : σ ⟨i, h9⟩ = σ b := Fin.ext hri
        have h3 : (⟨i, h9⟩ : Fin 9) = b := by
          have := congrArg σ h2
          rw [hinv, hinv] at this
          exact this
        rw [← h3]; exact hi
      · rw [hge i (by omega)] at hri
        have := (σ b).isLt
        omega
    · intro hb
      exact ⟨b.1, hb, hlt b.1 b.2⟩
  refine ⟨⟨C.gates.map (rgp r), r C.output⟩, ⟨k.1, by rw [← hsz] at hk; exact hk⟩, ?_, hsz, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    refine ⟨(hF g0 hg0).1, ?_⟩
    show (g0.inputs.map r).length ≤ 2
    rw [List.length_map]; exact (hF g0 hg0).2
  · intro x
    show (wf (C.gates.map (rgp r)) (List.ofFn x)).getD (r C.output) false
      = (wf C.gates (List.ofFn fun i : Fin 9 => x (σ i))).getD C.output false
    refine (pkey 9 r hlt' hge C.gates (List.ofFn x) (List.ofFn fun i : Fin 9 => x (σ i))
      (by simp) (by simp) ?_ C.output).symm
    intro v
    by_cases hv : v < 9
    · rw [hlt v hv]
      have e1 := getD_ofFn (fun i : Fin 9 => x (σ i)) ⟨v, hv⟩
      have e2 := getD_ofFn x (σ ⟨v, hv⟩)
      rw [e2]
      exact e1
    · rw [hge v (by omega), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  · have e : ((C.gates.map (rgp r))[k.1]'(by rw [hsz]; exact hk)) = rgp r C.gates[k.1] :=
      List.getElem_map _
    show ((C.gates.map (rgp r))[k.1]'(by rw [hsz]; exact hk)).op ≠ GateOp.or
    rw [e]
    exact hop
  · intro j
    have hj : j.1 < C.gates.length := by have := j.2; rw [← hsz]; exact this
    have e : ((C.gates.map (rgp r))[j.1]'(by rw [hsz]; exact hj)) = rgp r C.gates[j.1] :=
      List.getElem_map _
    show (σ a).1 ∈ ((C.gates.map (rgp r))[j.1]'(by rw [hsz]; exact hj)).inputs ↔ j = ⟨k.1, _⟩
    rw [e]
    show (σ a).1 ∈ (C.gates[j.1]).inputs.map r ↔ _
    rw [hmemr, Fin.ext_iff]
    have := hread ⟨j.1, hj⟩
    rw [Fin.ext_iff] at this
    exact this
