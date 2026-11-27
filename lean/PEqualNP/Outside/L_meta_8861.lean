import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8861

open PEqualNP.Defs.LratEncoding PEqualNP.CircuitLowerBounds

theorem litP (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  have h1 : (2 * v + 2) / 2 = v + 1 := by omega
  have h2 : (2 * v + 2) % 2 = 0 := by omega
  simp only [litVal, P, h1, h2]
  cases a (v + 1) <;> rfl

theorem litQ (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  have h1 : (2 * v + 3) / 2 = v + 1 := by omega
  have h2 : (2 * v + 3) % 2 = 1 := by omega
  simp only [litVal, Q, h1, h2]
  cases a (v + 1) <;> rfl

theorem litL (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> cases h : a (v + 1) <;> simp [L, litP, litQ, h]

def W (n : ℕ) (val : ℕ → ℕ → Bool) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then val (k - n) r else false

theorem gen (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hsat : FormulaSat (enc n s g rows)) :
    ∃ (val : ℕ → ℕ → Bool),
      (∀ j < s, ∃ (o : GateOp) (lst : List ℕ), (o = GateOp.and ∨ o = GateOp.or) ∧ lst.length ≤ 2 ∧
        ∀ r ∈ rows, val j r = o.eval (lst.map fun i => W n val j i r)) ∧
      ∃ out : ℕ, ∀ r ∈ rows, W n val s out r = g r := by
  obtain ⟨a, ha⟩ := hsat
  have mem : ∀ c, (c ∈ fOp n s ∨ c ∈ fSrcAlo n s ∨ c ∈ fSrcEq n s rows ∨ c ∈ fGate n s rows ∨
      c ∈ fOutAlo n s ∨ c ∈ fOutEq n s g rows) → ClauseSat a c := by
    intro c hc
    apply ha
    simp only [enc, List.mem_append]
    tauto
  have hOp : ∀ j < s, a (ix n s 0 j 0 + 1) = true ∨ a (ix n s 0 j 1 + 1) = true ∨
      a (ix n s 0 j 2 + 1) = true := by
    intro j hj
    have := mem [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]
      (Or.inl (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
    simpa [ClauseSat, litP] using this
  have hAlo : ∀ e ∈ [1, 2], ∀ j < s, ∃ k < n + j + 1, a (ix n s e j k + 1) = true := by
    intro e he j hj
    obtain ⟨l, hl, hv⟩ := mem ((List.range (n + j + 1)).map fun k => P (ix n s e j k))
      (Or.inr (Or.inl (List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)))
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    exact ⟨k, List.mem_range.1 hk, by rw [litP] at hv; exact hv⟩
  have hSrc : ∀ e ∈ [1, 2], ∀ j < s, ∀ r ∈ rows, ∀ k < n + j + 1, ∀ c ∈ srcEq n s e j k r,
      ClauseSat a c :=
    fun e he j hj r hr k hk c hc => mem c (Or.inr (Or.inr (Or.inl (List.mem_flatMap.2 ⟨e, he,
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr,
        List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hc⟩⟩⟩⟩))))
  have hG : ∀ j < s, ∀ r ∈ rows, ∀ c ∈ gateCl n s j r, ClauseSat a c :=
    fun j hj r hr c hc => mem c (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_flatMap.2 ⟨j,
      List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr, hc⟩⟩)))))
  have hOA : ∃ k < n + s + 1, a (ix n s 6 0 k + 1) = true := by
    obtain ⟨l, hl, hv⟩ := mem ((List.range (n + s + 1)).map fun k => P (ix n s 6 0 k))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_singleton.2 rfl))))))
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
    exact ⟨k, List.mem_range.1 hk, by rw [litP] at hv; exact hv⟩
  have hOE : ∀ r ∈ rows, ∀ k < n + s + 1, ∀ c ∈ outEq n s g k r, ClauseSat a c :=
    fun r hr k hk c hc => mem c (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_flatMap.2 ⟨r,
      hr, List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, hc⟩⟩))))))
  have src : ∀ e ∈ [1, 2], ∀ j < s, ∀ k < n + j + 1, a (ix n s e j k + 1) = true → ∀ r ∈ rows,
      a (ix n s (e + 3) j r + 1) = (if k < n then r.testBit k else if k < n + j then
        a (ix n s 3 (k - n) r + 1) else false) := by
    intro e he j hj k hk hsel r hr
    have H := hSrc e he j hj r hr k hk
    by_cases h1 : k < n
    · have := H [Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)] (by simp [srcEq, h1])
      simp [ClauseSat, litQ, litL, hsel] at this
      rw [if_pos h1]
      exact this
    · by_cases h2 : k < n + j
      · have c1 := H [Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)]
          (by simp [srcEq, h1, h2])
        have c2 := H [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]
          (by simp [srcEq, h1, h2])
        simp [ClauseSat, litQ, litP, hsel] at c1 c2
        rw [if_neg h1, if_pos h2]
        revert c1 c2
        cases a (ix n s (e + 3) j r + 1) <;> cases a (ix n s 3 (k - n) r + 1) <;> simp
      · have := H [Q (ix n s e j k), Q (ix n s (e + 3) j r)] (by simp [srcEq, h1, h2])
        simp [ClauseSat, litQ, hsel] at this
        rw [if_neg h1, if_neg h2]
        exact this
  refine ⟨fun j r => a (ix n s 3 j r + 1), ?_, ?_⟩
  · intro j hj
    obtain ⟨k1, hk1, hs1⟩ := hAlo 1 (by simp) j hj
    obtain ⟨k2, hk2, hs2⟩ := hAlo 2 (by simp) j hj
    have e1 : ∀ r ∈ rows, a (ix n s 4 j r + 1) = (if k1 < n then r.testBit k1 else
        if k1 < n + j then a (ix n s 3 (k1 - n) r + 1) else false) :=
      src 1 (by simp) j hj k1 hk1 hs1
    have e2 : ∀ r ∈ rows, a (ix n s 5 j r + 1) = (if k2 < n then r.testBit k2 else
        if k2 < n + j then a (ix n s 3 (k2 - n) r + 1) else false) :=
      src 2 (by simp) j hj k2 hk2 hs2
    rcases hOp j hj with hop | hop | hop
    · refine ⟨GateOp.and, [k1, k2], Or.inl rfl, by simp, fun r hr => ?_⟩
      have key : a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) && a (ix n s 5 j r + 1)) := by
        have hc := hG j hj r hr
        simp [gateCl, ClauseSat, litP, litQ, hop] at hc
        revert hc
        cases a (ix n s 3 j r + 1) <;> cases a (ix n s 4 j r + 1) <;>
          cases a (ix n s 5 j r + 1) <;> simp
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
        Bool.and_true]
      rw [key, e1 r hr, e2 r hr]
      rfl
    · refine ⟨GateOp.or, [k1, k2], Or.inr rfl, by simp, fun r hr => ?_⟩
      have key : a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) || a (ix n s 5 j r + 1)) := by
        have hc := hG j hj r hr
        simp [gateCl, ClauseSat, litP, litQ, hop] at hc
        revert hc
        cases a (ix n s 3 j r + 1) <;> cases a (ix n s 4 j r + 1) <;>
          cases a (ix n s 5 j r + 1) <;> simp
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [key, e1 r hr, e2 r hr]
      rfl
    · refine ⟨GateOp.and, [], Or.inl rfl, by simp, fun r hr => ?_⟩
      simp only [List.map_nil, GateOp.eval, List.all_nil]
      have hc := hG j hj r hr
      simp [gateCl, ClauseSat, litP, litQ, hop] at hc
      revert hc
      cases a (ix n s 3 j r + 1) <;> simp
  · obtain ⟨k, hk, hsel⟩ := hOA
    refine ⟨k, fun r hr => ?_⟩
    have H := hOE r hr k hk
    unfold W
    by_cases h1 : k < n
    · rw [if_pos h1]
      by_contra h2
      have := H [Q (ix n s 6 0 k)] (by simp [outEq, h1, h2])
      simp [ClauseSat, litQ, hsel] at this
    · rw [if_neg h1]
      by_cases h2 : k < n + s
      · rw [if_pos h2]
        have := H [Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)] (by simp [outEq, h1, h2])
        simpa [ClauseSat, litQ, litL, hsel] using this
      · rw [if_neg h2]
        cases hg : g r
        · rfl
        · have := H [Q (ix n s 6 0 k)] (by simp [outEq, h1, h2, hg])
          simp [ClauseSat, litQ, hsel] at this

theorem getD_snoc (w : List Bool) (v : Bool) (k : ℕ) :
    (w ++ [v]).getD k false =
      if k < w.length then w.getD k false else if k = w.length then v else false := by
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
      List.getElem_append_left h1]
  · subst h2
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem build (n s : ℕ) (val : ℕ → ℕ → Bool) (o : ℕ → GateOp) (lst : ℕ → List ℕ) (r : ℕ)
    (hol : ∀ j < s, val j r = (o j).eval ((lst j).map fun i => W n val j i r)) :
    ∀ j ≤ s,
      (((List.range j).map fun t => (⟨o t, lst t⟩ : Gate)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun i : Fin n => r.testBit i)).length = n + j ∧
      ∀ k, (((List.range j).map fun t => (⟨o t, lst t⟩ : Gate)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun i : Fin n => r.testBit i)).getD k false = W n val j k r := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by simp, fun k => ?_⟩
    simp only [List.range_zero, List.map_nil, List.foldl_nil]
    by_cases hk : k < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hk)]
      simp [W, hk]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp [W, hk]
  | succ j ih =>
    intro hj
    obtain ⟨ihl, ihv⟩ := ih (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    generalize hw : ((List.range j).map fun t => (⟨o t, lst t⟩ : Gate)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun i : Fin n => r.testBit i) = w at ihl ihv
    have hfun : (fun i => w.getD i false) = fun i => W n val j i r := funext ihv
    have hv : (o j).eval ((lst j).map fun i => w.getD i false) = val j r := by
      rw [hfun, hol j (by omega)]
    refine ⟨by simp [ihl]; omega, fun k => ?_⟩
    rw [getD_snoc, ihl, hv]
    by_cases h1 : k < n + j
    · rw [if_pos h1, ihv k]
      unfold W
      split_ifs <;> first | rfl | omega
    · by_cases h2 : k = n + j
      · subst h2
        rw [if_neg h1, if_pos rfl]
        unfold W
        rw [if_neg (by omega), if_pos (by omega)]
        congr 1
        omega
      · rw [if_neg h1, if_neg h2]
        unfold W
        rw [if_neg (by omega), if_neg (by omega)]

end PEqualNP.Outside.L_meta_8861

theorem PEqualNP.Outside.L_meta_8861 : ∀ (x1 x2 : ℕ) (x3 : ℕ → Bool) (x4 : List ℕ), (∀ x5 ∈ x4, x5 < (2 : ℕ) ^ x1) → PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc x1 x2 x3 x4) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ x2 ∧ ∀ x8 ∈ x4, x7.eval (List.ofFn fun (x10 : Fin x1) => x8.testBit ↑x10) = x3 x8 := by
  intro x1 x2 x3 x4 _ hsat
  obtain ⟨val, hg, out, hout⟩ := PEqualNP.Outside.L_meta_8861.gen x1 x2 x3 x4 hsat
  haveI : Inhabited PEqualNP.CircuitLowerBounds.GateOp := ⟨PEqualNP.CircuitLowerBounds.GateOp.and⟩
  choose! o lst hol using hg
  refine ⟨⟨(List.range x2).map fun t => (⟨o t, lst t⟩ : PEqualNP.CircuitLowerBounds.Gate), out⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    have h := hol j (List.mem_range.1 hj)
    refine ⟨?_, h.2.1⟩
    rcases h.1 with h' | h' <;> simp [h']
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro r hr
    have hb := PEqualNP.Outside.L_meta_8861.build x1 x2 val o lst r
      (fun j hj => (hol j hj).2.2 r hr) x2 le_rfl
    rw [← hout r hr, ← hb.2 out]
    rfl
