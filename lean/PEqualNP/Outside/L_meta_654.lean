import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_654

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step: the gate adds one wire.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_length (gs : List Gate) : ∀ W : List Bool,
    (gs.foldl stp W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [stp]
    omega

theorem getD_snoc_eq (W : List Bool) (v : Bool) : (W ++ [v]).getD W.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

-- The new name of a wire: the first a wires move by σ, the others shift from a to b.
def rho (a b : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ := if i < a then σ i else i - a + b

def relG (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

theorem getD_rho (ID Inew rest : List Bool) (σ : ℕ → ℕ)
    (hσ : ∀ i, i < ID.length → σ i < Inew.length ∧ ID.getD i false = Inew.getD (σ i) false)
    (i : ℕ) :
    (Inew ++ rest).getD (rho ID.length Inew.length σ i) false = (ID ++ rest).getD i false := by
  unfold rho
  by_cases h : i < ID.length
  · rw [if_pos h, List.getD_append _ _ _ _ (hσ i h).1, List.getD_append _ _ _ _ h]
    exact (hσ i h).2.symm
  · rw [if_neg h]
    have h1 : ID.length ≤ i := Nat.le_of_not_lt h
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ h1]
    congr 1
    omega

theorem relabel_spec (ID Inew : List Bool) (σ : ℕ → ℕ)
    (hσ : ∀ i, i < ID.length → σ i < Inew.length ∧ ID.getD i false = Inew.getD (σ i) false)
    (gs : List Gate) :
    ∀ rest : List Bool, ∃ rest' : List Bool,
      (gs.map (relG (rho ID.length Inew.length σ))).foldl stp (Inew ++ rest) = Inew ++ rest' ∧
        gs.foldl stp (ID ++ rest) = ID ++ rest' := by
  induction gs with
  | nil => intro rest; exact ⟨rest, rfl, rfl⟩
  | cons g gs ih =>
    intro rest
    obtain ⟨rest', h1, h2⟩ :=
      ih (rest ++ [g.op.eval (g.inputs.map fun i => (ID ++ rest).getD i false)])
    refine ⟨rest', ?_, ?_⟩
    · rw [← h1]
      simp only [List.map_cons, List.foldl_cons]
      congr 1
      simp only [stp, relG, List.map_map]
      have : ((fun i => (Inew ++ rest).getD i false) ∘ rho ID.length Inew.length σ)
          = fun i => (ID ++ rest).getD i false := by
        funext i
        exact getD_rho ID Inew rest σ hσ i
      rw [this]
      simp
    · rw [← h2]
      simp only [List.foldl_cons]
      congr 1
      simp [stp]

-- Each term (c, l, r) adds three gates: OR(l, r), AND(c, that), OR(the output so far, that).
def addTerms : List (ℕ × ℕ × ℕ) → ℕ → ℕ → List Gate
  | [], _, _ => []
  | (c, l, r) :: ts, L, acc =>
    ⟨GateOp.or, [l, r]⟩ :: ⟨GateOp.and, [c, L]⟩ :: ⟨GateOp.or, [acc, L + 1]⟩ ::
      addTerms ts (L + 3) (L + 2)

def finalAcc : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | _ :: ts, L, _ => finalAcc ts (L + 3) (L + 2)

theorem addTerms_length : ∀ (ts : List (ℕ × ℕ × ℕ)) (L acc : ℕ),
    (addTerms ts L acc).length = 3 * ts.length := by
  intro ts
  induction ts with
  | nil => intro L acc; simp [addTerms]
  | cons τ ts ih =>
    intro L acc
    obtain ⟨c, l, r⟩ := τ
    simp only [addTerms, List.length_cons, ih]
    omega

theorem addTerms_ok : ∀ (ts : List (ℕ × ℕ × ℕ)) (L acc : ℕ), ∀ g ∈ addTerms ts L acc,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro ts
  induction ts with
  | nil => intro L acc g hg; simp [addTerms] at hg
  | cons τ ts ih =>
    intro L acc g hg
    obtain ⟨c, l, r⟩ := τ
    simp only [addTerms, List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | hg
    · simp
    · simp
    · simp
    · exact ih _ _ g hg

theorem addTerms_spec : ∀ (ts : List (ℕ × ℕ × ℕ)) (W : List Bool) (acc : ℕ),
    (acc < W.length ∨ W.length + 3 * ts.length ≤ acc) →
    (∀ τ ∈ ts, τ.1 < W.length ∧ τ.2.1 < W.length ∧ τ.2.2 < W.length) →
    (((addTerms ts W.length acc).foldl stp W).getD (finalAcc ts W.length acc) false = true ↔
      (W.getD acc false = true ∨ ∃ τ ∈ ts, W.getD τ.1 false = true ∧
        (W.getD τ.2.1 false = true ∨ W.getD τ.2.2 false = true))) := by
  intro ts
  induction ts with
  | nil => intro W acc _ _; simp [addTerms, finalAcc]
  | cons τ ts ih =>
    intro W acc hacc hts
    obtain ⟨c, l, r⟩ := τ
    obtain ⟨hc, hl, hr⟩ := hts (c, l, r) (by simp)
    simp only at hc hl hr
    have s1 : stp W ⟨GateOp.or, [l, r]⟩ = W ++ [W.getD l false || W.getD r false] := by
      simp [stp, GateOp.eval]
    have s2 : stp (W ++ [W.getD l false || W.getD r false]) ⟨GateOp.and, [c, W.length]⟩
        = W ++ [W.getD l false || W.getD r false]
          ++ [W.getD c false && (W.getD l false || W.getD r false)] := by
      simp only [stp, List.map_cons, List.map_nil]
      rw [List.getD_append _ _ _ _ hc, getD_snoc_eq]
      simp [GateOp.eval]
    have hacc' : (W ++ [W.getD l false || W.getD r false]
        ++ [W.getD c false && (W.getD l false || W.getD r false)]).getD acc false
        = W.getD acc false := by
      rcases hacc with h | h
      · rw [List.append_assoc, List.getD_append _ _ _ _ h]
      · simp only [List.length_cons] at h
        rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by omega)]
    have hlen2 : (W ++ [W.getD l false || W.getD r false]).length = W.length + 1 := by simp
    have s3 : stp (W ++ [W.getD l false || W.getD r false]
        ++ [W.getD c false && (W.getD l false || W.getD r false)])
          ⟨GateOp.or, [acc, W.length + 1]⟩
        = W ++ [W.getD l false || W.getD r false]
          ++ [W.getD c false && (W.getD l false || W.getD r false)]
          ++ [W.getD acc false || (W.getD c false && (W.getD l false || W.getD r false))] := by
      simp only [stp, List.map_cons, List.map_nil]
      rw [hacc', ← hlen2, getD_snoc_eq]
      simp [GateOp.eval]
    simp only [addTerms, finalAcc, List.foldl_cons]
    rw [s1, s2, s3]
    generalize hW' : W ++ [W.getD l false || W.getD r false]
        ++ [W.getD c false && (W.getD l false || W.getD r false)]
        ++ [W.getD acc false || (W.getD c false && (W.getD l false || W.getD r false))] = W'
    have hlen' : W'.length = W.length + 3 := by rw [← hW']; simp
    have hpre : ∀ i, i < W.length → W'.getD i false = W.getD i false := by
      intro i hi
      rw [← hW', List.append_assoc, List.append_assoc]
      exact List.getD_append _ _ _ _ hi
    have hlast : W'.getD (W.length + 2) false
        = (W.getD acc false || (W.getD c false && (W.getD l false || W.getD r false))) := by
      rw [← hW']
      have e : (W ++ [W.getD l false || W.getD r false]
          ++ [W.getD c false && (W.getD l false || W.getD r false)]).length = W.length + 2 := by
        simp
      rw [← e]
      exact getD_snoc_eq _ _
    have hts' : ∀ τ ∈ ts, τ.1 < W'.length ∧ τ.2.1 < W'.length ∧ τ.2.2 < W'.length := by
      intro τ hτ
      obtain ⟨a1, a2, a3⟩ := hts τ (by simp [hτ])
      exact ⟨by omega, by omega, by omega⟩
    have key := ih W' (W.length + 2) (Or.inl (by omega)) hts'
    rw [hlen'] at key
    rw [key, hlast]
    constructor
    · rintro (h | ⟨τ, hτ, h1, h2⟩)
      · simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨(c, l, r), by simp, h1, h2⟩
      · obtain ⟨a1, a2, a3⟩ := hts τ (by simp [hτ])
        rw [hpre _ a1] at h1
        rw [hpre _ a2, hpre _ a3] at h2
        exact Or.inr ⟨τ, by simp [hτ], h1, h2⟩
    · rintro (h | ⟨τ, hτ, h1, h2⟩)
      · left
        rw [Bool.or_eq_true]
        exact Or.inl h
      · rcases List.mem_cons.mp hτ with rfl | hτ
        · left
          simp only at h1 h2
          simp only [Bool.or_eq_true, Bool.and_eq_true]
          exact Or.inr ⟨h1, h2⟩
        · obtain ⟨a1, a2, a3⟩ := hts τ (by simp [hτ])
          right
          refine ⟨τ, hτ, ?_, ?_⟩
          · rw [hpre _ a1]; exact h1
          · rw [hpre _ a2, hpre _ a3]; exact h2

-- A circuit on other inputs, with terms added on top.
def extC (a b : ℕ) (σ : ℕ → ℕ) (D : Circuit) (ts : List (ℕ × ℕ × ℕ)) : Circuit :=
  ⟨D.gates.map (relG (rho a b σ)) ++ addTerms ts (b + D.gates.length)
      (if D.output < a + D.gates.length then rho a b σ D.output
        else b + D.gates.length + 3 * ts.length),
    finalAcc ts (b + D.gates.length)
      (if D.output < a + D.gates.length then rho a b σ D.output
        else b + D.gates.length + 3 * ts.length)⟩

theorem extC_fanin (a b : ℕ) (σ : ℕ → ℕ) (D : Circuit) (ts : List (ℕ × ℕ × ℕ))
    (hF : FanInTwo D) : FanInTwo (extC a b σ D ts) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hF g0 hg0
    exact ⟨this.1, by simpa [relG] using this.2⟩
  · exact addTerms_ok _ _ _ g hg

theorem extC_size (a b : ℕ) (σ : ℕ → ℕ) (D : Circuit) (ts : List (ℕ × ℕ × ℕ)) :
    (extC a b σ D ts).size = D.size + 3 * ts.length := by
  show (D.gates.map _ ++ addTerms ts _ _).length = D.gates.length + 3 * ts.length
  rw [List.length_append, List.length_map, addTerms_length]

theorem extC_eval (D : Circuit) (ID Inew : List Bool) (σ : ℕ → ℕ) (ts : List (ℕ × ℕ × ℕ))
    (hσ : ∀ i, i < ID.length → σ i < Inew.length ∧ ID.getD i false = Inew.getD (σ i) false)
    (hts : ∀ τ ∈ ts, τ.1 < Inew.length ∧ τ.2.1 < Inew.length ∧ τ.2.2 < Inew.length) :
    ((extC ID.length Inew.length σ D ts).eval Inew = true ↔
      (D.eval ID = true ∨ ∃ τ ∈ ts, Inew.getD τ.1 false = true ∧
        (Inew.getD τ.2.1 false = true ∨ Inew.getD τ.2.2 false = true))) := by
  obtain ⟨rest', h1, h2⟩ := relabel_spec ID Inew σ hσ D.gates []
  rw [List.append_nil] at h1 h2
  have hrl : rest'.length = D.gates.length := by
    have := foldl_length D.gates ID
    rw [h2] at this
    simp at this
    omega
  have hWlen : (Inew ++ rest').length = Inew.length + D.gates.length := by simp [hrl]
  have hev : (extC ID.length Inew.length σ D ts).eval Inew
      = ((addTerms ts (Inew ++ rest').length
          (if D.output < ID.length + D.gates.length then rho ID.length Inew.length σ D.output
            else Inew.length + D.gates.length + 3 * ts.length)).foldl stp (Inew ++ rest')).getD
          (finalAcc ts (Inew ++ rest').length
            (if D.output < ID.length + D.gates.length then rho ID.length Inew.length σ D.output
              else Inew.length + D.gates.length + 3 * ts.length)) false := by
    rw [hWlen]
    simp only [Circuit.eval, wires_eq, extC, List.foldl_append, h1]
  have hDev : D.eval ID = (ID ++ rest').getD D.output false := by
    simp only [Circuit.eval, wires_eq, h2]
  have hacc : (Inew ++ rest').getD
      (if D.output < ID.length + D.gates.length then rho ID.length Inew.length σ D.output
        else Inew.length + D.gates.length + 3 * ts.length) false = D.eval ID := by
    rw [hDev]
    split_ifs with hin
    · exact getD_rho ID Inew rest' σ hσ D.output
    · rw [getD_ge _ _ (by rw [List.length_append, hrl]; omega),
        getD_ge _ _ (by rw [List.length_append, hrl]; omega)]
  have hcond : ((if D.output < ID.length + D.gates.length then rho ID.length Inew.length σ D.output
        else Inew.length + D.gates.length + 3 * ts.length) < (Inew ++ rest').length ∨
      (Inew ++ rest').length + 3 * ts.length ≤
        (if D.output < ID.length + D.gates.length then rho ID.length Inew.length σ D.output
          else Inew.length + D.gates.length + 3 * ts.length)) := by
    split_ifs with hin
    · left
      rw [hWlen]
      unfold rho
      split_ifs with h3
      · have := (hσ _ h3).1
        omega
      · omega
    · right
      rw [hWlen]
  have hts' : ∀ τ ∈ ts, τ.1 < (Inew ++ rest').length ∧ τ.2.1 < (Inew ++ rest').length ∧
      τ.2.2 < (Inew ++ rest').length := by
    intro τ hτ
    obtain ⟨a1, a2, a3⟩ := hts τ hτ
    rw [hWlen]
    exact ⟨by omega, by omega, by omega⟩
  rw [hev, addTerms_spec ts (Inew ++ rest') _ hcond hts', hacc]
  constructor
  · rintro (h | ⟨τ, hτ, e1, e2⟩)
    · exact Or.inl h
    · obtain ⟨a1, a2, a3⟩ := hts τ hτ
      rw [List.getD_append _ _ _ _ a1] at e1
      rw [List.getD_append _ _ _ _ a2, List.getD_append _ _ _ _ a3] at e2
      exact Or.inr ⟨τ, hτ, e1, e2⟩
  · rintro (h | ⟨τ, hτ, e1, e2⟩)
    · exact Or.inl h
    · obtain ⟨a1, a2, a3⟩ := hts τ hτ
      refine Or.inr ⟨τ, hτ, ?_, ?_⟩
      · rw [List.getD_append _ _ _ _ a1]; exact e1
      · rw [List.getD_append _ _ _ _ a2, List.getD_append _ _ _ _ a3]; exact e2

-- The terms of the first circuit: the even inner inputs are the centres.
def ts1 (N h a b : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (h + 1)).map (fun k => (N + 2 * k, (if k = 0 then a else N + (2 * k - 1)),
    (if k = h then b else N + (2 * k + 1))))

-- The terms of the second circuit: the odd inner inputs are the centres.
def ts2 (N h : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range h).map (fun k => (N + (2 * k + 1), N + 2 * k, N + (2 * k + 2)))

theorem comb1 (N h : ℕ) (w : ℕ → Bool) (a b : ℕ) :
    (∃ τ ∈ ts1 N h a b, w τ.1 = true ∧ (w τ.2.1 = true ∨ w τ.2.2 = true)) ↔
      ∃ i < 2 * h + 1, w (N + i) = true ∧ ((i = 0 ∧ w a = true) ∨
        (i + 1 = 2 * h + 1 ∧ w b = true) ∨ (i + 1 < 2 * h + 1 ∧ w (N + (i + 1)) = true)) := by
  constructor
  · rintro ⟨τ, hτ, h1, h2⟩
    simp only [ts1, List.mem_map, List.mem_range] at hτ
    obtain ⟨k, hk, rfl⟩ := hτ
    dsimp only at h1 h2
    rcases h2 with h2 | h2
    · by_cases k0 : k = 0
      · subst k0
        rw [if_pos rfl] at h2
        exact ⟨0, by omega, by simpa using h1, Or.inl ⟨rfl, h2⟩⟩
      · rw [if_neg k0] at h2
        refine ⟨2 * k - 1, by omega, h2, Or.inr (Or.inr ⟨by omega, ?_⟩)⟩
        rw [show N + (2 * k - 1 + 1) = N + 2 * k by omega]
        exact h1
    · by_cases kh : k = h
      · subst kh
        rw [if_pos rfl] at h2
        exact ⟨2 * k, by omega, h1, Or.inr (Or.inl ⟨rfl, h2⟩)⟩
      · rw [if_neg kh] at h2
        exact ⟨2 * k, by omega, h1, Or.inr (Or.inr ⟨by omega, h2⟩)⟩
  · rintro ⟨i, hi, h1, h2 | h2 | h2⟩
    · obtain ⟨rfl, ha⟩ := h2
      refine ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, ?_, Or.inl ?_⟩
      · dsimp only
        simpa using h1
      · dsimp only
        rw [if_pos rfl]
        exact ha
    · obtain ⟨hi2, hb⟩ := h2
      have e : i = 2 * h := by omega
      subst e
      refine ⟨_, List.mem_map.mpr ⟨h, List.mem_range.mpr (by omega), rfl⟩, h1, Or.inr ?_⟩
      dsimp only
      rw [if_pos rfl]
      exact hb
    · obtain ⟨hlt, hn⟩ := h2
      rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
      · refine ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩, h1, Or.inr ?_⟩
        dsimp only
        rw [if_neg (by omega)]
        exact hn
      · refine ⟨_, List.mem_map.mpr ⟨k + 1, List.mem_range.mpr (by omega), rfl⟩, ?_, Or.inl ?_⟩
        · dsimp only
          rw [show N + 2 * (k + 1) = N + (2 * k + 1 + 1) by omega]
          exact hn
        · dsimp only
          rw [if_neg (by omega), show N + (2 * (k + 1) - 1) = N + (2 * k + 1) by omega]
          exact h1

theorem comb2 (N h : ℕ) (w : ℕ → Bool) (a b : ℕ) :
    ((w a = true ∧ w N = true) ∨ (w b = true ∧ w (N + 2 * h) = true) ∨
        ∃ τ ∈ ts2 N h, w τ.1 = true ∧ (w τ.2.1 = true ∨ w τ.2.2 = true)) ↔
      ∃ i < 2 * h + 1, w (N + i) = true ∧ ((i = 0 ∧ w a = true) ∨
        (i + 1 = 2 * h + 1 ∧ w b = true) ∨ (i + 1 < 2 * h + 1 ∧ w (N + (i + 1)) = true)) := by
  constructor
  · rintro (⟨ha, h0⟩ | ⟨hb, hl⟩ | ⟨τ, hτ, h1, h2⟩)
    · exact ⟨0, by omega, by simpa using h0, Or.inl ⟨rfl, ha⟩⟩
    · exact ⟨2 * h, by omega, hl, Or.inr (Or.inl ⟨rfl, hb⟩)⟩
    · simp only [ts2, List.mem_map, List.mem_range] at hτ
      obtain ⟨k, hk, rfl⟩ := hτ
      dsimp only at h1 h2
      rcases h2 with h2 | h2
      · exact ⟨2 * k, by omega, h2, Or.inr (Or.inr ⟨by omega, h1⟩)⟩
      · exact ⟨2 * k + 1, by omega, h1, Or.inr (Or.inr ⟨by omega, h2⟩)⟩
  · rintro ⟨i, hi, h1, h2 | h2 | h2⟩
    · obtain ⟨rfl, ha⟩ := h2
      exact Or.inl ⟨ha, by simpa using h1⟩
    · obtain ⟨hi2, hb⟩ := h2
      have e : i = 2 * h := by omega
      subst e
      exact Or.inr (Or.inl ⟨hb, h1⟩)
    · obtain ⟨hlt, hn⟩ := h2
      rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
      · exact Or.inr (Or.inr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩,
          hn, Or.inl h1⟩)
      · exact Or.inr (Or.inr ⟨_, List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩,
          h1, Or.inr hn⟩)

-- The path condition of the statement, read on the list of input values.
theorem fin_conv (N m : ℕ) (x : Fin (N + m) → Bool) (u v : Fin N) :
    (∃ i : Fin m, x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd m u) = true) ∨
        (i.val + 1 = m ∧ x (Fin.castAdd m v) = true) ∨
        ∃ j : Fin m, j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)) ↔
      ∃ i < m, (List.ofFn x).getD (N + i) false = true ∧
        ((i = 0 ∧ (List.ofFn x).getD u.val false = true) ∨
          (i + 1 = m ∧ (List.ofFn x).getD v.val false = true) ∨
          (i + 1 < m ∧ (List.ofFn x).getD (N + (i + 1)) false = true)) := by
  have key : ∀ i (hi : i < m), (List.ofFn x).getD (N + i) false = x (Fin.natAdd N ⟨i, hi⟩) := by
    intro i hi
    rw [getD_ofFn x (N + i) (by omega)]
    rfl
  have ku : ∀ q : Fin N, (List.ofFn x).getD q.val false = x (Fin.castAdd m q) := by
    intro q
    have := q.isLt
    rw [getD_ofFn x q.val (by omega)]
    rfl
  constructor
  · rintro ⟨i, h1, h2⟩
    refine ⟨i.val, i.isLt, by rw [key _ i.isLt]; exact h1, ?_⟩
    rcases h2 with h | h | ⟨j, hj, hx⟩
    · exact Or.inl ⟨h.1, by rw [ku]; exact h.2⟩
    · exact Or.inr (Or.inl ⟨h.1, by rw [ku]; exact h.2⟩)
    · have hjl := j.isLt
      refine Or.inr (Or.inr ⟨by omega, ?_⟩)
      rw [key _ (by omega)]
      have e : (⟨i.val + 1, by omega⟩ : Fin m) = j := Fin.ext hj.symm
      rw [e]
      exact hx
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨⟨i, hi⟩, by rw [← key i hi]; exact h1, ?_⟩
    rcases h2 with h | h | ⟨hlt, hx⟩
    · exact Or.inl ⟨h.1, by rw [← ku]; exact h.2⟩
    · exact Or.inr (Or.inl ⟨h.1, by rw [← ku]; exact h.2⟩)
    · exact Or.inr (Or.inr ⟨⟨i + 1, hlt⟩, rfl, by rw [← key (i + 1) hlt]; exact hx⟩)

theorem main_aux : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize N g s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s + 3)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool => g (fun i : Fin N => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) || (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g s
  have hul := u.isLt
  have hvl := v.isLt
  constructor
  · rintro ⟨D, hF, hsz, hD⟩
    refine ⟨extC N (N + (2 * h + 1)) id D (ts1 N h u.val v.val), extC_fanin _ _ _ _ _ hF, ?_, ?_⟩
    · rw [extC_size]
      have e : (ts1 N h u.val v.val).length = h + 1 := by simp [ts1]
      have : D.size ≤ s := hsz
      omega
    · intro x
      have hσ : ∀ i, i < (List.ofFn (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i))).length →
          id i < (List.ofFn x).length ∧
            (List.ofFn (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i))).getD i false
              = (List.ofFn x).getD (id i) false := by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        refine ⟨by simp only [id]; omega, ?_⟩
        rw [getD_ofFn _ i hi, id, getD_ofFn x i (by omega)]
        rfl
      have hts : ∀ τ ∈ ts1 N h u.val v.val, τ.1 < (List.ofFn x).length ∧
          τ.2.1 < (List.ofFn x).length ∧ τ.2.2 < (List.ofFn x).length := by
        intro τ hτ
        simp only [ts1, List.mem_map, List.mem_range] at hτ
        obtain ⟨k, hk, rfl⟩ := hτ
        simp only [List.length_ofFn]
        refine ⟨by omega, ?_, ?_⟩ <;> split_ifs <;> omega
      have key := extC_eval D _ _ id _ hσ hts
      simp only [List.length_ofFn] at key
      apply Bool.eq_iff_iff.mpr
      rw [key, hD]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact or_congr Iff.rfl
        ((comb1 N h (fun i => (List.ofFn x).getD i false) u.val v.val).trans
          (fin_conv N (2 * h + 1) x u v).symm)
  · rintro ⟨D, hF, hsz, hD⟩
    refine ⟨extC (N + 2) (N + (2 * h + 1)) (fun i => if i ≤ N then i else N + 2 * h) D (ts2 N h),
      extC_fanin _ _ _ _ _ hF, ?_, ?_⟩
    · rw [extC_size]
      have e : (ts2 N h).length = h := by simp [ts2]
      have : D.size ≤ s := hsz
      omega
    · intro x
      obtain ⟨x', hx'⟩ : ∃ x' : Fin (N + 2) → Bool, ∀ i : Fin (N + 2),
          x' i = (List.ofFn x).getD (if i.val ≤ N then i.val else N + 2 * h) false :=
        ⟨_, fun _ => rfl⟩
      have hσ : ∀ i, i < (List.ofFn x').length →
          (fun i => if i ≤ N then i else N + 2 * h) i < (List.ofFn x).length ∧
            (List.ofFn x').getD i false
              = (List.ofFn x).getD ((fun i => if i ≤ N then i else N + 2 * h) i) false := by
        intro i hi
        simp only [List.length_ofFn] at hi ⊢
        refine ⟨by split_ifs <;> omega, ?_⟩
        rw [getD_ofFn x' i hi, hx']
      have hts : ∀ τ ∈ ts2 N h, τ.1 < (List.ofFn x).length ∧
          τ.2.1 < (List.ofFn x).length ∧ τ.2.2 < (List.ofFn x).length := by
        intro τ hτ
        simp only [ts2, List.mem_map, List.mem_range] at hτ
        obtain ⟨k, hk, rfl⟩ := hτ
        simp only [List.length_ofFn]
        exact ⟨by omega, by omega, by omega⟩
      have key := extC_eval D _ _ (fun i => if i ≤ N then i else N + 2 * h) _ hσ hts
      simp only [List.length_ofFn] at key
      have hDx := hD x'
      beta_reduce at hDx
      have e1 : (fun i : Fin N => x' (Fin.castAdd 2 i))
          = fun i : Fin N => x (Fin.castAdd (2 * h + 1) i) := by
        funext i
        have := i.isLt
        rw [hx', if_pos (by simp), getD_ofFn x _ (by simp; omega)]
        rfl
      have e2 : ∀ q : Fin N, x' (Fin.castAdd 2 q) = (List.ofFn x).getD q.val false := by
        intro q
        have := q.isLt
        rw [hx', if_pos (by simp)]
        rfl
      have e4 : x' (Fin.natAdd N (0 : Fin 2)) = (List.ofFn x).getD N false := by
        rw [hx', if_pos (by simp)]
        simp
      have e5 : x' (Fin.natAdd N (1 : Fin 2)) = (List.ofFn x).getD (N + 2 * h) false := by
        rw [hx', if_neg (by simp)]
      rw [e1, e2 u, e2 v, e4, e5] at hDx
      apply Bool.eq_iff_iff.mpr
      rw [key, hDx]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      have E := (comb2 N h (fun i => (List.ofFn x).getD i false) u.val v.val).trans
        (fin_conv N (2 * h + 1) x u v).symm
      constructor
      · rintro (((hg | h1) | h2) | h3)
        · exact Or.inl hg
        · exact Or.inr (E.mp (Or.inl h1))
        · exact Or.inr (E.mp (Or.inr (Or.inl h2)))
        · exact Or.inr (E.mp (Or.inr (Or.inr h3)))
      · rintro (hg | hE)
        · exact Or.inl (Or.inl (Or.inl hg))
        · rcases E.mpr hE with h1 | h2 | h3
          · exact Or.inl (Or.inl (Or.inr h1))
          · exact Or.inl (Or.inr h2)
          · exact Or.inr h3

end PEqualNP.Outside.L_meta_654

theorem PEqualNP.Outside.L_meta_654 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize N g s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s + 3)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 2) (fun x : Fin (N + 2) → Bool => g (fun i : Fin N => x (Fin.castAdd 2 i)) || (x (Fin.castAdd 2 u) && x (Fin.natAdd N (0 : Fin 2))) || (x (Fin.castAdd 2 v) && x (Fin.natAdd N (1 : Fin 2)))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + (2 * h + 1)) (fun x : Fin (N + 2 * h + 1) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h + 1) i)) || decide (∃ i : Fin (2 * h + 1), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h + 1) u) = true) ∨ (i.val + 1 = 2 * h + 1 ∧ x (Fin.castAdd (2 * h + 1) v) = true) ∨ ∃ j : Fin (2 * h + 1), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) :=
  PEqualNP.Outside.L_meta_654.main_aux
