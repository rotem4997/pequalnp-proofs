import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6168

open PEqualNP.Defs.LratEncoding PEqualNP.CircuitLowerBounds

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

/-- The wires after the first `t` gates of the family `gate`. -/
def run (gate : ℕ → Gate) (x : List Bool) (t : ℕ) : List Bool :=
  ((List.range t).map gate).foldl
    (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_succ (gate : ℕ → Gate) (x : List Bool) (t : ℕ) :
    run gate x (t + 1) = run gate x t ++
      [(gate t).op.eval ((gate t).inputs.map fun i => (run gate x t).getD i false)] := by
  simp [run, List.range_succ]

theorem getD_app_left (w : List Bool) (v : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_app_last (w : List Bool) (v : Bool) (i : ℕ) (hi : i = w.length) :
    (w ++ [v]).getD i false = v := by
  subst hi
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem core (n s : ℕ) (x : List Bool) (hx : x.length = n) (gate : ℕ → Gate) (W : ℕ → Bool)
    (hstep : ∀ j < s, ∀ w : List Bool, w.length = n + j →
      (∀ i < n, w.getD i false = x.getD i false) →
      (∀ i < j, w.getD (n + i) false = W i) →
      (gate j).op.eval ((gate j).inputs.map fun i => w.getD i false) = W j) :
    ∀ t ≤ s, (run gate x t).length = n + t ∧
      (∀ i < n, (run gate x t).getD i false = x.getD i false) ∧
      ∀ i < t, (run gate x t).getD (n + i) false = W i := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨by simp [run, hx], fun i _ => by simp [run], fun i hi => absurd hi (by omega)⟩
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hv := hstep t (by omega) _ h1 h2 h3
    rw [run_succ, hv]
    refine ⟨by simp [h1]; omega, ?_, ?_⟩
    · intro i hi
      rw [getD_app_left _ _ _ (by omega)]
      exact h2 i hi
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [getD_app_left _ _ _ (by omega)]
        exact h3 i hi
      · rw [getD_app_last _ _ _ (by omega)]

section ex
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {a : ℕ → Bool}

theorem e_op (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {j : ℕ} (hj : j < s) :
    a (ix n s 0 j 0 + 1) = true ∨ a (ix n s 0 j 1 + 1) = true ∨ a (ix n s 0 j 2 + 1) = true := by
  have hm : [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)] ∈ fOp n s :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have := h _ (by simp only [enc, List.mem_append]; tauto)
  simpa [cs_cons, cs_nil, litVal_P] using this

theorem e_src (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) : ∃ k, k ≤ n + j ∧ a (ix n s e j k + 1) = true := by
  have hm : (List.range (n + j + 1)).map (fun k => P (ix n s e j k)) ∈ fSrcAlo n s :=
    List.mem_flatMap.2 ⟨e, by rcases he with rfl | rfl <;> simp,
      List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩
  obtain ⟨l, hl, hv⟩ := h _ (by simp only [enc, List.mem_append]; tauto)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
  rw [litVal_P] at hv
  exact ⟨k, by have := List.mem_range.1 hk; omega, hv⟩

theorem e_srcEq (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j k r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hk : k ≤ n + j) :
    ∀ c ∈ srcEq n s e j k r, ClauseSat a c := by
  intro c hc
  have hm : c ∈ fSrcEq n s rows :=
    List.mem_flatMap.2 ⟨e, by rcases he with rfl | rfl <;> simp,
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr,
        List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hc⟩⟩⟩⟩
  exact h _ (by simp only [enc, List.mem_append]; tauto)

theorem e_srcA (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j k r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hk : k ≤ n + j) (hb : a (ix n s e j k + 1) = true)
    (hkn : k < n) : a (ix n s (e + 3) j r + 1) = r.testBit k := by
  have := e_srcEq h he hj hr hk [Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]
    (by simp [srcEq, hkn])
  simpa [cs_cons, cs_nil, litVal_Q, litVal_L, hb] using this

theorem e_srcB (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j k r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hk : k ≤ n + j) (hb : a (ix n s e j k + 1) = true)
    (hkn : n ≤ k) (hkj : k < n + j) :
    a (ix n s (e + 3) j r + 1) = a (ix n s 3 (k - n) r + 1) := by
  have hn : ¬ k < n := by omega
  have h1 := e_srcEq h he hj hr hk
    [Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)] (by simp [srcEq, hn, hkj])
  have h2 := e_srcEq h he hj hr hk
    [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)] (by simp [srcEq, hn, hkj])
  simp only [cs_cons, cs_nil, litVal_Q, litVal_P, hb] at h1 h2
  revert h1 h2
  cases a (ix n s (e + 3) j r + 1) <;> cases a (ix n s 3 (k - n) r + 1) <;> simp

theorem e_srcC (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {e j r : ℕ} (he : e = 1 ∨ e = 2)
    (hj : j < s) (hr : r ∈ rows) (hb : a (ix n s e j (n + j) + 1) = true) :
    a (ix n s (e + 3) j r + 1) = false := by
  have h1 := e_srcEq h he hj hr (le_refl _)
    [Q (ix n s e j (n + j)), Q (ix n s (e + 3) j r)] (by simp [srcEq])
  simpa [cs_cons, cs_nil, litVal_Q, hb] using h1

theorem e_gate (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {j r : ℕ}
    (hj : j < s) (hr : r ∈ rows) :
    (a (ix n s 0 j 0 + 1) = true →
      a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) && a (ix n s 5 j r + 1))) ∧
    (a (ix n s 0 j 1 + 1) = true →
      a (ix n s 3 j r + 1) = (a (ix n s 4 j r + 1) || a (ix n s 5 j r + 1))) ∧
    (a (ix n s 0 j 2 + 1) = true → a (ix n s 3 j r + 1) = true) := by
  have hg : ∀ c ∈ gateCl n s j r, ClauseSat a c := by
    intro c hc
    have hm : c ∈ fGate n s rows :=
      List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_flatMap.2 ⟨r, hr, hc⟩⟩
    exact h _ (by simp only [enc, List.mem_append]; tauto)
  simp only [gateCl, List.forall_mem_cons, List.not_mem_nil, cs_cons, cs_nil, litVal_Q,
    litVal_P] at hg
  revert hg
  cases a (ix n s 0 j 0 + 1) <;> cases a (ix n s 0 j 1 + 1) <;> cases a (ix n s 0 j 2 + 1) <;>
    cases a (ix n s 3 j r + 1) <;> cases a (ix n s 4 j r + 1) <;>
    cases a (ix n s 5 j r + 1) <;> simp

theorem e_out (h : ∀ c ∈ enc n s g rows, ClauseSat a c) :
    ∃ k, k ≤ n + s ∧ a (ix n s 6 0 k + 1) = true := by
  have hm : (List.range (n + s + 1)).map (fun k => P (ix n s 6 0 k)) ∈ fOutAlo n s := by
    simp [fOutAlo]
  obtain ⟨l, hl, hv⟩ := h _ (by simp only [enc, List.mem_append]; tauto)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hl
  rw [litVal_P] at hv
  exact ⟨k, by have := List.mem_range.1 hk; omega, hv⟩

theorem e_outEq (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {k r : ℕ}
    (hr : r ∈ rows) (hk : k ≤ n + s) :
    ∀ c ∈ outEq n s g k r, ClauseSat a c := by
  intro c hc
  have hm : c ∈ fOutEq n s g rows :=
    List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨k, List.mem_range.2 (by omega), hc⟩⟩
  exact h _ (by simp only [enc, List.mem_append]; tauto)

theorem e_outA (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {k r : ℕ}
    (hr : r ∈ rows) (hk : k ≤ n + s) (hb : a (ix n s 6 0 k + 1) = true) (hkn : k < n) :
    r.testBit k = g r := by
  by_contra hne
  have := e_outEq h hr hk [Q (ix n s 6 0 k)] (by simp [outEq, hkn, hne])
  simp [cs_cons, cs_nil, litVal_Q, hb] at this

theorem e_outB (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {k r : ℕ}
    (hr : r ∈ rows) (hk : k ≤ n + s) (hb : a (ix n s 6 0 k + 1) = true) (hkn : n ≤ k)
    (hks : k < n + s) : a (ix n s 3 (k - n) r + 1) = g r := by
  have hn : ¬ k < n := by omega
  have := e_outEq h hr hk [Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]
    (by simp [outEq, hn, hks])
  simpa [cs_cons, cs_nil, litVal_Q, litVal_L, hb] using this

theorem e_outC (h : ∀ c ∈ enc n s g rows, ClauseSat a c) {r : ℕ}
    (hr : r ∈ rows) (hb : a (ix n s 6 0 (n + s) + 1) = true) : g r = false := by
  by_contra hne
  have hg : g r = true := by simpa using hne
  have := e_outEq h hr (le_refl _) [Q (ix n s 6 0 (n + s))] (by simp [outEq, hg])
  simp [cs_cons, cs_nil, litVal_Q, hb] at this

end ex

theorem sound (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hsat : FormulaSat (enc n s g rows)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.gates.length = s ∧
      ∀ r ∈ rows, ∀ x : List Bool, x.length = n → (∀ i < n, x.getD i false = r.testBit i) →
        D.eval x = g r := by
  obtain ⟨a, h⟩ := hsat
  have hsrc : ∀ e j : ℕ, ∃ k, (e = 1 ∨ e = 2) → j < s → k ≤ n + j ∧ a (ix n s e j k + 1) = true := by
    intro e j
    by_cases hc : (e = 1 ∨ e = 2) ∧ j < s
    · obtain ⟨k, hk⟩ := e_src h hc.1 hc.2
      exact ⟨k, fun _ _ => hk⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose src hsrc using hsrc
  obtain ⟨ko, hko, hbo⟩ := e_out h
  let gate : ℕ → Gate := fun j =>
    if a (ix n s 0 j 0 + 1) = true then ⟨GateOp.and, [src 1 j, src 2 j]⟩
    else if a (ix n s 0 j 1 + 1) = true then ⟨GateOp.or, [src 1 j, src 2 j]⟩
    else ⟨GateOp.and, []⟩
  refine ⟨⟨(List.range s).map gate, ko⟩, ?_, by simp, ?_⟩
  · intro gg hgg
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hgg
    simp only [gate]
    split_ifs <;> simp
  · intro r hr x hx hxr
    have hstep : ∀ j < s, ∀ w : List Bool, w.length = n + j →
        (∀ i < n, w.getD i false = x.getD i false) →
        (∀ i < j, w.getD (n + i) false = a (ix n s 3 i r + 1)) →
        (gate j).op.eval ((gate j).inputs.map fun i => w.getD i false) = a (ix n s 3 j r + 1) := by
      intro j hj w hw h2 h3
      have hu : ∀ e : ℕ, e = 1 ∨ e = 2 → w.getD (src e j) false = a (ix n s (e + 3) j r + 1) := by
        intro e he
        obtain ⟨hk, hb⟩ := hsrc e j he hj
        by_cases hkn : src e j < n
        · rw [h2 _ hkn, hxr _ hkn, e_srcA h he hj hr hk hb hkn]
        · by_cases hkj : src e j < n + j
          · rw [e_srcB h he hj hr hk hb (by omega) hkj]
            have := h3 (src e j - n) (by omega)
            rwa [show n + (src e j - n) = src e j by omega] at this
          · have he2 : src e j = n + j := by omega
            rw [he2] at hb ⊢
            rw [e_srcC h he hj hr hb, getD_big _ _ (by omega)]
      have hu1 := hu 1 (Or.inl rfl)
      have hu2 := hu 2 (Or.inr rfl)
      obtain ⟨g0, g1, g2⟩ := e_gate (g := g) h hj hr
      simp only [gate]
      split_ifs with c0 c1
      · show ([w.getD (src 1 j) false, w.getD (src 2 j) false]).all id = _
        rw [hu1, hu2, g0 c0]
        simp
      · show ([w.getD (src 1 j) false, w.getD (src 2 j) false]).any id = _
        rw [hu1, hu2, g1 c1]
        simp
      · have c2 : a (ix n s 0 j 2 + 1) = true := by
          rcases e_op h hj with h' | h' | h'
          · exact absurd h' c0
          · exact absurd h' c1
          · exact h'
        simp [GateOp.eval, g2 c2]
    obtain ⟨h1, h2, h3⟩ := core n s x hx gate (fun i => a (ix n s 3 i r + 1)) hstep s (le_refl _)
    show (run gate x s).getD ko false = g r
    by_cases hkn : ko < n
    · rw [h2 _ hkn, hxr _ hkn]
      exact e_outA h hr hko hbo hkn
    · by_cases hks : ko < n + s
      · have := h3 (ko - n) (by omega)
        rw [show n + (ko - n) = ko by omega] at this
        rw [this]
        exact e_outB h hr hko hbo (by omega) hks
      · have he2 : ko = n + s := by omega
        rw [he2] at hbo ⊢
        rw [getD_big _ _ (by omega), e_outC h hr hbo]

theorem testBit_foldr (l : List Bool) (i : ℕ) :
    (List.foldr Nat.bit 0 l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    cases i with
    | zero => simp
    | succ i => simp [Nat.testBit_bit_succ, ih]

/-- The packed extended row. -/
def pk (x3 : Gate) (x : List Bool) : ℕ :=
  List.foldr Nat.bit 0 (x ++ [x3.op.eval (List.map (fun i => x.getD i false) x3.inputs)])

theorem pk_inj (x3 : Gate) (x y : List Bool) (hl : x.length = y.length)
    (he : pk x3 x = pk x3 y) : x = y := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := congrArg (fun r => Nat.testBit r i) he
  simp only [pk, testBit_foldr] at this
  rw [getD_app_left _ _ _ h1, getD_app_left _ _ _ h2] at this
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem main : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : List (List Bool)),   x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or →     x3.inputs.length ≤ (2 : ℕ) →       (∀ x8 ∈ x4 ++ x5, x8.length = x1) →         (∀ x9 ∈ x5, x9 ∉ x4) →           (have x10 : List Bool → ℕ := fun (x10 : List Bool) => List.foldr Nat.bit (0 : ℕ) (x10 ++ [x3.op.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x3.inputs)]);             have x11 : List ℕ := List.map x10 x4;             PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (x1 + (1 : ℕ)) x2 (fun (x12 : ℕ) => x11.contains x12) (x11 ++ List.map x10 x5).eraseDups)) →             ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ x11.size ≤ x2 + (1 : ℕ) ∧ x11.gates.head? = Option.some x3 ∧ (∀ x12 ∈ x4, x11.eval x12 = Bool.true) ∧ ∀ x12 ∈ x5, x11.eval x12 = Bool.false := by
  intro x1 x2 x3 x4 x5 hop hlen hl hdisj h
  change FormulaSat (enc (x1 + 1) x2 (fun r => (x4.map (pk x3)).contains r)
    ((x4.map (pk x3)) ++ x5.map (pk x3)).eraseDups) at h
  obtain ⟨D, hm, hsz, hev⟩ := sound _ _ _ _ h
  have key : ∀ x, Circuit.eval ⟨x3 :: D.gates, D.output⟩ x =
      D.eval (x ++ [x3.op.eval (x3.inputs.map fun i => x.getD i false)]) := fun x => rfl
  have hrow : ∀ x ∈ x4 ++ x5, Circuit.eval ⟨x3 :: D.gates, D.output⟩ x =
      (x4.map (pk x3)).contains (pk x3 x) := by
    intro x hx
    rw [key]
    refine hev (pk x3 x) ?_ _ (by simp [hl x hx]) (fun i _ => (testBit_foldr _ _).symm)
    rw [List.mem_eraseDups, ← List.map_append]
    exact List.mem_map_of_mem hx
  refine ⟨⟨x3 :: D.gates, D.output⟩, ?_, ?_, rfl, ?_, ?_⟩
  · intro gg hgg
    rcases List.mem_cons.1 hgg with rfl | hgg
    · exact ⟨by simpa using hop, hlen⟩
    · exact hm gg hgg
  · simp [Circuit.size, hsz]
  · intro x hx
    rw [hrow x (List.mem_append_left _ hx)]
    simp only [List.contains_iff_mem, List.mem_map]
    exact ⟨x, hx, rfl⟩
  · intro x hx
    rw [hrow x (List.mem_append_right _ hx)]
    rw [Bool.eq_false_iff]
    intro hc
    simp only [List.contains_iff_mem, List.mem_map] at hc
    obtain ⟨y, hy, hxy⟩ := hc
    have : y = x := pk_inj x3 y x
      (by rw [hl y (List.mem_append_left _ hy), hl x (List.mem_append_right _ hx)]) hxy
    exact hdisj x hx (this ▸ hy)

end PEqualNP.Outside.L_meta_6168

theorem PEqualNP.Outside.L_meta_6168 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : List (List Bool)),   x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or →     x3.inputs.length ≤ (2 : ℕ) →       (∀ x8 ∈ x4 ++ x5, x8.length = x1) →         (∀ x9 ∈ x5, x9 ∉ x4) →           (have x10 : List Bool → ℕ := fun (x10 : List Bool) => List.foldr Nat.bit (0 : ℕ) (x10 ++ [x3.op.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x3.inputs)]);             have x11 : List ℕ := List.map x10 x4;             PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (x1 + (1 : ℕ)) x2 (fun (x12 : ℕ) => x11.contains x12) (x11 ++ List.map x10 x5).eraseDups)) →             ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ x11.size ≤ x2 + (1 : ℕ) ∧ x11.gates.head? = Option.some x3 ∧ (∀ x12 ∈ x4, x11.eval x12 = Bool.true) ∧ ∀ x12 ∈ x5, x11.eval x12 = Bool.false :=
  PEqualNP.Outside.L_meta_6168.main
