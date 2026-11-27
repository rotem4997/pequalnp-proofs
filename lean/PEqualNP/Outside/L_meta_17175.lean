import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17175

open PEqualNP.CircuitLowerBounds

/-- AND and OR are the monotone operations. -/
def isMono : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

/-- The wires a gate really reads: a NOT reads only its first wire. -/
def eff (g : Gate) : Finset ℕ :=
  match g.op with
  | GateOp.not => (g.inputs.take 1).toFinset
  | _ => g.inputs.toFinset

/-- One evaluation step. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The wires the output depends on, for gates evaluated from `n` existing wires. -/
def needs : List Gate → ℕ → ℕ → Finset ℕ
  | [], _, out => {out}
  | g :: gs, n, out =>
    if n ∈ needs gs (n + 1) out then (needs gs (n + 1) out).erase n ∪ eff g
    else needs gs (n + 1) out

/-- The number of needed gates that are not AND or OR. -/
def bads : List Gate → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | g :: gs, n, out =>
    bads gs (n + 1) out + (if n ∈ needs gs (n + 1) out ∧ isMono g.op = false then 1 else 0)

theorem getD_snoc_lt (w : List Bool) (v : Bool) (i : ℕ) (h : i < w.length) :
    (w ++ [v]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (w : List Bool) (v : Bool) :
    (w ++ [v]).getD w.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (w : List Bool) (v : Bool) (i : ℕ) (h : w.length < i) :
    (w ++ [v]).getD i false = false := by
  have h2 : (w ++ [v]).length ≤ i := by simp; omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h2]

theorem gate_congr (g : Gate) (x y : List Bool)
    (h : ∀ i ∈ eff g, x.getD i false = y.getD i false) :
    g.op.eval (g.inputs.map fun i => x.getD i false)
      = g.op.eval (g.inputs.map fun i => y.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    cases inputs with
    | nil => rfl
    | cons a l =>
      have := h a (by simp [eff])
      show (!(x.getD a false)) = !(y.getD a false)
      rw [this]
  | and =>
    have e : (inputs.map fun i => x.getD i false) = inputs.map fun i => y.getD i false :=
      List.map_congr_left (fun i hi => h i (by simp [eff, hi]))
    simp only [e]
  | or =>
    have e : (inputs.map fun i => x.getD i false) = inputs.map fun i => y.getD i false :=
      List.map_congr_left (fun i hi => h i (by simp [eff, hi]))
    simp only [e]
  | mod m =>
    have e : (inputs.map fun i => x.getD i false) = inputs.map fun i => y.getD i false :=
      List.map_congr_left (fun i hi => h i (by simp [eff, hi]))
    simp only [e]
  | maj =>
    have e : (inputs.map fun i => x.getD i false) = inputs.map fun i => y.getD i false :=
      List.map_congr_left (fun i hi => h i (by simp [eff, hi]))
    simp only [e]

theorem gate_mono (g : Gate) (hg : isMono g.op = true) (x y : List Bool)
    (h : ∀ i ∈ eff g, x.getD i false = true → y.getD i false = true) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not => simp [isMono] at hg
  | mod m => simp [isMono] at hg
  | maj => simp [isMono] at hg
  | and =>
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    intro H i hi
    exact h i (by simp [eff, hi]) (H i hi)
  | or =>
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, H⟩
    exact ⟨i, hi, h i (by simp [eff, hi]) H⟩

theorem dep (gs : List Gate) : ∀ (n out : ℕ) (x y : List Bool), x.length = n → y.length = n →
    (∀ i ∈ needs gs n out, x.getD i false = y.getD i false) →
    (gs.foldl step x).getD out false = (gs.foldl step y).getD out false := by
  induction gs with
  | nil =>
    intro n out x y _ _ h
    exact h out (by simp [needs])
  | cons g gs ih =>
    intro n out x y hx hy h
    simp only [List.foldl_cons]
    apply ih (n + 1) out
    · simp [step, hx]
    · simp [step, hy]
    · intro i hi
      rcases Nat.lt_trichotomy i n with hlt | heq | hgt
      · have hm : i ∈ needs (g :: gs) n out := by
          simp only [needs]
          split_ifs with hn
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hi⟩)
          · exact hi
        have := h i hm
        simp only [step]
        rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact this
      · subst heq
        have hm : ∀ j ∈ eff g, x.getD j false = y.getD j false := by
          intro j hj
          apply h
          simp only [needs]
          rw [if_pos hi]
          exact Finset.mem_union_right _ hj
        have e := gate_congr g x y hm
        simp only [step]
        have ex := getD_snoc_eq x (g.op.eval (g.inputs.map fun i => x.getD i false))
        have ey := getD_snoc_eq y (g.op.eval (g.inputs.map fun i => y.getD i false))
        rw [hx] at ex
        rw [hy] at ey
        rw [ex, ey, e]
      · simp only [step]
        rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]

theorem mono (gs : List Gate) : ∀ (n out : ℕ) (x y : List Bool), x.length = n → y.length = n →
    bads gs n out = 0 →
    (∀ i ∈ needs gs n out, x.getD i false = true → y.getD i false = true) →
    (gs.foldl step x).getD out false = true → (gs.foldl step y).getD out false = true := by
  induction gs with
  | nil =>
    intro n out x y _ _ _ h
    exact h out (by simp [needs])
  | cons g gs ih =>
    intro n out x y hx hy hb h
    simp only [List.foldl_cons]
    simp only [bads] at hb
    apply ih (n + 1) out
    · simp [step, hx]
    · simp [step, hy]
    · omega
    · intro i hi
      rcases Nat.lt_trichotomy i n with hlt | heq | hgt
      · have hm : i ∈ needs (g :: gs) n out := by
          simp only [needs]
          split_ifs with hn
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hi⟩)
          · exact hi
        have := h i hm
        simp only [step]
        rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact this
      · subst heq
        have hm : ∀ j ∈ eff g, x.getD j false = true → y.getD j false = true := by
          intro j hj
          apply h
          simp only [needs]
          rw [if_pos hi]
          exact Finset.mem_union_right _ hj
        have hmono : isMono g.op = true := by
          by_contra hc
          have hc' : isMono g.op = false := by simpa using hc
          rw [if_pos ⟨hi, hc'⟩] at hb
          omega
        have e := gate_mono g hmono x y hm
        simp only [step]
        have ex := getD_snoc_eq x (g.op.eval (g.inputs.map fun i => x.getD i false))
        have ey := getD_snoc_eq y (g.op.eval (g.inputs.map fun i => y.getD i false))
        rw [hx] at ex
        rw [hy] at ey
        rw [ex, ey]
        exact e
      · simp only [step]
        rw [getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ (by omega)]
        exact id

theorem eff_card (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (eff g).card + (if isMono g.op = false then 1 else 0) ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop hlen
  have h1 : inputs.toFinset.card ≤ inputs.length := List.toFinset_card_le inputs
  have h2 : (inputs.take 1).toFinset.card ≤ (inputs.take 1).length :=
    List.toFinset_card_le (inputs.take 1)
  have h3 : (inputs.take 1).length ≤ 1 := by simp
  rcases hop with rfl | rfl | rfl
  · simp only [eff, isMono]
    simp
    omega
  · simp only [eff, isMono]
    simp
    omega
  · simp only [eff, isMono]
    simp
    omega

theorem count (gs : List Gate) :
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ n out, (needs gs n out).card + bads gs n out ≤ gs.length + 1 := by
  induction gs with
  | nil =>
    intro _ n out
    simp [needs, bads]
  | cons g gs ih =>
    intro hF n out
    have ih' := ih (fun g hg => hF g (List.mem_cons_of_mem _ hg)) (n + 1) out
    have heff := eff_card g (hF g (by simp))
    simp only [needs, bads, List.length_cons]
    by_cases hn : n ∈ needs gs (n + 1) out
    · rw [if_pos hn]
      have h1 : ((needs gs (n + 1) out).erase n ∪ eff g).card
          ≤ ((needs gs (n + 1) out).erase n).card + (eff g).card := Finset.card_union_le _ _
      have h2 := Finset.card_erase_of_mem hn
      have h3 : 0 < (needs gs (n + 1) out).card := Finset.card_pos.mpr ⟨n, hn⟩
      by_cases hm : isMono g.op = false
      · rw [if_pos hm] at heff
        rw [if_pos ⟨hn, hm⟩]
        omega
      · rw [if_neg hm] at heff
        rw [if_neg (fun h => hm h.2)]
        omega
    · rw [if_neg hn, if_neg (fun h => hn h.1)]
      omega

theorem one_true {N : ℕ} (u v : Fin N) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = true ↔ (i = u.val ∨ i = N + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  have hu := u.isLt
  have hv := v.isLt
  by_cases h1 : i < N
  · rw [List.getElem?_append_left (by simpa using h1)]
    simp [h1, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simpa using h1)]
    by_cases h2 : i - N < N
    · simp [h2, Fin.ext_iff]
      omega
    · simp [h2]
      omega

theorem one_len {N : ℕ} (u v : Fin N) : (PEqualNP.Represents.oneEach u v).length = N + N := by
  simp [PEqualNP.Represents.oneEach]

theorem main (N : ℕ) (hN : 2 ≤ N) (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hR : PEqualNP.Represents.Represents (fun u v : Fin N => decide (u = v)) C) :
    2 * N - 2 ≤ C.size := by
  have hcount := count C.gates hF (N + N) C.output
  have hev : ∀ u v : Fin N,
      (C.gates.foldl step (PEqualNP.Represents.oneEach u v)).getD C.output false
        = decide (u = v) := fun u v => hR u v
  have hrow : ∀ a b : Fin N, a ≠ b → a.val ∉ needs C.gates (N + N) C.output →
      b.val ∉ needs C.gates (N + N) C.output → False := by
    intro a b hab ha hb
    have key := dep C.gates (N + N) C.output (PEqualNP.Represents.oneEach a a)
      (PEqualNP.Represents.oneEach b a) (one_len _ _) (one_len _ _) (by
        intro i hi
        rw [Bool.eq_iff_iff, one_true, one_true]
        have h1 : i ≠ a.val := fun h => ha (h ▸ hi)
        have h2 : i ≠ b.val := fun h => hb (h ▸ hi)
        tauto)
    rw [hev, hev] at key
    simp at key
    exact hab key.symm
  have hcol : ∀ a b : Fin N, a ≠ b → N + a.val ∉ needs C.gates (N + N) C.output →
      N + b.val ∉ needs C.gates (N + N) C.output → False := by
    intro a b hab ha hb
    have key := dep C.gates (N + N) C.output (PEqualNP.Represents.oneEach a a)
      (PEqualNP.Represents.oneEach a b) (one_len _ _) (one_len _ _) (by
        intro i hi
        rw [Bool.eq_iff_iff, one_true, one_true]
        have h1 : i ≠ N + a.val := fun h => ha (h ▸ hi)
        have h2 : i ≠ N + b.val := fun h => hb (h ▸ hi)
        tauto)
    rw [hev, hev] at key
    simp at key
    exact hab key
  by_cases hb : bads C.gates (N + N) C.output = 0
  · -- monotone case: every input wire is needed
    have hrow' : ∀ a : Fin N, a.val ∈ needs C.gates (N + N) C.output := by
      intro a
      by_contra ha
      obtain ⟨u, hu⟩ : ∃ u : Fin N, u ≠ a := by
        by_cases h0 : a.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      have key := mono C.gates (N + N) C.output (PEqualNP.Represents.oneEach a a)
        (PEqualNP.Represents.oneEach u a) (one_len _ _) (one_len _ _) hb (by
          intro i hi
          rw [one_true, one_true]
          have h1 : i ≠ a.val := fun h => ha (h ▸ hi)
          tauto)
      rw [hev, hev] at key
      simp at key
      exact hu key
    have hcol' : ∀ a : Fin N, N + a.val ∈ needs C.gates (N + N) C.output := by
      intro a
      by_contra ha
      obtain ⟨u, hu⟩ : ∃ u : Fin N, u ≠ a := by
        by_cases h0 : a.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
        · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
      have key := mono C.gates (N + N) C.output (PEqualNP.Represents.oneEach a a)
        (PEqualNP.Represents.oneEach a u) (one_len _ _) (one_len _ _) hb (by
          intro i hi
          rw [one_true, one_true]
          have h1 : i ≠ N + a.val := fun h => ha (h ▸ hi)
          tauto)
      rw [hev, hev] at key
      simp at key
      exact hu key.symm
    have hsub : Finset.range (N + N) ⊆ needs C.gates (N + N) C.output := by
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases h1 : i < N
      · exact hrow' ⟨i, h1⟩
      · have := hcol' ⟨i - N, by omega⟩
        have e : N + (i - N) = i := by omega
        simpa [e] using this
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    unfold Circuit.size
    omega
  · -- some needed gate is a NOT: the tree bound gains one
    have hmiss : ((Finset.range (N + N)).filter
        (fun i => i ∉ needs C.gates (N + N) C.output)).card ≤ 2 := by
      rw [← Finset.card_filter_add_card_filter_not (s := (Finset.range (N + N)).filter
        (fun i => i ∉ needs C.gates (N + N) C.output)) (fun i => i < N)]
      have c1 : (((Finset.range (N + N)).filter
          (fun i => i ∉ needs C.gates (N + N) C.output)).filter (fun i => i < N)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb'
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb'
        by_contra hab
        exact hrow ⟨a, ha.2⟩ ⟨b, hb'.2⟩ (fun h => hab (by simpa [Fin.ext_iff] using h))
          ha.1.2 hb'.1.2
      have c2 : (((Finset.range (N + N)).filter
          (fun i => i ∉ needs C.gates (N + N) C.output)).filter (fun i => ¬ i < N)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb'
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb'
        by_contra hab
        have ea : N + (a - N) = a := by omega
        have eb : N + (b - N) = b := by omega
        exact hcol ⟨a - N, by omega⟩ ⟨b - N, by omega⟩
          (fun h => hab (by simp [Fin.ext_iff] at h; omega))
          (by simpa [ea] using ha.1.2) (by simpa [eb] using hb'.1.2)
      omega
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range (N + N))
      (fun i => i ∈ needs C.gates (N + N) C.output)
    have hle : ((Finset.range (N + N)).filter
        (fun i => i ∈ needs C.gates (N + N) C.output)).card
          ≤ (needs C.gates (N + N) C.output).card := by
      apply Finset.card_le_card
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    rw [Finset.card_range] at hsplit
    unfold Circuit.size
    omega

end PEqualNP.Outside.L_meta_17175

theorem PEqualNP.Outside.L_meta_17175 : ∀ (N : ℕ), 2 ≤ N → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents (fun u v : Fin N => decide (u = v)) C → 2 * N - 2 ≤ C.size :=
  PEqualNP.Outside.L_meta_17175.main
