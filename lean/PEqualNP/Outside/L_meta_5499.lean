import Mathlib
import PEqualNP.Defs

-- Lower bound for a small graph: set some vertices to false one at a time (each costs a gate), then an
-- exhaustive truth-table search, replayed by the kernel, bounds what is left.
namespace PEqualNP.Outside.L_meta_5499_aux

-- Gate removal after fixing one input: copied from the merged PEqualNP/Outside/L_meta_4003.lean.
namespace D


open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

def Const {Y : Type} (f : Y → Bool) : Prop := ∃ c, ∀ y, f y = c

def Drop {Y : Type} (n : ℕ) (F : ℕ → Y → Bool) (j : ℕ) : Prop :=
  Const (F (n + j)) ∨ ∃ w < n + j, ∀ y, F (n + j) y = F w y

theorem restrict (n m : ℕ) (gs : List Gate) (F : ℕ → (Fin m → Bool) → Bool)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i < n, Const (F i) ∨ ∃ k < m, ∀ y, F i y = (List.ofFn y).getD k false)
    (hF : ∀ (j : ℕ) (hj : j < gs.length) (y : Fin m → Bool), F (n + j) y =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then F i y else false)) :
    ∀ K ≤ gs.length, ∃ (ds : List Gate) (S : Finset ℕ),
      (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
      (∀ j ∈ S, j < K ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
      ∀ w < n + K, Const (F w) ∨
        ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
  intro K
  induction K with
  | zero =>
    intro _
    refine ⟨[], ∅, by simp, by simp, by simp, by simp, fun w hw => ?_⟩
    simpa [run] using hin w (by omega)
  | succ K ih =>
    intro hK
    obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := ih (by omega)
    have h2' : ∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j := fun j hj =>
      ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
    by_cases hd : Drop n F K
    · refine ⟨ds, S, h1, hb, h2', h3, fun w hw => ?_⟩
      rcases Nat.lt_or_ge w (n + K) with h | h
      · exact h4 w h
      · rw [show w = n + K by omega]
        rcases hd with hc | ⟨u, hu, he⟩
        · exact Or.inl hc
        · rcases h4 u hu with ⟨c, hc⟩ | ⟨k, hk, hk'⟩
          · exact Or.inl ⟨c, fun y => (he y).trans (hc y)⟩
          · exact Or.inr ⟨k, hk, fun y => (he y).trans (hk' y)⟩
    · have hnc : ¬ Const (F (n + K)) := fun h => hd (Or.inl h)
      have hne : ∀ u < n + K, ¬ ∀ y, F (n + K) y = F u y := fun u hu h => hd (Or.inr ⟨u, hu, h⟩)
      have addg : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
          g.inputs.length ≤ 2 → (∀ i ∈ g.inputs, i < m + ds.length) →
          (∀ y, F (n + K) y = g.op.eval (g.inputs.map fun i =>
            (run ds (List.ofFn y)).getD i false)) →
          ∃ (ds : List Gate) (S : Finset ℕ),
            (∀ g ∈ ds, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
              g.inputs.length ≤ 2) ∧
            (∀ (j : ℕ) (hj : j < ds.length), ∀ i ∈ ds[j].inputs, i < m + j) ∧
            (∀ j ∈ S, j < K + 1 ∧ ¬ Drop n F j) ∧ ds.length ≤ S.card ∧
            ∀ w < n + (K + 1), Const (F w) ∨
              ∃ k < m + ds.length, ∀ y, F w y = (run ds (List.ofFn y)).getD k false := by
        intro g ho hl hgb hg
        have hKS : K ∉ S := fun h => by have := (h2 K h).1; omega
        refine ⟨ds ++ [g], insert K S, ?_, ?_, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.1 hg' with h | h
          · exact h1 g' h
          · rw [List.mem_singleton.1 h]; exact ⟨ho, hl⟩
        · intro j hj i hi
          rcases Nat.lt_or_ge j ds.length with h | h
          · rw [List.getElem_append_left h] at hi
            exact hb j h i hi
          · have hjj : j = ds.length := by simp at hj; omega
            subst hjj
            exact hgb i (by simpa using hi)
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | h
          · exact ⟨by omega, hd⟩
          · exact h2' j h
        · rw [Finset.card_insert_of_notMem hKS]; simp; omega
        · intro w hw
          rcases Nat.lt_or_ge w (n + K) with h | h
          · rcases h4 w h with hc | ⟨k, hk, hk'⟩
            · exact Or.inl hc
            · refine Or.inr ⟨k, by simp; omega, fun y => ?_⟩
              rw [run_snoc, getD_lt _ _ _ (by rw [run_length, List.length_ofFn]; exact hk)]
              exact hk' y
          · refine Or.inr ⟨m + ds.length, by simp, fun y => ?_⟩
            have hl' : (run ds (List.ofFn y)).length = m + ds.length := by
              rw [run_length, List.length_ofFn]
            rw [show w = n + K by omega, run_snoc, ← hl', getD_at]
            exact hg y
      have hval : ∀ i, (∃ c, ∀ y, (if i < n + K then F i y else false) = c) ∨
          (i < n + K ∧ ∃ k < m + ds.length, ∀ y,
            F i y = (run ds (List.ofFn y)).getD k false) := by
        intro i
        by_cases hi : i < n + K
        · rcases h4 i hi with ⟨c, hc⟩ | h
          · exact Or.inl ⟨c, fun y => by rw [if_pos hi]; exact hc y⟩
          · exact Or.inr ⟨hi, h⟩
        · exact Or.inl ⟨false, fun y => by rw [if_neg hi]⟩
      have hj : K < gs.length := by omega
      have hFK := hF K hj
      obtain ⟨hop, hlen⟩ := hops _ (List.getElem_mem hj)
      generalize gs[K].inputs = I at *
      generalize gs[K].op = o at *
      match I, hlen with
      | [], _ =>
        refine absurd ⟨o.eval [], fun y => ?_⟩ hnc
        simpa using hFK y
      | [a], _ =>
        rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
        · refine absurd ⟨o.eval [c], fun y => ?_⟩ hnc
          rw [hFK y, List.map_singleton, hc y]
        · rcases hop with rfl | rfl | rfl
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine absurd (fun y => ?_) (hne a ha)
            rw [hFK y]; simp [GateOp.eval, ha]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]
      | [a, b], _ =>
        rcases hop with rfl | rfl | rfl
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c && if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · exact absurd ⟨false, fun y => by rw [he y]; rfl⟩ hnc
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y && c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd ⟨false, fun y => by rw [he y]; simp⟩ hnc
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
            · refine addg ⟨GateOp.and, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · have he : ∀ y, F (n + K) y = (c || if b < n + K then F b y else false) := by
              intro y
              rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval]
            cases c
            · by_cases hb' : b < n + K
              · exact absurd (fun y => by rw [he y, if_pos hb']; rfl) (hne b hb')
              · exact absurd ⟨false, fun y => by rw [he y, if_neg hb']; rfl⟩ hnc
            · exact absurd ⟨true, fun y => by rw [he y]; rfl⟩ hnc
          · rcases hval b with ⟨c, hc⟩ | ⟨hb', l, hl, hl'⟩
            · have he : ∀ y, F (n + K) y = (F a y || c) := by
                intro y
                rw [hFK y, List.map_cons, List.map_singleton, hc y]; simp [GateOp.eval, ha]
              cases c
              · exact absurd (fun y => by rw [he y]; simp) (hne a ha)
              · exact absurd ⟨true, fun y => by rw [he y]; simp⟩ hnc
            · refine addg ⟨GateOp.or, [k, l]⟩ (by simp) (by simp) (by simpa using ⟨hk, hl⟩) fun y => ?_
              rw [hFK y]; simp [GateOp.eval, ha, hb', hk' y, hl' y]
        · rcases hval a with ⟨c, hc⟩ | ⟨ha, k, hk, hk'⟩
          · refine absurd ⟨!c, fun y => ?_⟩ hnc
            rw [hFK y, List.map_cons, hc y]; simp [GateOp.eval]
          · refine addg ⟨GateOp.not, [k]⟩ (by simp) (by simp) (by simpa using hk) fun y => ?_
            rw [hFK y]; simp [GateOp.eval, ha, hk' y]

theorem circuit (n m : ℕ) (C : Circuit) (X : (Fin m → Bool) → List Bool)
    (hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hX : ∀ y, (X y).length = n)
    (hin : ∀ i < n, (∃ c, ∀ y, (X y).getD i false = c) ∨
      ∃ k < m, ∀ y, (X y).getD i false = (List.ofFn y).getD k false)
    (hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin m → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun i => if i < n + j then (C.wires (X y)).getD i false else false))
    (hinw : ∀ i < n, ∀ y, (C.wires (X y)).getD i false = (X y).getD i false)
    (hout : C.output < n + C.gates.length)
    (hnc : ¬ ∃ c, ∀ y, C.eval (X y) = c) :
    ∃ (D : Circuit) (S : Finset ℕ),
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (hj : j < D.gates.length), ∀ i ∈ D.gates[j].inputs, i < m + j) ∧
      D.output < m + D.gates.length ∧ D.gates.length ≤ S.card ∧
      (∀ j ∈ S, j < C.gates.length ∧
        ¬ Drop n (fun w (y : Fin m → Bool) => (C.wires (X y)).getD w false) j) ∧
      ∀ y, D.eval (List.ofFn y) = C.eval (X y) := by
  obtain ⟨ds, S, h1, hb, h2, h3, h4⟩ := restrict n m C.gates
    (fun w y => (C.wires (X y)).getD w false) hops (fun i hi => by
      rcases hin i hi with ⟨c, hc⟩ | ⟨k, hk, h⟩
      · exact Or.inl ⟨c, fun y => (hinw i hi y).trans (hc y)⟩
      · exact Or.inr ⟨k, hk, fun y => (hinw i hi y).trans (h y)⟩) hrec C.gates.length le_rfl
  rcases h4 C.output hout with hc | ⟨k, hk, hk'⟩
  · exact absurd hc hnc
  · exact ⟨⟨ds, k⟩, S, h1, hb, hk, h3, h2, fun y => (hk' y).symm⟩

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def rds (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

theorem eval_congr (g : Gate) (u v : ℕ → Bool)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huv : ∀ i ∈ rds g, u i = v i) : g.op.eval (g.inputs.map u) = g.op.eval (g.inputs.map v) := by
  rcases hop with h | h | h
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [List.map_congr_left huv]
  · simp only [rds, h] at huv
    rw [h]
    cases hi : g.inputs with
    | nil => rfl
    | cons a t =>
      have := huv a (by simp [hi])
      simp [GateOp.eval, this]

theorem getD_sn (l : List Bool) (b : Bool) (t : ℕ) :
    (l ++ [b]).getD t false = if t = l.length then b else l.getD t false := by
  rcases lt_trichotomy t l.length with h | h | h
  · rw [if_neg (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem indep (v : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hno : ∀ g ∈ gs, v ∉ rds g) (x y : List Bool) (hl : x.length = y.length)
    (hxy : ∀ i, i ≠ v → x.getD i false = y.getD i false) :
    ∀ i, i ≠ v → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih' := ih (fun g' h => hop g' (by simp [h])) (fun g' h => hno g' (by simp [h]))
    intro i hi
    have e : g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
        g.op.eval (g.inputs.map fun i => (run gs y).getD i false) :=
      eval_congr g _ _ (hop g (by simp)) fun k hk =>
        ih' k fun hc => hno g (by simp) (hc ▸ hk)
    rw [run_snoc, run_snoc, getD_sn, getD_sn, run_length, run_length, hl, e]
    split_ifs
    · rfl
    · exact ih' i hi

theorem one_drop (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C) (i : Fin n)
    (b : Bool)
    (hess : ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (hnc : ¬ ∃ c, ∀ y : Fin n → Bool, C.eval (List.ofFn (Function.update y i b)) = c) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (List.ofFn (Function.update y i b)) := by
  have hops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  have hw : ∀ x, C.wires x = run C.gates x := fun _ => rfl
  have hev : ∀ x, C.eval x = (run C.gates x).getD C.output false := fun _ => rfl
  have hout : C.output < n + C.gates.length := by
    by_contra hcon
    obtain ⟨x, y, -, hxy⟩ := hess
    apply hxy
    rw [hev, hev, List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega),
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
  let X : (Fin n → Bool) → List Bool := fun y => List.ofFn (Function.update y i b)
  have hXl : ∀ y, (X y).length = n := fun y => by simp [X]
  have hXi : ∀ y, (X y).getD i false = b := by
    intro y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    simp
  have hXk : ∀ (k : ℕ), k < n → k ≠ i → ∀ y, (X y).getD k false = (List.ofFn y).getD k false := by
    intro k hk hki y
    simp only [X]
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simpa using hk),
      List.getElem_ofFn, List.getElem_ofFn]
    exact Function.update_of_ne (fun hc => hki (congrArg Fin.val hc)) _ _
  have hinw : ∀ k < n, ∀ y, (C.wires (X y)).getD k false = (X y).getD k false := by
    intro k hk y
    rw [hw]
    exact run_input _ _ _ (by rw [hXl]; exact hk)
  have hrec : ∀ (j : ℕ) (hj : j < C.gates.length) (y : Fin n → Bool),
      (C.wires (X y)).getD (n + j) false = C.gates[j].op.eval
        (C.gates[j].inputs.map fun k =>
          if k < n + j then (C.wires (X y)).getD k false else false) := by
    intro j hj y
    have h := run_gate C.gates (X y) j hj
    rw [hXl] at h
    exact h
  have hoi : C.output ≠ i := by
    intro h
    apply hnc
    refine ⟨b, fun y => ?_⟩
    rw [hev, h, run_input _ _ _ (by simp)]
    exact hXi y
  have hread : ∃ g ∈ C.gates, (i : ℕ) ∈ rds g := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, y, hxy, hne⟩ := hess
    apply hne
    rw [hev, hev]
    refine indep i C.gates (fun g hg => (hops g hg).1) hcon _ _ (by simp) (fun k hk => ?_) _ hoi
    by_cases h : k < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_ofFn, List.getElem_ofFn]
      exact hxy _ fun hc => hk (congrArg Fin.val hc)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  obtain ⟨g, hg, hgi⟩ := hread
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
  obtain ⟨D, S, d1, -, -, d4, d5, d6⟩ := circuit n n C X hops hXl (fun k hk => by
      by_cases h : k = i
      · exact Or.inl ⟨b, fun y => by rw [h]; exact hXi y⟩
      · exact Or.inr ⟨k, hk, hXk k hk h⟩) hrec hinw hout hnc
  refine ⟨D, fun g hg => ?_, ?_, fun y => d6 y⟩
  · obtain ⟨h1, h2⟩ := d1 g hg
    exact ⟨by simpa using h1, h2⟩
  · have hdrop : Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
      obtain ⟨hop, hlen⟩ := hops _ hg
      have hv := hrec j hj
      have hii : ∀ y, (if (i : ℕ) < n + j then (C.wires (X y)).getD (i : ℕ) false else false) = b := by
        intro y
        rw [if_pos (by have := i.2; omega), hinw i i.2, hXi]
      generalize hI : C.gates[j].inputs = I at *
      generalize hO : C.gates[j].op = o at *
      have two : ∀ c : ℕ, (∀ y, (C.wires (X y)).getD (n + j) false =
          (b && if c < n + j then (C.wires (X y)).getD c false else false)) ∨
          (∀ y, (C.wires (X y)).getD (n + j) false =
          (b || if c < n + j then (C.wires (X y)).getD c false else false)) →
          Drop n (fun w (y : Fin n → Bool) => (C.wires (X y)).getD w false) j := by
        intro c hc
        by_cases hcl : c < n + j
        · simp only [hcl, if_true] at hc
          rcases hc with hc | hc <;> cases b
          · exact Or.inl ⟨false, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inr ⟨c, hcl, fun y => by simp only; rw [hc y]; rfl⟩
          · exact Or.inl ⟨true, fun y => by simp only; rw [hc y]; rfl⟩
        · simp only [hcl, if_false] at hc
          rcases hc with hc | hc
          · exact Or.inl ⟨b && false, fun y => hc y⟩
          · exact Or.inl ⟨b || false, fun y => hc y⟩
      match I, hlen with
      | [], _ =>
        exfalso
        simp only [rds, hO, hI] at hgi
        rcases hop with rfl | rfl | rfl <;> simp at hgi
      | [a], _ =>
        have hai : a = i := by
          simp only [rds, hO, hI] at hgi
          rcases hop with rfl | rfl | rfl
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
          · exact (List.mem_singleton.1 hgi).symm
        subst hai
        refine Or.inl ⟨o.eval [b], fun y => ?_⟩
        simp only
        rw [hv y, List.map_singleton, hii y]
      | [a, c], _ =>
        rcases hop with rfl | rfl | rfl
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inl fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.and_comm]
        · have hac : (i : ℕ) = a ∨ (i : ℕ) = c := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          rcases hac with rfl | rfl
          · refine two c (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval]
          · refine two a (Or.inr fun y => ?_)
            rw [hv y, List.map_cons, List.map_singleton, hii y]
            simp [GateOp.eval, Bool.or_comm]
        · have hai : (i : ℕ) = a := by
            simp only [rds, hO, hI] at hgi
            simpa using hgi
          subst hai
          refine Or.inl ⟨!b, fun y => ?_⟩
          simp only
          rw [hv y, List.map_cons, hii y]
          rfl
    have hsub : S ⊆ (Finset.range C.gates.length).erase j := by
      intro k hk
      obtain ⟨h1, h2⟩ := d5 k hk
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_range.2 h1⟩
      rintro rfl
      exact h2 hdrop
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 hj), Finset.card_range] at h1
    change D.gates.length + 1 ≤ C.gates.length
    omega


end D


open PEqualNP.CircuitLowerBounds

-- Generic exhaustive search over truth tables (bit j of a table is the value on row j).
-- A table list is kept newest first. M is the all-true table, F the target table.

def mem (t : ℕ) : List ℕ → Bool
  | [] => false
  | a :: r => Nat.beq t a || mem t r

def pairsWith (a : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | b :: r => (a &&& b) :: (a ||| b) :: pairsWith a acc r

-- every table one new gate can have (up to tables already present or zero)
def prs (M : ℕ) : List ℕ → List ℕ
  | [] => [M]
  | a :: r => (M ^^^ a) :: pairsWith a (prs M r) r

def c0 (F : ℕ) (L : List ℕ) : Bool := Nat.beq F 0 || mem F L

def nw (Z acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | t :: r => if (Nat.beq t 0 || mem t Z || mem t acc) = true then nw Z acc r else nw Z (t :: acc) r

def orHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t ||| c) F || orHit F t r

def andHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t &&& c) F || andHit F t r

-- can a gate reading the new table t and one old table (or t alone) give F
def newOK (M F t : ℕ) (L : List ℕ) : Bool :=
  Nat.beq F (M ^^^ t) || (Nat.beq (t ||| F) F && orHit F t L) ||
    (Nat.beq (t &&& F) F && andHit F t L)

def can (M F : ℕ) : ℕ → List ℕ → Bool
  | 0, L => c0 F L
  | 1, L => c0 F L || mem F (prs M L)
  | 2, L => c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)
  | k + 3, L => c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))

theorem mem_iff (t : ℕ) (L : List ℕ) : mem t L = true ↔ t ∈ L := by
  induction L with
  | nil => simp [mem]
  | cons a r ih => simp [mem, ih]

theorem pairsWith_mem (a x : ℕ) (acc r : List ℕ) :
    x ∈ pairsWith a acc r ↔ x ∈ acc ∨ ∃ c ∈ r, x = a &&& c ∨ x = a ||| c := by
  induction r with
  | nil => simp [pairsWith]
  | cons b r ih =>
    simp only [pairsWith, List.mem_cons, ih, or_and_right, exists_or, exists_eq_left]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | (h | h) | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

theorem prs_cons (M t x : ℕ) (L : List ℕ) :
    x ∈ prs M (t :: L) ↔ x = M ^^^ t ∨ x ∈ prs M L ∨ ∃ c ∈ L, x = t &&& c ∨ x = t ||| c := by
  simp only [prs, List.mem_cons, pairsWith_mem]

theorem M_mem (M : ℕ) (L : List ℕ) : M ∈ prs M L := by
  induction L with
  | nil => simp [prs]
  | cons a r ih => exact (prs_cons M a M r).2 (Or.inr (Or.inl ih))

theorem not_mem (M a : ℕ) (L : List ℕ) (h : a ∈ L) : M ^^^ a ∈ prs M L := by
  induction L with
  | nil => simp at h
  | cons b r ih =>
    rw [prs_cons]
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (ih h))

theorem pair_mem (M a b : ℕ) (L : List ℕ) (ha : a ∈ L) (hb : b ∈ L) :
    (a &&& b ∈ L ∨ a &&& b ∈ prs M L) ∧ (a ||| b ∈ L ∨ a ||| b ∈ prs M L) := by
  induction L with
  | nil => simp at ha
  | cons x r ih =>
    rcases List.mem_cons.1 ha with ha1 | ha1 <;> rcases List.mem_cons.1 hb with hb1 | hb1
    · rw [ha1, hb1]
      simp
    · rw [ha1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨b, hb1, Or.inl rfl⟩))),
        Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨b, hb1, Or.inr rfl⟩)))⟩
    · rw [hb1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨a, ha1, Or.inl (Nat.land_comm _ _)⟩))),
        Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨a, ha1, Or.inr (Nat.lor_comm _ _)⟩)))⟩
    · obtain ⟨h1, h2⟩ := ih ha1 hb1
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inl h1)))
      · rcases h2 with h2 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h2)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inl h2)))

theorem and_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a &&& b = 0 ∨ a &&& b ∈ L ∨ a &&& b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simp
  rcases hb with hb | hb
  · subst hb; simp
  exact Or.inr (pair_mem M a b L ha hb).1

theorem or_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a ||| b = 0 ∨ a ||| b ∈ L ∨ a ||| b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; rw [Nat.zero_or]; tauto
  rcases hb with hb | hb
  · subst hb; rw [Nat.or_zero]; tauto
  exact Or.inr (pair_mem M a b L ha hb).2

theorem not_in (M a : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) : M ^^^ a ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simpa using M_mem M L
  exact not_mem M a L ha

theorem nw_acc (Z acc ts : List ℕ) (t : ℕ) (h : t ∈ acc) : t ∈ nw Z acc ts := by
  induction ts generalizing acc with
  | nil => simpa [nw] using h
  | cons s r ih =>
    simp only [nw]
    split
    · exact ih acc h
    · exact ih (s :: acc) (List.mem_cons_of_mem _ h)

theorem nw_mem (Z acc ts : List ℕ) (t : ℕ) (h : t ∈ ts) (h0 : t ≠ 0) (hZ : t ∉ Z) :
    t ∈ nw Z acc ts := by
  induction ts generalizing acc with
  | nil => simp at h
  | cons s r ih =>
    simp only [nw]
    rcases List.mem_cons.1 h with h | h
    · subst h
      split
      · rename_i hc
        simp only [Bool.or_eq_true, Nat.beq_eq, mem_iff] at hc
        rcases hc with (hc | hc) | hc
        · exact absurd hc h0
        · exact absurd hc hZ
        · exact nw_acc Z acc r t hc
      · exact nw_acc Z (t :: acc) r t (List.mem_cons_self)
    · split
      · exact ih acc h
      · exact ih (s :: acc) h

theorem orHit_iff (F t : ℕ) (L : List ℕ) : orHit F t L = true ↔ ∃ c ∈ L, t ||| c = F := by
  induction L with
  | nil => simp [orHit]
  | cons c r ih => simp [orHit, ih]

theorem andHit_iff (F t : ℕ) (L : List ℕ) : andHit F t L = true ↔ ∃ c ∈ L, t &&& c = F := by
  induction L with
  | nil => simp [andHit]
  | cons c r ih => simp [andHit, ih]

theorem newOK_complete (M F t : ℕ) (L : List ℕ)
    (h : F = M ^^^ t ∨ ∃ c ∈ L, F = t &&& c ∨ F = t ||| c) : newOK M F t L = true := by
  unfold newOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff]
  rcases h with h | ⟨c, hc, h | h⟩
  · exact Or.inl (Or.inl h)
  · right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_land]
  · left; right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_lor]

theorem newOK_sound (M F t : ℕ) (L : List ℕ) (h : newOK M F t L = true) :
    F ∈ prs M (t :: L) := by
  unfold newOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff] at h
  rw [prs_cons]
  rcases h with (h | ⟨_, c, hc, h⟩) | ⟨_, c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨c, hc, Or.inr h.symm⟩)
  · exact Or.inr (Or.inr ⟨c, hc, Or.inl h.symm⟩)

-- a gate built only from old tables adds nothing new
theorem absorb (M t x : ℕ) (L : List ℕ) (ht : t = 0 ∨ t ∈ L) (hx : x ∈ prs M (t :: L)) :
    x = 0 ∨ x ∈ L ∨ x ∈ prs M L := by
  rcases (prs_cons M t x L).1 hx with h | h | ⟨c, hc, h | h⟩
  · subst h; exact Or.inr (Or.inr (not_in M t L ht))
  · exact Or.inr (Or.inr h)
  · subst h; exact and_in M t c L ht (Or.inr hc)
  · subst h; exact or_in M t c L ht (Or.inr hc)

theorem can_of_c0 (M F k : ℕ) (L : List ℕ) (h : c0 F L = true) : can M F k L = true := by
  rcases k with _ | _ | _ | k <;> simp [can, h]

theorem c0_iff (F : ℕ) (L : List ℕ) : c0 F L = true ↔ F = 0 ∨ F ∈ L := by
  simp [c0, mem_iff]

-- a found table F one gate away
theorem can_of_prs (M F k : ℕ) (L : List ℕ) (h : F ∈ prs M L) : can M F (k + 1) L = true := by
  rcases k with _ | _ | k
  · simp [can, mem_iff, h]
  · simp [can, mem_iff, h]
  · by_cases hc : c0 F L = true
    · exact can_of_c0 M F _ L hc
    · rw [c0_iff] at hc
      push_neg at hc
      show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨F, nw_mem L [] _ F h hc.1 hc.2, can_of_c0 M F _ _ (by simp [c0, mem_iff])⟩

theorem mono (M F : ℕ) : ∀ (k : ℕ) (L : List ℕ), can M F k L = true → can M F (k + 1) L = true := by
  intro k
  induction k with
  | zero =>
    intro L h
    exact can_of_c0 M F 1 L h
  | succ k ih =>
    intro L h
    rcases k with _ | _ | k
    · -- from fuel 1 to fuel 2
      simp only [can, Bool.or_eq_true, mem_iff] at h
      rcases h with h | h
      · exact can_of_c0 M F 2 L h
      · exact can_of_prs M F 1 L h
    · -- from fuel 2 to fuel 3
      simp only [can, Bool.or_eq_true, mem_iff, List.any_eq_true] at h
      rcases h with (h | h) | ⟨t, ht, h⟩
      · exact can_of_c0 M F 3 L h
      · exact can_of_prs M F 2 L h
      · have hF := newOK_sound M F t L h
        have ht' : t ∈ prs M L := ht
        by_cases h0 : t = 0 ∨ t ∈ L
        · rcases absorb M t F L h0 hF with h1 | h1 | h1
          · exact can_of_c0 M F 3 L (by simp [c0, h1])
          · exact can_of_c0 M F 3 L (by simp [c0, mem_iff, h1])
          · exact can_of_prs M F 2 L h1
        · push_neg at h0
          show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F 2 (t :: L))) = true
          simp only [Bool.or_eq_true, List.any_eq_true]
          refine Or.inr ⟨t, nw_mem L [] _ t ht' h0.1 h0.2, ?_⟩
          exact can_of_prs M F 1 (t :: L) hF
    · show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 1 + 2) (t :: L))) = true
      have h' : (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true := h
      simp only [Bool.or_eq_true, List.any_eq_true] at h' ⊢
      rcases h' with h' | ⟨t, ht, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨t, ht, ih (t :: L) h'⟩

-- one new gate whose table t is new
theorem can_step (M F k t : ℕ) (L : List ℕ) (ht : t ∈ prs M L) (h0 : t ≠ 0) (hL : t ∉ L)
    (h : can M F k (t :: L) = true) : can M F (k + 1) L = true := by
  rcases k with _ | _ | k
  · simp only [can, c0_iff, List.mem_cons] at h
    rcases h with h | h | h
    · exact can_of_c0 M F 1 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 0 L ht
    · exact can_of_c0 M F 1 L (by simp [c0, mem_iff, h])
  · simp only [can, Bool.or_eq_true, c0_iff, List.mem_cons, mem_iff] at h
    rcases h with (h | h | h) | h
    · exact can_of_c0 M F 2 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 1 L ht
    · exact can_of_c0 M F 2 L (by simp [c0, mem_iff, h])
    · rcases (prs_cons M t F L).1 h with h1 | h1 | h1
      · show (c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, newOK_complete M F t L (Or.inl h1)⟩
      · exact can_of_prs M F 1 L h1
      · show (c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, newOK_complete M F t L (Or.inr h1)⟩
  · show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true
    simp only [Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨t, nw_mem L [] _ t ht h0 hL, h⟩

-- every wire i (also a missing one) is matched on rows j < N by zero or a table of L
def Inv (N : ℕ) (L : List ℕ) (w : ℕ → List Bool) : Prop :=
  ∀ i, ∃ a, (a = 0 ∨ a ∈ L) ∧ ∀ j < N, a.testBit j = (w j).getD i false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eq_of_bits (N a b : ℕ) (ha : a < 2 ^ N) (hb : b < 2 ^ N)
    (h : ∀ j < N, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · exact h i hi
  · have hp : 2 ^ N ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem gate_tab (N M : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (L : List ℕ) (hb : ∀ a ∈ L, a < 2 ^ N) (w : ℕ → List Bool) (hI : Inv N L w) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ t, (t = 0 ∨ t ∈ L ∨ t ∈ prs M L) ∧ t < 2 ^ N ∧
      ∀ j < N, t.testBit j = g.op.eval (g.inputs.map fun i => (w j).getD i false) := by
  have hz : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have hbd : ∀ a, (a = 0 ∨ a ∈ L) → a < 2 ^ N := by
    intro a ha
    rcases ha with ha | ha
    · rw [ha]; exact hz
    · exact hb a ha
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with hop | hop | hop <;> subst hop
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
    · exact ⟨0, Or.inl rfl, hz, fun j _ => by simp [GateOp.eval]⟩
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
  | [i], _ =>
    obtain ⟨a, ha, haw⟩ := hI i
    rcases hop with hop | hop | hop <;> subst hop
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · refine ⟨M ^^^ a, Or.inr (Or.inr (not_in M a L ha)), Nat.xor_lt_two_pow hMb (hbd a ha),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_xor, haw j hj, hM j hj]
  | [i1, i2], _ =>
    obtain ⟨a, ha, haw⟩ := hI i1
    obtain ⟨b, hb', hbw⟩ := hI i2
    rcases hop with hop | hop | hop <;> subst hop
    · refine ⟨a &&& b, and_in M a b L ha hb', Nat.and_lt_two_pow _ (hbd b hb'), fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_land, haw j hj, hbw j hj]
    · refine ⟨a ||| b, or_in M a b L ha hb', Nat.or_lt_two_pow (hbd a ha) (hbd b hb'),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_lor, haw j hj, hbw j hj]
    · refine ⟨M ^^^ a, Or.inr (Or.inr (not_in M a L ha)), Nat.xor_lt_two_pow hMb (hbd a ha),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_xor, haw j hj, hM j hj]
  | _ :: _ :: _ :: _, h => simp at h

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h, List.getElem?_append_left h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem inv_snoc (N m : ℕ) (L L' : List ℕ) (w : ℕ → List Bool) (v : ℕ → Bool) (t : ℕ)
    (hw : ∀ j, (w j).length = m) (hI : Inv N L w) (hLL : ∀ a ∈ L, a ∈ L')
    (ht : t = 0 ∨ t ∈ L') (htv : ∀ j < N, t.testBit j = v j) :
    Inv N L' (fun j => w j ++ [v j]) := by
  intro i
  by_cases h1 : i < m
  · obtain ⟨a, ha, haw⟩ := hI i
    refine ⟨a, ?_, fun j hj => ?_⟩
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (hLL a ha)
    · simp only [getD_snoc, hw j, if_pos h1]
      exact haw j hj
  · by_cases h2 : i = m
    · refine ⟨t, ht, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_pos h2]
      exact htv j hj
    · refine ⟨0, Or.inl rfl, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_neg h2, Nat.zero_testBit]

theorem sound (N M F : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (hF : F < 2 ^ N) :
    ∀ (gs : List Gate) (k m : ℕ) (L : List ℕ) (w : ℕ → List Bool),
      (∀ a ∈ L, a < 2 ^ N) → (∀ j, (w j).length = m) → Inv N L w →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      gs.length ≤ k → ∀ o : ℕ,
      (∀ j < N, (gs.foldl stp (w j)).getD o false = F.testBit j) → can M F k L = true := by
  intro gs
  induction gs with
  | nil =>
    intro k m L w hb _ hI _ _ o ho
    obtain ⟨a, ha, haw⟩ := hI o
    have hab : a < 2 ^ N := by
      rcases ha with ha | ha
      · rw [ha]; exact Nat.two_pow_pos N
      · exact hb a ha
    have hEq : a = F := eq_of_bits N a F hab hF (fun j hj => by
      rw [haw j hj]; exact ho j hj)
    exact can_of_c0 M F k L (by rw [c0_iff, ← hEq]; tauto)
  | cons g gs ih =>
    intro k m L w hb hw hI hg hk o ho
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : gs.length ≤ k := by simp at hk; omega
    obtain ⟨t, htm, htb, htv⟩ :=
      gate_tab N M hM hMb L hb w hI g (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2
    have hw' : ∀ j, (stp (w j) g).length = m + 1 := by
      intro j; simp [stp, hw j]
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    have ho' : ∀ j < N, (gs.foldl stp (stp (w j) g)).getD o false = F.testBit j := ho
    by_cases hold : t = 0 ∨ t ∈ L
    · have hI' : Inv N L (fun j => stp (w j) g) :=
        inv_snoc N m L L w _ t hw hI (fun a h => h) hold htv
      exact mono M F k L (ih k (m + 1) L _ hb hw' hI' hg' hk' o ho')
    · push_neg at hold
      have htp : t ∈ prs M L := by
        rcases htm with h | h | h
        · exact absurd h hold.1
        · exact absurd h hold.2
        · exact h
      have hI' : Inv N (t :: L) (fun j => stp (w j) g) :=
        inv_snoc N m L (t :: L) w _ t hw hI (fun a h => List.mem_cons_of_mem _ h)
          (Or.inr List.mem_cons_self) htv
      have hb' : ∀ a ∈ t :: L, a < 2 ^ N := by
        intro a h
        rcases List.mem_cons.1 h with h | h
        · rw [h]; exact htb
        · exact hb a h
      exact can_step M F k t L htp hold.1 hold.2 (ih k (m + 1) (t :: L) _ hb' hw' hI' hg' hk' o ho')

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

-- the generic statement: n inputs, rows j < N (row j sets input i to bit i of j),
-- all-true table M, target table F, input tables L0 (any order), K gates are too few
theorem main_gen (n N M F K : ℕ) (L0 : List ℕ) (f : (Fin n → Bool) → Bool)
    (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N) (hF : F < 2 ^ N)
    (hL0 : ∀ a ∈ L0, a < 2 ^ N)
    (hin : ∀ i < n, ∃ a ∈ L0, ∀ j < N, a.testBit j = j.testBit i)
    (hf : ∀ j < N, f (fun i => j.testBit i) = F.testBit j)
    (hs : can M F K L0 = false) :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → K + 1 ≤ t := by
  intro t ⟨C, hfan, hsize, heval⟩
  by_contra hlt
  have hk : C.gates.length ≤ K := by
    have : C.size = C.gates.length := rfl
    omega
  have hI : Inv N L0 (fun j => List.ofFn (fun i : Fin n => j.testBit i)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨a, ha, haj⟩ := hin i hi
      refine ⟨a, Or.inr ha, fun j hj => ?_⟩
      rw [ofFn_getD, dif_pos hi]
      exact haj j hj
    · refine ⟨0, Or.inl rfl, fun j _ => ?_⟩
      rw [ofFn_getD, dif_neg hi, Nat.zero_testBit]
  have ho : ∀ j < N, (C.gates.foldl stp (List.ofFn (fun i : Fin n => j.testBit i))).getD
      C.output false = F.testBit j := by
    intro j hj
    rw [← hf j hj, ← heval]
    rfl
  have := sound N M F hM hMb hF C.gates K n L0 _ hL0 (fun j => by simp) hI hfan hk C.output ho
  rw [hs] at this
  exact absurd this (by decide)


-- fixing an input that matters, with a non-constant remainder, removes at least one gate
theorem drop (n s : ℕ) (f : (Fin n → Bool) → Bool) (i : Fin n)
    (h : PEqualNP.MetaComplexity.HasCircuitSize n f s)
    (hess : ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update y i false)) :
    1 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x i false)) (s - 1) := by
  obtain ⟨C, h1, h2, h3⟩ := h
  obtain ⟨E, d1, d2, d3⟩ := D.one_drop n C h1 i false (by
    obtain ⟨x, hx⟩ := hess
    refine ⟨Function.update x i false, Function.update x i true, fun j hj => ?_, ?_⟩
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · rw [h3, h3]; exact hx) (by
    rintro ⟨c, hc⟩
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← h3, ← h3, hc, hc])
  exact ⟨by omega, E, d1, by omega, fun x => by rw [d3, h3]⟩

theorem search : can 0xffffffffffffffff 0xfafaa0a0fafaa0a0 3 [0xffffffff00000000, 0xffff0000ffff0000, 0xff00ff00ff00ff00, 0xf0f0f0f0f0f0f0f0, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa] = false := by
  decide +kernel

theorem final : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)) t → 7 ≤ t := by
  intro t h0
  obtain ⟨a1, h1⟩ := drop 6 (t) _ 1 h0
    ⟨fun j => decide (j = 3), by decide⟩
    ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 2), by decide⟩
  obtain ⟨a2, h2⟩ := drop 6 (t - 1) _ 3 h1
    ⟨fun j => decide (j = 0), by decide⟩
    ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 2), by decide⟩
  obtain ⟨a3, h3⟩ := drop 6 (t - 1 - 1) _ 5 h2
    ⟨fun j => decide (j = 0), by decide⟩
    ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 2), by decide⟩
  have hb := main_gen 6 64 0xffffffffffffffff 0xfafaa0a0fafaa0a0 3 [0xffffffff00000000, 0xffff0000ffff0000, 0xff00ff00ff00ff00, 0xf0f0f0f0f0f0f0f0, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa] _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) search (t - 1 - 1 - 1) h3
  omega

end PEqualNP.Outside.L_meta_5499_aux

theorem PEqualNP.Outside.L_meta_5499 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)) t → 7 ≤ t := by
  intro t h
  exact PEqualNP.Outside.L_meta_5499_aux.final t h
