import Mathlib
import PEqualNP.Defs

/-!
Helpers for L-clb-005 (Shannon's counting argument). A fan-in two circuit with at most `s`
gates behaves, on inputs of length `n`, like one of finitely many descriptors, so if there are
fewer descriptors than Boolean functions on `n` bits, some function has no such circuit.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-- The gate condition of `SIZE`: AND, OR, NOT gates of fan-in at most two. -/
def Basic (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-- One evaluation step. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

/-- Replace every wire index by its minimum with `m`. -/
def clamp (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (min · m)⟩

theorem getD_min (w : List Bool) (m i : ℕ) (hw : w.length ≤ m) :
    w.getD (min i m) false = w.getD i false := by
  by_cases h : i ≤ m
  · rw [min_eq_left h]
  · have h' : m < i := not_le.mp h
    rw [min_eq_right (le_of_lt h'), List.getD_eq_default _ _ hw,
      List.getD_eq_default _ _ (le_trans hw (le_of_lt h'))]

theorem step_clamp (w : List Bool) (m : ℕ) (g : Gate) (hw : w.length ≤ m) :
    step w (clamp m g) = step w g := by
  have h : (fun i => w.getD (min i m) false) = fun i => w.getD i false :=
    funext fun i => getD_min w m i hw
  simp only [step, clamp, List.map_map, Function.comp_def, h]

theorem foldl_step_clamp (m : ℕ) (gs : List Gate) (x : List Bool)
    (h : x.length + gs.length ≤ m) :
    (gs.map (clamp m)).foldl step x = gs.foldl step x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    simp only [List.length_cons] at h
    rw [step_clamp x m g (by omega)]
    apply ih
    simp [step]; omega

/-- The gate that is constantly `false`. -/
def falseGate : Gate := ⟨GateOp.or, []⟩

theorem foldl_step_replicate (k : ℕ) (w : List Bool) :
    (List.replicate k falseGate).foldl step w = w ++ List.replicate k false := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    simp [step, falseGate, GateOp.eval, List.replicate_succ]

theorem getD_append_replicate_false (w : List Bool) (k o : ℕ) :
    (w ++ List.replicate k false).getD o false = w.getD o false := by
  by_cases h : o < w.length
  · rw [List.getD_append _ _ _ _ h]
  · have h' : w.length ≤ o := not_lt.mp h
    rw [List.getD_append_right _ _ _ _ h', List.getD_eq_default _ _ h']
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl

/-- The normal form of `C` for inputs of length `n` and size bound `s`: indices clamped to
`n + s`, padded with constant gates to exactly `s` gates. -/
def normalize (n s : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (clamp (n + s)) ++ List.replicate (s - C.gates.length) falseGate,
    min C.output (n + s)⟩

theorem normalize_eval (n s : ℕ) (C : Circuit) (hs : C.size ≤ s) (x : List Bool)
    (hx : x.length = n) : (normalize n s C).eval x = C.eval x := by
  have hs' : C.gates.length ≤ s := hs
  have hlen : (C.gates.foldl step x).length ≤ n + s := by
    rw [foldl_step_length]; omega
  rw [Circuit.eval, Circuit.eval, wires_eq, wires_eq]
  simp only [normalize, List.foldl_append]
  rw [foldl_step_clamp (n + s) C.gates x (by omega), foldl_step_replicate]
  rw [getD_min _ _ _ (by simp [foldl_step_length]; omega)]
  rw [getD_append_replicate_false]

/-- A gate descriptor: one of three operations and up to two wire indices below `m`. -/
abbrev GD (m : ℕ) : Type := Fin 3 × Option (Fin m) × Option (Fin m)

/-- The gate a descriptor stands for. -/
def decodeGate {m : ℕ} (d : GD m) : Gate :=
  ⟨match d.1 with
    | 0 => GateOp.and
    | 1 => GateOp.or
    | 2 => GateOp.not,
   (d.2.1.toList ++ d.2.2.toList).map Fin.val⟩

/-- A circuit descriptor for `n` inputs and exactly `s` gates. -/
abbrev CD (n s : ℕ) : Type := List.Vector (GD (n + s + 1)) s × Fin (n + s + 1)

/-- The circuit a descriptor stands for. -/
def decode {n s : ℕ} (d : CD n s) : Circuit := ⟨d.1.toList.map decodeGate, d.2.val⟩

theorem exists_decodeGate {m : ℕ} (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < m) :
    ∃ d : GD m, decodeGate d = g := by
  obtain ⟨op, inputs⟩ := g
  have hk : ∃ k : Fin 3, (match k with
      | 0 => GateOp.and
      | 1 => GateOp.or
      | 2 => GateOp.not) = op := by
    rcases hop with h | h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩
  obtain ⟨k, hk⟩ := hk
  match inputs, hlen, hin with
  | [], _, _ => exact ⟨(k, none, none), by simp [decodeGate, hk]⟩
  | [a], _, hin =>
    exact ⟨(k, some ⟨a, hin a (by simp)⟩, none), by simp [decodeGate, hk]⟩
  | [a, b], _, hin =>
    exact ⟨(k, some ⟨a, hin a (by simp)⟩, some ⟨b, hin b (by simp)⟩), by simp [decodeGate, hk]⟩
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

theorem exists_map_decodeGate {m : ℕ} (gs : List Gate)
    (h : ∀ g ∈ gs, ∃ d : GD m, decodeGate d = g) :
    ∃ ds : List (GD m), ds.map decodeGate = gs := by
  induction gs with
  | nil => exact ⟨[], rfl⟩
  | cons g gs ih =>
    obtain ⟨d, hd⟩ := h g (by simp)
    obtain ⟨ds, hds⟩ := ih fun g' hg' => h g' (by simp [hg'])
    exact ⟨d :: ds, by simp [hd, hds]⟩

/-- Every basic circuit with at most `s` gates agrees, on inputs of length `n`, with the
circuit of some descriptor. -/
theorem exists_decode (n s : ℕ) (C : Circuit) (hC : Basic C) (hs : C.size ≤ s) :
    ∃ d : CD n s, ∀ x : List Bool, x.length = n → (decode d).eval x = C.eval x := by
  have hs' : C.gates.length ≤ s := hs
  have hg : ∀ g ∈ (normalize n s C).gates, ∃ d : GD (n + s + 1), decodeGate d = g := by
    intro g hg
    simp only [normalize, List.mem_append, List.mem_map, List.mem_replicate] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | ⟨_, rfl⟩
    · refine exists_decodeGate _ (hC g0 hg0).1 (by simpa [clamp] using (hC g0 hg0).2) ?_
      intro i hi
      simp only [clamp, List.mem_map] at hi
      obtain ⟨j, _, rfl⟩ := hi
      exact Nat.lt_succ_of_le (min_le_right _ _)
    · exact exists_decodeGate _ (Or.inr (Or.inl rfl)) (by simp [falseGate])
        (by simp [falseGate])
  obtain ⟨ds, hds⟩ := exists_map_decodeGate _ hg
  have hlen : ds.length = s := by
    have := congrArg List.length hds
    simp [normalize] at this
    omega
  refine ⟨(⟨ds, hlen⟩, ⟨min C.output (n + s), Nat.lt_succ_of_le (min_le_right _ _)⟩), ?_⟩
  intro x hx
  have : decode (n := n) (s := s)
      (⟨ds, hlen⟩, ⟨min C.output (n + s), Nat.lt_succ_of_le (min_le_right _ _)⟩) =
      normalize n s C := by
    simp [decode, List.Vector.toList, hds, normalize]
  rw [this, normalize_eval n s C hs x hx]

/-- The number of descriptors. -/
def count (n s : ℕ) : ℕ := (3 * ((n + s + 2) * (n + s + 2))) ^ s * (n + s + 1)

theorem card_CD (n s : ℕ) : Fintype.card (CD n s) = count n s := by
  simp [count, Fintype.card_prod, card_vector, Fintype.card_option]

/-- Shannon's counting argument: with fewer descriptors than functions, some function on `n`
bits is computed by no basic circuit with at most `s` gates. -/
theorem exists_hard (n s : ℕ) (h : count n s < 2 ^ 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : Circuit, Basic C → C.size ≤ s →
      ∃ v : Fin n → Bool, C.eval (List.ofFn v) ≠ f v := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective
      (fun (d : CD n s) (v : Fin n → Bool) => (decode d).eval (List.ofFn v)) := by
    intro f
    obtain ⟨C, hC, hs, hf⟩ := hcon f
    obtain ⟨d, hd⟩ := exists_decode n s C hC hs
    exact ⟨d, funext fun v => (hd _ List.length_ofFn).trans (hf v)⟩
  have hcard := Fintype.card_le_of_surjective _ hsurj
  rw [card_CD] at hcard
  simp at hcard
  omega

end PEqualNP.CircuitLowerBounds.Helpers
