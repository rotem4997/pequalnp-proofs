import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# Counting small circuits

Helper for `L-meta-002`. A circuit on `n` inputs with at most `s` gates never has a wire
numbered `n + s` or more, so every wire number in it can be cut down to `B = n + s` without
changing what it computes. Such circuits are then listed by a finite type of codes, and there
are fewer codes than Boolean functions on `n` inputs once `n ≥ 5` and `s = 2 ^ n / (4 * n)`.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

/-- Cut every wire number of a gate down to `B`. -/
def capGate (B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => min i B)⟩

theorem getD_min_of_length_le (w : List Bool) (B i : ℕ) (h : w.length ≤ B) :
    w.getD (min i B) false = w.getD i false := by
  by_cases hi : i ≤ B
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

theorem wiresFrom_capGate (B : ℕ) (gs : List Gate) : ∀ w : List Bool,
    w.length + gs.length ≤ B → wiresFrom (gs.map (capGate B)) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have e : (capGate B g).op.eval ((capGate B g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [capGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_min_of_length_le w B i (by omega)
    have step : wiresFrom ((g :: gs).map (capGate B)) w
        = wiresFrom (gs.map (capGate B))
            (w ++ [(capGate B g).op.eval ((capGate B g).inputs.map fun i => w.getD i false)]) :=
      rfl
    have step' : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [step, step', e]
    exact ih _ (by simp; omega)

/-- The code of one gate: an operation out of three and up to two wire numbers at most `B`. -/
abbrev GCode (B : ℕ) : Type := Fin 3 × Option (Fin (B + 1)) × Option (Fin (B + 1))

def decOp (i : Fin 3) : GateOp := if i = 0 then GateOp.and else if i = 1 then GateOp.or else GateOp.not

def decGate (B : ℕ) (c : GCode B) : Gate :=
  ⟨decOp c.1, (c.2.1.toList ++ c.2.2.toList).map Fin.val⟩

theorem exists_gcode (B : ℕ) (g : Gate) (h : Ok g) : ∃ c : GCode B, decGate B c = capGate B g := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  have hop' : ∃ i : Fin 3, decOp i = op := by
    rcases hop with h | h | h
    · exact ⟨0, by simp only [decOp]; exact (h : op = GateOp.and).symm⟩
    · exact ⟨1, by simp only [decOp]; exact (h : op = GateOp.or).symm⟩
    · exact ⟨2, by simp only [decOp]; exact (h : op = GateOp.not).symm⟩
  obtain ⟨i, hi⟩ := hop'
  have lt : ∀ a : ℕ, min a B < B + 1 := fun a => by omega
  match inputs, hlen with
  | [], _ => exact ⟨(i, none, none), by simp [decGate, capGate, hi]⟩
  | [a], _ => exact ⟨(i, some ⟨min a B, lt a⟩, none), by simp [decGate, capGate, hi]⟩
  | [a, b], _ =>
    exact ⟨(i, some ⟨min a B, lt a⟩, some ⟨min b B, lt b⟩), by simp [decGate, capGate, hi]⟩
  | _ :: _ :: _ :: _, h => simp at h

/-- The code of a circuit with exactly `t` gates and wire numbers at most `B`. -/
abbrev Code (B t : ℕ) : Type := (Fin t → GCode B) × Fin (B + 1)

def decode {B t : ℕ} (c : Code B t) : Circuit :=
  ⟨List.ofFn (fun i => decGate B (c.1 i)), c.2⟩

/-- The function on `n` inputs that the circuit with code `c` computes. -/
def sem (n : ℕ) {B t : ℕ} (c : Code B t) : (Fin n → Bool) → Bool :=
  fun x => (decode c).eval (List.ofFn x)

theorem exists_code (n s : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s) :
    ∃ t : Fin (s + 1), ∃ c : Code (n + s) t, sem n c = f := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  choose! enc henc using exists_gcode (n + s)
  refine ⟨⟨C.gates.length, by omega⟩,
    (fun i => enc (C.gates[(i : ℕ)]'i.isLt), ⟨min C.output (n + s), by omega⟩), ?_⟩
  funext x
  have hg : List.ofFn (fun i : Fin C.gates.length => decGate (n + s) (enc (C.gates[(i : ℕ)]'i.isLt)))
      = C.gates.map (capGate (n + s)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      exact henc _ (ok _ (List.getElem_mem _))
  rw [← hev x]
  simp only [sem, decode, Circuit.eval, wires_eq]
  rw [hg, wiresFrom_capGate _ _ _ (by simp; omega)]
  exact getD_min_of_length_le _ _ _ (by rw [length_wiresFrom]; simp; omega)

theorem pow_bound : ∀ n : ℕ, 5 ≤ n → 4 * n + 8 ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- For `n ≥ 5` some function on `n` inputs has no circuit with at most `2 ^ n / (4 * n)` gates. -/
theorem counting (n : ℕ) (hn : 5 ≤ n) :
    ∃ f : (Fin n → Bool) → Bool, ¬ HasCircuitSize n f (2 ^ n / (4 * n)) := by
  by_contra hall
  push Not at hall
  set s := 2 ^ n / (4 * n) with hs
  set B := n + s with hB
  let φ : (Σ t : Fin (s + 1), Code B t) → ((Fin n → Bool) → Bool) := fun p => sem n p.2
  have hsurj : Function.Surjective φ := by
    intro f
    obtain ⟨t, c, hc⟩ := exists_code n s f (hall f)
    exact ⟨⟨t, c⟩, hc⟩
  have hcard := Fintype.card_le_of_surjective φ hsurj
  have hN := pow_bound n hn
  have h4 : 4 * n * s ≤ 2 ^ n := Nat.mul_div_le _ _
  have hterm : ∀ t : Fin (s + 1), Fintype.card (Code B t) ≤ (2 ^ (2 * n)) ^ s * (B + 1) := by
    intro t
    have e : Fintype.card (Code B t) = (3 * ((B + 2) * (B + 2))) ^ (t : ℕ) * (B + 1) := by
      simp [Code, GCode]
    rw [e]
    have hb : 2 * (B + 2) ≤ 2 ^ n := by nlinarith
    have hg : 3 * ((B + 2) * (B + 2)) ≤ 2 ^ (2 * n) := by
      rw [pow_mul', sq]; nlinarith
    have h1 : 1 ≤ 3 * ((B + 2) * (B + 2)) := by nlinarith
    calc (3 * ((B + 2) * (B + 2))) ^ (t : ℕ) * (B + 1)
        ≤ (3 * ((B + 2) * (B + 2))) ^ s * (B + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h1 (by omega))
      _ ≤ (2 ^ (2 * n)) ^ s * (B + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hg s)
  have hsum : Fintype.card (Σ t : Fin (s + 1), Code B t)
      ≤ (s + 1) * ((2 ^ (2 * n)) ^ s * (B + 1)) := by
    rw [Fintype.card_sigma]
    calc (Finset.univ.sum fun t : Fin (s + 1) => Fintype.card (Code B t))
        ≤ Finset.univ.sum fun _ : Fin (s + 1) => (2 ^ (2 * n)) ^ s * (B + 1) :=
          Finset.sum_le_sum (fun t _ => hterm t)
      _ = (s + 1) * ((2 ^ (2 * n)) ^ s * (B + 1)) := by simp
  have hfun : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by simp
  have hb : 2 * (B + 2) ≤ 2 ^ n := by nlinarith
  have hsB : (s + 1) * (B + 1) ≤ (B + 2) * (B + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsb : (s + 1) * (B + 1) ≤ 2 ^ (2 * n) := by
    rw [pow_mul', sq]; nlinarith [Nat.mul_le_mul hb hb]
  have hle : 2 ^ 2 ^ n ≤ 2 ^ (2 * n * s + 2 * n) := by
    calc 2 ^ 2 ^ n ≤ (s + 1) * ((2 ^ (2 * n)) ^ s * (B + 1)) := by
          rw [← hfun]; exact hcard.trans hsum
      _ = (2 ^ (2 * n)) ^ s * ((s + 1) * (B + 1)) := by ring
      _ ≤ (2 ^ (2 * n)) ^ s * 2 ^ (2 * n) := Nat.mul_le_mul_left _ hsb
      _ = 2 ^ (2 * n * s + 2 * n) := by rw [← pow_mul, ← pow_add]
  have hlt : 2 * n * s + 2 * n < 2 ^ n := by nlinarith [h4, hN]
  exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) hlt))

end PEqualNP.MetaComplexity.Helpers
