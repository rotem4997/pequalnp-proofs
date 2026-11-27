import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete the later input of the final AND from the shared initial segment and expose its operation.
-- The three children use at most twelve earlier gates and explicit postprocessing.
theorem PEqualNP.Outside.R_meta_2289_2 :
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
       x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
       x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
     let w : List Gate → ℕ → (Fin 9 → Bool) → Bool :=
       fun gs a x => (⟨gs, a⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6])
     ∀ (gs : List Gate) (a j k : ℕ), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 12 →
       10 ≤ a → a < 10 + gs.length → (fun x => w gs a x && (w gs j x && w gs k x)) ≠ f) →
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
       x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
       x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
     let w : List Gate → ℕ → (Fin 9 → Bool) → Bool :=
       fun gs a x => (⟨gs, a⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6])
     ∀ (gs : List Gate) (a j k : ℕ), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 12 →
       10 ≤ a → a < 10 + gs.length → (fun x => w gs a x && (w gs j x || w gs k x)) ≠ f) →
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
       x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
       x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
     let w : List Gate → ℕ → (Fin 9 → Bool) → Bool :=
       fun gs a x => (⟨gs, a⟩ : Circuit).eval (List.ofFn x ++ [x 0 && x 6])
     ∀ (gs : List Gate) (a j : ℕ), FanInTwo ⟨gs, 0⟩ → gs.length ≤ 12 →
       10 ≤ a → a < 10 + gs.length → (fun x => w gs a x && !(w gs j x)) ≠ f) →
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → x1.length ≤ (13 : ℕ) → x2 < x3 → x3 < (10 : ℕ) + x1.length → (fun (x8 : Fin (9 : ℕ) → Bool) => { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))]) && { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ))])) ≠ fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) := by
  intro andCase orCase notCase gs a b fan size order bound eq
  let f : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let input (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 6]
  let step (xs : List Bool) (g : Gate) :=
    xs ++ [g.op.eval (g.inputs.map fun j => xs.getD j false)]
  let W (gs : List Gate) (x : Fin 9 → Bool) := gs.foldl step (input x)
  let w (gs : List Gate) (a : ℕ) (x : Fin 9 → Bool) := (W gs x).getD a false
  have target (x : Fin 9 → Bool) : (w gs a x && w gs b x) = f x := congrFun eq x
  have wlen (hs : List Gate) (xs : List Bool) : (hs.foldl step xs).length = xs.length + hs.length := by
    induction hs generalizing xs with
    | nil => simp
    | cons g hs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have prefixValue (hs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (hs.foldl step xs).getD i false = xs.getD i false := by
    induction hs generalizing xs with
    | nil => rfl
    | cons g hs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have inputLen (x : Fin 9 → Bool) : (input x).length = 10 := by simp [input]
  have positiveRaw : ∀ i : Fin 10, ∃ k : Fin 2,
      let x : Fin 9 → Bool := fun j => (![3, 12] k : ℕ).testBit j.val
      f x = true ∧ (input x).getD i false = false := by
    dsimp only [f, input]
    decide
  have an : 10 ≤ a := by
    by_contra! small
    obtain ⟨k, yes, low⟩ := positiveRaw ⟨a, small⟩
    let x : Fin 9 → Bool := fun j => (![3, 12] k : ℕ).testBit j.val
    have h := (Bool.and_eq_true_iff.mp ((target x).trans yes)).1
    have same := prefixValue gs (input x) a (by rw [inputLen]; omega)
    exact Bool.noConfusion (h.symm.trans (same.trans low))
  have splitGate (hs : List Gate) (i : ℕ) (valid : i < hs.length) :
      ∃ pre g post, hs = pre ++ g :: post ∧ pre.length = i := by
    induction hs generalizing i with
    | nil => simp at valid
    | cons g hs ih =>
      cases i with
      | zero => exact ⟨[], g, hs, rfl, rfl⟩
      | succ i =>
        obtain ⟨pre, h, post, e, hl⟩ := ih i (by simpa using valid)
        exact ⟨g :: pre, h, post, congrArg (g :: ·) e, by simp [hl]⟩
  obtain ⟨pre, g, post, split, plen⟩ := splitGate gs (b - 10) (by omega)
  have bg : 10 + pre.length = b := by omega
  have preLen (x : Fin 9 → Bool) : (W pre x).length = b := by
    change (pre.foldl step (input x)).length = b
    rw [wlen, inputLen, bg]
  have ori (x : Fin 9 → Bool) : W gs x = post.foldl step (step (W pre x) g) := by
    change gs.foldl step (input x) = _
    rw [split, List.foldl_append]
    rfl
  have earlier (x : Fin 9 → Bool) : w gs a x = w pre a x := by
    unfold w
    rw [ori, prefixValue _ _ _ (by simp [step, preLen]; omega)]
    exact List.getD_append _ _ _ _ (by rw [preLen]; exact order)
  have later (x : Fin 9 → Bool) : w gs b x = g.op.eval (g.inputs.map (fun i => w pre i x)) := by
    conv_lhs => unfold w; rw [ori, prefixValue _ _ _ (by simp [step, preLen])]
    unfold step
    rw [← preLen x]
    simp [w]
  have hp : FanInTwo ⟨pre, 0⟩ := by
    intro h hh
    exact fan h (by rw [split]; exact List.mem_append_left _ hh)
  have hfan := fan g (by rw [split]; simp)
  have hsize : pre.length ≤ 12 := by
    rw [split] at size
    simp at size
    omega
  have has : a < 10 + pre.length := by omega
  have combined (x : Fin 9 → Bool) :
      (w pre a x && g.op.eval (g.inputs.map (fun i => w pre i x))) = f x := by
    rw [← earlier, ← later, target]
  have ops : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfan.1
  have hlen := hfan.2
  rcases ops with hop | hop | hop
  · cases hin : g.inputs with
    | nil =>
      apply andCase pre a a a hp hsize an has
      funext x
      change (w pre a x && (w pre a x && w pre a x)) = f x
      have e := combined x
      rw [hop, hin] at e
      change (w pre a x && true) = f x at e
      simpa using e
    | cons j rest =>
      cases rest with
      | nil =>
        apply andCase pre a j j hp hsize an has
        funext x
        change (w pre a x && (w pre j x && w pre j x)) = f x
        have e := combined x
        rw [hop, hin] at e
        change (w pre a x && (w pre j x && true)) = f x at e
        simpa using e
      | cons k rest =>
        have ht : rest = [] := by simpa [hin] using hlen
        apply andCase pre a j k hp hsize an has
        funext x
        change (w pre a x && (w pre j x && w pre k x)) = f x
        have e := combined x
        rw [hop, hin, ht] at e
        change (w pre a x && (w pre j x && (w pre k x && true))) = f x at e
        simpa using e
  · cases hin : g.inputs with
    | nil =>
      have e := combined (fun _ => true)
      rw [hop, hin] at e
      change (w pre a (fun _ => true) && false) = true at e
      simp at e
    | cons j rest =>
      cases rest with
      | nil =>
        apply orCase pre a j j hp hsize an has
        funext x
        change (w pre a x && (w pre j x || w pre j x)) = f x
        have e := combined x
        rw [hop, hin] at e
        change (w pre a x && (w pre j x || false)) = f x at e
        simpa using e
      | cons k rest =>
        have ht : rest = [] := by simpa [hin] using hlen
        apply orCase pre a j k hp hsize an has
        funext x
        change (w pre a x && (w pre j x || w pre k x)) = f x
        have e := combined x
        rw [hop, hin, ht] at e
        change (w pre a x && (w pre j x || (w pre k x || false))) = f x at e
        simpa using e
  · cases hin : g.inputs with
    | nil =>
      apply notCase pre a b hp hsize an has
      funext x
      change (w pre a x && !(w pre b x)) = f x
      have e := combined x
      rw [hop, hin] at e
      change (w pre a x && !false) = f x at e
      have missing : w pre b x = false := by
        unfold w
        exact List.getD_eq_default _ _ (by rw [preLen])
      simpa only [missing] using e
    | cons j rest =>
      apply notCase pre a j hp hsize an has
      funext x
      change (w pre a x && !(w pre j x)) = f x
      have e := combined x
      rw [hop, hin] at e
      exact e
