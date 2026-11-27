import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17111

namespace MatrixBase
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def entry (i : Fin 4) (x : Fin 4 → Bool) : Bool :=
  x (Fin.ofNat 4 (i.val / 2)) && x (Fin.ofNat 4 (2 + i.val % 2))

def probe (i : Fin 4) (j : Fin 4) := decide (j.val = i.val / 2 ∨ j.val = 2 + i.val % 2)

theorem hit : ∀ i k : Fin 4, entry i (probe k) = decide (i=k) := by decide
theorem singleton : ∀ i k : Fin 4, entry i (fun j => decide (j=k)) = false := by decide

theorem raw (C : Circuit) (x : Fin 4 → Bool) (k : Fin 4) :
    (C.wires (List.ofFn x)).getD k.val false = x k := by
  have aux (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp; omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  change (C.gates.foldl _ (List.ofFn x)).getD k.val false = x k
  rw [aux _ _ _ (by simpa using k.isLt)]
  fin_cases k <;> rfl

theorem length (C : Circuit) (x : Fin 4 → Bool) : (C.wires (List.ofFn x)).length = 4+C.size := by
  have aux (gs : List Gate) (xs : List Bool) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih];simp;omega
  change (C.gates.foldl _ (List.ofFn x)).length = 4 + C.gates.length
  rw [aux,List.length_ofFn]

theorem one (C : Circuit) (o : Fin 4 → ℕ)
    (sem : ∀ i x, (C.wires (List.ofFn x)).getD (o i) false = entry i x) : 4 ≤ C.size := by
  have inj : Function.Injective o := by
    intro i k same
    have e : entry i (probe i) = entry k (probe i) := by rw [←sem,←sem,same]
    rw [hit,hit] at e
    simpa [eq_comm] using e
  have bound (i : Fin 4) : o i ∈ Finset.Ico 4 (4+C.size) := by
    apply Finset.mem_Ico.mpr
    constructor
    · by_contra! h
      let k : Fin 4 := ⟨o i,h⟩
      let x := fun j : Fin 4 => decide (j=k)
      have bad := sem i x
      rw [show o i = k.val from rfl,raw] at bad
      rw [show entry i x = false from singleton i k] at bad
      simp [x] at bad
    · by_contra! h
      have bad := sem i (probe i)
      rw [List.getD_eq_default _ _ (by rw [length];exact h), hit] at bad
      simp at bad
  have size := Finset.card_le_card (s:=Finset.univ.image o) (t:=Finset.Ico 4 (4+C.size))
    (by intro j hj; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj; exact bound i)
  rw [Finset.card_image_of_injective _ inj] at size
  simpa using size

end MatrixBase

namespace MatrixBase

theorem exactBase : let n : ℕ := 1; ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 * n - 5 ∧ ∀ x : Fin (4 * n) → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (List.range n).any (fun i => (List.ofFn x).getD i false && (List.ofFn x).getD (2 * n + 2 * i) false) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (List.range n).any (fun i => (List.ofFn x).getD i false && (List.ofFn x).getD (2 * n + 2 * i + 1) false) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (List.range n).any (fun i => (List.ofFn x).getD (n + i) false && (List.ofFn x).getD (2 * n + 2 * i) false) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (List.range n).any (fun i => (List.ofFn x).getD (n + i) false && (List.ofFn x).getD (2 * n + 2 * i + 1) false) := by
  dsimp only
  rintro ⟨C,o,_,size,sem⟩
  have h := one C o (by
    intro i x
    obtain ⟨a,b,c,d⟩ := sem x
    fin_cases i
    · change _ = (x 0 && x 2)
      simpa [List.range_succ,List.getD_eq_getElem?_getD,List.ofFn_succ] using a
    · change _ = (x 0 && x 3)
      simpa [List.range_succ,List.getD_eq_getElem?_getD,List.ofFn_succ] using b
    · change _ = (x 1 && x 2)
      simpa [List.range_succ,List.getD_eq_getElem?_getD,List.ofFn_succ] using c
    · change _ = (x 1 && x 3)
      simpa [List.range_succ,List.getD_eq_getElem?_getD,List.ofFn_succ] using d)
  omega

end MatrixBase

namespace MatrixTwo

def mm (x : Fin 8 → Bool) : Fin 4 → Bool :=
  ![(x 0 && x 4 || x 1 && x 6),
    (x 0 && x 5 || x 1 && x 7),
    (x 2 && x 4 || x 3 && x 6),
    (x 2 && x 5 || x 3 && x 7)]

theorem mm_zero (x : Fin 8 → Bool) : mm x 0 = (x 0 && x 4 || x 1 && x 6) := rfl
theorem mm_one (x : Fin 8 → Bool) : mm x 1 = (x 0 && x 5 || x 1 && x 7) := rfl
theorem mm_two (x : Fin 8 → Bool) : mm x 2 = (x 2 && x 4 || x 3 && x 6) := rfl
theorem mm_three (x : Fin 8 → Bool) : mm x 3 = (x 2 && x 5 || x 3 && x 7) := rfl

def mmRow (row : ℕ) (i : Fin 8) : Bool := row.testBit i.val

def affectOut₀ : Fin 8 → Fin 4 := ![0, 0, 2, 2, 0, 1, 0, 1]
def affectOut₁ : Fin 8 → Fin 4 := ![1, 1, 3, 3, 2, 3, 2, 3]
def affectRow₀ : Fin 8 → ℕ := ![16, 64, 16, 64, 1, 1, 2, 2]
def affectRow₁ : Fin 8 → ℕ := ![32, 128, 32, 128, 4, 4, 8, 8]

theorem affectSamples : ∀ i : Fin 8, affectOut₀ i ≠ affectOut₁ i ∧
    mm (Function.update (mmRow (affectRow₀ i)) i false) (affectOut₀ i) ≠
      mm (Function.update (mmRow (affectRow₀ i)) i true) (affectOut₀ i) ∧
    mm (Function.update (mmRow (affectRow₁ i)) i false) (affectOut₁ i) ≠
      mm (Function.update (mmRow (affectRow₁ i)) i true) (affectOut₁ i) := by
  decide +kernel

theorem affectsTwo : ∀ i : Fin 8, ∃ j k : Fin 4, j ≠ k ∧
    (∃ x, mm (Function.update x i false) j ≠ mm (Function.update x i true) j) ∧
    (∃ x, mm (Function.update x i false) k ≠ mm (Function.update x i true) k) := by
  intro i
  obtain ⟨different, first, second⟩ := affectSamples i
  exact ⟨affectOut₀ i, affectOut₁ i, different,
    ⟨mmRow (affectRow₀ i), first⟩, ⟨mmRow (affectRow₁ i), second⟩⟩

def pairInput (i j : Fin 8) (row : Fin 8 → Bool) (bits : Fin 4) : Fin 8 → Bool :=
  Function.update (Function.update row i (bits.val.testBit 0)) j (bits.val.testBit 1)

theorem pairInput_other (i j k : Fin 8) (row : Fin 8 → Bool) (bits : Fin 4)
    (hi : k ≠ i) (hj : k ≠ j) :
    pairInput i j row bits k = row k := by
  rw [pairInput, Function.update_of_ne hj, Function.update_of_ne hi]

def pairRows : Fin 8 → Fin 8 → ℕ := ![
  ![0, 96, 16, 80, 36, 20, 24, 18],
  ![96, 0, 80, 64, 68, 65, 136, 72],
  ![16, 80, 0, 96, 33, 17, 18, 18],
  ![80, 64, 96, 0, 65, 65, 130, 66],
  ![36, 68, 33, 65, 0, 1, 6, 3],
  ![20, 65, 17, 65, 1, 0, 3, 6],
  ![24, 136, 18, 130, 6, 3, 0, 2],
  ![18, 72, 18, 66, 3, 6, 2, 0]]

def packOutput (v : Fin 4 → Bool) : ℕ :=
  (if v 0 then 1 else 0) + (if v 1 then 2 else 0) +
  (if v 2 then 4 else 0) + (if v 3 then 8 else 0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pairSamples : ∀ i j : Fin 8, i ≠ j → ∀ a b : Fin 4,
    packOutput (mm (pairInput i j (mmRow (pairRows i j)) a)) =
      packOutput (mm (pairInput i j (mmRow (pairRows i j)) b)) → a = b := by
  decide +kernel

theorem pairSeparates : ∀ i j : Fin 8, i ≠ j →
    ∃ row : Fin 8 → Bool, Function.Injective (fun bits : Fin 4 => mm (pairInput i j row bits)) := by
  intro i j different
  refine ⟨mmRow (pairRows i j), ?_⟩
  intro a b equal
  exact pairSamples i j different a b (congrArg packOutput equal)

end MatrixTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

namespace MatrixNetwork

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

variable {d : ℕ}

abbrev Slot (d : Nat) (C : Circuit) := Fin (d + C.gates.length + 4)

def inp (C : Circuit) (i : Fin d) : Slot d C :=
  ⟨i.val, by have := i.isLt; omega⟩

def out (C : Circuit) (i : Fin 4) : Slot d C :=
  ⟨d + C.gates.length + i.val, by have := i.isLt; omega⟩

theorem inp_inj (C : Circuit) : Function.Injective (inp (d:=d) C) :=
  fun _ _ h => Fin.ext (congrArg (fun v : Slot d C => v.val) h)

theorem out_inj (C : Circuit) : Function.Injective (out (d:=d) C) := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  change d + C.gates.length + i.val = d + C.gates.length + j.val at h'
  omega

def reads (C : Circuit) (o : Fin 4 → Nat) (b : Slot d C) : List Nat :=
  if h₀ : b.val < d then [] else
  if h : b.val < d + C.gates.length then
    (C.gates[b.val - d]'(by omega)).inputs
  else [o ⟨b.val - (d + C.gates.length), by have := b.isLt; omega⟩]

def raw (C : Circuit) (o : Fin 4 → Nat) (a b : Slot d C) : Prop :=
  a.val < b.val ∧ a.val < d + C.gates.length ∧ a.val ∈ reads (d:=d) C o b

def alive (C : Circuit) (o : Fin 4 → Nat) (a : Slot d C) : Prop :=
  ∃ j : Fin 4, Relation.ReflTransGen (raw (d:=d) C o) a (out (d:=d) C j)

def liveRead (C : Circuit) (o : Fin 4 → Nat) (a b : Slot d C) : Prop :=
  raw (d:=d) C o a b ∧ alive (d:=d) C o b

lemma live_read_source {C : Circuit} {o : Fin 4 → Nat} {a b : Slot d C}
    (h : liveRead (d:=d) C o a b) : alive (d:=d) C o a := by
  obtain ⟨j, path⟩ := h.2
  exact ⟨j, path.head h.1⟩

lemma out_always_alive (C : Circuit) (o : Fin 4 → Nat) (j : Fin 4) :
    alive (d:=d) C o (out (d:=d) C j) := ⟨j, .refl⟩

lemma live_read_step {C : Circuit} {o : Fin 4 → Nat} {a : Slot d C}
    (ha : alive (d:=d) C o a) (hn : a.val < d + C.gates.length) :
    ∃ b, liveRead (d:=d) C o a b := by
  obtain ⟨j, path⟩ := ha
  have ne : a ≠ out (d:=d) C j := by
    intro h; subst a
    change d + C.gates.length + j.val < d + C.gates.length at hn
    omega
  rcases Relation.ReflTransGen.cases_head path with h | ⟨b, edge, rest⟩
  · exact (ne h).elim
  · exact ⟨b, edge, j, rest⟩

lemma from_out_impossible {C : Circuit} {o : Fin 4 → Nat}
    (j : Fin 4) (b : Slot d C) : ¬ liveRead (d:=d) C o (out (d:=d) C j) b := by
  intro h
  have bad := h.1.2.1
  change d + C.gates.length + j.val < d + C.gates.length at bad
  omega

def value (C : Circuit) (o : Fin 4 → Nat) (x : Fin d → Bool) (a : Slot d C) : Bool :=
  if a.val < d + C.gates.length then (C.wires (List.ofFn x)).getD a.val false
  else (C.wires (List.ofFn x)).getD
    (o ⟨a.val - (d + C.gates.length), by have := a.isLt; omega⟩) false

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem inp_value (C : Circuit) (o : Fin 4 → Nat) (x : Fin d → Bool) (i : Fin d) :
    value (d:=d) C o x (inp (d:=d) C i) = x i := by
  have hi : i.val < d + C.gates.length := by have := i.isLt; omega
  unfold value
  split
  · change (wiresFrom C.gates (List.ofFn x)).getD i.val false = x i
    rw [getD_wiresFrom _ _ _ (by simpa using i.isLt)]
    exact getD_ofFn d x false i
  · rename_i bad
    exact (bad hi).elim

theorem out_value (C : Circuit) (o : Fin 4 → Nat) (x : Fin d → Bool) (j : Fin 4) :
    value (d:=d) C o x (out (d:=d) C j) = (C.wires (List.ofFn x)).getD (o j) false := by
  have hn : ¬ d + C.gates.length + j.val < d + C.gates.length := by omega
  unfold value
  split
  · rename_i bad
    exact (hn bad).elim
  · apply congrArg (fun idx : Fin 4 => (C.wires (List.ofFn x)).getD (o idx) false)
    apply Fin.ext
    simp [out]

theorem gate_value (C : Circuit) (x : Fin d → Bool) (p : Nat) (g : Gate)
    (hp : C.gates[p]? = some g) :
    (C.wires (List.ofFn x)).getD (d + p) false =
      g.op.eval (g.inputs.map fun a =>
        if a < d + p then (C.wires (List.ofFn x)).getD a false else false) := by
  obtain ⟨pre, post, hgs, plen⟩ := split_at C.gates p g hp
  let w := wiresFrom pre (List.ofFn x)
  have wl : w.length = d + p := by simp [w, length_wiresFrom, plen]
  simp only [Circuit.wires, hgs, List.foldl_append, List.foldl_cons]
  change (wiresFrom post (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])).getD
        (d + p) false = _
  rw [getD_wiresFrom _ _ _ (by simp [wl])]
  have headValue : (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]).getD (d + p) false =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by rw [← wl]; simp
  rw [headValue]
  congr 1
  apply List.map_congr_left
  intro a ha
  by_cases h : a < d + p
  · rw [if_pos (by simpa [wl] using h)]
    change w.getD a false = (wiresFrom post
           (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD a false
    rw [getD_wiresFrom post (w ++ [_]) a (by simp [wl]; omega)]
    rw [List.getD_append _ _ _ _ (by simpa [wl] using h)]
  · rw [if_neg (by simpa [wl] using h), List.getD_eq_default _ _ (by omega)]

theorem raw_difference {C : Circuit} {o : Fin 4 → Nat} (x y : Fin d → Bool) (b : Slot d C)
    (nonInput : ∀ i, b ≠ inp (d:=d) C i) (diff : value (d:=d) C o x b ≠ value (d:=d) C o y b) :
    ∃ a, raw (d:=d) C o a b ∧ value (d:=d) C o x a ≠ value (d:=d) C o y a := by
  classical
  have hb : ¬ b.val < d := by
    intro lt
    exact nonInput ⟨b.val, lt⟩ (Fin.ext rfl)
  by_cases hgate : b.val < d + C.gates.length
  · let p := b.val - d
    have hpos : b.val = d + p := by dsimp [p]; omega
    have hp : p < C.gates.length := by omega
    let g := C.gates[p]
    have hget : C.gates[p]? = some g := List.getElem?_eq_getElem hp
    have ds : ∃ a ∈ g.inputs, a < b.val ∧
        (C.wires (List.ofFn x)).getD a false ≠ (C.wires (List.ofFn y)).getD a false := by
      by_contra none
      apply diff
      have bnd : d + p < d + C.gates.length := by omega
      simp only [value, hpos, if_pos bnd, gate_value (d:=d) C x p g hget, gate_value (d:=d) C y p g hget]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro a am
      by_cases hl : a < b.val
      · rw [if_pos (by omega), if_pos (by omega)]
        by_contra hne
        exact none ⟨a, am, hl, hne⟩
      · rw [if_neg (by omega), if_neg (by omega)]
    obtain ⟨a, am, al, delta⟩ := ds
    let w : Slot d C := ⟨a, by omega⟩
    have wlt : w.val < d + C.gates.length := by change a < _; omega
    refine ⟨w, ⟨al, wlt, ?_⟩, ?_⟩
    · simpa only [reads, dif_neg hb, dif_pos hgate] using am
    · simpa only [value, if_pos wlt] using delta
  · let j : Fin 4 := ⟨b.val - (d + C.gates.length), by have := b.isLt; omega⟩
    have oj : o j < d + C.gates.length := by
      by_contra! beyond
      apply diff
      simp only [value, if_neg hgate]
      change (wiresFrom C.gates (List.ofFn x)).getD (o j) false =
         (wiresFrom C.gates (List.ofFn y)).getD (o j) false
      rw [List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega),
          List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)]
    let w : Slot d C := ⟨o j, by omega⟩
    refine ⟨w, ⟨by dsimp [w]; omega, oj, ?_⟩, ?_⟩
    · simp [reads, hb, hgate, w, j]
    · have wlt : w.val < d + C.gates.length := oj
      simpa only [value, if_pos wlt, if_neg hgate] using diff

theorem raw_before {C : Circuit} {o : Fin 4 → Nat} {a b : Slot d C}
    (h : raw (d:=d) C o a b) : a.val < b.val := h.1

theorem live_before {C : Circuit} {o : Fin 4 → Nat} {a b : Slot d C}
    (h : liveRead (d:=d) C o a b) : a.val < b.val := h.1.1

theorem raw_to_live_path {C : Circuit} {o : Fin 4 → Nat} {a b : Slot d C}
    (path : Relation.ReflTransGen (raw (d:=d) C o) a b) (hj : alive (d:=d) C o b) :
    Relation.ReflTransGen (liveRead (d:=d) C o) a b := by
  induction path with
  | refl => exact .refl
  | @tail b c p e ih =>
    have aliveB := live_read_source (show liveRead (d:=d) C o b c from ⟨e, hj⟩)
    exact (ih aliveB).tail ⟨e, hj⟩

noncomputable def succ (C : Circuit) (o : Fin 4 → Nat) (u : Slot d C) : Finset (Slot d C) := by
  classical
  exact Finset.univ.filter (fun v => liveRead (d:=d) C o u v)

noncomputable def pred (C : Circuit) (o : Fin 4 → Nat) (v : Slot d C) : Finset (Slot d C) := by
  classical
  exact Finset.univ.filter (fun u => liveRead (d:=d) C o u v)

noncomputable def liveGates (C : Circuit) (o : Fin 4 → Nat) : Finset (Slot d C) := by
  classical
  exact Finset.univ.filter (fun u => d ≤ u.val ∧ u.val < d + C.gates.length ∧ alive (d:=d) C o u)

theorem mem_succ {C : Circuit} {o : Fin 4 → Nat} {u v : Slot d C} :
    v ∈ succ (d:=d) C o u ↔ liveRead (d:=d) C o u v := by
  classical
  simp [succ]

theorem mem_pred {C : Circuit} {o : Fin 4 → Nat} {u v : Slot d C} :
    u ∈ pred (d:=d) C o v ↔ liveRead (d:=d) C o u v := by
  classical
  simp [pred]

theorem mem_liveGates {C : Circuit} {o : Fin 4 → Nat} {u : Slot d C} :
    u ∈ liveGates (d:=d) C o ↔ d ≤ u.val ∧ u.val < d + C.gates.length ∧ alive (d:=d) C o u := by
  classical
  simp [liveGates]

def inputs (C : Circuit) : Finset (Slot d C) :=
  Finset.univ.map ⟨inp (d:=d) C, inp_inj (d:=d) C⟩

def sinks (C : Circuit) : Finset (Slot d C) :=
  Finset.univ.map ⟨out (d:=d) C, out_inj (d:=d) C⟩

theorem read_card (C : Circuit) (o : Fin 4 → Nat) (v : Slot d C) :
    (pred (d:=d) C o v).card ≤ (reads (d:=d) C o v).length := by
  classical
  have sub : (pred (d:=d) C o v).image Fin.val ⊆ (reads (d:=d) C o v).toFinset := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    have edge := mem_pred.mp hu
    exact List.mem_toFinset.mpr edge.1.2.2
  have le := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at le
  exact le.trans (List.toFinset_card_le _)

theorem degree_balance (C : Circuit) (o : Fin 4 → Nat) :
    (∑ u : Slot d C, (succ (d:=d) C o u).card) = ∑ v : Slot d C, (pred (d:=d) C o v).card := by
  classical
  simp only [succ, pred, Finset.card_filter]
  exact Finset.sum_comm

theorem indicator_sum {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (n : Nat) :
    (∑ a, (if a ∈ s then n else 0)) = n * s.card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem live_gate_le (C : Circuit) (o : Fin 4 → Nat) : (liveGates (d:=d) C o).card ≤ C.gates.length := by
  classical
  let den : Slot d C → Nat := fun u => u.val - d
  have inj : Set.InjOn den (liveGates (d:=d) C o) := by
    intro a ha b hb eq
    have h1 := (mem_liveGates.mp ha).1
    have h2 := (mem_liveGates.mp hb).1
    apply Fin.ext
    dsimp [den] at eq
    omega
  have incl : (liveGates (d:=d) C o).image den ⊆ Finset.range C.gates.length := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨lo, bound, _⟩ := mem_liveGates.mp hu
    apply Finset.mem_range.mpr
    dsimp [den]
    omega
  have bc := Finset.card_le_card incl
  rwa [Finset.card_image_of_injOn inj, Finset.card_range] at bc

theorem atMostIn (C : Circuit) (o : Fin 4 → Nat) (fit : FanInTwo C) (v : Slot d C) :
    (pred (d:=d) C o v).card ≤ (if v ∈ liveGates (d:=d) C o then 2 else 0) +
      (if v ∈ sinks (d:=d) C then 1 else 0) := by
  classical
  by_cases aliveV : alive (d:=d) C o v
  · by_cases hv0 : v.val < d
    · have zero : (pred (d:=d) C o v).card ≤ 0 := by
        simpa [reads, hv0] using read_card (d:=d) C o v
      exact zero.trans (Nat.zero_le _)
    · by_cases hv1 : v.val < d + C.gates.length
      · have m : v ∈ liveGates (d:=d) C o := mem_liveGates.mpr ⟨by omega, hv1, aliveV⟩
        have idx : v.val - d < C.gates.length := by omega
        have ih : (pred (d:=d) C o v).card ≤ (C.gates[v.val - d]'idx).inputs.length := by
          simpa [reads, hv0, hv1] using read_card (d:=d) C o v
        have legal := (fit _ (List.getElem_mem idx)).2
        rw [ite_eq_left m]
        omega
      · let j : Fin 4 := ⟨v.val - (d + C.gates.length), by have := v.isLt; omega⟩
        have hs : out (d:=d) C j = v := by
          apply Fin.ext
          change d + C.gates.length + (v.val - (d + C.gates.length)) = v.val
          omega
        have sv : v ∈ sinks (d:=d) C := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hs⟩
        have ih : (pred (d:=d) C o v).card ≤ 1 := by
          simpa [reads, hv0, hv1] using read_card (d:=d) C o v
        rw [ite_eq_left sv]
        omega
  · have empty : pred (d:=d) C o v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact aliveV (mem_pred.mp hu).2
    simp [empty]

theorem enoughSlots (C : Circuit) (o : Fin 4 → Nat) (fit : FanInTwo C)
    (ha : ∀ i, alive (d:=d) C o (inp (d:=d) C i))
    (label : Fin d → Slot d C) (inj : Function.Injective label)
    (fork : ∀ i, ∃ a b, a ≠ b ∧ liveRead (d:=d) C o (label i) a ∧ liveRead (d:=d) C o (label i) b) :
    2 * d ≤ C.gates.length + 4 := by
  classical
  let forks : Finset (Slot d C) := Finset.univ.map ⟨label, inj⟩
  have pointwise (v : Slot d C) : (if v ∈ inputs (d:=d) C then 1 else 0) +
      (if v ∈ liveGates (d:=d) C o then 1 else 0) + (if v ∈ forks then 1 else 0)
        ≤ (succ (d:=d) C o v).card := by
    have lowerFork : v ∈ forks → 2 ≤ (succ (d:=d) C o v).card := by
      intro hv
      obtain ⟨i, _, h⟩ := Finset.mem_map.mp hv
      change label i = v at h
      obtain ⟨a, b, ne, ra, rb⟩ := fork i
      have inc : ({a,b} : Finset (Slot d C)) ⊆ succ (d:=d) C o v := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_succ.mpr (h ▸ ra)
        · exact mem_succ.mpr (h ▸ rb)
      simpa [ne] using Finset.card_le_card inc
    have lowerLive (h : alive (d:=d) C o v) (hn : v.val < d + C.gates.length) : 1 ≤ (succ (d:=d) C o v).card := by
      obtain ⟨b, e⟩ := live_read_step h hn
      exact Finset.card_pos.mpr ⟨b, mem_succ.mpr e⟩
    by_cases vi : v ∈ inputs (d:=d) C
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp vi
      change inp (d:=d) C i = v at hi
      have lt : v.val < d := by rw [← hi]; exact i.isLt
      have ng : v ∉ liveGates (d:=d) C o := fun h => Nat.not_le_of_lt lt (mem_liveGates.mp h).1
      rw [ite_eq_left vi, ite_eq_right ng]
      split_ifs with vf
      · exact lowerFork vf
      · exact lowerLive (hi ▸ ha i) (by omega)
    · rw [ite_eq_right vi]
      by_cases vg : v ∈ liveGates (d:=d) C o
      · obtain ⟨_, lt, hh⟩ := mem_liveGates.mp vg
        rw [ite_eq_left vg]
        split_ifs with vf
        · exact lowerFork vf
        · exact lowerLive hh lt
      · rw [ite_eq_right vg]
        split_ifs with vf
        · exact (by decide : 1 ≤ 2).trans (lowerFork vf)
        · exact Nat.zero_le _
  have lower := Finset.sum_le_sum (s := Finset.univ) (fun v _ => pointwise v)
  have upper := Finset.sum_le_sum (s := Finset.univ) (fun v _ => atMostIn (d:=d) C o fit v)
  have ci : (inputs (d:=d) C).card = d := by simp [inputs]
  have cf : forks.card = d := by simp [forks]
  have co : (sinks (d:=d) C).card = 4 := by simp [sinks]
  simp only [Finset.sum_add_distrib, indicator_sum, Nat.one_mul, ci, cf, co] at lower upper
  rw [degree_balance (d:=d)] at lower
  have gates := live_gate_le (d:=d) C o
  omega

end MatrixNetwork

namespace MatrixBranch

namespace Route

open Relation

def Branches {m : Nat} (reads : Fin m → Fin m → Prop) (v : Fin m) : Prop :=
  ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Follow {m : Nat} (reads : Fin m → Fin m → Prop) (v w : Fin m) : Prop :=
  reads v w ∧ ¬ Branches reads v

def Avoid {m : Nat} (reads : Fin m → Fin m → Prop) (cut v w : Fin m) : Prop :=
  reads v w ∧ v ≠ cut ∧ w ≠ cut

theorem follow_unique {m : Nat} {reads : Fin m → Fin m → Prop} {v a b : Fin m}
    (step : Follow reads v a) (other : reads v b) : a = b := by
  by_contra different
  exact step.2 ⟨a, b, step.1, other, different⟩

theorem exists_boundary {m : Nat} (reads : Fin m → Fin m → Prop)
    (forward : ∀ {a b}, reads a b → a < b) (v : Fin m) :
    ∃ cut : Fin m, (Branches reads cut ∨ ∀ w, ¬ reads cut w) ∧ ReflTransGen (Follow reads) v cut := by
  classical
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases branches : Branches reads v
    · exact ⟨v, Or.inl branches, ReflTransGen.refl⟩
    by_cases goes : ∃ next, reads v next
    · obtain ⟨next, edge⟩ := goes
      have increase := forward edge
      have nextLt : distance next < distance v := by
        dsimp [distance]
        have bound := next.isLt
        change v.val < next.val at increase
        omega
      obtain ⟨cut, stop, route⟩ := ih next nextLt
      exact ⟨cut, stop, route.head ⟨edge, branches⟩⟩
    · exact ⟨v, Or.inr (fun w h => goes ⟨w, h⟩), ReflTransGen.refl⟩

theorem through {m : Nat} {reads : Fin m → Fin m → Prop} {source cut out : Fin m}
    (route : ReflTransGen (Follow reads) source cut) (dead : ∀ w, ¬ reads out w)
    (path : ReflTransGen reads source out) : ReflTransGen reads cut out := by
  refine ReflTransGen.head_induction_on (motive := fun a _ =>
    ReflTransGen reads a out → ReflTransGen reads cut out) route (fun h => h) ?_ path
  intro a c step tail ih h
  rcases h.cases_head with he | ⟨d, edge, next⟩
  · exact (dead c (he ▸ step.1)).elim
  · have hd := follow_unique step edge
    subst d
    exact ih next

theorem dead_only_self {m : Nat} {reads : Fin m → Fin m → Prop} {a b : Fin m}
    (dead : ∀ w, ¬ reads a w) (route : ReflTransGen reads a b) : a = b := by
  rcases route.cases_head with equal | ⟨next, edge, _⟩
  · exact equal
  · exact (dead next edge).elim

theorem cannot_avoid {m : Nat} {reads : Fin m → Fin m → Prop} {source cut out : Fin m}
    (route : ReflTransGen (Follow reads) source cut) (dead : ∀ w, ¬ reads out w)
    (path : ReflTransGen (Avoid reads cut) source out) : source = cut := by
  refine ReflTransGen.head_induction_on (motive := fun a _ =>
    ReflTransGen (Avoid reads cut) a out → a = cut) route (fun _ => rfl) ?_ path
  intro a c step tail ih h
  rcases h.cases_head with he | ⟨d, edge, next⟩
  · exact (dead c (he ▸ step.1)).elim
  · have hd := follow_unique step edge.1
    subst d
    exact (edge.2.2 (ih next)).elim

theorem trace {m n : Nat} {reads : Fin m → Fin m → Prop} {inputWire : Fin n → Fin m}
    (forward : ∀ {a b}, reads a b → a < b) {x y : Fin m → Bool}
    (localStep : ∀ b, (∀ i, inputWire i ≠ b) → x b ≠ y b → ∃ a, reads a b ∧ x a ≠ y a)
    {out : Fin m} (different : x out ≠ y out) :
    ∃ i, x (inputWire i) ≠ y (inputWire i) ∧ ReflTransGen reads (inputWire i) out := by
  classical
  have track : ∀ k (b : Fin m), b.val = k → x b ≠ y b →
      ∃ i, x (inputWire i) ≠ y (inputWire i) ∧ ReflTransGen reads (inputWire i) b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases atInput : ∃ i, inputWire i = b
      · obtain ⟨i, rfl⟩ := atInput
        exact ⟨i, diff, ReflTransGen.refl⟩
      · obtain ⟨a, edge, ha⟩ := localStep b (fun i he => atInput ⟨i, he⟩) diff
        have order : a.val < b.val := forward edge
        obtain ⟨i, hi, path⟩ := ih a.val (order.trans_eq hb) a rfl ha
        exact ⟨i, hi, path.tail edge⟩
  exact track out.val out rfl different

theorem trace_avoiding {m n : Nat} {reads : Fin m → Fin m → Prop}
    {inputWire : Fin n → Fin m} (forward : ∀ {a b}, reads a b → a < b)
    {x y : Fin m → Bool}
    (localStep : ∀ b, (∀ i, inputWire i ≠ b) → x b ≠ y b → ∃ a, reads a b ∧ x a ≠ y a)
    {out cut : Fin m} (sameCut : x cut = y cut) (different : x out ≠ y out) :
    ∃ i, x (inputWire i) ≠ y (inputWire i) ∧ ReflTransGen (Avoid reads cut) (inputWire i) out := by
  classical
  have track : ∀ k (b : Fin m), b.val = k → x b ≠ y b →
      ∃ i, x (inputWire i) ≠ y (inputWire i) ∧ ReflTransGen (Avoid reads cut) (inputWire i) b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases atInput : ∃ i, inputWire i = b
      · obtain ⟨i, rfl⟩ := atInput
        exact ⟨i, diff, ReflTransGen.refl⟩
      · obtain ⟨a, edge, ha⟩ := localStep b (fun i he => atInput ⟨i, he⟩) diff
        have order : a.val < b.val := forward edge
        obtain ⟨i, hi, path⟩ := ih a.val (order.trans_eq hb) a rfl ha
        have aOff : a ≠ cut := by rintro rfl; exact ha sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨i, hi, path.tail ⟨edge, aOff, bOff⟩⟩
  exact track out.val out rfl different

theorem branch_labels {m n q : Nat} (reads : Fin m → Fin m → Prop)
    (forward : ∀ {a b}, reads a b → a < b)
    (inputWire : Fin n → Fin m) (outputWire : Fin q → Fin m)
    (outInjective : Function.Injective outputWire)
    (sinks : ∀ j w, ¬ reads (outputWire j) w)
    (reachable : ∀ i, ∃ j k : Fin q, j ≠ k ∧ ReflTransGen reads (inputWire i) (outputWire j) ∧
      ReflTransGen reads (inputWire i) (outputWire k))
    (val : (Fin n → Bool) → Fin m → Bool)
    (onInput : ∀ x i, val x (inputWire i) = x i)
    (localStep : ∀ x y b, (∀ i, inputWire i ≠ b) → val x b ≠ val y b →
      ∃ a, reads a b ∧ val x a ≠ val y a)
    (separation : ∀ i j : Fin n, i ≠ j → ∃ rows : Fin 4 → Fin n → Bool,
      (∀ a b k, k ≠ i → k ≠ j → rows a k = rows b k) ∧
      Function.Injective (fun a => fun d : Fin q => val (rows a) (outputWire d))) :
    ∃ label : Fin n → Fin m, Function.Injective label ∧ ∀ i, Branches reads (label i) := by
  classical
  let label (i : Fin n) := Classical.choose (exists_boundary reads forward (inputWire i))
  have boundary (i : Fin n) := Classical.choose_spec (exists_boundary reads forward (inputWire i))
  have route (i : Fin n) : ReflTransGen (Follow reads) (inputWire i) (label i) := (boundary i).2
  have branches (i : Fin n) : Branches reads (label i) := by
    rcases (boundary i).1 with fork | dead
    · exact fork
    · obtain ⟨j, k, hjk, pathJ, pathK⟩ := reachable i
      have atJ := dead_only_self dead (through (route i) (sinks j) pathJ)
      have atK := dead_only_self dead (through (route i) (sinks k) pathK)
      exact (hjk (outInjective (atJ.symm.trans atK))).elim
  refine ⟨label, ?_, branches⟩
  intro i j equal
  by_contra hij
  obtain ⟨rows, unchanged, distinct⟩ := separation i j hij
  have cutInj : Function.Injective (fun a : Fin 4 => val (rows a) (label i)) := by
    intro a b sameCut
    apply distinct
    funext d
    by_contra hd
    obtain ⟨p, different, path⟩ := trace_avoiding forward (localStep (rows a) (rows b)) sameCut hd
    have pIn : p = i ∨ p = j := by
      by_contra! h
      apply different
      rw [onInput, onInput]
      exact unchanged a b p h.1 h.2
    rcases pIn with hpi | hpj
    · have pathI : ReflTransGen (Avoid reads (label i)) (inputWire i) (outputWire d) := by
        simpa only [hpi] using path
      have atCut := cannot_avoid (route i) (sinks d) pathI
      apply different
      rw [hpi, atCut]
      exact sameCut
    · have pathJ : ReflTransGen (Avoid reads (label j)) (inputWire j) (outputWire d) := by
        simpa only [hpj, equal] using path
      have atCut := cannot_avoid (route j) (sinks d) pathJ
      apply different
      rw [hpj, atCut, ← equal]
      exact sameCut
  have count : 4 ≤ 2 := by
    simpa using Fintype.card_le_of_injective (fun a : Fin 4 => val (rows a) (label i)) cutInj
  omega

end Route

def pairInput {arity : ℕ} (i j : Fin arity) (row : Fin arity → Bool) (bits : Fin 4) : Fin arity → Bool :=
  Function.update (Function.update row i (bits.val.testBit 0)) j (bits.val.testBit 1)

theorem pairInput_other {arity : ℕ} (i j k : Fin arity) (row : Fin arity → Bool) (bits : Fin 4)
    (hi : k ≠ i) (hj : k ≠ j) :
    pairInput i j row bits k = row k := by
  rw [pairInput, Function.update_of_ne hj, Function.update_of_ne hi]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation

theorem bound (n : ℕ) (f : (Fin (4*n) → Bool) → Fin 4 → Bool) (C : Circuit) (o : Fin 4 → ℕ)
    (legal : FanInTwo C)
    (out : ∀ x j, (C.wires (List.ofFn x)).getD (o j) false = f x j)
    (affectsTwo : ∀ i : Fin (4*n), ∃ j k : Fin 4, j ≠ k ∧
      (∃ x, f (Function.update x i false) j ≠ f (Function.update x i true) j) ∧
      (∃ x, f (Function.update x i false) k ≠ f (Function.update x i true) k))
    (pairSeparates : ∀ i j : Fin (4*n), i ≠ j → ∃ row, Function.Injective
      (fun bits : Fin 4 => f (pairInput i j row bits))) : 8*n ≤ C.size+4 := by
  classical
  have correct (x : Fin (4*n) → Bool) (j : Fin 4) :
      MatrixNetwork.value (d:=4*n) C o x (MatrixNetwork.out (d:=4*n) C j) = f x j := by
    rw [MatrixNetwork.out_value]
    exact out x j
  have reachesRaw (i : Fin (4*n)) (j : Fin 4) (row : Fin (4*n) → Bool)
      (different : f (Function.update row i false) j ≠ f (Function.update row i true) j) :
      ReflTransGen (MatrixNetwork.raw (d:=4*n) C o) (MatrixNetwork.inp (d:=4*n) C i) (MatrixNetwork.out (d:=4*n) C j) := by
    let x := Function.update row i false
    let y := Function.update row i true
    have diff : MatrixNetwork.value (d:=4*n) C o x (MatrixNetwork.out (d:=4*n) C j) ≠ MatrixNetwork.value (d:=4*n) C o y (MatrixNetwork.out (d:=4*n) C j) := by
      simpa only [correct] using different
    obtain ⟨k, changed, path⟩ := Route.trace (reads := MatrixNetwork.raw (d:=4*n) C o) (inputWire := MatrixNetwork.inp (d:=4*n) C) (MatrixNetwork.raw_before (d:=4*n))
      (fun b h => MatrixNetwork.raw_difference (d:=4*n) x y b (fun l e => h l e.symm)) diff
    have hk : k = i := by
      by_contra hn
      apply changed
      simp only [MatrixNetwork.inp_value (d:=4*n), x, y, Function.update_of_ne hn]
    simpa only [hk] using path
  have inputAlive (i : Fin (4*n)) : MatrixNetwork.alive (d:=4*n) C o (MatrixNetwork.inp (d:=4*n) C i) := by
    obtain ⟨j, k, hjk, ⟨row, diff⟩, other⟩ := affectsTwo i
    exact ⟨j, reachesRaw i j row diff⟩
  have reach (i : Fin (4*n)) : ∃ j k : Fin 4, j ≠ k ∧
      ReflTransGen (MatrixNetwork.liveRead (d:=4*n) C o) (MatrixNetwork.inp (d:=4*n) C i) (MatrixNetwork.out (d:=4*n) C j) ∧
      ReflTransGen (MatrixNetwork.liveRead (d:=4*n) C o) (MatrixNetwork.inp (d:=4*n) C i) (MatrixNetwork.out (d:=4*n) C k) := by
    obtain ⟨j, k, hjk, ⟨x, hx⟩, ⟨y, hy⟩⟩ := affectsTwo i
    exact ⟨j, k, hjk,
      MatrixNetwork.raw_to_live_path (d:=4*n) (reachesRaw i j x hx) (MatrixNetwork.out_always_alive (d:=4*n) C o j),
      MatrixNetwork.raw_to_live_path (d:=4*n) (reachesRaw i k y hy) (MatrixNetwork.out_always_alive (d:=4*n) C o k)⟩
  let val (x : Fin (4*n) → Bool) (a : MatrixNetwork.Slot (4*n) C) : Bool :=
    if MatrixNetwork.alive (d:=4*n) C o a then MatrixNetwork.value (d:=4*n) C o x a else false
  have input (x : Fin (4*n) → Bool) (i : Fin (4*n)) : val x (MatrixNetwork.inp (d:=4*n) C i) = x i := by
    simpa only [val, ite_eq_left (inputAlive i)] using MatrixNetwork.inp_value (d:=4*n) C o x i
  have output (x : Fin (4*n) → Bool) (j : Fin 4) : val x (MatrixNetwork.out (d:=4*n) C j) = f x j := by
    simpa only [val, ite_eq_left (MatrixNetwork.out_always_alive (d:=4*n) C o j)] using correct x j
  have localStep (x y : Fin (4*n) → Bool) (b : MatrixNetwork.Slot (4*n) C)
      (nonInput : ∀ i, MatrixNetwork.inp (d:=4*n) C i ≠ b) (different : val x b ≠ val y b) :
      ∃ a, MatrixNetwork.liveRead (d:=4*n) C o a b ∧ val x a ≠ val y a := by
    by_cases aliveB : MatrixNetwork.alive (d:=4*n) C o b
    · have hd : MatrixNetwork.value (d:=4*n) C o x b ≠ MatrixNetwork.value (d:=4*n) C o y b := by
        simpa only [val, ite_eq_left aliveB] using different
      obtain ⟨a, step, changes⟩ := MatrixNetwork.raw_difference (d:=4*n) x y b
        (fun i e => nonInput i e.symm) hd
      have liveStep : MatrixNetwork.liveRead (d:=4*n) C o a b := ⟨step, aliveB⟩
      have aliveA := MatrixNetwork.live_read_source (d:=4*n) liveStep
      exact ⟨a, liveStep, by simpa only [val, ite_eq_left aliveA] using changes⟩
    · simp [val, aliveB] at different
  have separated (i j : Fin (4*n)) (hne : i ≠ j) : ∃ rows : Fin 4 → Fin (4*n) → Bool,
      (∀ a b k, k ≠ i → k ≠ j → rows a k = rows b k) ∧
      Function.Injective (fun a => fun d : Fin 4 => val (rows a) (MatrixNetwork.out (d:=4*n) C d)) := by
    obtain ⟨row, injective⟩ := pairSeparates i j hne
    refine ⟨pairInput i j row, ?_, ?_⟩
    · intro a b k hi hj
      rw [pairInput_other i j k row a hi hj, pairInput_other i j k row b hi hj]
    · intro a b same
      apply injective
      funext d
      simpa only [output] using congrFun same d
  obtain ⟨label, injective, branches⟩ :=
    Route.branch_labels (MatrixNetwork.liveRead (d:=4*n) C o) (MatrixNetwork.live_before (d:=4*n)) (MatrixNetwork.inp (d:=4*n) C) (MatrixNetwork.out (d:=4*n) C)
      (MatrixNetwork.out_inj (d:=4*n) C) (MatrixNetwork.from_out_impossible (d:=4*n)) reach val input localStep separated
  have h := MatrixNetwork.enoughSlots (d:=4*n) C o legal inputAlive label injective (by
    intro i
    obtain ⟨a, b, ra, rb, ne⟩ := branches i
    exact ⟨a, b, ne, ra, rb⟩)
  change 8*n ≤ C.gates.length+4
  omega

end MatrixBranch

namespace MatrixLift

private def raw (n : ℕ) (g : Fin 4) (i : ℕ) : ℕ :=
  ![i,n+i,2*n+2*i,2*n+2*i+1] g

private def row (j : Fin 4) : Fin 4 := ![0,0,1,1] j
private def col (j : Fin 4) : Fin 4 := ![2,3,2,3] j

def mm (n : ℕ) (x : Fin (4*n) → Bool) (j : Fin 4) : Bool :=
  (List.range n).any fun i => (List.ofFn x).getD (raw n (row j) i) false &&
    (List.ofFn x).getD (raw n (col j) i) false

private def address {n} (g : Fin 4) (i : Fin n) : Fin (4*n) :=
  ⟨raw n g i.val, by have h := i.isLt; fin_cases g <;> simp [raw] <;> omega⟩

private theorem address_inj {n} {g h : Fin 4} {i j : Fin n}
    (eq : address g i = address h j) : g=h ∧ i=j := by
  have val := congrArg Fin.val eq
  have hi := i.isLt
  have hj := j.isLt
  fin_cases g <;> fin_cases h <;> simp [address,raw] at val ⊢ <;>
    first | exact Fin.ext val | omega

private theorem cover {n : ℕ} (u : Fin (4*n)) : ∃ g i, address g i = u := by
  have hu := u.isLt
  by_cases a : u.val < n
  · exact ⟨0,⟨_,a⟩,Fin.ext rfl⟩
  by_cases b : u.val < 2*n
  · refine ⟨1,⟨u.val-n,by omega⟩,Fin.ext ?_⟩
    change n+(u.val-n)=u.val; omega
  let i : Fin n := ⟨(u.val-2*n)/2,by omega⟩
  by_cases parity : (u.val-2*n)%2=0
  · refine ⟨2,i,Fin.ext ?_⟩
    change 2*n+2*((u.val-2*n)/2)=u.val; omega
  · refine ⟨3,i,Fin.ext ?_⟩
    change 2*n+2*((u.val-2*n)/2)+1=u.val; omega

private noncomputable def code (n : ℕ) : Fin 4 × Fin n ≃ Fin (4*n) :=
  Equiv.ofBijective (fun p => address p.1 p.2)
    ⟨fun _ _ h => Prod.ext (address_inj h).1 (address_inj h).2, fun u => by
      obtain ⟨g,i,h⟩ := cover u; exact ⟨(g,i),h⟩⟩

private noncomputable def emb {n} (e : Fin 2 ↪ Fin n) : Fin 8 ↪ Fin (4*n) :=
  (code 2).symm.toEmbedding.trans
    (((Function.Embedding.refl (Fin 4)).prodMap e).trans (code n).toEmbedding)

private theorem emb_addr {n} (e : Fin 2 ↪ Fin n) (g : Fin 4) (i : Fin 2) :
    emb e (address g i) = address g (e i) := by
  change (code n) ((Function.Embedding.refl (Fin 4)).prodMap e
    ((code 2).symm ((code 2) (g,i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem hit {n} (x : Fin (4*n) → Bool) (j : Fin 4) :
    mm n x j = true ↔ ∃ i : Fin n, x (address (row j) i) = true ∧ x (address (col j) i) = true := by
  rw [mm, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hg⟩
    let t : Fin n := ⟨i, List.mem_range.mp hi⟩
    refine ⟨t,?_⟩
    change ((List.ofFn x).getD (address (row j) t).val false &&
      (List.ofFn x).getD (address (col j) t).val false) = true at hg
    simpa using hg
  · rintro ⟨t,h₁,h₂⟩
    refine ⟨t.val, List.mem_range.mpr t.isLt,?_⟩
    change ((List.ofFn x).getD (address (row j) t).val false &&
      (List.ofFn x).getD (address (col j) t).val false) = true
    simp [h₁,h₂]

private noncomputable def expand {n} (e : Fin 2 ↪ Fin n) (x : Fin 8 → Bool) : Fin (4*n) → Bool :=
  Function.extend (emb e) x (fun _ => false)

private theorem on_image {n} (e : Fin 2 ↪ Fin n) (x : Fin 8 → Bool) (v : Fin 8) :
    expand e x (emb e v) = x v := (emb e).injective.extend_apply _ _ _

private theorem outside {n} (e : Fin 2 ↪ Fin n) (x : Fin 8 → Bool) (u : Fin (4*n))
    (h : ¬ ∃ v, emb e v = u) : expand e x u = false := Function.extend_apply' _ _ _ h

private theorem eval_expand {n} (e : Fin 2 ↪ Fin n) (x : Fin 8 → Bool) :
    mm n (expand e x) = mm 2 x := by
  funext j
  apply Bool.eq_iff_iff.mpr
  rw [hit,hit]
  constructor
  · rintro ⟨t,hl,hr⟩
    have has : ∃ v, emb e v = address (row j) t := by
      by_contra no
      rw [outside e x _ no] at hl
      contradiction
    obtain ⟨v,hv⟩ := has
    obtain ⟨g,i,rfl⟩ := cover (n := 2) v
    rw [emb_addr] at hv
    have tEq := (address_inj hv).2
    subst t
    refine ⟨i,?_,?_⟩
    · rwa [← emb_addr, on_image] at hl
    · rwa [← emb_addr, on_image] at hr
  · rintro ⟨i,hl,hr⟩
    exact ⟨e i, by rwa [← emb_addr,on_image],by rwa [← emb_addr,on_image]⟩

private theorem update_expand {n} (e : Fin 2 ↪ Fin n) (x : Fin 8 → Bool) (v : Fin 8) (b : Bool) :
    expand e (Function.update x v b) = Function.update (expand e x) (emb e v) b := by
  funext l
  by_cases h : ∃ t, emb e t=l
  · obtain ⟨t,rfl⟩ := h
    by_cases eq : t=v
    · subst t; simp [on_image]
    · rw [on_image, Function.update_of_ne eq, Function.update_of_ne ((emb e).injective.ne eq),on_image]
  · rw [outside e _ _ h, Function.update_of_ne (fun eq => h ⟨v,eq.symm⟩), outside e _ _ h]

private theorem two_lanes {n : ℕ} (hn : 2≤n) (i j : Fin n) :
    ∃ (e : Fin 2 ↪ Fin n) (s t : Fin 2), e s=i ∧ e t=j := by
  have make (u v : Fin n) (ne : u≠v) : ∃ e : Fin 2 ↪ Fin n, e 0=u ∧ e 1=v := by
    let f : Fin 2 → Fin n := ![u,v]
    refine ⟨⟨f,?_⟩, rfl,rfl⟩
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [f]
  by_cases eq : i=j
  · subst j
    let a : Fin n := ⟨0,by omega⟩
    let b : Fin n := ⟨1,by omega⟩
    have ab : a≠b := by simp [a,b]
    obtain ⟨w,diff⟩ : ∃ w : Fin n, i ≠ w := by
      by_cases ia : i=a
      · exact ⟨b,ia ▸ ab⟩
      · exact ⟨a,ia⟩
    obtain ⟨e,h,_⟩ := make i w diff
    exact ⟨e,0,0,h,h⟩
  · obtain ⟨e,h₁,h₂⟩ := make i j eq
    exact ⟨e,0,1,h₁,h₂⟩

set_option maxRecDepth 8192 in
private theorem two_exact : ∀ x, mm 2 x=MatrixTwo.mm x := by decide +kernel

theorem project {n : ℕ} (hn : 2 ≤ n) (i j : Fin (4*n)) :
    ∃ (e : Fin 8 ↪ Fin (4*n)) (lift : (Fin 8 → Bool) → (Fin (4*n) → Bool)) (i' j' : Fin 8),
      e i'=i ∧ e j'=j ∧ (∀ x, mm n (lift x) = MatrixTwo.mm x) ∧
      (∀ x t b, lift (Function.update x t b) = Function.update (lift x) (e t) b) := by
  obtain ⟨g,u,rfl⟩ := cover i
  obtain ⟨h,v,rfl⟩ := cover j
  obtain ⟨e,s,t,hs,ht⟩ := two_lanes hn u v
  refine ⟨emb e,expand e,address g s,address h t,?_,?_,
    fun x => (eval_expand e x).trans (two_exact x), update_expand e⟩
  · rw [emb_addr,hs]
  · rw [emb_addr,ht]

end MatrixLift

namespace MatrixLift

def pairInput {d : ℕ} (i j : Fin d) (row : Fin d → Bool) (bits : Fin 4) : Fin d → Bool :=
  Function.update (Function.update row i (bits.val.testBit 0)) j (bits.val.testBit 1)

theorem pairInput_other {d : ℕ} (i j k : Fin d) (row : Fin d → Bool) (bits : Fin 4)
    (hi : k ≠ i) (hj : k ≠ j) : pairInput i j row bits k = row k := by
  rw [pairInput,Function.update_of_ne hj,Function.update_of_ne hi]

theorem affectsTwo (n : ℕ) (hn : 2 ≤ n) (i : Fin (4*n)) : ∃ j k : Fin 4, j ≠ k ∧
    (∃ x, mm n (Function.update x i false) j ≠ mm n (Function.update x i true) j) ∧
    (∃ x, mm n (Function.update x i false) k ≠ mm n (Function.update x i true) k) := by
  obtain ⟨e,lift,p,_,ei,_,eval,upd⟩ := project hn i i
  obtain ⟨j,k,ne,⟨r,hr⟩,⟨s,hs⟩⟩ := MatrixTwo.affectsTwo p
  refine ⟨j,k,ne,⟨lift r,?_⟩,⟨lift s,?_⟩⟩
  · simpa only [←ei, ←upd,eval] using hr
  · simpa only [←ei, ←upd,eval] using hs

theorem pairSeparates (n : ℕ) (hn : 2 ≤ n) (i j : Fin (4*n)) (ne : i ≠ j) :
    ∃ row : Fin (4*n) → Bool, Function.Injective (fun bits : Fin 4 => mm n (pairInput i j row bits)) := by
  obtain ⟨e,lift,p,q,ei,ej,eval,upd⟩ := project hn i j
  have pq : p ≠ q := by
    intro h
    exact ne (ei.symm.trans ((congrArg e h).trans ej))
  obtain ⟨r,distinct⟩ := MatrixTwo.pairSeparates p q pq
  refine ⟨lift r,?_⟩
  have eq (bits : Fin 4) : mm n (pairInput i j (lift r) bits) = MatrixTwo.mm (MatrixTwo.pairInput p q r bits) := by
    rw [pairInput,← ei,← ej,← upd,← upd,eval]
    rfl
  intro a b h
  exact distinct ((eq a).symm.trans (h.trans (eq b)))

end MatrixLift

end PEqualNP.Outside.L_meta_17111

open PEqualNP.Outside.L_meta_17111 in
theorem PEqualNP.Outside.L_meta_17111 : ∀ n : ℕ, 0 < n → ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 * n - 5 ∧ ∀ x : Fin (4 * n) → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (List.range n).any (fun i => (List.ofFn x).getD i false && (List.ofFn x).getD (2 * n + 2 * i) false) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (List.range n).any (fun i => (List.ofFn x).getD i false && (List.ofFn x).getD (2 * n + 2 * i + 1) false) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (List.range n).any (fun i => (List.ofFn x).getD (n + i) false && (List.ofFn x).getD (2 * n + 2 * i) false) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (List.range n).any (fun i => (List.ofFn x).getD (n + i) false && (List.ofFn x).getD (2 * n + 2 * i + 1) false) := by
  intro n positive
  by_cases big : 2 ≤ n
  · rintro ⟨C,o,fan,size,spec⟩
    have outputs (x : Fin (4*n) → Bool) (j : Fin 4) :
        (C.wires (List.ofFn x)).getD (o j) false = MatrixLift.mm n x j := by
      obtain ⟨a,b,c,d⟩ := spec x
      fin_cases j
      · exact a
      · exact b
      · exact c
      · exact d
    have lower := MatrixBranch.bound n (MatrixLift.mm n) C o fan outputs
      (MatrixLift.affectsTwo n big) (MatrixLift.pairSeparates n big)
    omega
  · have eq : n = 1 := by omega
    subst n
    exact MatrixBase.exactBase
