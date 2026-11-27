import PEqualNP.Defs

-- The first-branch argument and backwards tracing are adapted from
-- L-meta-11365 (#15327, Apache-2.0), via the accepted L_meta_11868 (same repository, Apache-2.0).

namespace PEqualNP.Outside.L_meta_15074

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

namespace Network

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

abbrev Slot (C : Circuit) := Fin (6 + C.gates.length + 2)

def inp (C : Circuit) (i : Fin 6) : Slot C :=
  ⟨i.val, by have := i.isLt; omega⟩

def out (C : Circuit) (i : Fin 2) : Slot C :=
  ⟨6 + C.gates.length + i.val, by have := i.isLt; omega⟩

theorem inp_inj (C : Circuit) : Function.Injective (inp C) :=
  fun _ _ h => Fin.ext (congrArg (fun v : Slot C => v.val) h)

theorem out_inj (C : Circuit) : Function.Injective (out C) := by
  intro i j h
  have h' := congrArg Fin.val h
  apply Fin.ext
  change 6 + C.gates.length + i.val = 6 + C.gates.length + j.val at h'
  omega

def reads (C : Circuit) (o : Fin 2 → Nat) (b : Slot C) : List Nat :=
  if h₀ : b.val < 6 then [] else
  if h : b.val < 6 + C.gates.length then
    (C.gates[b.val - 6]'(by omega)).inputs
  else [o ⟨b.val - (6 + C.gates.length), by have := b.isLt; omega⟩]

def raw (C : Circuit) (o : Fin 2 → Nat) (a b : Slot C) : Prop :=
  a.val < b.val ∧ a.val < 6 + C.gates.length ∧ a.val ∈ reads C o b

def alive (C : Circuit) (o : Fin 2 → Nat) (a : Slot C) : Prop :=
  ∃ j : Fin 2, Relation.ReflTransGen (raw C o) a (out C j)

def liveRead (C : Circuit) (o : Fin 2 → Nat) (a b : Slot C) : Prop :=
  raw C o a b ∧ alive C o b

lemma live_read_source {C : Circuit} {o : Fin 2 → Nat} {a b : Slot C}
    (h : liveRead C o a b) : alive C o a := by
  obtain ⟨j, path⟩ := h.2
  exact ⟨j, path.head h.1⟩

lemma out_always_alive (C : Circuit) (o : Fin 2 → Nat) (j : Fin 2) :
    alive C o (out C j) := ⟨j, .refl⟩

lemma live_read_step {C : Circuit} {o : Fin 2 → Nat} {a : Slot C}
    (ha : alive C o a) (hn : a.val < 6 + C.gates.length) :
    ∃ b, liveRead C o a b := by
  obtain ⟨j, path⟩ := ha
  have ne : a ≠ out C j := by
    intro h; subst a
    change 6 + C.gates.length + j.val < 6 + C.gates.length at hn
    omega
  rcases Relation.ReflTransGen.cases_head path with h | ⟨b, edge, rest⟩
  · exact (ne h).elim
  · exact ⟨b, edge, j, rest⟩

lemma from_out_impossible {C : Circuit} {o : Fin 2 → Nat}
    (j : Fin 2) (b : Slot C) : ¬ liveRead C o (out C j) b := by
  intro h
  have bad := h.1.2.1
  change 6 + C.gates.length + j.val < 6 + C.gates.length at bad
  omega

def value (C : Circuit) (o : Fin 2 → Nat) (x : Fin 6 → Bool) (a : Slot C) : Bool :=
  if a.val < 6 + C.gates.length then (C.wires (List.ofFn x)).getD a.val false
  else (C.wires (List.ofFn x)).getD
    (o ⟨a.val - (6 + C.gates.length), by have := a.isLt; omega⟩) false

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem inp_value (C : Circuit) (o : Fin 2 → Nat) (x : Fin 6 → Bool) (i : Fin 6) :
    value C o x (inp C i) = x i := by
  have hi : i.val < 6 + C.gates.length := by have := i.isLt; omega
  unfold value
  split
  · change (wiresFrom C.gates (List.ofFn x)).getD i.val false = x i
    rw [getD_wiresFrom _ _ _ (by simpa using i.isLt)]
    exact getD_ofFn 6 x false i
  · rename_i bad
    exact (bad hi).elim

theorem out_value (C : Circuit) (o : Fin 2 → Nat) (x : Fin 6 → Bool) (j : Fin 2) :
    value C o x (out C j) = (C.wires (List.ofFn x)).getD (o j) false := by
  have hn : ¬ 6 + C.gates.length + j.val < 6 + C.gates.length := by omega
  unfold value
  split
  · rename_i bad
    exact (hn bad).elim
  · apply congrArg (fun idx : Fin 2 => (C.wires (List.ofFn x)).getD (o idx) false)
    apply Fin.ext
    simp [out]

theorem gate_value (C : Circuit) (x : Fin 6 → Bool) (p : Nat) (g : Gate)
    (hp : C.gates[p]? = some g) :
    (C.wires (List.ofFn x)).getD (6 + p) false =
      g.op.eval (g.inputs.map fun a =>
        if a < 6 + p then (C.wires (List.ofFn x)).getD a false else false) := by
  obtain ⟨pre, post, hgs, plen⟩ := split_at C.gates p g hp
  let w := wiresFrom pre (List.ofFn x)
  have wl : w.length = 6 + p := by simp [w, length_wiresFrom, plen]
  simp only [Circuit.wires, hgs, List.foldl_append, List.foldl_cons]
  change (wiresFrom post (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])).getD
        (6 + p) false = _
  rw [getD_wiresFrom _ _ _ (by simp [wl])]
  have headValue : (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]).getD (6 + p) false =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by rw [← wl]; simp
  rw [headValue]
  congr 1
  apply List.map_congr_left
  intro a ha
  by_cases h : a < 6 + p
  · rw [if_pos (by simpa [wl] using h)]
    change w.getD a false = (wiresFrom post
           (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD a false
    rw [getD_wiresFrom post (w ++ [_]) a (by simp [wl]; omega)]
    rw [List.getD_append _ _ _ _ (by simpa [wl] using h)]
  · rw [if_neg (by simpa [wl] using h), List.getD_eq_default _ _ (by omega)]

theorem raw_difference {C : Circuit} {o : Fin 2 → Nat} (x y : Fin 6 → Bool) (b : Slot C)
    (nonInput : ∀ i, b ≠ inp C i) (diff : value C o x b ≠ value C o y b) :
    ∃ a, raw C o a b ∧ value C o x a ≠ value C o y a := by
  classical
  have hb : ¬ b.val < 6 := by
    intro lt
    exact nonInput ⟨b.val, lt⟩ (Fin.ext rfl)
  by_cases hgate : b.val < 6 + C.gates.length
  · let p := b.val - 6
    have hpos : b.val = 6 + p := by dsimp [p]; omega
    have hp : p < C.gates.length := by omega
    let g := C.gates[p]
    have hget : C.gates[p]? = some g := List.getElem?_eq_getElem hp
    have ds : ∃ a ∈ g.inputs, a < b.val ∧
        (C.wires (List.ofFn x)).getD a false ≠ (C.wires (List.ofFn y)).getD a false := by
      by_contra none
      apply diff
      have bnd : 6 + p < 6 + C.gates.length := by omega
      simp only [value, hpos, if_pos bnd, gate_value C x p g hget, gate_value C y p g hget]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro a am
      by_cases hl : a < b.val
      · rw [if_pos (by omega), if_pos (by omega)]
        by_contra hne
        exact none ⟨a, am, hl, hne⟩
      · rw [if_neg (by omega), if_neg (by omega)]
    obtain ⟨a, am, al, d⟩ := ds
    let w : Slot C := ⟨a, by omega⟩
    have wlt : w.val < 6 + C.gates.length := by change a < _; omega
    refine ⟨w, ⟨al, wlt, ?_⟩, ?_⟩
    · simpa only [reads, dif_neg hb, dif_pos hgate] using am
    · simpa only [value, if_pos wlt] using d
  · let j : Fin 2 := ⟨b.val - (6 + C.gates.length), by have := b.isLt; omega⟩
    have oj : o j < 6 + C.gates.length := by
      by_contra! beyond
      apply diff
      simp only [value, if_neg hgate]
      change (wiresFrom C.gates (List.ofFn x)).getD (o j) false =
         (wiresFrom C.gates (List.ofFn y)).getD (o j) false
      rw [List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega),
          List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)]
    let w : Slot C := ⟨o j, by omega⟩
    refine ⟨w, ⟨by dsimp [w]; omega, oj, ?_⟩, ?_⟩
    · simp [reads, hb, hgate, w, j]
    · have wlt : w.val < 6 + C.gates.length := oj
      simpa only [value, if_pos wlt, if_neg hgate] using diff

theorem raw_before {C : Circuit} {o : Fin 2 → Nat} {a b : Slot C}
    (h : raw C o a b) : a.val < b.val := h.1

theorem live_before {C : Circuit} {o : Fin 2 → Nat} {a b : Slot C}
    (h : liveRead C o a b) : a.val < b.val := h.1.1

theorem raw_to_live_path {C : Circuit} {o : Fin 2 → Nat} {a b : Slot C}
    (path : Relation.ReflTransGen (raw C o) a b) (hj : alive C o b) :
    Relation.ReflTransGen (liveRead C o) a b := by
  induction path with
  | refl => exact .refl
  | @tail b c p e ih =>
    have aliveB := live_read_source (show liveRead C o b c from ⟨e, hj⟩)
    exact (ih aliveB).tail ⟨e, hj⟩



noncomputable def succ (C : Circuit) (o : Fin 2 → Nat) (u : Slot C) : Finset (Slot C) := by
  classical
  exact Finset.univ.filter (fun v => liveRead C o u v)

noncomputable def pred (C : Circuit) (o : Fin 2 → Nat) (v : Slot C) : Finset (Slot C) := by
  classical
  exact Finset.univ.filter (fun u => liveRead C o u v)

noncomputable def liveGates (C : Circuit) (o : Fin 2 → Nat) : Finset (Slot C) := by
  classical
  exact Finset.univ.filter (fun u => 6 ≤ u.val ∧ u.val < 6 + C.gates.length ∧ alive C o u)

theorem mem_succ {C : Circuit} {o : Fin 2 → Nat} {u v : Slot C} :
    v ∈ succ C o u ↔ liveRead C o u v := by
  classical
  simp [succ]

theorem mem_pred {C : Circuit} {o : Fin 2 → Nat} {u v : Slot C} :
    u ∈ pred C o v ↔ liveRead C o u v := by
  classical
  simp [pred]

theorem mem_liveGates {C : Circuit} {o : Fin 2 → Nat} {u : Slot C} :
    u ∈ liveGates C o ↔ 6 ≤ u.val ∧ u.val < 6 + C.gates.length ∧ alive C o u := by
  classical
  simp [liveGates]

def inputs (C : Circuit) : Finset (Slot C) :=
  Finset.univ.map ⟨inp C, inp_inj C⟩

def sinks (C : Circuit) : Finset (Slot C) :=
  Finset.univ.map ⟨out C, out_inj C⟩

theorem read_card (C : Circuit) (o : Fin 2 → Nat) (v : Slot C) :
    (pred C o v).card ≤ (reads C o v).length := by
  classical
  have sub : (pred C o v).image Fin.val ⊆ (reads C o v).toFinset := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    have edge := mem_pred.mp hu
    exact List.mem_toFinset.mpr edge.1.2.2
  have le := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at le
  exact le.trans (List.toFinset_card_le _)

theorem degree_balance (C : Circuit) (o : Fin 2 → Nat) :
    (∑ u : Slot C, (succ C o u).card) = ∑ v : Slot C, (pred C o v).card := by
  classical
  simp only [succ, pred, Finset.card_filter]
  exact Finset.sum_comm

theorem indicator_sum {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (n : Nat) :
    (∑ a, (if a ∈ s then n else 0)) = n * s.card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem live_gate_le (C : Circuit) (o : Fin 2 → Nat) : (liveGates C o).card ≤ C.gates.length := by
  classical
  let den : Slot C → Nat := fun u => u.val - 6
  have inj : Set.InjOn den (liveGates C o) := by
    intro a ha b hb eq
    have h1 := (mem_liveGates.mp ha).1
    have h2 := (mem_liveGates.mp hb).1
    apply Fin.ext
    dsimp [den] at eq
    omega
  have incl : (liveGates C o).image den ⊆ Finset.range C.gates.length := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨lo, bound, _⟩ := mem_liveGates.mp hu
    apply Finset.mem_range.mpr
    dsimp [den]
    omega
  have bc := Finset.card_le_card incl
  rwa [Finset.card_image_of_injOn inj, Finset.card_range] at bc

theorem atMostIn (C : Circuit) (o : Fin 2 → Nat) (fit : FanInTwo C) (v : Slot C) :
    (pred C o v).card ≤ (if v ∈ liveGates C o then 2 else 0) +
      (if v ∈ sinks C then 1 else 0) := by
  classical
  by_cases aliveV : alive C o v
  · by_cases hv0 : v.val < 6
    · have zero : (pred C o v).card ≤ 0 := by
        simpa [reads, hv0] using read_card C o v
      exact zero.trans (Nat.zero_le _)
    · by_cases hv1 : v.val < 6 + C.gates.length
      · have m : v ∈ liveGates C o := mem_liveGates.mpr ⟨by omega, hv1, aliveV⟩
        have idx : v.val - 6 < C.gates.length := by omega
        have ih : (pred C o v).card ≤ (C.gates[v.val - 6]'idx).inputs.length := by
          simpa [reads, hv0, hv1] using read_card C o v
        have legal := (fit _ (List.getElem_mem idx)).2
        rw [ite_eq_left m]
        omega
      · let j : Fin 2 := ⟨v.val - (6 + C.gates.length), by have := v.isLt; omega⟩
        have hs : out C j = v := by
          apply Fin.ext
          change 6 + C.gates.length + (v.val - (6 + C.gates.length)) = v.val
          omega
        have sv : v ∈ sinks C := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, hs⟩
        have ih : (pred C o v).card ≤ 1 := by
          simpa [reads, hv0, hv1] using read_card C o v
        rw [ite_eq_left sv]
        omega
  · have empty : pred C o v = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact aliveV (mem_pred.mp hu).2
    simp [empty]

theorem enoughSlots (C : Circuit) (o : Fin 2 → Nat) (fit : FanInTwo C)
    (ha : ∀ i, alive C o (inp C i))
    (label : Fin 2 → Slot C) (inj : Function.Injective label)
    (fork : ∀ i, ∃ a b, a ≠ b ∧ liveRead C o (label i) a ∧ liveRead C o (label i) b) :
    6 ≤ C.gates.length := by
  classical
  let forks : Finset (Slot C) := Finset.univ.map ⟨label, inj⟩
  have pointwise (v : Slot C) : (if v ∈ inputs C then 1 else 0) +
      (if v ∈ liveGates C o then 1 else 0) + (if v ∈ forks then 1 else 0)
        ≤ (succ C o v).card := by
    have lowerFork : v ∈ forks → 2 ≤ (succ C o v).card := by
      intro hv
      obtain ⟨i, _, h⟩ := Finset.mem_map.mp hv
      change label i = v at h
      obtain ⟨a, b, ne, ra, rb⟩ := fork i
      have inc : ({a,b} : Finset (Slot C)) ⊆ succ C o v := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_succ.mpr (h ▸ ra)
        · exact mem_succ.mpr (h ▸ rb)
      simpa [ne] using Finset.card_le_card inc
    have lowerLive (h : alive C o v) (hn : v.val < 6 + C.gates.length) : 1 ≤ (succ C o v).card := by
      obtain ⟨b, e⟩ := live_read_step h hn
      exact Finset.card_pos.mpr ⟨b, mem_succ.mpr e⟩
    by_cases vi : v ∈ inputs C
    · obtain ⟨i, _, hi⟩ := Finset.mem_map.mp vi
      change inp C i = v at hi
      have lt : v.val < 6 := by rw [← hi]; exact i.isLt
      have ng : v ∉ liveGates C o := fun h => Nat.not_le_of_lt lt (mem_liveGates.mp h).1
      rw [ite_eq_left vi, ite_eq_right ng]
      split_ifs with vf
      · exact lowerFork vf
      · exact lowerLive (hi ▸ ha i) (by omega)
    · rw [ite_eq_right vi]
      by_cases vg : v ∈ liveGates C o
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
  have upper := Finset.sum_le_sum (s := Finset.univ) (fun v _ => atMostIn C o fit v)
  have ci : (inputs C).card = 6 := by simp [inputs]
  have cf : forks.card = 2 := by simp [forks]
  have co : (sinks C).card = 2 := by simp [sinks]
  simp only [Finset.sum_add_distrib, indicator_sum, Nat.one_mul, ci, cf, co] at lower upper
  rw [degree_balance] at lower
  have gates := live_gate_le C o
  omega

end Network

def sp (x : Fin 6 → Bool) : Fin 2 → Bool :=
  ![(x 0 && x 2 || x 1 && x 3),
    (x 0 && x 4 || x 1 && x 5)]

theorem sp_zero (x : Fin 6 → Bool) : sp x 0 = (x 0 && x 2 || x 1 && x 3) := rfl
theorem sp_one (x : Fin 6 → Bool) : sp x 1 = (x 0 && x 4 || x 1 && x 5) := rfl

def spRow (row : ℕ) (i : Fin 6) : Bool := row.testBit i.val

-- every input changes some output
def affectOut : Fin 6 → Fin 2 := ![0, 0, 0, 0, 1, 1]
def affectRow : Fin 6 → ℕ := ![4, 8, 1, 2, 1, 2]

theorem affectSamples : ∀ i : Fin 6,
    sp (Function.update (spRow (affectRow i)) i false) (affectOut i) ≠
      sp (Function.update (spRow (affectRow i)) i true) (affectOut i) := by
  decide +kernel

-- the two shared inputs change both outputs
def sel : Fin 2 → Fin 6 := ![0, 1]
def forkRow₀ : Fin 2 → ℕ := ![4, 8]
def forkRow₁ : Fin 2 → ℕ := ![16, 32]

theorem forkSamples : ∀ i : Fin 2,
    sp (Function.update (spRow (forkRow₀ i)) (sel i) false) 0 ≠
      sp (Function.update (spRow (forkRow₀ i)) (sel i) true) 0 ∧
    sp (Function.update (spRow (forkRow₁ i)) (sel i) false) 1 ≠
      sp (Function.update (spRow (forkRow₁ i)) (sel i) true) 1 := by
  decide +kernel

def pairInput (i j : Fin 6) (row : Fin 6 → Bool) (bits : Fin 4) : Fin 6 → Bool :=
  Function.update (Function.update row i (bits.val.testBit 0)) j (bits.val.testBit 1)

theorem pairInput_other (i j k : Fin 6) (row : Fin 6 → Bool) (bits : Fin 4)
    (hi : k ≠ i) (hj : k ≠ j) :
    pairInput i j row bits k = row k := by
  rw [pairInput, Function.update_of_ne hj, Function.update_of_ne hi]

def packOutput (v : Fin 2 → Bool) : ℕ :=
  (if v 0 then 1 else 0) + (if v 1 then 2 else 0)

theorem pairSamples : ∀ i j : Fin 2, i ≠ j → ∀ a b : Fin 4,
    packOutput (sp (pairInput (sel i) (sel j) (spRow 24) a)) =
      packOutput (sp (pairInput (sel i) (sel j) (spRow 24) b)) → a = b := by
  decide +kernel

theorem pairSeparates : ∀ i j : Fin 2, i ≠ j →
    Function.Injective (fun bits : Fin 4 => sp (pairInput (sel i) (sel j) (spRow 24) bits)) := by
  intro i j different a b equal
  exact pairSamples i j different a b (congrArg packOutput equal)

namespace Route

open Relation

-- The first branch route and the backwards trace follow L-meta-11365.
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


theorem branch_labels {m n q r : Nat} (reads : Fin m → Fin m → Prop)
    (forward : ∀ {a b}, reads a b → a < b)
    (inputWire : Fin n → Fin m) (outputWire : Fin q → Fin m)
    (outInjective : Function.Injective outputWire)
    (sinks : ∀ j w, ¬ reads (outputWire j) w)
    (sel : Fin r → Fin n)
    (reachable : ∀ i, ∃ j k : Fin q, j ≠ k ∧ ReflTransGen reads (inputWire (sel i)) (outputWire j) ∧
      ReflTransGen reads (inputWire (sel i)) (outputWire k))
    (val : (Fin n → Bool) → Fin m → Bool)
    (onInput : ∀ x i, val x (inputWire i) = x i)
    (localStep : ∀ x y b, (∀ i, inputWire i ≠ b) → val x b ≠ val y b →
      ∃ a, reads a b ∧ val x a ≠ val y a)
    (separation : ∀ i j : Fin r, i ≠ j → ∃ rows : Fin 4 → Fin n → Bool,
      (∀ a b k, k ≠ sel i → k ≠ sel j → rows a k = rows b k) ∧
      Function.Injective (fun a => fun d : Fin q => val (rows a) (outputWire d))) :
    ∃ label : Fin r → Fin m, Function.Injective label ∧ ∀ i, Branches reads (label i) := by
  classical
  let label (i : Fin r) := Classical.choose (exists_boundary reads forward (inputWire (sel i)))
  have boundary (i : Fin r) := Classical.choose_spec (exists_boundary reads forward (inputWire (sel i)))
  have route (i : Fin r) : ReflTransGen (Follow reads) (inputWire (sel i)) (label i) := (boundary i).2
  have branches (i : Fin r) : Branches reads (label i) := by
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
    have pIn : p = sel i ∨ p = sel j := by
      by_contra! h
      apply different
      rw [onInput, onInput]
      exact unchanged a b p h.1 h.2
    rcases pIn with hpi | hpj
    · have pathI : ReflTransGen (Avoid reads (label i)) (inputWire (sel i)) (outputWire d) := by
        simpa only [hpi] using path
      have atCut := cannot_avoid (route i) (sinks d) pathI
      apply different
      rw [hpi, atCut]
      exact sameCut
    · have pathJ : ReflTransGen (Avoid reads (label j)) (inputWire (sel j)) (outputWire d) := by
        simpa only [hpj, equal] using path
      have atCut := cannot_avoid (route j) (sinks d) pathJ
      apply different
      rw [hpj, atCut, ← equal]
      exact sameCut
  have count : 4 ≤ 2 := by
    simpa using Fintype.card_le_of_injective (fun a : Fin 4 => val (rows a) (label i)) cutInj
  omega

end Route

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation

theorem sums_size (C : Circuit) (o : Fin 2 → ℕ) (legal : FanInTwo C)
    (correct : ∀ x j, Network.value C o x (Network.out C j) = sp x j) :
    6 ≤ C.gates.length := by
  classical
  have reachesRaw (i : Fin 6) (j : Fin 2) (row : Fin 6 → Bool)
      (different : sp (Function.update row i false) j ≠ sp (Function.update row i true) j) :
      ReflTransGen (Network.raw C o) (Network.inp C i) (Network.out C j) := by
    let x := Function.update row i false
    let y := Function.update row i true
    have diff : Network.value C o x (Network.out C j) ≠ Network.value C o y (Network.out C j) := by
      simpa only [correct] using different
    obtain ⟨k, changed, path⟩ := Route.trace (reads := Network.raw C o) (inputWire := Network.inp C) Network.raw_before
      (fun b h => Network.raw_difference x y b (fun l e => h l e.symm)) diff
    have hk : k = i := by
      by_contra hn
      apply changed
      simp only [Network.inp_value, x, y, Function.update_of_ne hn]
    simpa only [hk] using path
  have inputAlive (i : Fin 6) : Network.alive C o (Network.inp C i) :=
    ⟨affectOut i, reachesRaw i (affectOut i) (spRow (affectRow i)) (affectSamples i)⟩
  have reach (i : Fin 2) : ∃ j k : Fin 2, j ≠ k ∧
      ReflTransGen (Network.liveRead C o) (Network.inp C (sel i)) (Network.out C j) ∧
      ReflTransGen (Network.liveRead C o) (Network.inp C (sel i)) (Network.out C k) :=
    ⟨0, 1, by decide,
      Network.raw_to_live_path (reachesRaw (sel i) 0 _ (forkSamples i).1) (Network.out_always_alive C o 0),
      Network.raw_to_live_path (reachesRaw (sel i) 1 _ (forkSamples i).2) (Network.out_always_alive C o 1)⟩
  let val (x : Fin 6 → Bool) (a : Network.Slot C) : Bool :=
    if Network.alive C o a then Network.value C o x a else false
  have input (x : Fin 6 → Bool) (i : Fin 6) : val x (Network.inp C i) = x i := by
    simpa only [val, if_pos (inputAlive i)] using Network.inp_value C o x i
  have output (x : Fin 6 → Bool) (j : Fin 2) : val x (Network.out C j) = sp x j := by
    simpa only [val, if_pos (Network.out_always_alive C o j)] using correct x j
  have localStep (x y : Fin 6 → Bool) (b : Network.Slot C)
      (nonInput : ∀ i, Network.inp C i ≠ b) (different : val x b ≠ val y b) :
      ∃ a, Network.liveRead C o a b ∧ val x a ≠ val y a := by
    by_cases aliveB : Network.alive C o b
    · have hd : Network.value C o x b ≠ Network.value C o y b := by
        simpa only [val, if_pos aliveB] using different
      obtain ⟨a, step, changes⟩ := Network.raw_difference x y b
        (fun i e => nonInput i e.symm) hd
      have liveStep : Network.liveRead C o a b := ⟨step, aliveB⟩
      have aliveA := Network.live_read_source liveStep
      exact ⟨a, liveStep, by simpa only [val, if_pos aliveA] using changes⟩
    · simp [val, aliveB] at different
  have separated (i j : Fin 2) (hne : i ≠ j) : ∃ rows : Fin 4 → Fin 6 → Bool,
      (∀ a b k, k ≠ sel i → k ≠ sel j → rows a k = rows b k) ∧
      Function.Injective (fun a => fun d : Fin 2 => val (rows a) (Network.out C d)) := by
    refine ⟨pairInput (sel i) (sel j) (spRow 24), ?_, ?_⟩
    · intro a b k hi hj
      rw [pairInput_other _ _ k _ a hi hj, pairInput_other _ _ k _ b hi hj]
    · intro a b same
      apply pairSeparates i j hne
      funext d
      simpa only [output] using congrFun same d
  obtain ⟨label, injective, branches⟩ :=
    Route.branch_labels (Network.liveRead C o) Network.live_before (Network.inp C) (Network.out C)
      (Network.out_inj C) Network.from_out_impossible sel reach val input localStep separated
  exact Network.enoughSlots C o legal inputAlive label injective (by
    intro i
    obtain ⟨a, b, ra, rb, ne⟩ := branches i
    exact ⟨a, b, ne, ra, rb⟩)

end PEqualNP.Outside.L_meta_15074

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_15074 in
theorem PEqualNP.Outside.L_meta_15074 :
    ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 2 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ x : Fin 6 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 && x 2 || x 1 && x 3) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 && x 4 || x 1 && x 5) := by
  rintro ⟨C, o, legal, budget, correct⟩
  have truth (x : Fin 6 → Bool) (j : Fin 2) : Network.value C o x (Network.out C j) = sp x j := by
    rw [Network.out_value]
    fin_cases j
    · exact (correct x).1
    · exact (correct x).2
  have minimum := sums_size C o legal truth
  change C.gates.length ≤ 5 at budget
  omega
