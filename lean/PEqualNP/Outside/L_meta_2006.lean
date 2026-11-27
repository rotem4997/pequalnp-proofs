import Mathlib
import PEqualNP.Defs

-- Normal form: reads go back, no degenerate gate, reads sorted.

namespace PEqualNP.Outside.L_meta_2006

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
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

lemma wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

lemma eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

lemma V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

lemma gate_val_aux {n : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = n) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < n + i) :
    V gs x (n + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (n + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at n pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

lemma V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

lemma V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]


-- Wire renaming after the deletion of gate j.
def sg (n : ℕ) (j : ℕ) (u : ℕ) : ℕ := if n + j < u then u - 1 else u

lemma sg_le (n j u : ℕ) (h : u ≤ n + j) : sg n j u = u := by
  have h' : ¬ n + j < u := by omega
  simp [sg, h']

lemma sg_gt (n j u : ℕ) (h : n + j < u) : sg n j u = u - 1 := by
  simp [sg, h]

def sh (n j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg n j)⟩

def del (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) : List Gate :=
  ((gs.map f).eraseIdx j).map (sh n j)

lemma del_get (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hij : i ≠ j) :
    ∃ i', sg n j (n + i) = n + i' ∧ (del n f j gs)[i']? = some (sh n j (f g)) ∧
      ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h : i < j
  · refine ⟨i, sg_le n j _ (by omega), ?_, Or.inl ⟨rfl, h⟩⟩
    simp [del, List.getElem?_eraseIdx, h, hg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : ¬ k < j := by omega
    refine ⟨k, ?_, ?_, Or.inr ⟨rfl, by omega⟩⟩
    · rw [sg_gt n j _ (by omega)]; omega
    · simp [del, List.getElem?_eraseIdx, hk, hg]

lemma del_inv (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i' : ℕ) (g' : Gate)
    (h : (del n f j gs)[i']? = some g') :
    ∃ i g, gs[i]? = some g ∧ g' = sh n j (f g) ∧ ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h3 : i' < j
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i', g, hg, rfl, Or.inl ⟨rfl, h3⟩⟩
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i' + 1, g, hg, rfl, Or.inr ⟨rfl, by omega⟩⟩

lemma del_back (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < n + i ∧ u ≠ n + j)
    (i' : ℕ) (g' : Gate) (h : (del n f j gs)[i']? = some g') :
    ∀ u ∈ g'.inputs, u < n + i' := by
  obtain ⟨i, g, hg, rfl, hi⟩ := del_inv n f j gs i' g' h
  intro u hu
  simp only [sh, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hfb i g hg v hv
  unfold sg
  split_ifs <;> omega

lemma del_val (n : ℕ) (f : Gate → Gate) (j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (x : List Bool) (hx : x.length = n)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < n + i ∧ u ≠ n + j)
    (hfv : ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x))) :
    ∀ u, u ≠ n + j → V (del n f j gs) x (sg n j u) = V gs x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    have hlen : (del n f j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    by_cases h1 : u < n
    · rw [sg_le n j u (by omega)]
      exact V_in _ _ x u (by omega)
    · obtain ⟨i, rfl⟩ : ∃ i, u = n + i := ⟨u - n, by omega⟩
      have hij : i ≠ j := by omega
      by_cases h2 : i < gs.length
      · have hg : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        obtain ⟨i', hs, hd, _⟩ := del_get n f j gs i gs[i] hg hij
        rw [hs, gate_val_aux _ x hx i' _ hd (del_back n f j gs hfb i' _ hd),
          gate_val_aux gs x hx i _ hg (hback i _ hg), ← hfv i _ hg]
        simp only [sh, List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        exact ih w (hfb i _ hg w hw).1 (hfb i _ hg w hw).2
      · rw [V_out gs x _ (by omega)]
        apply V_out
        rw [hlen]
        unfold sg
        split_ifs <;> omega


def Mon (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i

lemma core (n : ℕ) (gs : List Gate) (out : ℕ) (j : ℕ) (hj : j < gs.length) (f : Gate → Gate)
    (out' : ℕ) (hout : out' ≠ n + j)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < n + i)
    (hfm : ∀ g ∈ gs, (f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (f g).inputs.length ≤ 2)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < n + i ∧ u ≠ n + j)
    (hfv : ∀ (x : List Bool), x.length = n → ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x)))
    (hov : ∀ (x : List Bool), x.length = n → V gs x out' = V gs x out) :
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ Back n gs' ∧ gs'.length < gs.length ∧
      ∀ (x : List Bool), x.length = n → V gs' x o = V gs x out := by
  refine ⟨del n f j gs, sg n j out', ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨i', hi'⟩ := List.getElem?_of_mem hg'
    obtain ⟨i, g, hg, rfl, _⟩ := del_inv n f j gs i' g' hi'
    have h := hfm g (List.mem_of_getElem? hg)
    exact ⟨h.1, by simpa [sh] using h.2⟩
  · intro i' g' hi'
    exact del_back n f j gs hfb i' g' hi'
  · have hlen : (del n f j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    omega
  · intro x hx
    rw [del_val n f j gs hj x hx hback hfb (hfv x hx) out' hout, hov x hx]

-- Case one: the gate copies wire w.
def f1 (n j w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun u => if u = n + j then w else u)⟩

-- Case two: the gate gj is a constant.
def f2 (n j : ℕ) (gj g : Gate) : Gate :=
  if g.op.eval [] = gj.op.eval [] then ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩
  else if n + j ∈ g.inputs then gj else g

lemma all_filter (W : ℕ → Bool) (a : ℕ) (h : W a = true) (l : List ℕ) :
    ((l.filter (fun u => decide (u ≠ a))).map W).all id = (l.map W).all id := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro H b ⟨u, hu, rfl⟩
    by_cases hb : u = a
    · subst hb; simpa using h
    · exact H _ ⟨u, ⟨hu, hb⟩, rfl⟩
  · rintro H b ⟨u, ⟨hu, _⟩, rfl⟩
    exact H _ ⟨u, hu, rfl⟩

lemma any_filter (W : ℕ → Bool) (a : ℕ) (h : W a = false) (l : List ℕ) :
    ((l.filter (fun u => decide (u ≠ a))).map W).any id = (l.map W).any id := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨u, ⟨hu, _⟩, rfl⟩, hb⟩
    exact ⟨_, ⟨u, hu, rfl⟩, hb⟩
  · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
    have hne : u ≠ a := by
      rintro rfl
      rw [h] at hb
      simp at hb
    exact ⟨_, ⟨u, ⟨hu, hne⟩, rfl⟩, hb⟩

lemma f2_val (n j : ℕ) (gj g : Gate) (W : ℕ → Bool)
    (hgj : gj.op = GateOp.and ∨ gj.op = GateOp.or) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : gj.inputs = []) (hW : W (n + j) = gj.op.eval []) :
    (f2 n j gj g).op.eval ((f2 n j gj g).inputs.map W) = g.op.eval (g.inputs.map W) := by
  rcases hgj with h1 | h1 <;> rcases hg with h2 | h2
  · have hc : W (n + j) = true := by rw [hW, h1]; rfl
    have e : f2 n j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact all_filter W _ hc _
  · have hc : W (n + j) = true := by rw [hW, h1]; rfl
    by_cases hm : n + j ∈ g.inputs
    · have e : f2 n j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, hc⟩
    · have e : f2 n j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (n + j) = false := by rw [hW, h1]; rfl
    by_cases hm : n + j ∈ g.inputs
    · have e : f2 n j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, by simp [hc]⟩
    · have e : f2 n j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (n + j) = false := by rw [hW, h1]; rfl
    have e : f2 n j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact any_filter W _ hc _

lemma f2_cases (n j : ℕ) (gj g : Gate) :
    f2 n j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ n + j))⟩ ∨
    f2 n j gj g = gj ∨ (f2 n j gj g = g ∧ n + j ∉ g.inputs) := by
  unfold f2
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rfl, h2⟩)

lemma shape (n : ℕ) (gs : List Gate) (j : ℕ) (g : Gate) (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hb : ∀ u ∈ g.inputs, u < n + j)
    (hdeg : g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    g.inputs = [] ∨ ∃ w, w < n + j ∧
      ∀ (x : List Bool), x.length = n → V gs x (n + j) = V gs x w := by
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact Or.inl rfl
  · right
    refine ⟨a, hb a (by simp [hin]), fun x hx => ?_⟩
    rw [gate_val_aux gs x hx j g hg hb, hin]
    rcases hop with h | h <;> simp [h, GateOp.eval]
  · right
    rw [hin] at hdeg
    have hab : a = b := by simpa using hdeg
    subst hab
    refine ⟨a, hb a (by simp [hin]), fun x hx => ?_⟩
    rw [gate_val_aux gs x hx j g hg hb, hin]
    rcases hop with h | h <;> simp [h, GateOp.eval]
  · rw [hin] at hlen
    simp at hlen


-- The gate that replaces g when k wires exist.
def T (k : ℕ) (g : Gate) : Gate :=
  if g.op.eval [] = true ∧ g.inputs.any (fun u => decide (k ≤ u)) = true then ⟨GateOp.or, []⟩
  else ⟨g.op, g.inputs.filter (fun u => decide (u < k))⟩

def fix : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => T k g :: fix (k + 1) gs

lemma T_cases (k : ℕ) (g : Gate) :
    T k g = ⟨GateOp.or, []⟩ ∨ T k g = ⟨g.op, g.inputs.filter (fun u => decide (u < k))⟩ := by
  unfold T
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma T_mon (k : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (T k g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (T k g).inputs.length ≤ 2 := by
  rcases T_cases k g with e | e
  · rw [e]; simp
  · rw [e]; exact ⟨h.1, le_trans (List.length_filter_le _ _) h.2⟩

lemma T_back (k : ℕ) (g : Gate) : ∀ u ∈ (T k g).inputs, u < k := by
  intro u hu
  rcases T_cases k g with e | e
  · rw [e] at hu; simp at hu
  · rw [e] at hu
    simp only [List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2

lemma T_val (w : List Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (T w.length g).op.eval ((T w.length g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hbad : ∀ u, w.length ≤ u → w.getD u false = false := fun u hu =>
    List.getD_eq_default _ _ hu
  rcases hop with h | h
  · by_cases hb : g.inputs.any (fun u => decide (w.length ≤ u)) = true
    · have e : T w.length g = ⟨GateOp.or, []⟩ := by simp [T, h, GateOp.eval, hb]
      rw [e, h]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      rw [List.any_eq_true] at hb
      obtain ⟨u, hu, hk⟩ := hb
      exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by rw [hbad u (by simpa using hk)]; simp⟩
    · have e : T w.length g = ⟨g.op, g.inputs.filter (fun u => decide (u < w.length))⟩ := by
        simp [T, hb]
      have hall : g.inputs.filter (fun u => decide (u < w.length)) = g.inputs := by
        rw [List.filter_eq_self]
        intro u hu
        by_contra hk
        exact hb (List.any_eq_true.mpr ⟨u, hu, by simpa using hk⟩)
      rw [e]
      simp only [hall]
  · have e : T w.length g = ⟨g.op, g.inputs.filter (fun u => decide (u < w.length))⟩ := by
      simp [T, h, GateOp.eval]
    rw [e]
    simp only [h, GateOp.eval]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨b, ⟨u, ⟨hu, _⟩, rfl⟩, hb⟩
      exact ⟨_, ⟨u, hu, rfl⟩, hb⟩
    · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
      have hlt : u < w.length := by
        by_contra hk
        rw [hbad u (by omega)] at hb
        simp at hb
      exact ⟨_, ⟨u, ⟨hu, hlt⟩, rfl⟩, hb⟩

lemma fix_wires : ∀ (gs : List Gate) (k : ℕ) (w : List Bool), w.length = k →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    wiresFrom (fix k gs) w = wiresFrom gs w := by
  intro gs
  induction gs with
  | nil => intro k w _ _; rfl
  | cons g gs ih =>
    intro k w hk hops
    subst hk
    have h1 : wiresFrom (fix w.length (g :: gs)) w = wiresFrom (fix (w.length + 1) gs)
        (w ++ [(T w.length g).op.eval ((T w.length g).inputs.map fun i => w.getD i false)]) := rfl
    have h2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h1, h2, T_val w g (hops g (by simp))]
    exact ih _ _ (by simp) (fun g' hg' => hops g' (by simp [hg']))

lemma fix_len : ∀ (gs : List Gate) (k : ℕ), (fix k gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro k; rfl
  | cons g gs ih => intro k; simp [fix, ih]

lemma fix_mon : ∀ (gs : List Gate) (k : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ g' ∈ fix k gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro k _ g' hg'; simp [fix] at hg'
  | cons g gs ih =>
    intro k hm g' hg'
    simp only [fix, List.mem_cons] at hg'
    rcases hg' with rfl | hg'
    · exact T_mon k g (hm g (by simp))
    · exact ih (k + 1) (fun g2 hg2 => hm g2 (by simp [hg2])) g' hg'

lemma fix_back : ∀ (gs : List Gate) (k j : ℕ) (g' : Gate), (fix k gs)[j]? = some g' →
    ∀ u ∈ g'.inputs, u < k + j := by
  intro gs
  induction gs with
  | nil => intro k j g' h; simp [fix] at h
  | cons g gs ih =>
    intro k j g' h u hu
    cases j with
    | zero =>
      simp [fix] at h
      subst h
      exact T_back k g u hu
    | succ j =>
      simp [fix] at h
      have := ih (k + 1) j g' h u hu
      omega


lemma step (n : ℕ) (gs : List Gate) (out : ℕ) (hmon : Mon gs) (hback : Back n gs)
    (x1 x0 : List Bool) (h1 : x1.length = n) (h0 : x0.length = n)
    (hne : V gs x1 out ≠ V gs x0 out)
    (hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ Back n gs' ∧ gs'.length < gs.length ∧
      ∀ (x : List Bool), x.length = n → V gs' x o = V gs x out := by
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hmon g hg).1
  obtain ⟨gj, hmem, hdeg⟩ := hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hgj : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
  rcases shape n gs j gs[j] hgj (hops _ hmem) (hmon _ hmem).2 (hback j _ hgj) hdeg with hin | ⟨w, hw, hv⟩
  · -- a constant gate
    have hc : ∀ (x : List Bool), x.length = n → V gs x (n + j) = gs[j].op.eval [] := by
      intro x hx
      rw [gate_val_aux gs x hx j _ hgj (hback j _ hgj), hin]
      rfl
    have hout : out ≠ n + j := by
      rintro rfl
      exact hne (by rw [hc x1 h1, hc x0 h0])
    refine core n gs out j hj (f2 n j gs[j]) out hout hback ?_ ?_ ?_ (fun _ _ => rfl)
    · intro g hg
      rcases f2_cases n j gs[j] g with e | e | ⟨e, _⟩
      · rw [e]
        exact ⟨(hmon g hg).1, le_trans (List.length_filter_le _ _) (hmon g hg).2⟩
      · rw [e]; exact hmon _ hmem
      · rw [e]; exact hmon g hg
    · intro i g hg u hu
      rcases f2_cases n j gs[j] g with e | e | ⟨e, hn⟩
      · rw [e] at hu
        simp only [List.mem_filter, decide_eq_true_eq] at hu
        exact ⟨hback i g hg u hu.1, hu.2⟩
      · rw [e, hin] at hu
        simp at hu
      · rw [e] at hu
        refine ⟨hback i g hg u hu, ?_⟩
        rintro rfl
        exact hn hu
    · intro x hx i g hg
      exact f2_val n j gs[j] g (V gs x) (hops _ hmem) (hops g (List.mem_of_getElem? hg)) hin (hc x hx)
  · -- a copy of wire w
    refine core n gs out j hj (f1 n j w) (if out = n + j then w else out) ?_ hback ?_ ?_ ?_ ?_
    · split_ifs with h
      · omega
      · exact h
    · intro g hg
      exact ⟨(hmon g hg).1, by simpa [f1] using (hmon g hg).2⟩
    · intro i g hg u hu
      simp only [f1, List.mem_map] at hu
      obtain ⟨v, hv', rfl⟩ := hu
      have := hback i g hg v hv'
      split_ifs with h
      · omega
      · exact ⟨this, h⟩
    · intro x hx i g hg
      simp only [f1, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u _
      simp only [Function.comp]
      split_ifs with h
      · rw [h, hv x hx]
      · rfl
    · intro x hx
      split_ifs with h
      · rw [h, hv x hx]
      · rfl

-- Sorting the two reads of a gate.
def srt (g : Gate) : Gate :=
  ⟨g.op, [min (g.inputs.getD 0 0) (g.inputs.getD 1 0), max (g.inputs.getD 0 0) (g.inputs.getD 1 0)]⟩

lemma srt_val (g : Gate) (a b : ℕ) (hin : g.inputs = [a, b])
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (W : ℕ → Bool) :
    (srt g).op.eval ((srt g).inputs.map W) = g.op.eval (g.inputs.map W) := by
  rcases le_total a b with h | h <;> rcases hop with e | e <;>
    simp [srt, hin, e, GateOp.eval, h, Bool.and_comm, Bool.or_comm]

lemma map_wires (f : Gate → Gate) : ∀ (gs : List Gate) (w : List Bool),
    (∀ g ∈ gs, ∀ W : ℕ → Bool,
      (f g).op.eval ((f g).inputs.map W) = g.op.eval (g.inputs.map W)) →
    wiresFrom (gs.map f) w = wiresFrom gs w := by
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    have h1 : wiresFrom ((g :: gs).map f) w = wiresFrom (gs.map f)
        (w ++ [(f g).op.eval ((f g).inputs.map fun i => w.getD i false)]) := rfl
    have h2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [h1, h2, h g (by simp) (fun i => w.getD i false)]
    exact ih _ (fun g' hg' => h g' (by simp [hg']))

lemma two (g : Gate) (hlen : g.inputs.length ≤ 2)
    (hnd : ¬ (g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0)) :
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b := by
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rw [hin] at hnd; simp at hnd
  · rw [hin] at hnd; simp at hnd
  · rw [hin] at hnd
    exact ⟨a, b, rfl, fun h => hnd (Or.inr (by simpa using h))⟩
  · rw [hin] at hlen; simp at hlen

lemma base (n : ℕ) (gs : List Gate) (out : ℕ) (hmon : Mon gs) (hback : Back n gs)
    (hx : ∃ x1 x0 : List Bool, x1.length = n ∧ x0.length = n ∧ V gs x1 out ≠ V gs x0 out)
    (hnd : ¬ ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ gs'.length ≤ gs.length ∧
      (∀ x : List Bool, x.length = n → V gs' x o = V gs x out) ∧ o < n + gs'.length ∧
      ∀ (j : ℕ) (g' : Gate), gs'[j]? = some g' →
        ∃ a b, g'.inputs = [a, b] ∧ a < b ∧ b < n + j := by
  obtain ⟨x1, x0, h1, h0, hne⟩ := hx
  have htwo : ∀ g ∈ gs, ∃ a b, g.inputs = [a, b] ∧ a ≠ b := fun g hg =>
    two g (hmon g hg).2 (fun h => hnd ⟨g, hg, h⟩)
  have hw : ∀ w : List Bool, wiresFrom (gs.map srt) w = wiresFrom gs w := by
    intro w
    apply map_wires
    intro g hg W
    obtain ⟨a, b, hin, _⟩ := htwo g hg
    exact srt_val g a b hin (by simpa using (hmon g hg).1) W
  have ho : out < n + gs.length := by
    by_contra h
    apply hne
    rw [V_out gs x1 out (by omega), V_out gs x0 out (by omega)]
  refine ⟨gs.map srt, out, ?_, by simp, fun x _ => ?_, by simpa using ho, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨(hmon g hg).1, by simp [srt]⟩
  · unfold V
    rw [hw]
  · intro j g' hj
    simp at hj
    obtain ⟨g, hg, rfl⟩ := hj
    obtain ⟨a, b, hin, hab⟩ := htwo g (List.mem_of_getElem? hg)
    have ha := hback j g hg a (by simp [hin])
    have hb := hback j g hg b (by simp [hin])
    refine ⟨min a b, max a b, by simp [srt, hin], ?_, ?_⟩
    · omega
    · omega

lemma ind (n : ℕ) : ∀ (m : ℕ) (gs : List Gate) (out : ℕ), gs.length ≤ m → Mon gs → Back n gs →
    (∃ x1 x0 : List Bool, x1.length = n ∧ x0.length = n ∧ V gs x1 out ≠ V gs x0 out) →
    ∃ (gs' : List Gate) (o : ℕ), Mon gs' ∧ gs'.length ≤ gs.length ∧
      (∀ x : List Bool, x.length = n → V gs' x o = V gs x out) ∧ o < n + gs'.length ∧
      ∀ (j : ℕ) (g' : Gate), gs'[j]? = some g' →
        ∃ a b, g'.inputs = [a, b] ∧ a < b ∧ b < n + j := by
  intro m
  induction m with
  | zero =>
    intro gs out hm hmon hback hx
    by_cases hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0
    · obtain ⟨x1, x0, h1, h0, hne⟩ := hx
      obtain ⟨gs2, o2, _, _, hl, _⟩ := step n gs out hmon hback x1 x0 h1 h0 hne hd
      omega
    · exact base n gs out hmon hback hx hd
  | succ m ih =>
    intro gs out hm hmon hback hx
    by_cases hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0
    · obtain ⟨x1, x0, h1, h0, hne⟩ := hx
      obtain ⟨gs2, o2, hm2, hb2, hl, hv⟩ := step n gs out hmon hback x1 x0 h1 h0 hne hd
      obtain ⟨gs3, o3, hm3, hl3, hv3, ho3, hf3⟩ := ih gs2 o2 (by omega) hm2 hb2
        ⟨x1, x0, h1, h0, by rw [hv x1 h1, hv x0 h0]; exact hne⟩
      exact ⟨gs3, o3, hm3, by omega, fun x hx' => by rw [hv3 x hx', hv x hx'], ho3, hf3⟩
    · exact base n gs out hmon hback hx hd

lemma top (n : ℕ) (gs : List Gate) (out : ℕ) (hmon : Monotone2 ⟨gs, out⟩) (x y : Fin n → Bool)
    (hxy : circuitFun n ⟨gs, out⟩ x ≠ circuitFun n ⟨gs, out⟩ y) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ Circuit.size ⟨gs, out⟩ ∧
      circuitFun n D = circuitFun n ⟨gs, out⟩ ∧ D.output < n + D.size ∧
      ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
        ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < n + j := by
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    simpa using (hmon g hg).1
  have hfw : ∀ w : List Bool, w.length = n → wiresFrom (fix n gs) w = wiresFrom gs w :=
    fun w hw => fix_wires gs n w hw hops
  have hne : V (fix n gs) (List.ofFn x) out ≠ V (fix n gs) (List.ofFn y) out := by
    unfold V
    rw [hfw _ (by simp), hfw _ (by simp)]
    exact hxy
  obtain ⟨gs', o, hm, hl, hv, ho, hf⟩ := ind n (fix n gs).length (fix n gs) out le_rfl
    (fix_mon gs n hmon) (fix_back gs n) ⟨List.ofFn x, List.ofFn y, by simp, by simp, hne⟩
  refine ⟨⟨gs', o⟩, hm, ?_, ?_, ho, hf⟩
  · have := fix_len gs n
    show gs'.length ≤ gs.length
    omega
  · funext z
    show V gs' (List.ofFn z) o = V gs (List.ofFn z) out
    rw [hv _ (by simp)]
    unfold V
    rw [hfw _ (by simp)]

end PEqualNP.Outside.L_meta_2006

theorem PEqualNP.Outside.L_meta_2006 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x4 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x5) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ x5.output < x1 + x5.size ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → ∃ (x9 : ℕ) (x10 : ℕ), x7.inputs = [x9, x10] ∧ x9 < x10 ∧ x10 < x1 + x6 := by
  intro n C hmon hx
  obtain ⟨gs, out⟩ := C
  obtain ⟨x, y, hxy⟩ := hx
  exact PEqualNP.Outside.L_meta_2006.top n gs out hmon x y hxy
