import Mathlib
import PEqualNP.Defs

-- Deleting a degenerate gate: a copy of a wire or a constant.

namespace PEqualNP.Outside.L_meta_1959

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

lemma gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) :
    V gs x (26 + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (26 + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at 26 pre post g x hx
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

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

-- Wire renaming after the deletion of gate j.
def sg (j : ℕ) (u : ℕ) : ℕ := if 26 + j < u then u - 1 else u

lemma sg_le (j u : ℕ) (h : u ≤ 26 + j) : sg j u = u := by
  have h' : ¬ 26 + j < u := by omega
  simp [sg, h']

lemma sg_gt (j u : ℕ) (h : 26 + j < u) : sg j u = u - 1 := by
  simp [sg, h]

def sh (j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg j)⟩

def del (f : Gate → Gate) (j : ℕ) (gs : List Gate) : List Gate :=
  ((gs.map f).eraseIdx j).map (sh j)

lemma del_get (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hij : i ≠ j) :
    ∃ i', sg j (26 + i) = 26 + i' ∧ (del f j gs)[i']? = some (sh j (f g)) ∧
      ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h : i < j
  · refine ⟨i, sg_le j _ (by omega), ?_, Or.inl ⟨rfl, h⟩⟩
    simp [del, List.getElem?_eraseIdx, h, hg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : ¬ k < j := by omega
    refine ⟨k, ?_, ?_, Or.inr ⟨rfl, by omega⟩⟩
    · rw [sg_gt j _ (by omega)]; omega
    · simp [del, List.getElem?_eraseIdx, hk, hg]

lemma del_inv (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i' : ℕ) (g' : Gate)
    (h : (del f j gs)[i']? = some g') :
    ∃ i g, gs[i]? = some g ∧ g' = sh j (f g) ∧ ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h3 : i' < j
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i', g, hg, rfl, Or.inl ⟨rfl, h3⟩⟩
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i' + 1, g, hg, rfl, Or.inr ⟨rfl, by omega⟩⟩

lemma del_back (f : Gate → Gate) (j : ℕ) (gs : List Gate)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (i' : ℕ) (g' : Gate) (h : (del f j gs)[i']? = some g') :
    ∀ u ∈ g'.inputs, u < 26 + i' := by
  obtain ⟨i, g, hg, rfl, hi⟩ := del_inv f j gs i' g' h
  intro u hu
  simp only [sh, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hfb i g hg v hv
  unfold sg
  split_ifs <;> omega

lemma del_val (f : Gate → Gate) (j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (x : List Bool) (hx : x.length = 26)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (hfv : ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x))) :
    ∀ u, u ≠ 26 + j → V (del f j gs) x (sg j u) = V gs x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    have hlen : (del f j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    by_cases h1 : u < 26
    · rw [sg_le j u (by omega)]
      exact V_in _ _ x u (by omega)
    · obtain ⟨i, rfl⟩ : ∃ i, u = 26 + i := ⟨u - 26, by omega⟩
      have hij : i ≠ j := by omega
      by_cases h2 : i < gs.length
      · have hg : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        obtain ⟨i', hs, hd, _⟩ := del_get f j gs i gs[i] hg hij
        rw [hs, gate_val_aux _ x hx i' _ hd (del_back f j gs hfb i' _ hd),
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

lemma core (gs : List Gate) (out : ℕ) (j : ℕ) (hj : j < gs.length) (f : Gate → Gate) (out' : ℕ)
    (hout : out' ≠ 26 + j)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i)
    (hfm : ∀ g ∈ gs, (f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (f g).inputs.length ≤ 2)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (hfv : ∀ (x : List Bool), x.length = 26 → ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x)))
    (hov : ∀ (x : List Bool), x.length = 26 → V gs x out' = V gs x out) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size < gs.length ∧
      ∀ (x : List Bool), x.length = 26 → D.eval x = Circuit.eval ⟨gs, out⟩ x := by
  refine ⟨⟨del f j gs, sg j out'⟩, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨i', hi'⟩ := List.getElem?_of_mem hg'
    obtain ⟨i, g, hg, rfl, _⟩ := del_inv f j gs i' g' hi'
    have h := hfm g (List.mem_of_getElem? hg)
    exact ⟨h.1, by simpa [sh] using h.2⟩
  · intro i' hi' u hu
    rw [gateAt_eq _ i' hi'] at hu
    exact del_back f j gs hfb i' _ (List.getElem?_eq_getElem hi') u hu
  · show (del f j gs).length < gs.length
    simp [del, List.length_eraseIdx, hj]
    omega
  · intro x hx
    rw [eval_eq, eval_eq, del_val f j gs hj x hx hback hfb (hfv x hx) out' hout, hov x hx]

-- Case one: the gate copies wire w.
def f1 (j w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun u => if u = 26 + j then w else u)⟩

-- Case two: the gate gj is a constant.
def f2 (j : ℕ) (gj g : Gate) : Gate :=
  if g.op.eval [] = gj.op.eval [] then ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩
  else if 26 + j ∈ g.inputs then gj else g

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

lemma f2_val (j : ℕ) (gj g : Gate) (W : ℕ → Bool)
    (hgj : gj.op = GateOp.and ∨ gj.op = GateOp.or) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : gj.inputs = []) (hW : W (26 + j) = gj.op.eval []) :
    (f2 j gj g).op.eval ((f2 j gj g).inputs.map W) = g.op.eval (g.inputs.map W) := by
  rcases hgj with h1 | h1 <;> rcases hg with h2 | h2
  · have hc : W (26 + j) = true := by rw [hW, h1]; rfl
    have e : f2 j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact all_filter W _ hc _
  · have hc : W (26 + j) = true := by rw [hW, h1]; rfl
    by_cases hm : 26 + j ∈ g.inputs
    · have e : f2 j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, hc⟩
    · have e : f2 j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (26 + j) = false := by rw [hW, h1]; rfl
    by_cases hm : 26 + j ∈ g.inputs
    · have e : f2 j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, by simp [hc]⟩
    · have e : f2 j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (26 + j) = false := by rw [hW, h1]; rfl
    have e : f2 j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact any_filter W _ hc _

lemma f2_cases (j : ℕ) (gj g : Gate) :
    f2 j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩ ∨
    f2 j gj g = gj ∨ (f2 j gj g = g ∧ 26 + j ∉ g.inputs) := by
  unfold f2
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rfl, h2⟩)

lemma shape (gs : List Gate) (j : ℕ) (g : Gate) (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hb : ∀ u ∈ g.inputs, u < 26 + j)
    (hdeg : g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    g.inputs = [] ∨ ∃ w, w < 26 + j ∧
      ∀ (x : List Bool), x.length = 26 → V gs x (26 + j) = V gs x w := by
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

lemma main (gs : List Gate) (out : ℕ) (hmon : Monotone2 ⟨gs, out⟩) (hrb : ReadsBack 26 ⟨gs, out⟩)
    (x1 x0 : List Bool) (h1 : x1.length = 26) (h0 : x0.length = 26)
    (ht : Circuit.eval ⟨gs, out⟩ x1 = true) (hf : Circuit.eval ⟨gs, out⟩ x0 = false)
    (hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size < gs.length ∧
      ∀ (x : List Bool), x.length = 26 → D.eval x = Circuit.eval ⟨gs, out⟩ x := by
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hmon g hg).1
  have hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i := by
    intro i g hg u hu
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hg
    have := hrb i hi u
    rw [gateAt_eq _ i hi] at this
    exact this hu
  obtain ⟨gj, hmem, hdeg⟩ := hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hgj : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
  rcases shape gs j gs[j] hgj (hops _ hmem) (hmon _ hmem).2 (hback j _ hgj) hdeg with hin | ⟨w, hw, hv⟩
  · -- a constant gate
    have hc : ∀ (x : List Bool), x.length = 26 → V gs x (26 + j) = gs[j].op.eval [] := by
      intro x hx
      rw [gate_val_aux gs x hx j _ hgj (hback j _ hgj), hin]
      rfl
    have hout : out ≠ 26 + j := by
      rintro rfl
      rw [eval_eq, hc x1 h1] at ht
      rw [eval_eq, hc x0 h0, ht] at hf
      exact Bool.noConfusion hf
    refine core gs out j hj (f2 j gs[j]) out hout hback ?_ ?_ ?_ (fun _ _ => rfl)
    · intro g hg
      rcases f2_cases j gs[j] g with e | e | ⟨e, _⟩
      · rw [e]
        exact ⟨(hmon g hg).1, le_trans (List.length_filter_le _ _) (hmon g hg).2⟩
      · rw [e]; exact hmon _ hmem
      · rw [e]; exact hmon g hg
    · intro i g hg u hu
      rcases f2_cases j gs[j] g with e | e | ⟨e, hn⟩
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
      exact f2_val j gs[j] g (V gs x) (hops _ hmem) (hops g (List.mem_of_getElem? hg)) hin (hc x hx)
  · -- a copy of wire w
    refine core gs out j hj (f1 j w) (if out = 26 + j then w else out) ?_ hback ?_ ?_ ?_ ?_
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

lemma quad : ({0, 1, 2, 5} : Finset (Fin 13)).card = 4 ∧
    ∀ x5 : Fin 13, (({0, 1, 2, 5} : Finset (Fin 13)).filter
      (fun x6 => x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1959

theorem PEqualNP.Outside.L_meta_1959 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∃ x10 ∈ x4.gates, x10.inputs.length < (2 : ℕ) ∨ x10.inputs.getD (0 : ℕ) (0 : ℕ) = x10.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x11 ∧ x2 x11 ∧ x11.size < x4.size := by
  intro x1 x2 x3 C hmon hback hsound _ _ hd
  obtain ⟨gs, out⟩ := C
  have hacc := hsound.1 0 0 (by decide)
  have hrej := hsound.2 {0, 1, 2, 5} PEqualNP.Outside.L_meta_1959.quad.1
    PEqualNP.Outside.L_meta_1959.quad.2
  obtain ⟨D, hD1, hD2, hD3, hD4⟩ := PEqualNP.Outside.L_meta_1959.main gs out hmon hback _ _
    (by simp) (by simp) hacc hrej hd
  refine ⟨D, hD1, hD2, ⟨?_, ?_⟩, hD3⟩
  · intro p l hpl
    rw [hD4 _ (by simp)]
    exact hsound.1 p l hpl
  · intro Q hc hk
    rw [hD4 _ (by simp)]
    exact hsound.2 Q hc hk
