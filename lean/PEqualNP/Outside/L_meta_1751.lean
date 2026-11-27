import Mathlib
import PEqualNP.Defs

-- No AND below an AND: bridge to the tagged two-level count.

namespace PEqualNP.Outside.L_meta_1751

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

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

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
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

theorem eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

theorem V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

theorem gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
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

theorem gate_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : Fin gs.length)
    (hw : ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ)) :
    V gs x (26 + (i : ℕ)) = (gs.get i).op.eval ((gs.get i).inputs.map (V gs x)) :=
  gate_val_aux gs x hx i (gs.get i) (by simp) hw

theorem or_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : Fin gs.length)
    (hw : ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ)) (hop : (gs.get i).op = GateOp.or) :
    V gs x (26 + (i : ℕ)) = true ↔ ∃ w ∈ (gs.get i).inputs, V gs x w = true := by
  rw [gate_val gs x hx i hw, hop]
  simp [GateOp.eval]

-- The input with the points of S and the lines of R switched on.
def inp (S R : Finset (Fin 13)) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u ∈ S)) ++ List.ofFn (fun v : Fin 13 => decide (v ∈ R))

theorem inp_len (S R : Finset (Fin 13)) : (inp S R).length = 26 := by
  simp [inp]

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : ℕ) (h : j < m) :
    (List.ofFn F).getD j d = F ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem V_point (gs : List Gate) (S R : Finset (Fin 13)) (w : ℕ) (h : w < 13) :
    V gs (inp S R) w = decide ((⟨w, h⟩ : Fin 13) ∈ S) := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by rw [inp_len]; omega)]
  unfold inp
  rw [List.getD_append _ _ _ _ (by simp; exact h)]
  exact getD_ofFn 13 _ false w h

theorem V_line (gs : List Gate) (S R : Finset (Fin 13)) (w : ℕ) (h1 : 13 ≤ w) (h2 : w < 26) :
    V gs (inp S R) w = decide ((⟨w - 13, by omega⟩ : Fin 13) ∈ R) := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by rw [inp_len]; omega)]
  unfold inp
  rw [List.getD_append_right _ _ _ _ (by simp; exact h1)]
  simp only [List.length_ofFn]
  exact getD_ofFn 13 _ false (w - 13) (by omega)

theorem orP (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0)) :
    ∀ w : ℕ, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0) →
      ∀ S R : Finset (Fin 13),
        (V gs (inp S R) w = true ↔ ∃ p ∈ S, V gs (inp {p} ∅) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP S R
    rcases hP with h | ⟨j, rfl, hj⟩
    · rw [V_point gs S R w h]
      constructor
      · intro hm
        exact ⟨⟨w, h⟩, by simpa using hm, by rw [V_point gs _ _ w h]; simp⟩
      · rintro ⟨p, hp, hv⟩
        rw [V_point gs _ _ w h] at hv
        simp at hv
        rw [hv]
        simpa using hp
    · obtain ⟨hop, hin⟩ := h0 j hj
      rw [or_val gs _ (inp_len S R) j (hwire j) hop]
      constructor
      · rintro ⟨w', hw', hv⟩
        obtain ⟨p, hp, hv'⟩ := (ih w' (hwire j w' hw') (hin w' hw') S R).1 hv
        exact ⟨p, hp, (or_val gs _ (inp_len _ _) j (hwire j) hop).2 ⟨w', hw', hv'⟩⟩
      · rintro ⟨p, hp, hv⟩
        obtain ⟨w', hw', hv'⟩ := (or_val gs _ (inp_len _ _) j (hwire j) hop).1 hv
        exact ⟨w', hw', (ih w' (hwire j w' hw') (hin w' hw') S R).2 ⟨p, hp, hv'⟩⟩

theorem orL (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1)) :
    ∀ w : ℕ, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1) →
      ∀ S R : Finset (Fin 13),
        (V gs (inp S R) w = true ↔ ∃ l ∈ R, V gs (inp ∅ {l}) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP S R
    rcases hP with h | ⟨j, rfl, hj⟩
    · rw [V_line gs S R w h.1 h.2]
      constructor
      · intro hm
        exact ⟨⟨w - 13, by omega⟩, by simpa using hm, by rw [V_line gs _ _ w h.1 h.2]; simp⟩
      · rintro ⟨p, hp, hv⟩
        rw [V_line gs _ _ w h.1 h.2] at hv
        simp at hv
        rw [hv]
        simpa using hp
    · obtain ⟨hop, hin⟩ := h1 j hj
      rw [or_val gs _ (inp_len S R) j (hwire j) hop]
      constructor
      · rintro ⟨w', hw', hv⟩
        obtain ⟨p, hp, hv'⟩ := (ih w' (hwire j w' hw') (hin w' hw') S R).1 hv
        exact ⟨p, hp, (or_val gs _ (inp_len _ _) j (hwire j) hop).2 ⟨w', hw', hv'⟩⟩
      · rintro ⟨p, hp, hv⟩
        obtain ⟨w', hw', hv'⟩ := (or_val gs _ (inp_len _ _) j (hwire j) hop).1 hv
        exact ⟨w', hw', (ih w' (hwire j w' hw') (hin w' hw') S R).2 ⟨p, hp, hv'⟩⟩

-- The points, and the lines, that switch a wire on alone.
def PSw (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => V gs (inp {p} ∅) w = true)

def LSw (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => V gs (inp ∅ {l}) w = true)

theorem PSw_input (gs : List Gate) (w : ℕ) (h : w < 13) : (PSw gs w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [PSw, Finset.mem_filter, Finset.mem_univ, true_and, V_point gs _ _ w h] at ha hb
  simp at ha hb
  rw [← ha, ← hb]

theorem LSw_input (gs : List Gate) (w : ℕ) (h1 : 13 ≤ w) (h2 : w < 26) : (LSw gs w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [LSw, Finset.mem_filter, Finset.mem_univ, true_and, V_line gs _ _ w h1 h2] at ha hb
  simp at ha hb
  rw [← ha, ← hb]

-- Abstract OR gates: the set of a gate is the union of at most two pieces.
def Piece {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (i : Fin N)
    (X : Finset (Fin 13)) : Prop :=
  X.card ≤ 1 ∨ ∃ j, j < i ∧ K j ∧ S j = X

def Built {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) : Prop :=
  ∀ i, K i → ∃ X Y, Piece K S i X ∧ Piece K S i Y ∧ S i = X ∪ Y

theorem split {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) = n → K i → 2 ≤ (S i).card →
      ∃ X Y : Finset (Fin 13), S i = X ∪ Y ∧ X ≠ S i ∧ Y ≠ S i ∧
        (X.card ≤ 1 ∨ ∃ j, K j ∧ S j = X) ∧ (Y.card ≤ 1 ∨ ∃ j, K j ∧ S j = Y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hK h2
    obtain ⟨X, Y, hX, hY, hXY⟩ := hB i hK
    by_cases hXe : X = S i
    · rcases hX with hX | ⟨j, hji, hKj, hSj⟩
      · rw [hXe] at hX; omega
      · have hSji : S j = S i := by rw [hSj, hXe]
        have := ih j (by rw [← hi]; exact hji) j rfl hKj (by rw [hSji]; exact h2)
        rw [hSji] at this
        exact this
    · by_cases hYe : Y = S i
      · rcases hY with hY | ⟨j, hji, hKj, hSj⟩
        · rw [hYe] at hY; omega
        · have hSji : S j = S i := by rw [hSj, hYe]
          have := ih j (by rw [← hi]; exact hji) j rfl hKj (by rw [hSji]; exact h2)
          rw [hSji] at this
          exact this
      · refine ⟨X, Y, hXY, hXe, hYe, ?_, ?_⟩
        · rcases hX with hX | ⟨j, _, hKj, hSj⟩
          · exact Or.inl hX
          · exact Or.inr ⟨j, hKj, hSj⟩
        · rcases hY with hY | ⟨j, _, hKj, hSj⟩
          · exact Or.inl hY
          · exact Or.inr ⟨j, hKj, hSj⟩

theorem card_lt_of_ne {X Z : Finset (Fin 13)} (h : X ⊆ Z) (hne : X ≠ Z) : X.card < Z.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩)

theorem cnt3 {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (i : Fin N) (hK : K i) (h3 : (S i).card = 3) :
    ∃ j, K j ∧ (S j).card = 2 ∧ S j ⊆ S i := by
  obtain ⟨X, Y, hXY, hXe, hYe, hX, hY⟩ := split K S hB i i rfl hK (by omega)
  have hXs : X ⊆ S i := by rw [hXY]; exact Finset.subset_union_left
  have hYs : Y ⊆ S i := by rw [hXY]; exact Finset.subset_union_right
  have hXc := card_lt_of_ne hXs hXe
  have hYc := card_lt_of_ne hYs hYe
  have hu : (S i).card ≤ X.card + Y.card := by rw [hXY]; exact Finset.card_union_le X Y
  by_cases hX2 : X.card = 2
  · rcases hX with hX | ⟨j, hKj, hSj⟩
    · omega
    · exact ⟨j, hKj, by rw [hSj]; exact hX2, by rw [hSj]; exact hXs⟩
  · have hY2 : Y.card = 2 := by omega
    rcases hY with hY | ⟨j, hKj, hSj⟩
    · omega
    · exact ⟨j, hKj, by rw [hSj]; exact hY2, by rw [hSj]; exact hYs⟩

theorem cnt {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (i : Fin N) (hK : K i) (h2 : 2 ≤ (S i).card) (h4 : (S i).card ≤ 4) :
    ∃ O' : Finset (Fin N), (∀ j ∈ O', K j ∧ 2 ≤ (S j).card ∧ S j ⊆ S i) ∧
      (S i).card ≤ O'.card + 1 := by
  classical
  obtain h | h | h : (S i).card = 2 ∨ (S i).card = 3 ∨ (S i).card = 4 := by omega
  · refine ⟨{i}, ?_, by simp; omega⟩
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨hK, h2, Finset.Subset.refl _⟩
  · obtain ⟨j, hKj, hj2, hjs⟩ := cnt3 K S hB i hK h
    have hne : i ≠ j := by intro e; rw [e] at h; omega
    refine ⟨{i, j}, ?_, by rw [Finset.card_pair hne]; omega⟩
    intro m hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨hK, h2, Finset.Subset.refl _⟩
    · exact ⟨hKj, by omega, hjs⟩
  · obtain ⟨X, Y, hXY, hXe, hYe, hX, hY⟩ := split K S hB i i rfl hK (by omega)
    have hXs : X ⊆ S i := by rw [hXY]; exact Finset.subset_union_left
    have hYs : Y ⊆ S i := by rw [hXY]; exact Finset.subset_union_right
    have hXc := card_lt_of_ne hXs hXe
    have hYc := card_lt_of_ne hYs hYe
    have hu : (S i).card ≤ X.card + Y.card := by rw [hXY]; exact Finset.card_union_le X Y
    have three : ∀ Z : Finset (Fin 13), Z ⊆ S i → Z.card = 3 → (Z.card ≤ 1 ∨ ∃ j, K j ∧ S j = Z) →
        ∃ O' : Finset (Fin N), (∀ j ∈ O', K j ∧ 2 ≤ (S j).card ∧ S j ⊆ S i) ∧
          (S i).card ≤ O'.card + 1 := by
      intro Z hZs hZ3 hZ
      rcases hZ with hZ | ⟨j, hKj, hSj⟩
      · omega
      · obtain ⟨j', hKj', hj'2, hj's⟩ := cnt3 K S hB j hKj (by rw [hSj]; exact hZ3)
        have hj3 : (S j).card = 3 := by rw [hSj]; exact hZ3
        have e1 : i ≠ j := by intro e; rw [e] at h; omega
        have e2 : i ≠ j' := by intro e; rw [e] at h; omega
        have e3 : j ≠ j' := by intro e; rw [e] at hj3; omega
        refine ⟨{i, j, j'}, ?_, ?_⟩
        · intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl
          · exact ⟨hK, h2, Finset.Subset.refl _⟩
          · exact ⟨hKj, by omega, by rw [hSj]; exact hZs⟩
          · exact ⟨hKj', by omega, fun x hx => hZs (hSj ▸ hj's hx)⟩
        · have : ({i, j, j'} : Finset (Fin N)).card = 3 :=
            Finset.card_eq_three.2 ⟨i, j, j', e1, e2, e3, rfl⟩
          omega
    by_cases hX3 : X.card = 3
    · exact three X hXs hX3 hX
    · by_cases hY3 : Y.card = 3
      · exact three Y hYs hY3 hY
      · have hX2 : X.card = 2 := by omega
        have hY2 : Y.card = 2 := by omega
        rcases hX with hX | ⟨j1, hK1, hS1⟩
        · omega
        · rcases hY with hY | ⟨j2, hK2, hS2⟩
          · omega
          · have e1 : i ≠ j1 := by intro e; rw [e, hS1] at h; omega
            have e2 : i ≠ j2 := by intro e; rw [e, hS2] at h; omega
            have e3 : j1 ≠ j2 := by
              intro e
              have hXYe : X = Y := by rw [← hS1, ← hS2, e]
              rw [hXY, hXYe, Finset.union_self] at h
              omega
            refine ⟨{i, j1, j2}, ?_, ?_⟩
            · intro m hm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact ⟨hK, h2, Finset.Subset.refl _⟩
              · exact ⟨hK1, by rw [hS1]; omega, by rw [hS1]; exact hXs⟩
              · exact ⟨hK2, by rw [hS2]; omega, by rw [hS2]; exact hYs⟩
            · have : ({i, j1, j2} : Finset (Fin N)).card = 3 :=
                Finset.card_eq_three.2 ⟨i, j1, j2, e1, e2, e3, rfl⟩
              omega

theorem arith (u k m : ℕ) (h4 : u ≤ 4) (hs : u ≤ k * (m + 1)) : 5 * u ≤ 4 * m + 8 * k := by
  obtain hk | hk | hk | hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · subst hk; omega
  · subst hk; omega
  · subst hk; omega
  · omega

theorem group_bound {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (Lg : Finset (Fin 13)) (hL : Lg.card ≤ 4)
    (Tg : Finset (Fin N)) (Bs : Fin N → Finset (Fin 13)) (hsub : ∀ j ∈ Tg, Bs j ⊆ Lg)
    (hgate : ∀ j ∈ Tg, 2 ≤ (Bs j).card → ∃ i, K i ∧ S i = Bs j)
    (Og : Finset (Fin N)) (hOg : ∀ i, K i → 2 ≤ (S i).card → S i ⊆ Lg → i ∈ Og) :
    5 * (Tg.biUnion Bs).card ≤ 4 * Og.card + 8 * Tg.card := by
  have hu : (Tg.biUnion Bs).card ≤ 4 :=
    le_trans (Finset.card_le_card (Finset.biUnion_subset.2 hsub)) hL
  have hj : ∀ j ∈ Tg, (Bs j).card ≤ Og.card + 1 := by
    intro j hjT
    by_cases h2 : 2 ≤ (Bs j).card
    · obtain ⟨i, hKi, hSi⟩ := hgate j hjT h2
      have h4 : (S i).card ≤ 4 := by
        rw [hSi]; exact le_trans (Finset.card_le_card (hsub j hjT)) hL
      obtain ⟨O', hO', hc⟩ := cnt K S hB i hKi (by rw [hSi]; exact h2) h4
      have hsubO : O' ⊆ Og := fun j' hj' => hOg j' (hO' j' hj').1 (hO' j' hj').2.1
        (fun x hx => hsub j hjT (hSi ▸ (hO' j' hj').2.2 hx))
      have hcc := Finset.card_le_card hsubO
      rw [hSi] at hc
      omega
    · omega
  have hs : (Tg.biUnion Bs).card ≤ Tg.card * (Og.card + 1) := by
    calc (Tg.biUnion Bs).card ≤ ∑ j ∈ Tg, (Bs j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Tg, (Og.card + 1) := Finset.sum_le_sum hj
      _ = Tg.card * (Og.card + 1) := by simp
  exact arith _ _ _ hu hs

-- Reachability among the top gates: m feeds the top OR gate i.
def E (gs : List Gate) (kind : Fin gs.length → Fin 4) (m i : Fin gs.length) : Prop :=
  kind i = 3 ∧ 26 + (m : ℕ) ∈ (gs.get i).inputs

theorem up (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or)
    (x : List Bool) (hx : x.length = 26) (j i : Fin gs.length)
    (hr : Relation.ReflTransGen (E gs kind) j i) (hv : V gs x (26 + (j : ℕ)) = true) :
    V gs x (26 + (i : ℕ)) = true := by
  induction hr with
  | refl => exact hv
  | tail _ hE ih => exact (or_val gs x hx _ (hwire _) (h3 _ hE.1)).2 ⟨_, hE.2, ih⟩

theorem down (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))
    (x : List Bool) (hx : x.length = 26) :
    ∀ (n : ℕ) (i : Fin gs.length), (i : ℕ) = n → (kind i = 2 ∨ kind i = 3) →
      V gs x (26 + (i : ℕ)) = true →
      ∃ j, kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j i ∧ V gs x (26 + (j : ℕ)) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hk hv
    rcases hk with hk | hk
    · exact ⟨i, hk, Relation.ReflTransGen.refl, hv⟩
    · obtain ⟨hop, hin⟩ := h3 i hk
      obtain ⟨w, hw, hvw⟩ := (or_val gs x hx i (hwire i) hop).1 hv
      obtain ⟨m, rfl, hkm⟩ := hin w hw
      have hlt := hwire i _ hw
      obtain ⟨j, hj, hr, hvj⟩ := ih m (by omega) m rfl hkm hvw
      exact ⟨j, hj, hr.tail ⟨hk, hw⟩, hvj⟩

theorem reach_two (gs : List Gate) (kind : Fin gs.length → Fin 4) (j i : Fin gs.length)
    (hi : kind i = 2) (hr : Relation.ReflTransGen (E gs kind) j i) : j = i := by
  cases hr with
  | refl => rfl
  | tail _ hE =>
    have h := hE.1
    rw [hi] at h
    exact absurd h (by decide)

theorem reach_three (gs : List Gate) (kind : Fin gs.length → Fin 4) (j i : Fin gs.length)
    (hj : kind j = 2) (hi : kind i = 3) (hr : Relation.ReflTransGen (E gs kind) j i) :
    ∃ m : Fin gs.length, 26 + (m : ℕ) ∈ (gs.get i).inputs ∧ Relation.ReflTransGen (E gs kind) j m := by
  cases hr with
  | refl =>
    rw [hj] at hi
    exact absurd hi (by decide)
  | tail hr' hE => exact ⟨_, hE.2, hr'⟩

-- The terms below a set I of top gates number at most |I| plus the top OR gates.
theorem count (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 →
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3)) :
    ∀ (k : ℕ) (I U : Finset (Fin gs.length)), (∀ i ∈ I, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3)) →
      (∀ j ∈ U, kind j = 2 ∧ ∃ i ∈ I, Relation.ReflTransGen (E gs kind) j i) →
      U.card ≤ I.card +
        (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card := by
  intro k
  induction k with
  | zero =>
    intro I U hI hU
    have hUe : U = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨_, i, hi, _⟩ := hU j hj
      exact absurd (hI i hi).1 (by omega)
    simp [hUe]
  | succ k ih =>
    intro I U hI hU
    have hmono : (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card
        ≤ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).card := by
      apply Finset.card_le_card
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1, by omega⟩
    by_cases hex : ∃ i0 ∈ I, (i0 : ℕ) = k
    · obtain ⟨i0, hi0, hi0k⟩ := hex
      have hIpos : 1 ≤ I.card := Finset.card_pos.2 ⟨i0, hi0⟩
      have hIe : (I.erase i0).card = I.card - 1 := Finset.card_erase_of_mem hi0
      have herase : ∀ i ∈ I.erase i0, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
        intro i hi
        obtain ⟨hne, hiI⟩ := Finset.mem_erase.1 hi
        have h1 := (hI i hiI).1
        have h2 : (i : ℕ) ≠ k := by
          intro e
          exact hne (Fin.ext (by omega))
        exact ⟨by omega, (hI i hiI).2⟩
      rcases (hI i0 hi0).2 with hk2 | hk3
      · have hU' : ∀ j ∈ U.erase i0, kind j = 2 ∧
            ∃ i ∈ I.erase i0, Relation.ReflTransGen (E gs kind) j i := by
          intro j hj
          obtain ⟨hne, hjU⟩ := Finset.mem_erase.1 hj
          obtain ⟨hj2, i, hiI, hr⟩ := hU j hjU
          refine ⟨hj2, i, Finset.mem_erase.2 ⟨?_, hiI⟩, hr⟩
          intro e
          subst e
          exact hne (reach_two gs kind j i hk2 hr)
        have h := ih (I.erase i0) (U.erase i0) herase hU'
        have hUc : U.card - 1 ≤ (U.erase i0).card := Finset.pred_card_le_card_erase
        omega
      · let J : Finset (Fin gs.length) :=
          Finset.univ.filter (fun m : Fin gs.length => 26 + (m : ℕ) ∈ (gs.get i0).inputs)
        have hJmem : ∀ m, m ∈ J ↔ 26 + (m : ℕ) ∈ (gs.get i0).inputs := by
          intro m
          simp [J]
        have hJc : J.card ≤ 2 := by
          have himg : (J.image (fun m : Fin gs.length => 26 + (m : ℕ))).card = J.card := by
            apply Finset.card_image_of_injective
            intro a b hab
            exact Fin.ext (by simpa using hab)
          have hsub : J.image (fun m : Fin gs.length => 26 + (m : ℕ)) ⊆ (gs.get i0).inputs.toFinset := by
            intro w hw
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hw
            exact List.mem_toFinset.2 ((hJmem m).1 hm)
          have h1 := Finset.card_le_card hsub
          have h2 := List.toFinset_card_le (gs.get i0).inputs
          have h3' := hlen i0
          omega
        have hI' : ∀ i ∈ I.erase i0 ∪ J, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact herase i hi
          · have hin := (hJmem i).1 hi
            have hlt := hwire i0 _ hin
            obtain ⟨j, hj, hkj⟩ := h3 i0 hk3 _ hin
            have hji : j = i := Fin.ext (by omega)
            subst hji
            exact ⟨by omega, hkj⟩
        have hU' : ∀ j ∈ U, kind j = 2 ∧
            ∃ i ∈ I.erase i0 ∪ J, Relation.ReflTransGen (E gs kind) j i := by
          intro j hjU
          obtain ⟨hj2, i, hiI, hr⟩ := hU j hjU
          by_cases e : i = i0
          · subst e
            obtain ⟨m, hm, hr'⟩ := reach_three gs kind j i hj2 hk3 hr
            exact ⟨hj2, m, Finset.mem_union_right _ ((hJmem m).2 hm), hr'⟩
          · exact ⟨hj2, i, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hiI⟩), hr⟩
        have h := ih (I.erase i0 ∪ J) U hI' hU'
        have hcu := Finset.card_union_le (I.erase i0) J
        have hstep : (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card + 1
            ≤ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).card := by
          have hmem : i0 ∈ Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hk3, by omega⟩
          have hsub : Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)
              ⊆ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).erase i0 := by
            intro m hm
            rw [Finset.mem_filter] at hm
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hm.1, hm.2.1, by omega⟩⟩
            intro e
            subst e
            omega
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_add_one hmem
          omega
        omega
    · have hI' : ∀ i ∈ I, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
        intro i hi
        have h1 := (hI i hi).1
        have h2 : (i : ℕ) ≠ k := fun e => hex ⟨i, hi, e⟩
        exact ⟨by omega, (hI i hi).2⟩
      have h := ih I U hI' hU
      omega

-- The plane: p lies on l when p - l is in the difference set.
def Lp (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def Pl (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def TQ (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun v : Fin 13 => ∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))

def Q0 (d : Fin 13) : Finset (Fin 13) :=
  if d = 4 ∨ d = 5 ∨ d = 6 then {2, 4, 5, 6} else if d = 7 ∨ d = 8 then {2, 4, 7, 8} else {2, 10, 11, 12}

def Qf (p l : Fin 13) : Finset (Fin 13) := (Q0 (p - l)).image (fun q => q + l)

theorem geo_quad : ∀ p l : Fin 13, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (Qf p l).card = 4 ∧
    (∀ k : Fin 13, ((Qf p l).filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qf p l ∧ l ∈ TQ (Qf p l) := by
  decide +kernel

theorem geo_lines : ∀ p p' : Fin 13, p ≠ p' → (Lp p ∩ Lp p').card ≤ 1 := by
  decide +kernel

theorem geo_points : ∀ l l' : Fin 13, l ≠ l' → (Pl l ∩ Pl l').card ≤ 1 := by
  decide +kernel

theorem geo_Lp : ∀ p : Fin 13, (Lp p).card = 4 := by
  decide +kernel

theorem geo_Pl : ∀ l : Fin 13, (Pl l).card = 4 := by
  decide +kernel

theorem builtL (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1)) :
    Built (fun i : Fin gs.length => kind i = 1) (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) := by
  intro i hi
  obtain ⟨hop, hin⟩ := h1 i hi
  have hpiece : ∀ w ∈ (gs.get i).inputs, Piece (fun i : Fin gs.length => kind i = 1)
      (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) i (LSw gs w) := by
    intro w hw
    rcases hin w hw with h | ⟨j, rfl, hj⟩
    · exact Or.inl (LSw_input gs w h.1 h.2)
    · have hlt := hwire i _ hw
      exact Or.inr ⟨j, Fin.lt_def.2 (by omega), hj, rfl⟩
  have hmem : ∀ l, l ∈ LSw gs (26 + (i : ℕ)) ↔ ∃ w ∈ (gs.get i).inputs, l ∈ LSw gs w := by
    intro l
    simp only [LSw, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_val gs _ (inp_len _ _) i (hwire i) hop
  have hl := hlen i
  rcases hgi : (gs.get i).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨LSw gs a, ∅, hpiece a (by rw [hgi]; simp), Or.inl (by simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨LSw gs a, LSw gs b, hpiece a (by rw [hgi]; simp), hpiece b (by rw [hgi]; simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · rw [hgi] at hl
    simp at hl

theorem builtP (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0)) :
    Built (fun i : Fin gs.length => kind i = 0) (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) := by
  intro i hi
  obtain ⟨hop, hin⟩ := h0 i hi
  have hpiece : ∀ w ∈ (gs.get i).inputs, Piece (fun i : Fin gs.length => kind i = 0)
      (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) i (PSw gs w) := by
    intro w hw
    rcases hin w hw with h | ⟨j, rfl, hj⟩
    · exact Or.inl (PSw_input gs w h)
    · have hlt := hwire i _ hw
      exact Or.inr ⟨j, Fin.lt_def.2 (by omega), hj, rfl⟩
  have hmem : ∀ l, l ∈ PSw gs (26 + (i : ℕ)) ↔ ∃ w ∈ (gs.get i).inputs, l ∈ PSw gs w := by
    intro l
    simp only [PSw, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_val gs _ (inp_len _ _) i (hwire i) hop
  have hl := hlen i
  rcases hgi : (gs.get i).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨PSw gs a, ∅, hpiece a (by rw [hgi]; simp), Or.inl (by simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨PSw gs a, PSw gs b, hpiece a (by rw [hgi]; simp), hpiece b (by rw [hgi]; simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · rw [hgi] at hl
    simp at hl

-- A term is switched on exactly by a point of A together with a line of B.
theorem term_sets (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1))
    (h2 : ∀ i : Fin gs.length, kind i = 2 → (gs.get i).op = GateOp.and ∧
      ∃ a b : ℕ, ((gs.get i).inputs = [a, b] ∨ (gs.get i).inputs = [b, a]) ∧
        (a < 13 ∨ ∃ j : Fin gs.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧
        ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gs.length, b = 26 + (j : ℕ) ∧ kind j = 1))
    (i : Fin gs.length) (hi : kind i = 2) :
    ∃ A B : Finset (Fin 13),
      (∀ S R : Finset (Fin 13), V gs (inp S R) (26 + (i : ℕ)) = true ↔
        (∃ p ∈ S, p ∈ A) ∧ (∃ l ∈ R, l ∈ B)) ∧
      (2 ≤ A.card → ∃ j : Fin gs.length, kind j = 0 ∧ PSw gs (26 + (j : ℕ)) = A) ∧
      (2 ≤ B.card → ∃ j : Fin gs.length, kind j = 1 ∧ LSw gs (26 + (j : ℕ)) = B) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := h2 i hi
  refine ⟨PSw gs a, LSw gs b, ?_, ?_, ?_⟩
  · intro S R
    have hv : V gs (inp S R) (26 + (i : ℕ)) = true ↔
        V gs (inp S R) a = true ∧ V gs (inp S R) b = true := by
      rw [gate_val gs _ (inp_len S R) i (hwire i), hop]
      rcases hin with hin | hin
      · rw [hin]; simp [GateOp.eval]
      · rw [hin]; simp [GateOp.eval, and_comm]
    rw [hv, orP gs kind hwire h0 a ha S R, orL gs kind hwire h1 b hb S R]
    simp [PSw, LSw]
  · intro hc
    rcases ha with h | ⟨j, rfl, hj⟩
    · have := PSw_input gs a h
      omega
    · exact ⟨j, hj, rfl⟩
  · intro hc
    rcases hb with h | ⟨j, rfl, hj⟩
    · have := LSw_input gs b h.1 h.2
      omega
    · exact ⟨j, hj, rfl⟩

theorem dbl {α β : Type} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a ∈ s, (t.filter (r a)).card = ∑ b ∈ t, (s.filter (fun a => r a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem main (gs : List Gate) (kind : Fin gs.length → Fin 4) (jo : Fin gs.length)
    (hop : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1))
    (h2 : ∀ i : Fin gs.length, kind i = 2 → (gs.get i).op = GateOp.and ∧
      ∃ a b : ℕ, ((gs.get i).inputs = [a, b] ∨ (gs.get i).inputs = [b, a]) ∧
        (a < 13 ∨ ∃ j : Fin gs.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧
        ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gs.length, b = 26 + (j : ℕ) ∧ kind j = 1))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))
    (hjo : kind jo = 2 ∨ kind jo = 3)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) (26 + (jo : ℕ)) = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      V gs (inp Q (TQ Q)) (26 + (jo : ℕ)) = false) :
    64 ≤ gs.length := by
  classical
  have hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2 :=
    fun i => (hop _ (List.get_mem gs i)).2
  have h3op : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or := fun i hi => (h3 i hi).1
  have hts : ∀ i : Fin gs.length, ∃ A B : Finset (Fin 13), kind i = 2 →
      ((∀ S R : Finset (Fin 13), V gs (inp S R) (26 + (i : ℕ)) = true ↔
        (∃ p ∈ S, p ∈ A) ∧ (∃ l ∈ R, l ∈ B)) ∧
      (2 ≤ A.card → ∃ j : Fin gs.length, kind j = 0 ∧ PSw gs (26 + (j : ℕ)) = A) ∧
      (2 ≤ B.card → ∃ j : Fin gs.length, kind j = 1 ∧ LSw gs (26 + (j : ℕ)) = B)) := by
    intro i
    by_cases hi : kind i = 2
    · obtain ⟨A, B, h⟩ := term_sets gs kind hwire h0 h1 h2 i hi
      exact ⟨A, B, fun _ => h⟩
    · exact ⟨∅, ∅, fun h => absurd h hi⟩
  choose A B hAB using hts
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (Fin gs.length),
      ∀ j, j ∈ T ↔ (kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j jo) :=
    ⟨Finset.univ.filter (fun j => kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j jo), by simp⟩
  have hcov : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      ∃ j ∈ T, p ∈ A j ∧ l ∈ B j := by
    intro p l hpl
    obtain ⟨j, hj, hr, hv⟩ := down gs kind hwire h3 _ (inp_len _ _) jo jo rfl hjo (hacc p l hpl)
    obtain ⟨⟨p', hp', hpA⟩, ⟨l', hl', hlB⟩⟩ := ((hAB j hj).1 {p} {l}).1 hv
    rw [Finset.mem_singleton] at hp' hl'
    subst hp'
    subst hl'
    exact ⟨j, (hTmem j).2 ⟨hj, hr⟩, hpA, hlB⟩
  have hinc : ∀ j ∈ T, ∀ p ∈ A j, ∀ l ∈ B j, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro j hjT p hp l hl
    obtain ⟨hj, hr⟩ := (hTmem j).1 hjT
    by_contra hn
    obtain ⟨hc, hk, hpQ, hlQ⟩ := geo_quad p l hn
    have hv : V gs (inp (Qf p l) (TQ (Qf p l))) (26 + (j : ℕ)) = true :=
      ((hAB j hj).1 _ _).2 ⟨⟨p, hpQ, hp⟩, ⟨l, hlQ, hl⟩⟩
    have hup := up gs kind hwire h3op _ (inp_len _ _) j jo hr hv
    rw [hrej _ hc hk] at hup
    exact absurd hup (by simp)
  have hBsing : ∀ j ∈ T, 2 ≤ (A j).card → ∀ l ∈ B j, B j = {l} := by
    intro j hjT hc l hl
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hl, ?_⟩
    intro l' hl'
    by_contra hne
    have hsub : A j ⊆ Pl l' ∩ Pl l := by
      intro p hp
      simp only [Finset.mem_inter, Pl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hinc j hjT p hp l' hl', hinc j hjT p hp l hl⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := geo_points l' l hne
    omega
  have hAsing : ∀ j : Fin gs.length, ¬ 2 ≤ (A j).card → ∀ p ∈ A j, A j = {p} := by
    intro j hc p hp
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hp, ?_⟩
    intro p' hp'
    exact Finset.card_le_one.1 (by omega) p' hp' p hp
  obtain ⟨Tp, hTp⟩ : ∃ Tp : Fin 13 → Finset (Fin gs.length),
      ∀ p j, j ∈ Tp p ↔ (j ∈ T ∧ A j = {p}) :=
    ⟨fun p => T.filter (fun j => A j = {p}), by simp⟩
  obtain ⟨Tl, hTl⟩ : ∃ Tl : Fin 13 → Finset (Fin gs.length),
      ∀ l j, j ∈ Tl l ↔ (j ∈ T ∧ 2 ≤ (A j).card ∧ B j = {l}) :=
    ⟨fun l => T.filter (fun j => 2 ≤ (A j).card ∧ B j = {l}), by simp⟩
  obtain ⟨Op, hOp⟩ : ∃ Op : Fin 13 → Finset (Fin gs.length),
      ∀ p i, i ∈ Op p ↔ (kind i = 1 ∧ 2 ≤ (LSw gs (26 + (i : ℕ))).card ∧ LSw gs (26 + (i : ℕ)) ⊆ Lp p) :=
    ⟨fun p => Finset.univ.filter (fun i : Fin gs.length =>
      kind i = 1 ∧ 2 ≤ (LSw gs (26 + (i : ℕ))).card ∧ LSw gs (26 + (i : ℕ)) ⊆ Lp p), by simp⟩
  obtain ⟨Ol, hOl⟩ : ∃ Ol : Fin 13 → Finset (Fin gs.length),
      ∀ l i, i ∈ Ol l ↔ (kind i = 0 ∧ 2 ≤ (PSw gs (26 + (i : ℕ))).card ∧ PSw gs (26 + (i : ℕ)) ⊆ Pl l) :=
    ⟨fun l => Finset.univ.filter (fun i : Fin gs.length =>
      kind i = 0 ∧ 2 ≤ (PSw gs (26 + (i : ℕ))).card ∧ PSw gs (26 + (i : ℕ)) ⊆ Pl l), by simp⟩
  -- the two group bounds
  have gp : ∀ p : Fin 13, 5 * ((Tp p).biUnion B).card ≤ 4 * (Op p).card + 8 * (Tp p).card := by
    intro p
    apply group_bound (fun i : Fin gs.length => kind i = 1)
      (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) (builtL gs kind hlen hwire h1) (Lp p)
      (le_of_eq (geo_Lp p)) (Tp p) B
    · intro j hj l hl
      obtain ⟨hjT, hA⟩ := (hTp p j).1 hj
      simp only [Lp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc j hjT p (by rw [hA]; simp) l hl
    · intro j hj hc
      obtain ⟨hjT, _⟩ := (hTp p j).1 hj
      exact (hAB j ((hTmem j).1 hjT).1).2.2 hc
    · intro i hK hc hs
      exact (hOp p i).2 ⟨hK, hc, hs⟩
  have gl : ∀ l : Fin 13, 5 * ((Tl l).biUnion A).card ≤ 4 * (Ol l).card + 8 * (Tl l).card := by
    intro l
    apply group_bound (fun i : Fin gs.length => kind i = 0)
      (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) (builtP gs kind hlen hwire h0) (Pl l)
      (le_of_eq (geo_Pl l)) (Tl l) A
    · intro j hj p hp
      obtain ⟨hjT, _, hBj⟩ := (hTl l j).1 hj
      simp only [Pl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc j hjT p hp l (by rw [hBj]; simp)
    · intro j hj hc
      obtain ⟨hjT, _⟩ := (hTl l j).1 hj
      exact (hAB j ((hTmem j).1 hjT).1).2.1 hc
    · intro i hK hc hs
      exact (hOl l i).2 ⟨hK, hc, hs⟩
  -- every incident pair is covered by a group
  have hcovp : ∀ p : Fin 13, 4 ≤ ((Tp p).biUnion B).card +
      (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A)).card := by
    intro p
    have hsub : Lp p ⊆ (Tp p).biUnion B ∪ Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A) := by
      intro l hl
      have hpl : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
        simpa only [Lp, Finset.mem_filter, Finset.mem_univ, true_and] using hl
      obtain ⟨j, hjT, hpA, hlB⟩ := hcov p l hpl
      by_cases hc : 2 ≤ (A j).card
      · apply Finset.mem_union_right
        rw [Finset.mem_filter, Finset.mem_biUnion]
        exact ⟨Finset.mem_univ _, j, (hTl l j).2 ⟨hjT, hc, hBsing j hjT hc l hlB⟩, hpA⟩
      · apply Finset.mem_union_left
        rw [Finset.mem_biUnion]
        exact ⟨j, (hTp p j).2 ⟨hjT, hAsing j hc p hpA⟩, hlB⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le ((Tp p).biUnion B)
      (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A))
    have hc3 := geo_Lp p
    omega
  have hswap : ∑ p : Fin 13, (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A)).card
      = ∑ l : Fin 13, ((Tl l).biUnion A).card := by
    rw [dbl Finset.univ Finset.univ (fun (p l : Fin 13) => p ∈ (Tl l).biUnion A)]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    ext p
    simp
  have hC : 52 ≤ ∑ p : Fin 13, ((Tp p).biUnion B).card + ∑ l : Fin 13, ((Tl l).biUnion A).card := by
    rw [← hswap, ← Finset.sum_add_distrib]
    calc 52 = ∑ _p : Fin 13, 4 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p _ => hcovp p)
  have hG1 : 5 * ∑ p : Fin 13, ((Tp p).biUnion B).card
      ≤ 4 * ∑ p : Fin 13, (Op p).card + 8 * ∑ p : Fin 13, (Tp p).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun p _ => gp p)
  have hG2 : 5 * ∑ l : Fin 13, ((Tl l).biUnion A).card
      ≤ 4 * ∑ l : Fin 13, (Ol l).card + 8 * ∑ l : Fin 13, (Tl l).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun l _ => gl l)
  -- the groups use different gates
  have hO1 : ∑ p : Fin 13, (Op p).card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 1)).card := by
    have hd : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Op := by
      intro p _ p' _ hne
      show Disjoint (Op p) (Op p')
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨_, hc, hs⟩ := (hOp p i).1 hi
      obtain ⟨_, _, hs'⟩ := (hOp p' i).1 hi'
      have hc1 := Finset.card_le_card (Finset.subset_inter hs hs')
      have hc2 := geo_lines p p' hne
      omega
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hOp p i).1 hp).1⟩
  have hO2 : ∑ l : Fin 13, (Ol l).card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 0)).card := by
    have hd : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Ol := by
      intro l _ l' _ hne
      show Disjoint (Ol l) (Ol l')
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨_, hc, hs⟩ := (hOl l i).1 hi
      obtain ⟨_, _, hs'⟩ := (hOl l' i).1 hi'
      have hc1 := Finset.card_le_card (Finset.subset_inter hs hs')
      have hc2 := geo_points l l' hne
      omega
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hOl l i).1 hl).1⟩
  have hTT : ∑ p : Fin 13, (Tp p).card + ∑ l : Fin 13, (Tl l).card ≤ T.card := by
    have hd1 : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Tp := by
      intro p _ p' _ hne
      show Disjoint (Tp p) (Tp p')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := ((hTp p j).1 hj).2
      have e2 := ((hTp p' j).1 hj').2
      rw [e1] at e2
      exact hne (Finset.singleton_inj.1 e2)
    have hd2 : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Tl := by
      intro l _ l' _ hne
      show Disjoint (Tl l) (Tl l')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := ((hTl l j).1 hj).2.2
      have e2 := ((hTl l' j).1 hj').2.2
      rw [e1] at e2
      exact hne (Finset.singleton_inj.1 e2)
    rw [← Finset.card_biUnion hd1, ← Finset.card_biUnion hd2]
    have hint : (Finset.univ.biUnion Tp) ∩ (Finset.univ.biUnion Tl) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_inter.1 hj
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hj1
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hj2
      have e1 := ((hTp p j).1 hp).2
      have e2 := ((hTl l j).1 hl).2.1
      rw [e1, Finset.card_singleton] at e2
      omega
    have hun := Finset.card_union_add_card_inter (Finset.univ.biUnion Tp) (Finset.univ.biUnion Tl)
    rw [hint, Finset.card_empty] at hun
    have hsub : (Finset.univ.biUnion Tp) ∪ (Finset.univ.biUnion Tl) ⊆ T := by
      intro j hj
      rcases Finset.mem_union.1 hj with hj | hj
      · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hj
        exact ((hTp p j).1 hp).1
      · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hj
        exact ((hTl l j).1 hl).1
    have hc := Finset.card_le_card hsub
    omega
  -- the top part
  have hT2 : T.card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 2)).card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hTmem j).1 hj).1⟩
  have hT3 : T.card ≤ 1 + (Finset.univ.filter (fun i : Fin gs.length => kind i = 3)).card := by
    have h := count gs kind hlen hwire (fun i hi => (h3 i hi).2) gs.length {jo} T
      (by
        intro i hi
        rw [Finset.mem_singleton] at hi
        subst hi
        exact ⟨i.2, hjo⟩)
      (by
        intro j hj
        obtain ⟨a, b⟩ := (hTmem j).1 hj
        exact ⟨a, jo, Finset.mem_singleton_self _, b⟩)
    have hsub : Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < gs.length)
        ⊆ Finset.univ.filter (fun i : Fin gs.length => kind i = 3) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    omega
  have hN : (Finset.univ.filter (fun i : Fin gs.length => kind i = 0)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 1)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 2)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 3)).card = gs.length := by
    have h := Finset.card_eq_sum_card_fiberwise (f := kind) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Fin.sum_univ_four, Finset.card_univ, Fintype.card_fin] at h
    omega
  omega


-- ===== Bridge from circuits without an AND below an AND to tagged lists =====

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

theorem V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]

theorem V_gate_some (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ)
    (h : V gs x (26 + i) = true) : ∃ g, gs[i]? = some g := by
  have hi : i < gs.length := by
    by_contra hi
    rw [V_out gs x (26 + i) (by rw [hx]; omega)] at h
    exact Bool.false_ne_true h
  exact ⟨gs[i], List.getElem?_eq_getElem hi⟩

theorem orN (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) (hop : g.op = GateOp.or) :
    V gs x (26 + i) = true ↔ ∃ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

theorem andN (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) (hop : g.op = GateOp.and) :
    V gs x (26 + i) = true ↔ ∀ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

def side0 (c : ℕ → ℕ) (w : ℕ) : Prop := w < 13 ∨ (26 ≤ w ∧ c (w - 26) = 0)

def side1 (c : ℕ → ℕ) (w : ℕ) : Prop := (13 ≤ w ∧ w < 26) ∨ (26 ≤ w ∧ c (w - 26) = 1)

def sideT (c : ℕ → ℕ) (w : ℕ) : Prop := 26 ≤ w ∧ (c (w - 26) = 2 ∨ c (w - 26) = 3)

def lowW (c : ℕ → ℕ) (w : ℕ) : Prop := w < 26 ∨ (26 ≤ w ∧ (c (w - 26) = 0 ∨ c (w - 26) = 1))

def newGate (c : ℕ → ℕ) (j : ℕ) (g : Gate) : Gate :=
  if c j = 0 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide (w < 13 ∨ (26 ≤ w ∧ c (w - 26) = 0)))⟩
  else if c j = 1 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide ((13 ≤ w ∧ w < 26) ∨ (26 ≤ w ∧ c (w - 26) = 1)))⟩
  else if c j = 2 then g
  else if c j = 3 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide (26 ≤ w ∧ (c (w - 26) = 2 ∨ c (w - 26) = 3)))⟩
  else ⟨GateOp.or, []⟩

def newGates (c : ℕ → ℕ) (gs : List Gate) : List Gate := gs.mapIdx (fun j g => newGate c j g)

theorem newGates_len (c : ℕ → ℕ) (gs : List Gate) : (newGates c gs).length = gs.length := by
  simp [newGates]

theorem newGates_get (c : ℕ → ℕ) (gs : List Gate) (i : ℕ) (g : Gate) (hg : gs[i]? = some g) :
    (newGates c gs)[i]? = some (newGate c i g) := by
  simp [newGates, List.getElem?_mapIdx, hg]

theorem newGates_inv (c : ℕ → ℕ) (gs : List Gate) (i : ℕ) (g' : Gate)
    (hg : (newGates c gs)[i]? = some g') : ∃ g, gs[i]? = some g ∧ g' = newGate c i g := by
  have hi : i < gs.length := by
    have := (List.getElem?_eq_some_iff.1 hg).1
    rw [newGates_len] at this
    exact this
  refine ⟨gs[i], List.getElem?_eq_getElem hi, ?_⟩
  have h2 := newGates_get c gs i gs[i] (List.getElem?_eq_getElem hi)
  rw [hg] at h2
  exact Option.some.inj h2

theorem mem0 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 0) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ side0 c w := by
  simp [newGate, h, side0]

theorem mem1 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 1) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ side1 c w := by
  simp [newGate, h, side1]

theorem eq2 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : c i = 2) : newGate c i g = g := by
  simp [newGate, h]

theorem mem3 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 3) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ sideT c w := by
  simp [newGate, h, sideT]

theorem eq4 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : 4 ≤ c i) : newGate c i g = ⟨GateOp.or, []⟩ := by
  have h0 : c i ≠ 0 := by omega
  have h1 : c i ≠ 1 := by omega
  have h2 : c i ≠ 2 := by omega
  have h3 : c i ≠ 3 := by omega
  simp [newGate, h0, h1, h2, h3]

theorem newGate_or (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : c i ≠ 2) :
    (newGate c i g).op = GateOp.or := by
  unfold newGate
  split_ifs <;> rfl

theorem newGate_sub (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : w ∈ (newGate c i g).inputs) :
    w ∈ g.inputs := by
  unfold newGate at h
  split_ifs at h
  · exact (List.mem_filter.1 h).1
  · exact (List.mem_filter.1 h).1
  · exact h
  · exact (List.mem_filter.1 h).1
  · simp at h

theorem newGate_len (c : ℕ → ℕ) (i : ℕ) (g : Gate) :
    (newGate c i g).inputs.length ≤ g.inputs.length := by
  unfold newGate
  split_ifs
  · exact List.length_filter_le _ _
  · exact List.length_filter_le _ _
  · exact le_refl _
  · exact List.length_filter_le _ _
  · simp

def Hyp (gs : List Gate) (c : ℕ → ℕ) : Prop :=
  ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26 + i) ∧
    (c i = 0 ∨ c i = 1 → g.op = GateOp.or ∧ ∀ w ∈ g.inputs, lowW c w) ∧
    (c i = 2 → g.op = GateOp.and ∧
      ∃ a b, (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ side0 c a ∧ side1 c b) ∧
    (c i = 3 → g.op = GateOp.or) ∧
    (4 ≤ c i → g.op = GateOp.and ∧ (∀ w ∈ g.inputs, lowW c w) ∧
      ¬ ∃ a b, (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ side0 c a ∧ side1 c b) ∧
    (c i = 1 → ∀ p : Fin 13, V gs (inp {p} ∅) (26 + i) = false) ∧
    (c i = 0 → ∀ l : Fin 13, V gs (inp ∅ {l}) (26 + i) = true →
      ∃ p : Fin 13, V gs (inp {p} ∅) (26 + i) = true)

-- Monotonicity of the wires in the input.
theorem monoC (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c)
    (S R S' R' : Finset (Fin 13)) (hS : S ⊆ S') (hR : R ⊆ R') :
    ∀ w, V gs (inp S R) w = true → V gs (inp S' R') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h13 : w < 13
    · rw [V_point gs _ _ w h13] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact hS h
    by_cases h26 : w < 26
    · rw [V_line gs _ _ w (by omega) h26] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact hR h
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨⟨ho, _, hb⟩, _⟩ := H j g hg
    rcases ho with ho | ho
    · rw [andN gs _ (inp_len _ _) j g hg hb ho] at h ⊢
      intro u hu
      exact ih u (hb u hu) (h u hu)
    · rw [orN gs _ (inp_len _ _) j g hg hb ho] at h ⊢
      obtain ⟨u, hu, hv⟩ := h
      exact ⟨u, hu, ih u (hb u hu) hv⟩

-- The new list is below the old one everywhere.
theorem dom (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (x : List Bool) (hx : x.length = 26) :
    ∀ w, V (newGates c gs) x w = true → V gs x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h26 : w < 26
    · rw [V_in gs (newGates c gs) x w (by omega)]
      exact h
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g', hg'⟩ := V_gate_some _ x hx j h
    obtain ⟨g, hg, rfl⟩ := newGates_inv c gs j g' hg'
    obtain ⟨⟨ho, _, hb⟩, h01, h2, h3, h4, _⟩ := H j g hg
    have hbd : ∀ u ∈ (newGate c j g).inputs, u < 26 + j := fun u hu => hb u (newGate_sub c j g u hu)
    by_cases hc2 : c j = 2
    · have hand := (h2 hc2).1
      have e := eq2 c j g hc2
      rw [e] at hg'
      rw [andN _ x hx j g hg' hb hand] at h
      rw [andN gs x hx j g hg hb hand]
      intro u hu
      exact ih u (hb u hu) (h u hu)
    · rw [orN _ x hx j _ hg' hbd (newGate_or c j g hc2)] at h
      obtain ⟨u, hu, hv⟩ := h
      have hor : g.op = GateOp.or := by
        by_cases hc4 : 4 ≤ c j
        · rw [eq4 c j g hc4] at hu
          simp at hu
        · have : c j = 0 ∨ c j = 1 ∨ c j = 3 := by omega
          rcases this with h' | h' | h'
          · exact (h01 (Or.inl h')).1
          · exact (h01 (Or.inr h')).1
          · exact h3 h'
      rw [orN gs x hx j g hg hb hor]
      exact ⟨u, newGate_sub c j g u hu, ih u (hbd u hu) hv⟩

-- A point that fires a point-kind low gate fires its new version.
theorem lowP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13)
    (S R : Finset (Fin 13)) (hp : p ∈ S) :
    ∀ i, c i = 0 → V gs (inp {p} ∅) (26 + i) = true →
      V (newGates c gs) (inp S R) (26 + i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc hv
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) i hv
    obtain ⟨⟨_, _, hb⟩, h01, _, _, _, _, _⟩ := H i g hg
    obtain ⟨hor, hlow⟩ := h01 (Or.inl hc)
    rw [orN gs _ (inp_len _ _) i g hg hb hor] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [orN _ _ (inp_len _ _) i _ (newGates_get c gs i g hg)
      (fun u hu => hb u (newGate_sub c i g u hu)) (newGate_or c i g (by omega))]
    have hbw := hb w hw
    rcases hlow w hw with h | ⟨h26, hcw⟩
    · by_cases h13 : w < 13
      · refine ⟨w, (mem0 c i g w hc).2 ⟨hw, Or.inl h13⟩, ?_⟩
        rw [V_point gs _ _ w h13] at hvw
        rw [V_point _ _ _ w h13]
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hvw ⊢
        rw [hvw]; exact hp
      · rw [V_line gs _ _ w (by omega) h] at hvw
        simp at hvw
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hcw
      rcases hcw with hcw | hcw
      · refine ⟨26 + j, (mem0 c i g _ hc).2 ⟨hw, Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hcw⟩⟩, ?_⟩
        exact ih j (by omega) hcw hvw
      · obtain ⟨gj, hgj⟩ := V_gate_some gs _ (inp_len _ _) j hvw
        obtain ⟨_, _, _, _, _, hs1, _⟩ := H j gj hgj
        rw [hs1 hcw p] at hvw
        exact absurd hvw Bool.false_ne_true

theorem lowL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13)
    (S R : Finset (Fin 13)) (hl : l ∈ R) :
    ∀ i, c i = 1 → V gs (inp ∅ {l}) (26 + i) = true →
      V (newGates c gs) (inp S R) (26 + i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc hv
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) i hv
    obtain ⟨⟨_, _, hb⟩, h01, _, _, _, hs1i, _⟩ := H i g hg
    obtain ⟨hor, hlow⟩ := h01 (Or.inr hc)
    rw [orN gs _ (inp_len _ _) i g hg hb hor] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [orN _ _ (inp_len _ _) i _ (newGates_get c gs i g hg)
      (fun u hu => hb u (newGate_sub c i g u hu)) (newGate_or c i g (by omega))]
    have hbw := hb w hw
    rcases hlow w hw with h | ⟨h26, hcw⟩
    · by_cases h13 : w < 13
      · rw [V_point gs _ _ w h13] at hvw
        simp at hvw
      · refine ⟨w, (mem1 c i g w hc).2 ⟨hw, Or.inl ⟨by omega, h⟩⟩, ?_⟩
        rw [V_line gs _ _ w (by omega) h] at hvw
        rw [V_line _ _ _ w (by omega) h]
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hvw ⊢
        rw [hvw]; exact hl
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hcw
      rcases hcw with hcw | hcw
      · obtain ⟨gj, hgj⟩ := V_gate_some gs _ (inp_len _ _) j hvw
        obtain ⟨_, _, _, _, _, _, hs0⟩ := H j gj hgj
        obtain ⟨p0, hp0⟩ := hs0 hcw l hvw
        have hi : V gs (inp {p0} ∅) (26 + i) = true :=
          (orN gs _ (inp_len _ _) i g hg hb hor).2 ⟨26 + j, hw, hp0⟩
        rw [hs1i hc p0] at hi
        exact absurd hi Bool.false_ne_true
      · refine ⟨26 + j, (mem1 c i g _ hc).2 ⟨hw, Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hcw⟩⟩, ?_⟩
        exact ih j (by omega) hcw hvw

-- A low wire that fires on a point and a line fires on one of them alone.
theorem addLow (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p l : Fin 13) :
    ∀ w, lowW c w → V gs (inp {p} {l}) w = true →
      V gs (inp {p} ∅) w = true ∨ V gs (inp ∅ {l}) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hlw hv
    by_cases h13 : w < 13
    · left
      rw [V_point gs _ _ w h13] at hv ⊢
      exact hv
    by_cases h26 : w < 26
    · right
      rw [V_line gs _ _ w (by omega) h26] at hv ⊢
      exact hv
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    have hcj : c j = 0 ∨ c j = 1 := by
      rcases hlw with h | ⟨_, h⟩
      · omega
      · rw [Nat.add_sub_cancel_left] at h; exact h
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j hv
    obtain ⟨⟨_, _, hb⟩, h01, _⟩ := H j g hg
    obtain ⟨hor, hlow⟩ := h01 hcj
    rw [orN gs _ (inp_len _ _) j g hg hb hor] at hv
    obtain ⟨u, hu, hvu⟩ := hv
    rcases ih u (hb u hu) (hlow u hu) hvu with h | h
    · left
      exact (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, h⟩
    · right
      exact (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, h⟩

-- Quadrangles through two points, and quadrangles missing two lines.
def Q1 (d : Fin 13) : Finset (Fin 13) :=
  if d = 3 then {0, 2, 3, 4} else if d = 4 then {0, 1, 4, 6} else if d = 6 then {0, 1, 2, 6}
  else if d = 7 then {0, 1, 2, 7} else if d = 8 then {0, 1, 4, 8} else if d = 9 then {0, 2, 4, 9}
  else if d = 10 then {0, 1, 5, 10} else if d = 11 then {0, 1, 2, 11}
  else if d = 12 then {0, 1, 4, 12} else {0, 1, 2, 5}

def QP (p p' : Fin 13) : Finset (Fin 13) := (Q1 (p' - p)).image (fun q => q + p)

def Q2 (d : Fin 13) : Finset (Fin 13) :=
  if d = 1 then {5, 6, 7, 11} else if d = 2 then {4, 6, 7, 8} else if d = 3 then {2, 5, 7, 8}
  else if d = 4 then {2, 6, 8, 10} else if d = 5 then {2, 4, 7, 11} else if d = 6 then {4, 5, 8, 10}
  else if d = 8 then {2, 5, 6, 10} else if d = 9 then {2, 4, 6, 8} else if d = 10 then {2, 4, 5, 8}
  else if d = 12 then {4, 5, 6, 10} else {2, 4, 5, 6}

def QL (l l' : Fin 13) : Finset (Fin 13) := (Q2 (l' - l)).image (fun q => q + l)

theorem geoPP : ∀ p p' : Fin 13,
    (QP p p').card = 4 ∧
    (∀ k : Fin 13, ((QP p p').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ QP p p' ∧ p' ∈ QP p p' := by
  decide +kernel

theorem geoLL : ∀ l l' : Fin 13,
    (QL l l').card = 4 ∧
    (∀ k : Fin 13, ((QL l l').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    l ∈ TQ (QL l l') ∧ l' ∈ TQ (QL l l') := by
  decide +kernel

-- The wire fires on some quadrangle input.
def Bad (gs : List Gate) (w : ℕ) : Prop :=
  ∃ Q : Finset (Fin 13), Q.card = 4 ∧
    (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    V gs (inp Q (TQ Q)) w = true

theorem badPP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p p' : Fin 13) (w : ℕ)
    (h : V gs (inp {p, p'} ∅) w = true) : Bad gs w := by
  obtain ⟨h1, h2, h3, h4⟩ := geoPP p p'
  refine ⟨QP p p', h1, h2, monoC gs c H _ _ _ _ ?_ (Finset.empty_subset _) w h⟩
  intro q hq
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact h3
  · rw [Finset.mem_singleton.1 hq]; exact h4

theorem badLL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l l' : Fin 13) (w : ℕ)
    (h : V gs (inp ∅ {l, l'}) w = true) : Bad gs w := by
  obtain ⟨h1, h2, h3, h4⟩ := geoLL l l'
  refine ⟨QL l l', h1, h2, monoC gs c H _ _ _ _ (Finset.empty_subset _) ?_ w h⟩
  intro q hq
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact h3
  · rw [Finset.mem_singleton.1 hq]; exact h4

theorem badP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (h : V gs (inp {p} ∅) w = true) : Bad gs w :=
  badPP gs c H p p w (monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) w h)

theorem badL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13) (w : ℕ)
    (h : V gs (inp ∅ {l}) w = true) : Bad gs w :=
  badLL gs c H l l w (monoC gs c H _ _ _ _ (Finset.empty_subset _) (by simp) w h)

-- A low wire fired by a point is on the point side.
theorem firesP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (hl : lowW c w) (h : V gs (inp {p} ∅) w = true) : side0 c w := by
  by_cases h13 : w < 13
  · exact Or.inl h13
  by_cases h26 : w < 26
  · rw [V_line gs _ _ w (by omega) h26] at h
    simp at h
  obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
  rcases hl with hl | ⟨_, hl⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hl
  rcases hl with hl | hl
  · exact Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hl⟩
  · obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, hs1, _⟩ := H j g hg
    rw [hs1 hl p] at h
    exact absurd h Bool.false_ne_true

-- A low wire fired by a line is on the line side, or some point fires it too.
theorem firesL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13) (w : ℕ)
    (hl : lowW c w) (h : V gs (inp ∅ {l}) w = true) :
    side1 c w ∨ ∃ p0 : Fin 13, V gs (inp {p0} ∅) w = true := by
  by_cases h13 : w < 13
  · rw [V_point gs _ _ w h13] at h
    simp at h
  by_cases h26 : w < 26
  · exact Or.inl (Or.inl ⟨by omega, h26⟩)
  obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
  rcases hl with hl | ⟨_, hl⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hl
  rcases hl with hl | hl
  · obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, _, hs0⟩ := H j g hg
    exact Or.inr (hs0 hl l h)
  · exact Or.inl (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hl⟩)

-- A point-side wire fired by a point fires in the new list.
theorem side0D (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13)
    (S R : Finset (Fin 13)) (hp : p ∈ S) (w : ℕ) (hs : side0 c w)
    (h : V gs (inp {p} ∅) w = true) : V (newGates c gs) (inp S R) w = true := by
  rcases hs with h13 | ⟨h26, hc⟩
  · rw [V_point gs _ _ w h13] at h
    rw [V_point _ _ _ w h13]
    simp only [decide_eq_true_eq, Finset.mem_singleton] at h ⊢
    rw [h]; exact hp
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    exact lowP gs c H p S R hp j hc h

theorem side1D (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13)
    (S R : Finset (Fin 13)) (hl : l ∈ R) (w : ℕ) (hs : side1 c w)
    (h : V gs (inp ∅ {l}) w = true) : V (newGates c gs) (inp S R) w = true := by
  rcases hs with ⟨h13, h26⟩ | ⟨h26, hc⟩
  · rw [V_line gs _ _ w h13 h26] at h
    rw [V_line _ _ _ w h13 h26]
    simp only [decide_eq_true_eq, Finset.mem_singleton] at h ⊢
    rw [h]; exact hl
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    exact lowL gs c H l S R hl j hc h

theorem side0_low (c : ℕ → ℕ) (w : ℕ) (h : side0 c w) : lowW c w := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h, Or.inl h'⟩

theorem side1_low (c : ℕ → ℕ) (w : ℕ) (h : side1 c w) : lowW c w := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h.2
  · exact Or.inr ⟨h, Or.inr h'⟩

-- A line-side wire is not fired by a point.
theorem side1_noP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (hs : side1 c w) (h : V gs (inp {p} ∅) w = true) : False := by
  rcases hs with ⟨h13, h26⟩ | ⟨h26, hc⟩
  · rw [V_line gs _ _ w h13 h26] at h
    simp at h
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, hs1, _⟩ := H j g hg
    rw [hs1 hc p] at h
    exact absurd h Bool.false_ne_true

-- The main invariant: a wire fired by a point-line pair either is a top wire that still fires in
-- the new list, or fires on a quadrangle input.
theorem top (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p l : Fin 13) :
    ∀ w, V gs (inp {p} {l}) w = true →
      (sideT c w ∧ V (newGates c gs) (inp {p} {l}) w = true) ∨ Bad gs w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    have hlowcase : lowW c w → Bad gs w := by
      intro hlw
      rcases addLow gs c H p l w hlw hv with h | h
      · exact badP gs c H p w h
      · exact badL gs c H l w h
    by_cases h26 : w < 26
    · exact Or.inr (hlowcase (Or.inl h26))
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j hv
    obtain ⟨⟨ho, hlen, hb⟩, h01, h2, h3, h4, _⟩ := H j g hg
    have hgd := newGates_get c gs j g hg
    have hbd : ∀ u ∈ (newGate c j g).inputs, u < 26 + j := fun u hu => hb u (newGate_sub c j g u hu)
    have hsT : ∀ hh : c j = 2 ∨ c j = 3, sideT c (26 + j) := fun hh =>
      ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hh⟩
    by_cases hc01 : c j = 0 ∨ c j = 1
    · exact Or.inr (hlowcase (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hc01⟩))
    by_cases hc2 : c j = 2
    · obtain ⟨hand, a, b, hsh, ha, hbb⟩ := h2 hc2
      have hall := (andN gs _ (inp_len _ _) j g hg hb hand).1 hv
      have hma : a ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
      have hmb : b ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
      have hbl : V gs (inp ∅ {l}) b = true := by
        rcases addLow gs c H p l b (side1_low c b hbb) (hall b hmb) with h | h
        · exact (side1_noP gs c H p b hbb h).elim
        · exact h
      rcases addLow gs c H p l a (side0_low c a ha) (hall a hma) with h | h
      · left
        refine ⟨hsT (Or.inl hc2), ?_⟩
        have e := eq2 c j g hc2
        rw [e] at hgd
        rw [andN _ _ (inp_len _ _) j g hgd hb hand]
        intro u hu
        have hu' : u = a ∨ u = b := by
          rcases hsh with e | e
          · rw [e] at hu; simpa using hu
          · rw [e] at hu; simpa [or_comm] using hu
        rcases hu' with rfl | rfl
        · exact side0D gs c H p _ _ (by simp) _ ha h
        · exact side1D gs c H l _ _ (by simp) _ hbb hbl
      · right
        apply badL gs c H l
        rw [andN gs _ (inp_len _ _) j g hg hb hand]
        intro u hu
        have hu' : u = a ∨ u = b := by
          rcases hsh with e | e
          · rw [e] at hu; simpa using hu
          · rw [e] at hu; simpa [or_comm] using hu
        rcases hu' with rfl | rfl
        · exact h
        · exact hbl
    by_cases hc3 : c j = 3
    · have hor := h3 hc3
      obtain ⟨u, hu, hvu⟩ := (orN gs _ (inp_len _ _) j g hg hb hor).1 hv
      rcases ih u (hb u hu) hvu with ⟨hT, hd⟩ | ⟨Q, hQ1, hQ2, hQ3⟩
      · left
        refine ⟨hsT (Or.inr hc3), ?_⟩
        rw [orN _ _ (inp_len _ _) j _ hgd hbd (newGate_or c j g hc2)]
        exact ⟨u, (mem3 c j g u hc3).2 ⟨hu, hT⟩, hd⟩
      · right
        exact ⟨Q, hQ1, hQ2, (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, hQ3⟩⟩
    have hc4 : 4 ≤ c j := by omega
    obtain ⟨hand, hlow, hnsh⟩ := h4 hc4
    have hall := (andN gs _ (inp_len _ _) j g hg hb hand).1 hv
    right
    have key : ∀ S R : Finset (Fin 13), (∀ u ∈ g.inputs, V gs (inp S R) u = true) →
        V gs (inp S R) (26 + j) = true := fun S R hh =>
      (andN gs _ (inp_len _ _) j g hg hb hand).2 hh
    have hsplit : ∀ u ∈ g.inputs, V gs (inp {p} ∅) u = true ∨ V gs (inp ∅ {l}) u = true :=
      fun u hu => addLow gs c H p l u (hlow u hu) (hall u hu)
    by_cases hallP : ∀ u ∈ g.inputs, V gs (inp {p} ∅) u = true
    · exact badP gs c H p _ (key _ _ hallP)
    by_cases hallL : ∀ u ∈ g.inputs, V gs (inp ∅ {l}) u = true
    · exact badL gs c H l _ (key _ _ hallL)
    -- one input fires on the point only, another on the line only
    obtain ⟨a, ha, haP⟩ : ∃ a ∈ g.inputs, V gs (inp {p} ∅) a = true ∧ ¬ V gs (inp ∅ {l}) a = true := by
      by_contra hne
      apply hallL
      intro u hu
      by_contra hul
      rcases hsplit u hu with h | h
      · exact hne ⟨u, hu, h, hul⟩
      · exact hul h
    obtain ⟨b, hbm, hbL⟩ : ∃ b ∈ g.inputs, V gs (inp ∅ {l}) b = true ∧ ¬ V gs (inp {p} ∅) b = true := by
      by_contra hne
      apply hallP
      intro u hu
      by_contra hup
      rcases hsplit u hu with h | h
      · exact hup h
      · exact hne ⟨u, hu, h, hup⟩
    have hab : a ≠ b := by
      rintro rfl
      exact hbL.2 haP.1
    have hshape : g.inputs = [a, b] ∨ g.inputs = [b, a] := by
      match hgi : g.inputs, hlen, ha, hbm with
      | [], _, ha', _ => simp at ha'
      | [u], _, ha', hb' =>
        simp at ha' hb'
        exact absurd (ha'.trans hb'.symm) hab
      | [u, v], _, ha', hb' =>
        simp at ha' hb'
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hab
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hab
      | _ :: _ :: _ :: _, hl', _, _ => simp at hl'
    have hs0 := firesP gs c H p a (hlow a ha) haP.1
    rcases firesL gs c H l b (hlow b hbm) hbL.1 with hs1 | ⟨p0, hp0⟩
    · exact (hnsh ⟨a, b, hshape, hs0, hs1⟩).elim
    · apply badPP gs c H p p0
      apply key
      intro u hu
      have hu' : u = a ∨ u = b := by
        rcases hshape with e | e
        · rw [e] at hu; simpa using hu
        · rw [e] at hu; simpa [or_comm] using hu
      rcases hu' with rfl | rfl
      · exact monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) _ haP.1
      · exact monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) _ hp0

-- Cone lemmas, from the merged file L_meta_1600.lean.
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h



theorem newGate_op (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (newGate c i g).op = GateOp.and ∨ (newGate c i g).op = GateOp.or := by
  by_cases h2 : c i = 2
  · rw [eq2 c i g h2]; exact h
  · exact Or.inr (newGate_or c i g h2)

theorem core (gs : List Gate) (out : ℕ)
    (hmon : Monotone2 ⟨gs, out⟩) (hback : ReadsBack 26 ⟨gs, out⟩)
    (hnn : ¬ ∃ i j : ℕ, (gateAt ⟨gs, out⟩ i).op = GateOp.and ∧
      (gateAt ⟨gs, out⟩ j).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ i j)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      V gs (inp Q (TQ Q)) out = false) : 64 ≤ gs.length := by
  classical
  have hgat : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → gateAt (⟨gs, out⟩ : Circuit) i = g := by
    intro i g hg
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    exact gateAt_eq ⟨gs, out⟩ i hi
  have hG : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26 + i := by
    intro i g hg
    have e := hgat i g hg
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    have hm := hmon gs[i] (List.getElem_mem hi)
    refine ⟨by simpa using hm.1, hm.2, ?_⟩
    have hb := hback i hi
    rw [e] at hb
    exact hb
  obtain ⟨Top, hTop⟩ : ∃ Top : ℕ → Prop, ∀ j, Top j ↔
      ((gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∨
        ∃ k, (gateAt (⟨gs, out⟩ : Circuit) k).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ k j) :=
    ⟨_, fun j => Iff.rfl⟩
  have hread : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ w ∈ g.inputs, 26 ≤ w → Top (w - 26) →
      ∃ k, (gateAt (⟨gs, out⟩ : Circuit) k).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ k j := by
    intro j g hg w hw h26 hT
    have hj : j < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hbw := (hG j g hg).2.2 w hw
    have hw' : w ∈ (gateAt (⟨gs, out⟩ : Circuit) j).inputs := by rw [hgat j g hg]; exact hw
    rcases (hTop _).1 hT with h | ⟨k, hk, hkc⟩
    · exact ⟨w - 26, h, (inCone_iff 26 ⟨gs, out⟩ _ j hj).2 ⟨w, hw', h26, hbw, Or.inl rfl⟩⟩
    · exact ⟨k, hk, (inCone_iff 26 ⟨gs, out⟩ _ j hj).2 ⟨w, hw', h26, hbw, Or.inr hkc⟩⟩
  have hreadA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w ∈ g.inputs, 26 ≤ w →
      ¬ Top (w - 26) := by
    intro j g hg hop w hw h26 hT
    obtain ⟨k, hk, hkc⟩ := hread j g hg w hw h26 hT
    exact hnn ⟨k, j, hk, by rw [hgat j g hg]; exact hop, hkc⟩
  have hsex : ∀ j : ℕ, ∃ v : ℕ,
      (v = 1 ∧ (∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true) ∨
      (v = 0 ∧ ¬ ((∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true)) := by
    intro j
    by_cases h : ((∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true)
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, h⟩⟩
  choose s hs using hsex
  have hs01 : ∀ j, s j = 0 ∨ s j = 1 := by
    intro j
    rcases hs j with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  obtain ⟨shape, hshape⟩ : ∃ shape : ℕ → Prop, ∀ j, shape j ↔
      ∃ a b, ((gateAt (⟨gs, out⟩ : Circuit) j).inputs = [a, b] ∨
        (gateAt (⟨gs, out⟩ : Circuit) j).inputs = [b, a]) ∧ side0 s a ∧ side1 s b :=
    ⟨_, fun j => Iff.rfl⟩
  have hcex : ∀ j : ℕ, ∃ v : ℕ,
      (¬ Top j ∧ v = s j) ∨
      (Top j ∧ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ shape j ∧ v = 2) ∨
      (Top j ∧ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ ¬ shape j ∧ v = 4) ∨
      (Top j ∧ ¬ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ v = 3) := by
    intro j
    by_cases hT : Top j
    · by_cases ha : (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and
      · by_cases hsj : shape j
        · exact ⟨2, Or.inr (Or.inl ⟨hT, ha, hsj, rfl⟩)⟩
        · exact ⟨4, Or.inr (Or.inr (Or.inl ⟨hT, ha, hsj, rfl⟩))⟩
      · exact ⟨3, Or.inr (Or.inr (Or.inr ⟨hT, ha, rfl⟩))⟩
    · exact ⟨s j, Or.inl ⟨hT, rfl⟩⟩
  choose c hc using hcex
  have hcs : ∀ j, ¬ Top j → c j = s j := by
    intro j hT
    rcases hc j with h | h | h | h
    · exact h.2
    · exact absurd h.1 hT
    · exact absurd h.1 hT
    · exact absurd h.1 hT
  -- sides agree below an AND gate
  have tr0 : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ a ∈ g.inputs,
      (side0 s a ↔ side0 c a) := by
    intro j g hg hop a ha
    unfold side0
    constructor
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [← hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
  have tr1 : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ a ∈ g.inputs,
      (side1 s a ↔ side1 c a) := by
    intro j g hg hop a ha
    unfold side1
    constructor
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [← hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
  have H : Hyp gs c := by
    intro i g hg
    have hga := hgat i g hg
    have hs01i := hs01 i
    refine ⟨hG i g hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h01
      have hnT : ¬ Top i := by
        intro hT
        rcases hc i with h | h | h | h
        · exact h.1 hT
        · obtain ⟨_, _, _, e⟩ := h; omega
        · obtain ⟨_, _, _, e⟩ := h; omega
        · obtain ⟨_, _, e⟩ := h; omega
      have hor : g.op = GateOp.or := by
        rcases (hG i g hg).1 with h | h
        · exact absurd ((hTop i).2 (Or.inl (by rw [hga]; exact h))) hnT
        · exact h
      refine ⟨hor, fun w hw => ?_⟩
      by_cases h26 : w < 26
      · exact Or.inl h26
      · have hnTw : ¬ Top (w - 26) := fun hT =>
          hnT ((hTop i).2 (Or.inr (hread i g hg w hw (by omega) hT)))
        refine Or.inr ⟨by omega, ?_⟩
        rw [hcs _ hnTw]
        exact hs01 _
    · intro h2
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, hand, hsh, _⟩ := h
        rw [hga] at hand
        obtain ⟨a, b, hab, ha, hb⟩ := (hshape i).1 hsh
        rw [hga] at hab
        have hma : a ∈ g.inputs := by rcases hab with e | e <;> simp [e]
        have hmb : b ∈ g.inputs := by rcases hab with e | e <;> simp [e]
        exact ⟨hand, a, b, hab, (tr0 i g hg hand a hma).1 ha, (tr1 i g hg hand b hmb).1 hb⟩
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h3
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, hna, _⟩ := h
        rw [hga] at hna
        rcases (hG i g hg).1 with h' | h'
        · exact absurd h' hna
        · exact h'
    · intro h4
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, hand, hnsh, _⟩ := h
        rw [hga] at hand
        refine ⟨hand, fun w hw => ?_, ?_⟩
        · by_cases h26 : w < 26
          · exact Or.inl h26
          · refine Or.inr ⟨by omega, ?_⟩
            rw [hcs _ (hreadA i g hg hand w hw (by omega))]
            exact hs01 _
        · rintro ⟨a, b, hab, ha, hb⟩
          apply hnsh
          have hma : a ∈ g.inputs := by rcases hab with e | e <;> simp [e]
          have hmb : b ∈ g.inputs := by rcases hab with e | e <;> simp [e]
          exact (hshape i).2 ⟨a, b, by rw [hga]; exact hab,
            (tr0 i g hg hand a hma).2 ha, (tr1 i g hg hand b hmb).2 hb⟩
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h1 p
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h
        rcases hs i with h' | h'
        · exact h'.2.1 p
        · obtain ⟨e', _⟩ := h'; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h0 l hl
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h
        rcases hs i with h' | h'
        · obtain ⟨e', _⟩ := h'; omega
        · by_contra hne
          apply h'.2
          refine ⟨fun p => ?_, l, hl⟩
          by_contra hp
          exact hne ⟨p, by simpa using hp⟩
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
  have h00 : V gs (inp {0} {0}) out = true := hacc 0 0 (by decide)
  have hBadOut : ¬ Bad gs out := by
    rintro ⟨Q, h1, h2, h3⟩
    rw [hrej Q h1 h2] at h3
    exact Bool.false_ne_true h3
  have hT0 : sideT c out := by
    rcases top gs c H 0 0 out h00 with ⟨h, _⟩ | h
    · exact h
    · exact absurd h hBadOut
  obtain ⟨h26, hco⟩ := hT0
  obtain ⟨jo, rfl⟩ : ∃ j, out = 26 + j := ⟨out - 26, by omega⟩
  rw [Nat.add_sub_cancel_left] at hco
  have hjo : jo < gs.length := by
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) jo h00
    exact (List.getElem?_eq_some_iff.1 hg).1
  have hkex : ∀ i : ℕ, ∃ v : Fin 4, (c i = 1 ∧ v = 1) ∨ (c i = 2 ∧ v = 2) ∨ (c i = 3 ∧ v = 3) ∨
      (c i ≠ 1 ∧ c i ≠ 2 ∧ c i ≠ 3 ∧ v = 0) := by
    intro i
    by_cases h1 : c i = 1
    · exact ⟨1, Or.inl ⟨h1, rfl⟩⟩
    by_cases h2 : c i = 2
    · exact ⟨2, Or.inr (Or.inl ⟨h2, rfl⟩)⟩
    by_cases h3 : c i = 3
    · exact ⟨3, Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))⟩
    exact ⟨0, Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, rfl⟩))⟩
  choose kd hkd using hkex
  have k0 : ∀ i, kd i = 0 ↔ (c i = 0 ∨ 4 ≤ c i) := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k1 : ∀ i, kd i = 1 ↔ c i = 1 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k2 : ∀ i, kd i = 2 ↔ c i = 2 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k3 : ∀ i, kd i = 3 ↔ c i = 3 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have hlenD := newGates_len c gs
  have hD : ∀ i : Fin (newGates c gs).length,
      ∃ g, gs[(i : ℕ)]? = some g ∧ (newGates c gs).get i = newGate c i g := by
    intro i
    exact newGates_inv c gs i _ (by simp)
  have toFin : ∀ (i : Fin (newGates c gs).length) (w : ℕ), w < 26 + (i : ℕ) → 26 ≤ w →
      ∀ P : Fin 4 → Prop, P (kd (w - 26)) →
      ∃ j : Fin (newGates c gs).length, w = 26 + (j : ℕ) ∧ P (kd j) := by
    intro i w hw h26 P hP
    have hi := i.2
    refine ⟨⟨w - 26, by omega⟩, ?_, hP⟩
    show w = 26 + (w - 26)
    omega
  have hfin : 64 ≤ (newGates c gs).length → 64 ≤ gs.length := fun h => by rw [hlenD] at h; exact h
  apply hfin
  refine main (newGates c gs) (fun i => kd i) ⟨jo, by rw [hlenD]; exact hjo⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨g0, hg0, e⟩ := newGates_inv c gs i _ (List.getElem?_eq_getElem hi)
    rw [e]
    obtain ⟨⟨ho, hl, _⟩, _⟩ := H i g0 hg0
    exact ⟨newGate_op c i g0 ho, le_trans (newGate_len c i g0) hl⟩
  · intro i w hw
    obtain ⟨g, hg, e⟩ := hD i
    rw [e] at hw
    exact (H i g hg).1.2.2 w (newGate_sub c i g w hw)
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    rcases (k0 i).1 hk with h | h
    · refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
      obtain ⟨hw1, hw2⟩ := (mem0 c i g w h).1 hw
      rcases hw2 with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 0)
          ((k0 _).2 (Or.inl hcw)))
    · rw [eq4 c i g h]
      exact ⟨rfl, fun w hw => by simp at hw⟩
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k1 i).1 hk
    refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := (mem1 c i g w h).1 hw
    rcases hw2 with h13 | ⟨h26, hcw⟩
    · exact Or.inl h13
    · exact Or.inr (toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 1) ((k1 _).2 hcw))
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k2 i).1 hk
    rw [eq2 c i g h]
    obtain ⟨hand, a, b, hsh, ha, hb⟩ := (H i g hg).2.2.1 h
    have hma : a ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
    have hmb : b ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
    refine ⟨hand, a, b, hsh, ?_, ?_⟩
    · rcases ha with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i a ((H i g hg).1.2.2 a hma) h26 (fun v => v = 0)
          ((k0 _).2 (Or.inl hcw)))
    · rcases hb with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i b ((H i g hg).1.2.2 b hmb) h26 (fun v => v = 1) ((k1 _).2 hcw))
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k3 i).1 hk
    refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
    obtain ⟨hw1, h26, hcw⟩ := (mem3 c i g w h).1 hw
    refine toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 2 ∨ v = 3) ?_
    rcases hcw with hcw | hcw
    · exact Or.inl ((k2 _).2 hcw)
    · exact Or.inr ((k3 _).2 hcw)
  · rcases hco with hco | hco
    · exact Or.inl ((k2 _).2 hco)
    · exact Or.inr ((k3 _).2 hco)
  · intro p l hpl
    rcases top gs c H p l _ (hacc p l hpl) with ⟨_, h⟩ | h
    · exact h
    · exact absurd h hBadOut
  · intro Q h1 h2
    by_contra hne
    have ht : V (newGates c gs) (inp Q (TQ Q)) (26 + jo) = true := by simpa using hne
    have h3 := dom gs c H _ (inp_len _ _) _ ht
    rw [hrej Q h1 h2] at h3
    exact Bool.false_ne_true h3

end PEqualNP.Outside.L_meta_1751

theorem PEqualNP.Outside.L_meta_1751 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → ¬x3 x4 → (64 : ℕ) ≤ x4.size := by
  intro x1 x2 x3 C hmon hback hsound hnn
  obtain ⟨gs, out⟩ := C
  have hacc := hsound.1
  have hrej := hsound.2
  refine PEqualNP.Outside.L_meta_1751.core gs out hmon hback hnn ?_ ?_
  · intro p l hpl
    have he : PEqualNP.Outside.L_meta_1751.inp {p} {l}
        = List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l)) := by
      unfold PEqualNP.Outside.L_meta_1751.inp
      simp only [Finset.mem_singleton]
    rw [← PEqualNP.Outside.L_meta_1751.eval_eq, he]
    exact hacc p l hpl
  · intro Q hc hk
    have he : PEqualNP.Outside.L_meta_1751.inp Q (PEqualNP.Outside.L_meta_1751.TQ Q)
        = List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 =>
            decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) := by
      unfold PEqualNP.Outside.L_meta_1751.inp PEqualNP.Outside.L_meta_1751.TQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← PEqualNP.Outside.L_meta_1751.eval_eq, he]
    exact hrej Q hc hk
