import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1961_aux

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


namespace L1961

def isQuad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ k : Fin 13,
    (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2

def isInc26 (a b : Fin 26) : Bool :=
  if ha : a.1 < 13 then
    if hb : 13 ≤ b.1 then
      decide ((⟨a.1, ha⟩ : Fin 13) - ⟨b.1 - 13, by omega⟩ ∈ ({0, 1, 3, 9} : Finset (Fin 13)))
    else false
  else
    if hb : b.1 < 13 then
      decide ((⟨b.1, hb⟩ : Fin 13) - ⟨a.1 - 13, by omega⟩ ∈ ({0, 1, 3, 9} : Finset (Fin 13)))
    else false

def qHit (Q : Finset (Fin 13)) (a : Fin 26) : Bool :=
  if h : a.1 < 13 then decide (⟨a.1, h⟩ ∈ Q) else decide (⟨a.1 - 13, by omega⟩ ∈ TQ Q)

lemma qHit_eq_V (gs : List Gate) (Q : Finset (Fin 13)) (a : Fin 26) :
    V gs (inp Q (TQ Q)) a.1 = qHit Q a := by
  by_cases ha : a.1 < 13
  · rw [V_point gs Q (TQ Q) a.1 ha]; simp [qHit, ha]
  · rw [V_line gs Q (TQ Q) a.1 (by omega) a.2]; simp [qHit, ha]

lemma isInc26_symm (a b : Fin 26) : isInc26 a b = isInc26 b a := by
  unfold isInc26
  by_cases ha : a.1 < 13 <;> by_cases hb : b.1 < 13
  · have ha' : ¬ 13 ≤ a.1 := by omega
    have hb' : ¬ 13 ≤ b.1 := by omega
    simp [ha, hb, ha', hb']
  · have hb' : 13 ≤ b.1 := by omega
    simp [ha, hb, hb']
  · have ha' : 13 ≤ a.1 := by omega
    simp [ha, hb, ha']
  · simp [ha, hb]

lemma isInc26_self (a : Fin 26) : isInc26 a a = false := by
  unfold isInc26
  by_cases ha : a.1 < 13
  · have ha' : ¬ 13 ≤ a.1 := by omega
    simp [ha, ha']
  · simp [ha]

lemma isInc26_bipartite (a b c : Fin 26) (hab : isInc26 a b = true) (hbc : isInc26 b c = true) :
    isInc26 a c = false := by
  have hdiff : ∀ x y : Fin 26, isInc26 x y = true → (x.1 < 13 ↔ ¬ y.1 < 13) := by
    intro x y hxy
    unfold isInc26 at hxy
    by_cases hx : x.1 < 13 <;> by_cases hy : y.1 < 13
    · have : ¬ 13 ≤ y.1 := by omega
      simp [hx, this] at hxy
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy] at hxy
  have h1 := hdiff a b hab
  have h2 := hdiff b c hbc
  by_contra hne
  have hac : isInc26 a c = true := by cases h : isInc26 a c <;> simp_all
  have h3 := hdiff a c hac
  tauto

lemma unique_common_inc (a b c d : Fin 26) (hne : a ≠ b)
    (hac : isInc26 a c = true) (hbc : isInc26 b c = true)
    (had : isInc26 a d = true) (hbd : isInc26 b d = true) : c = d := by
  by_cases hc : c.1 < 13
  · have ha : 13 ≤ a.1 := by
      by_contra ha'; unfold isInc26 at hac; have : ¬ 13 ≤ c.1 := by omega
      simp [show a.1 < 13 by omega, this] at hac
    have hb : 13 ≤ b.1 := by
      by_contra hb'; unfold isInc26 at hbc; have : ¬ 13 ≤ c.1 := by omega
      simp [show b.1 < 13 by omega, this] at hbc
    have hd : d.1 < 13 := by
      by_contra hd'; unfold isInc26 at had; simp [show ¬ a.1 < 13 by omega, hd'] at had
    let la : Fin 13 := ⟨a.1 - 13, by omega⟩
    let lb : Fin 13 := ⟨b.1 - 13, by omega⟩
    have hlab : la ≠ lb := by
      intro e; apply hne; ext; simp only [la, lb, Fin.ext_iff] at e; omega
    have hac' : (⟨c.1, hc⟩ : Fin 13) - la ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at hac; have ha0 : ¬ a.1 < 13 := by omega
      simpa [ha0, hc, la] using hac
    have hbc' : (⟨c.1, hc⟩ : Fin 13) - lb ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at hbc; have hb0 : ¬ b.1 < 13 := by omega
      simpa [hb0, hc, lb] using hbc
    have had' : (⟨d.1, hd⟩ : Fin 13) - la ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at had; have ha0 : ¬ a.1 < 13 := by omega
      simpa [ha0, hd, la] using had
    have hbd' : (⟨d.1, hd⟩ : Fin 13) - lb ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at hbd; have hb0 : ¬ b.1 < 13 := by omega
      simpa [hb0, hd, lb] using hbd
    have hc_mem : (⟨c.1, hc⟩ : Fin 13) ∈ Pl la ∩ Pl lb := by
      simp only [Pl, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hac', hbc'⟩
    have hd_mem : (⟨d.1, hd⟩ : Fin 13) ∈ Pl la ∩ Pl lb := by
      simp only [Pl, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨had', hbd'⟩
    have hle := Finset.card_le_one.1 (geo_points la lb hlab) _ hc_mem _ hd_mem
    ext; simpa [Fin.ext_iff] using hle
  · have ha : a.1 < 13 := by
      by_contra ha'; unfold isInc26 at hac; have hc0 : ¬ c.1 < 13 := hc
      simp [ha', hc0] at hac
    have hb : b.1 < 13 := by
      by_contra hb'; unfold isInc26 at hbc; have hc0 : ¬ c.1 < 13 := hc
      simp [hb', hc0] at hbc
    have hd : 13 ≤ d.1 := by
      by_contra hd'; unfold isInc26 at had; have : ¬ 13 ≤ d.1 := by omega
      simp [ha, this] at had
    let pa : Fin 13 := ⟨a.1, ha⟩
    let pb : Fin 13 := ⟨b.1, hb⟩
    have hpab : pa ≠ pb := by
      intro e; apply hne; ext; simpa [pa, pb, Fin.ext_iff] using e
    have hac' : pa - (⟨c.1 - 13, by omega⟩ : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at hac; have hc0 : 13 ≤ c.1 := by omega
      simpa [ha, hc0, pa] using hac
    have hbc' : pb - (⟨c.1 - 13, by omega⟩ : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at hbc; have hc0 : 13 ≤ c.1 := by omega
      simpa [hb, hc0, pb] using hbc
    have had' : pa - (⟨d.1 - 13, by omega⟩ : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at had; simpa [ha, hd, pa] using had
    have hbd' : pb - (⟨d.1 - 13, by omega⟩ : Fin 13) ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
      unfold isInc26 at hbd; simpa [hb, hd, pb] using hbd
    have hc_mem : (⟨c.1 - 13, by omega⟩ : Fin 13) ∈ Lp pa ∩ Lp pb := by
      simp only [Lp, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hac', hbc'⟩
    have hd_mem : (⟨d.1 - 13, by omega⟩ : Fin 13) ∈ Lp pa ∩ Lp pb := by
      simp only [Lp, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨had', hbd'⟩
    have hle := Finset.card_le_one.1 (geo_lines pa pb hpab) _ hc_mem _ hd_mem
    ext; have := congrArg Fin.val hle; dsimp at this; omega

lemma star_card_le_4 (z : Fin 26) :
    (Finset.univ.filter (fun a : Fin 26 => isInc26 a z = true)).card ≤ 4 := by
  revert z; decide +kernel

lemma pair_in_quad (a b : Fin 26) (h : isInc26 a b = false) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ qHit Q a = true ∧ qHit Q b = true := by
  by_cases ha : a.1 < 13 <;> by_cases hb : b.1 < 13
  · obtain ⟨h1, h2, h3, h4⟩ := geoPP ⟨a.1, ha⟩ ⟨b.1, hb⟩
    exact ⟨QP ⟨a.1, ha⟩ ⟨b.1, hb⟩, ⟨h1, h2⟩, by simp [qHit, ha, h3], by simp [qHit, hb, h4]⟩
  · have hb' : 13 ≤ b.1 := by omega
    unfold isInc26 at h
    simp only [ha, hb', ↓reduceDIte, decide_eq_false_iff_not] at h
    obtain ⟨h1, h2, h3, h4⟩ := geo_quad ⟨a.1, ha⟩ ⟨b.1 - 13, by omega⟩ h
    exact ⟨Qf ⟨a.1, ha⟩ ⟨b.1 - 13, by omega⟩, ⟨h1, h2⟩, by simp [qHit, ha, h3], by simp [qHit, hb, h4]⟩
  · have ha' : 13 ≤ a.1 := by omega
    unfold isInc26 at h
    simp only [ha, hb, ↓reduceDIte, decide_eq_false_iff_not] at h
    obtain ⟨h1, h2, h3, h4⟩ := geo_quad ⟨b.1, hb⟩ ⟨a.1 - 13, by omega⟩ h
    exact ⟨Qf ⟨b.1, hb⟩ ⟨a.1 - 13, by omega⟩, ⟨h1, h2⟩, by simp [qHit, ha, h4], by simp [qHit, hb, h3]⟩
  · obtain ⟨h1, h2, h3, h4⟩ := geoLL ⟨a.1 - 13, by omega⟩ ⟨b.1 - 13, by omega⟩
    exact ⟨QL ⟨a.1 - 13, by omega⟩ ⟨b.1 - 13, by omega⟩, ⟨h1, h2⟩, by simp [qHit, ha, h3], by simp [qHit, hb, h4]⟩

lemma single_in_quad (a : Fin 26) :
    ∃ Q : Finset (Fin 13), isQuad Q ∧ qHit Q a = true := by
  obtain ⟨Q, hQ, ha, _⟩ := pair_in_quad a a (isInc26_self a)
  exact ⟨Q, hQ, ha⟩

lemma inc_false_on_quad (a b : Fin 26) (hab : isInc26 a b = true) (Q : Finset (Fin 13)) :
    ¬ (qHit Q a = true ∧ qHit Q b = true) := by
  rintro ⟨haQ, hbQ⟩
  unfold isInc26 at hab
  by_cases ha : a.1 < 13
  · have hb : 13 ≤ b.1 := by
      by_contra hb'; simp [ha, hb'] at hab
    have hb0 : ¬ b.1 < 13 := by omega
    simp only [qHit, ha, hb0, ↓reduceDIte, decide_eq_true_eq] at haQ hbQ
    simp only [ha, hb, ↓reduceDIte, decide_eq_true_eq] at hab
    simp only [TQ, Finset.mem_filter, Finset.mem_univ, true_and] at hbQ
    exact hbQ _ haQ hab
  · have hb : b.1 < 13 := by
      by_contra hb'; simp [ha, hb'] at hab
    simp only [qHit, ha, hb, ↓reduceDIte, decide_eq_true_eq] at haQ hbQ
    simp only [ha, hb, ↓reduceDIte, decide_eq_true_eq] at hab
    simp only [TQ, Finset.mem_filter, Finset.mem_univ, true_and] at haQ
    exact haQ _ hbQ hab

lemma gateOp_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    (inputs : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ w ∈ inputs, f1 w = true → f2 w = true) :
    op.eval (inputs.map f1) = true → op.eval (inputs.map f2) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
    intro h b ⟨w, hw, hb⟩
    subst hb
    exact hle w hw (h (f1 w) ⟨w, hw, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
    rintro ⟨b, ⟨w, hw, rfl⟩, hfw⟩
    exact ⟨f2 w, ⟨w, hw, rfl⟩, hle w hw hfw⟩

lemma wiresFrom_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
    (∀ i, w1.getD i false = true → w2.getD i false = true) →
    ∀ i, (wiresFrom gs w1).getD i false = true → (wiresFrom gs w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ hle i hi; exact hle i hi
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hgs g' (by simp [hg'])
    let v1 := g.op.eval (g.inputs.map fun i => w1.getD i false)
    let v2 := g.op.eval (g.inputs.map fun i => w2.getD i false)
    apply ih hgs' (w1 ++ [v1]) (w2 ++ [v2]) (by simp [hlen])
    intro i hi
    by_cases hlt : i < w1.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle i hi
    · by_cases heq : i = w1.length
      · subst heq
        have hv1 : (w1 ++ [v1]).getD w1.length false = v1 := by simp
        have hv2 : (w2 ++ [v2]).getD w1.length false = v2 := by rw [hlen]; simp
        rw [hv1] at hi
        rw [hv2]
        exact gateOp_mono hg g.inputs _ _ (fun w _ hw => hle w hw) hi
      · have hdef : (w1 ++ [v1]).getD i false = false :=
          List.getD_eq_default _ _ (by simp; omega)
        rw [hdef] at hi
        exact absurd hi (by decide)

lemma inCone_lt (C : Circuit) (a b : ℕ) (h : InCone 26 C a b) :
    a < b ∧ b < C.gates.length := by
  have hb : b < C.gates.length := by
    by_contra hnb
    have hl : (cones 26 C).length = C.gates.length := by simp [cones, coneFold_length]
    unfold InCone at h
    rw [List.getD_eq_default _ _ (by omega)] at h
    simp at h
  refine ⟨?_, hb⟩
  induction b using Nat.strong_induction_on generalizing a with
  | ind b ih =>
    rw [inCone_iff 26 C a b hb] at h
    obtain ⟨w, _, h26, hlt, hw | hw⟩ := h
    · omega
    · have := ih (w - 26) (by omega) a hw (by omega)
      omega

lemma inCone_trans (C : Circuit) (a b c : ℕ)
    (hab : InCone 26 C a b) (hbc : InCone 26 C b c) : InCone 26 C a c := by
  have hc := (inCone_lt C b c hbc).2
  induction c using Nat.strong_induction_on generalizing b with
  | ind c ih =>
    rw [inCone_iff 26 C b c hc] at hbc
    rw [inCone_iff 26 C a c hc]
    obtain ⟨w, hw, h26, hlt, rfl | hsub⟩ := hbc
    · exact ⟨w, hw, h26, hlt, Or.inr hab⟩
    · have hlt' : w - 26 < c := by omega
      have hlen' : w - 26 < C.gates.length := by omega
      exact ⟨w, hw, h26, hlt, Or.inr (ih (w - 26) hlt' b hab hsub hlen')⟩

lemma inCone_direct (C : Circuit) (a b : ℕ) (hb : b < C.gates.length)
    (hm : 26 + a ∈ (gateAt C b).inputs) (hab : a < b) : InCone 26 C a b :=
  (inCone_iff 26 C a b hb).2 ⟨26 + a, hm, by omega, by omega, Or.inl (by omega)⟩

lemma andPairs_unique (C : Circuit) (hAP : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    {i j a b : ℕ}
    (hiA : (gateAt C i).op = GateOp.and) (hjA : (gateAt C j).op = GateOp.and) (hij : InCone 26 C i j)
    (haA : (gateAt C a).op = GateOp.and) (hbA : (gateAt C b).op = GateOp.and) (hab : InCone 26 C a b) :
    a = i ∧ b = j := by
  let _ : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hlt1 := inCone_lt C i j hij
  have hlt2 := inCone_lt C a b hab
  unfold PEqualNP.TopForm.andPairs at hAP
  have hAP' : ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter (fun p =>
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2)).card ≤ 1 := by
    convert hAP
  have heq : (a, b) = (i, j) := by
    apply Finset.card_le_one.1 hAP'
    · exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 hlt2.2⟩, haA, hbA, hab⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 hlt1.2⟩, hiA, hjA, hij⟩
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

lemma out_is_gate (gs : List Gate) (out : ℕ)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) out = false) :
    26 ≤ out ∧ out < 26 + gs.length := by
  constructor
  · by_contra hlt
    obtain ⟨Q, hQ, hhit⟩ := single_in_quad ⟨out, by omega⟩
    have hv := qHit_eq_V gs Q ⟨out, by omega⟩
    rw [hhit, hrej Q hQ] at hv
    cases hv
  · by_contra hge
    have h00 := hacc 0 0 (by decide)
    rw [V_out gs _ out (by rw [inp_len]; omega)] at h00
    cases h00

def shiftDel (d w : ℕ) : ℕ :=
  if w < 26 + d then w else if w = 26 + d then 0 else w - 1

def gatesDel (d : ℕ) (gs : List Gate) : List Gate :=
  gs.take d ++ (gs.drop (d + 1)).map (fun g => ⟨g.op, g.inputs.map (shiftDel d)⟩)

lemma gatesDel_len (d : ℕ) (gs : List Gate) (hd : d < gs.length) :
    (gatesDel d gs).length = gs.length - 1 := by
  simp [gatesDel, Nat.min_eq_left (Nat.le_of_lt hd)]
  omega

lemma gatesDel_getElem_lt (d : ℕ) (gs : List Gate) (hd : d < gs.length) (k : ℕ) (hk : k < d) :
    (gatesDel d gs)[k]? = gs[k]? := by
  unfold gatesDel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk]

lemma gatesDel_getElem_ge (d : ℕ) (gs : List Gate) (hd : d < gs.length) (k : ℕ) (hk : d ≤ k)
    (_hk2 : k + 1 < gs.length) :
    (gatesDel d gs)[k]? = (gs[k + 1]?).map (fun g => ⟨g.op, g.inputs.map (shiftDel d)⟩) := by
  unfold gatesDel
  have hlt : (gs.take d).length = d := by simp [Nat.min_eq_left (Nat.le_of_lt hd)]
  rw [List.getElem?_append_right (by omega), hlt, List.getElem?_map, List.getElem?_drop]
  have hadd : d + 1 + (k - d) = k + 1 := by omega
  rw [hadd]

lemma gatesDel_mono (d : ℕ) (gs : List Gate)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ gatesDel d gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  unfold gatesDel at hg
  rcases List.mem_append.1 hg with hg | hg
  · exact hmon g (List.mem_of_mem_take hg)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have hm := hmon g0 (List.mem_of_mem_drop hg0)
    exact ⟨hm.1, by simp [hm.2]⟩

lemma gatesDel_readsBack (d : ℕ) (gs : List Gate) (hd : d < gs.length) (hback : ReadsBack 26 ⟨gs, 0⟩) :
    ReadsBack 26 ⟨gatesDel d gs, 0⟩ := by
  intro k hk w hw
  have hlen : (gatesDel d gs).length = gs.length - 1 := gatesDel_len d gs hd
  dsimp only at hk
  rw [hlen] at hk
  by_cases hkd : k < d
  · have hg := gatesDel_getElem_lt d gs hd k hkd
    have hga : gateAt ⟨gatesDel d gs, 0⟩ k = gateAt ⟨gs, 0⟩ k := by
      simp [gateAt, List.getD_eq_getElem?_getD, hg]
    rw [hga] at hw
    have hk0 : k < gs.length := by omega
    exact hback k hk0 w hw
  · have hk2 : k + 1 < gs.length := by omega
    have hg := gatesDel_getElem_ge d gs hd k (by omega) hk2
    obtain ⟨g0, hg0, hgk⟩ : ∃ g0, gs[k + 1]? = some g0 ∧
        gateAt ⟨gatesDel d gs, 0⟩ k = ⟨g0.op, g0.inputs.map (shiftDel d)⟩ := by
      have : gs[k + 1]? = some gs[k + 1] := List.getElem?_eq_getElem hk2
      refine ⟨gs[k + 1], this, ?_⟩
      simp [gateAt, List.getD_eq_getElem?_getD, hg, this]
    rw [hgk] at hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
    have hb0 := hback (k + 1) hk2 w0 (by simpa [gateAt, List.getD_eq_getElem?_getD, hg0] using hw0)
    unfold shiftDel
    split_ifs <;> omega

lemma gatesDel_eval (d out : ℕ) (gs : List Gate) (hd : d < gs.length)
    (hback : ReadsBack 26 ⟨gs, out⟩) (x : List Bool) (hx : x.length = 26) :
    ∀ w : ℕ, w < 26 + gs.length → w ≠ 26 + d →
      (26 ≤ w → ¬ InCone 26 ⟨gs, out⟩ d (w - 26)) →
      V (gatesDel d gs) x (shiftDel d w) = V gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hwd hwn
    by_cases hw26 : w < 26
    · have hs : shiftDel d w = w := by unfold shiftDel; rw [ite_eq_left (by omega)]
      rw [hs, V_in (gatesDel d gs) gs x w (by rw [hx]; exact hw26)]
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      have hkd : k ≠ d := by omega
      have hnck : ¬ InCone 26 ⟨gs, out⟩ d k := by simpa using hwn (by omega)
      have hga : gateAt ⟨gs, out⟩ k = gs[k] := gateAt_eq ⟨gs, out⟩ k hk
      have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
      have hbDel := gatesDel_readsBack d gs hd (fun m hm => hback m hm)
      by_cases hlt : k < d
      · have hs : shiftDel d (26 + k) = 26 + k := by unfold shiftDel; rw [ite_eq_left (by omega)]
        rw [hs]
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hg' : (gatesDel d gs)[k]? = some gs[k] := by rw [gatesDel_getElem_lt d gs hd k hlt, hg0]
        rw [gate_val_aux gs x hx k gs[k] hg0 hb0, gate_val_aux (gatesDel d gs) x hx k gs[k] hg' hb0]
        congr 1
        apply List.map_inj_left.2
        intro u hu
        have hu' : u < 26 + k := hb0 u hu
        have hsd : shiftDel d u = u := by unfold shiftDel; rw [ite_eq_left (by omega)]
        conv_lhs => rw [← hsd]
        apply ih u (by omega) (by omega) (by omega)
        intro hu26 hic
        apply hnck
        have hwa : u ∈ (gateAt ⟨gs, out⟩ k).inputs := by rw [hga]; exact hu
        exact (inCone_iff 26 ⟨gs, out⟩ d k hk).2 ⟨u, hwa, hu26, hu', Or.inr hic⟩
      · have hkgt : d < k := by omega
        have hs : shiftDel d (26 + k) = 26 + (k - 1) := by
          unfold shiftDel
          have h1 : ¬ 26 + k < 26 + d := by omega
          have h2 : ¬ 26 + k = 26 + d := by omega
          rw [ite_eq_right h1, ite_eq_right h2]; omega
        rw [hs]
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        let g' : Gate := ⟨gs[k].op, gs[k].inputs.map (shiftDel d)⟩
        have hg' : (gatesDel d gs)[k - 1]? = some g' := by
          have hg1 := gatesDel_getElem_ge d gs hd (k - 1) (by omega) (by omega)
          have hsub : k - 1 + 1 = k := by omega
          rw [hsub, hg0] at hg1
          simpa [g'] using hg1
        have hgd' : gateAt ⟨gatesDel d gs, 0⟩ (k - 1) = g' := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg']
        have hb' : ∀ v ∈ g'.inputs, v < 26 + (k - 1) := by
          intro v hv; rw [← hgd'] at hv; exact hbDel (k - 1) (by rw [gatesDel_len d gs hd]; omega) v hv
        rw [gate_val_aux gs x hx k gs[k] hg0 hb0, gate_val_aux (gatesDel d gs) x hx (k - 1) g' hg' hb']
        simp only [g', List.map_map]
        congr 1
        apply List.map_inj_left.2
        intro u hu
        have hu' : u < 26 + k := hb0 u hu
        have hud : u ≠ 26 + d := by
          intro hue
          apply hnck
          have hwa : u ∈ (gateAt ⟨gs, out⟩ k).inputs := by rw [hga]; exact hu
          exact (inCone_iff 26 ⟨gs, out⟩ d k hk).2 ⟨u, hwa, by omega, hu', Or.inl (by omega)⟩
        apply ih u (by omega) (by omega) hud
        intro hu26 hic
        apply hnck
        have hwa : u ∈ (gateAt ⟨gs, out⟩ k).inputs := by rw [hga]; exact hu
        exact (inCone_iff 26 ⟨gs, out⟩ d k hk).2 ⟨u, hwa, hu26, hu', Or.inr hic⟩

def pureOr (gs : List Gate) (w : ℕ) : Prop :=
  26 ≤ w → w - 26 < gs.length ∧ (gateAt ⟨gs, 0⟩ (w - 26)).op = GateOp.or ∧
    ∀ a : ℕ, InCone 26 ⟨gs, 0⟩ a (w - 26) → (gateAt ⟨gs, 0⟩ a).op = GateOp.or

lemma pureOr_step (gs : List Gate)
    (k : ℕ) (hk : k < gs.length) (hop : (gateAt ⟨gs, 0⟩ k).op = GateOp.or)
    (hin : ∀ u ∈ (gateAt ⟨gs, 0⟩ k).inputs, pureOr gs u) :
    pureOr gs (26 + k) := by
  intro _
  rw [Nat.add_sub_cancel_left]
  refine ⟨hk, hop, ?_⟩
  intro a ha
  rw [inCone_iff 26 ⟨gs, 0⟩ a k hk] at ha
  obtain ⟨u, hu, hu26, _, rfl | hic⟩ := ha
  · exact (hin u hu hu26).2.1
  · exact (hin u hu hu26).2.2 a hic

lemma no_nested_and_of_all_and_pureOr (gs : List Gate) (out : ℕ)
    (hand : ∀ k < gs.length, (gateAt ⟨gs, 0⟩ k).op = GateOp.and →
      ∀ u ∈ (gateAt ⟨gs, 0⟩ k).inputs, pureOr gs u) :
    ¬ ∃ a b : ℕ, (gateAt ⟨gs, out⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs, out⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ a b := by
  rintro ⟨a, b, ha, hb, hab⟩
  have hlt := inCone_lt ⟨gs, out⟩ a b hab
  dsimp only at hlt
  have hb' : (gateAt ⟨gs, 0⟩ b).op = GateOp.and := hb
  rw [inCone_iff 26 ⟨gs, out⟩ a b hlt.2] at hab
  obtain ⟨u, hu, hu26, _, rfl | hic⟩ := hab
  · have hpu := (hand b hlt.2 hb' u hu hu26).2.1
    change (gateAt ⟨gs, 0⟩ (u - 26)).op = GateOp.and at ha
    rw [hpu] at ha; cases ha
  · have hpu := (hand b hlt.2 hb' u hu hu26).2.2 a hic
    change (gateAt ⟨gs, 0⟩ a).op = GateOp.and at ha
    rw [hpu] at ha; cases ha

def orSetAvoid (gs : List Gate) (avoid : ℕ) (w : ℕ) : Finset (Fin 26) :=
  if hw : w < 26 then {⟨w, hw⟩}
  else if w = 26 + avoid then ∅
  else
    match gs[w - 26]? with
    | some g =>
      match g.op with
      | GateOp.or =>
        g.inputs.toFinset.biUnion (fun u => if u < w then orSetAvoid gs avoid u else ∅)
      | _ => ∅
    | none => ∅
termination_by w

lemma orSetAvoid_lt (gs : List Gate) (avoid w : ℕ) (hw : w < 26) :
    orSetAvoid gs avoid w = {⟨w, hw⟩} := by
  rw [orSetAvoid]; simp [hw]

lemma orSetAvoid_self (gs : List Gate) (avoid : ℕ) :
    orSetAvoid gs avoid (26 + avoid) = ∅ := by
  rw [orSetAvoid]
  have h1 : ¬ 26 + avoid < 26 := by omega
  simp [h1]

lemma orSetAvoid_or (gs : List Gate) (avoid k : ℕ) (g : Gate) (hk : k ≠ avoid)
    (hg : gs[k]? = some g) (hop : g.op = GateOp.or) (hb : ∀ u ∈ g.inputs, u < 26 + k) :
    orSetAvoid gs avoid (26 + k) = g.inputs.toFinset.biUnion (fun u => orSetAvoid gs avoid u) := by
  rw [orSetAvoid]
  have h1 : ¬ 26 + k < 26 := by omega
  have h2 : ¬ 26 + k = 26 + avoid := by omega
  simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hg, hop]
  ext a
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro ⟨u, hu, ha⟩
    split_ifs at ha with hlt
    · exact ⟨u, hu, ha⟩
    · simp at ha
  · rintro ⟨u, hu, ha⟩
    exact ⟨u, hu, by simp [hb u hu, ha]⟩

lemma orSetAvoid_sound (gs : List Gate) (avoid : ℕ) (hback : ReadsBack 26 ⟨gs, 0⟩)
    (x : List Bool) (hx : x.length = 26) :
    ∀ w : ℕ, w < 26 + gs.length →
      (∃ a ∈ orSetAvoid gs avoid w, x.getD a.1 false = true) → V gs x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt ⟨a, ha, hxa⟩
    by_cases hw26 : w < 26
    · rw [orSetAvoid_lt gs avoid w hw26, Finset.mem_singleton] at ha
      rw [ha] at hxa
      unfold V
      rw [getD_wiresFrom _ _ _ (by rw [hx]; exact hw26)]
      exact hxa
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      by_cases hka : k = avoid
      · subst hka; rw [orSetAvoid_self] at ha; simp at ha
      · rw [orSetAvoid] at ha
        have h1 : ¬ 26 + k < 26 := by omega
        have h2 : ¬ 26 + k = 26 + avoid := by omega
        simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hg0] at ha
        cases hop : gs[k].op with
        | or =>
          simp only [hop, Finset.mem_biUnion, List.mem_toFinset] at ha
          obtain ⟨u, hu, hau⟩ := ha
          have hult : u < 26 + k := hb0 u hu
          simp only [hult] at hau
          have hvu := ih u hult (by omega) ⟨a, hau, hxa⟩
          rw [gate_val_aux gs x hx k gs[k] hg0 hb0, hop]
          simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
          exact ⟨true, ⟨u, hu, hvu⟩, rfl⟩
        | _ => simp [hop] at ha

lemma orSetAvoid_complete (gs : List Gate) (avoid : ℕ) (hback : ReadsBack 26 ⟨gs, 0⟩)
    (x : List Bool) (hx : x.length = 26) (hav : V gs x (26 + avoid) = false) :
    ∀ w : ℕ, w < 26 + gs.length → (26 ≤ w → w ≠ 26 + avoid) →
      (∀ m : ℕ, 26 ≤ w → (m = w - 26 ∨ InCone 26 ⟨gs, 0⟩ m (w - 26)) → m ≠ avoid →
        (gateAt ⟨gs, 0⟩ m).op = GateOp.or) →
      V gs x w = true → ∃ a ∈ orSetAvoid gs avoid w, x.getD a.1 false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hne hor hVw
    by_cases hw26 : w < 26
    · refine ⟨⟨w, hw26⟩, by rw [orSetAvoid_lt gs avoid w hw26]; simp, ?_⟩
      unfold V at hVw
      rw [getD_wiresFrom _ _ _ (by rw [hx]; exact hw26)] at hVw
      exact hVw
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      have hka : k ≠ avoid := by have := hne (by omega); omega
      have hop : (gateAt ⟨gs, 0⟩ k).op = GateOp.or := hor k (by omega) (Or.inl (by omega)) hka
      have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
      have hop0 : gs[k].op = GateOp.or := by rw [← hga]; exact hop
      rw [orN gs x hx k gs[k] hg0 hb0 hop0] at hVw
      obtain ⟨u, hu, hVu⟩ := hVw
      have hult : u < 26 + k := hb0 u hu
      have hne_u : 26 ≤ u → u ≠ 26 + avoid := by
        intro hu26 heq; rw [heq, hav] at hVu; cases hVu
      have hor_u : ∀ m : ℕ, 26 ≤ u → (m = u - 26 ∨ InCone 26 ⟨gs, 0⟩ m (u - 26)) → m ≠ avoid →
          (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
        intro m hu26 hrel hma
        have hu' : u ∈ (gateAt ⟨gs, 0⟩ k).inputs := by rw [hga]; exact hu
        have hmk : InCone 26 ⟨gs, 0⟩ m k :=
          (inCone_iff 26 ⟨gs, 0⟩ m k hk).2
            ⟨u, hu', hu26, hult, by simpa [Nat.add_sub_cancel_left] using hrel⟩
        exact hor m (by omega) (Or.inr (by simpa [Nat.add_sub_cancel_left] using hmk)) hma
      obtain ⟨a, ha, hxa⟩ := ih u hult (by omega) hne_u hor_u hVu
      refine ⟨a, ?_, hxa⟩
      rw [orSetAvoid_or gs avoid k gs[k] hka hg0 hop0 hb0, Finset.mem_biUnion]
      exact ⟨u, List.mem_toFinset.2 hu, ha⟩

lemma orSetAvoid_nonempty (gs : List Gate) (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hlen : ∀ g ∈ gs, 0 < g.inputs.length) :
    ∀ w : ℕ, w < 26 + gs.length → pureOr gs w → (orSetAvoid gs gs.length w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hpo
    by_cases hw26 : w < 26
    · rw [orSetAvoid_lt gs gs.length w hw26]; simp
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      have hpo' := hpo (by omega)
      rw [Nat.add_sub_cancel_left] at hpo'
      have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
      have hop0 : gs[k].op = GateOp.or := by rw [← hga]; exact hpo'.2.1
      have hpos : 0 < gs[k].inputs.length := hlen gs[k] (List.getElem_mem hk)
      obtain ⟨u, hu⟩ : ∃ u, u ∈ gs[k].inputs := by
        cases h : gs[k].inputs with
        | nil => rw [h] at hpos; simp at hpos
        | cons x _ => exact ⟨x, by simp⟩
      have hult : u < 26 + k := hb0 u hu
      have hpo_u : pureOr gs u := by
        intro hu26
        refine ⟨by omega, hpo'.2.2 (u - 26) ?_, fun a ha => hpo'.2.2 a ?_⟩
        · exact (inCone_iff 26 ⟨gs, 0⟩ (u - 26) k hk).2 ⟨u, by rw [hga]; exact hu, hu26, hult, Or.inl rfl⟩
        · exact (inCone_iff 26 ⟨gs, 0⟩ a k hk).2 ⟨u, by rw [hga]; exact hu, hu26, hult, Or.inr ha⟩
      obtain ⟨a, ha⟩ := ih u hult (by omega) hpo_u
      refine ⟨a, ?_⟩
      rw [orSetAvoid_or gs gs.length k gs[k] (by omega) hg0 hop0 hb0, Finset.mem_biUnion]
      exact ⟨u, List.mem_toFinset.2 hu, ha⟩

inductive reachesOr (gs : List Gate) (avoid target : ℕ) : ℕ → Prop
  | base : reachesOr gs avoid target target
  | step {k : ℕ} {g : Gate} {u : ℕ} :
      gs[k]? = some g → k ≠ avoid → g.op = GateOp.or → u ∈ g.inputs → u < 26 + k →
      reachesOr gs avoid target u → reachesOr gs avoid target (26 + k)

lemma reachesOr_orSet (gs : List Gate) (avoid target w : ℕ) (hr : reachesOr gs avoid target w) :
    orSetAvoid gs avoid target ⊆ orSetAvoid gs avoid w := by
  induction hr with
  | base => exact Finset.Subset.rfl
  | @step k _g u hg _hk hop hu hlt _ ih =>
    intro a ha
    rw [orSetAvoid]
    have h1 : ¬ 26 + k < 26 := by omega
    have h2 : ¬ 26 + k = 26 + avoid := by omega
    simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hg, hop,
      Finset.mem_biUnion, List.mem_toFinset]
    exact ⟨u, hu, by simp [hlt, ih ha]⟩

lemma reachesOr_V (gs : List Gate) (avoid target : ℕ) (hback : ReadsBack 26 ⟨gs, 0⟩)
    (x : List Bool) (hx : x.length = 26) :
    ∀ w : ℕ, reachesOr gs avoid target w → V gs x target = true → V gs x w = true := by
  intro w hr ht
  induction hr with
  | base => exact ht
  | @step k g u hg hk hop hu _ _ ih =>
    have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hga : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
    have hb0 : ∀ v ∈ g.inputs, v < 26 + k := fun v hv => hback k hklen v (by rw [hga]; exact hv)
    exact (orN gs x hx k g hg hb0 hop).2 ⟨u, hu, ih⟩

lemma reachesOr_inCone (gs : List Gate) (avoid t w : ℕ) (ht : 26 ≤ t) (hr : reachesOr gs avoid t w) :
    w = t ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ (t - 26) (w - 26)) := by
  induction hr with
  | base => exact Or.inl rfl
  | @step k g u hg _ _ hu hlt _ ih =>
    right
    have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hga : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases ih with rfl | ⟨hu26, hic⟩
    · exact (inCone_iff 26 ⟨gs, 0⟩ (u - 26) k hklen).2 ⟨u, by rw [hga]; exact hu, ht, hlt, Or.inl rfl⟩
    · exact (inCone_iff 26 ⟨gs, 0⟩ (t - 26) k hklen).2 ⟨u, by rw [hga]; exact hu, hu26, hlt, Or.inr hic⟩

inductive reachesAvoiding (gs : List Gate) (skip target : ℕ) : ℕ → Prop
  | base : reachesAvoiding gs skip target target
  | step {k : ℕ} {g : Gate} {u : ℕ} :
      gs[k]? = some g → k ≠ skip → u ∈ g.inputs → u < 26 + k →
      reachesAvoiding gs skip target u → reachesAvoiding gs skip target (26 + k)

lemma reachesAvoiding_split (gs : List Gate) (skip target : ℕ)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w : ℕ, reachesAvoiding gs skip target w →
      reachesOr gs skip target w ∨
      ∃ a : ℕ, ∃ ga : Gate, gs[a]? = some ga ∧ ga.op = GateOp.and ∧ a ≠ skip ∧
        reachesAvoiding gs skip (26 + a) w ∧
        (∃ u ∈ ga.inputs, u < 26 + a ∧ reachesOr gs skip target u) := by
  intro w hr
  induction hr with
  | base => exact Or.inl reachesOr.base
  | @step k g u hg hks hu hlt _ ih =>
    rcases ih with hOr | ⟨a, ga, hga, haop, has, haw, u0, hu0, hult0, hOr0⟩
    · have hgmem : g ∈ gs := List.mem_of_getElem? hg
      rcases hgs g hgmem with hand | hor
      · exact Or.inr ⟨k, g, hg, hand, hks, reachesAvoiding.base, u, hu, hlt, hOr⟩
      · exact Or.inl (reachesOr.step hg hks hor hu hlt hOr)
    · exact Or.inr ⟨a, ga, hga, haop, has, reachesAvoiding.step hg hks hu hlt haw, u0, hu0, hult0, hOr0⟩

lemma reachesAvoiding_inCone (gs : List Gate) (skip t w : ℕ) (ht : 26 ≤ t) (hr : reachesAvoiding gs skip t w) :
    w = t ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ (t - 26) (w - 26)) := by
  induction hr with
  | base => exact Or.inl rfl
  | @step k g u hg _ hu hlt _ ih =>
    right
    have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hga : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases ih with rfl | ⟨hu26, hic⟩
    · exact (inCone_iff 26 ⟨gs, 0⟩ (u - 26) k hklen).2 ⟨u, by rw [hga]; exact hu, ht, hlt, Or.inl rfl⟩
    · exact (inCone_iff 26 ⟨gs, 0⟩ (t - 26) k hklen).2 ⟨u, by rw [hga]; exact hu, hu26, hlt, Or.inr hic⟩

def reachesBadOnlyVia (gs : List Gate) (Bad : Finset ℕ) (top w : ℕ) : Prop :=
  ∀ b ∈ Bad, b ≠ top → ¬ reachesAvoiding gs top (26 + b) w

lemma reachesBadOnlyVia_step (gs : List Gate) (Bad : Finset ℕ) (top k : ℕ) (g : Gate)
    (hk : gs[k]? = some g) (htop : k ≠ top) (hback : ∀ u ∈ g.inputs, u < 26 + k)
    (hreach : reachesBadOnlyVia gs Bad top (26 + k)) :
    ∀ u ∈ g.inputs, reachesBadOnlyVia gs Bad top u := by
  intro u hu b hb hbt hru
  exact hreach b hb hbt (reachesAvoiding.step hk htop hu (hback u hu) hru)

lemma mapIdx_mono (gs : List Gate) (patch : ℕ → Gate → Gate)
    (hp : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
      ((patch k g).op = GateOp.and ∨ (patch k g).op = GateOp.or) ∧ (patch k g).inputs.length ≤ 2) :
    ∀ g ∈ gs.mapIdx patch, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  rw [List.length_mapIdx] at hk
  rw [List.getElem_mapIdx]
  exact hp k gs[k] (List.getElem?_eq_getElem hk)

lemma mapIdx_readsBack (gs : List Gate) (patch : ℕ → Gate → Gate)
    (hp : ∀ (k : ℕ) (g : Gate), gs[k]? = some g → ∀ u ∈ (patch k g).inputs, u < 26 + k) :
    ReadsBack 26 ⟨gs.mapIdx patch, 0⟩ := by
  intro k hk u hu
  dsimp only at hk
  rw [List.length_mapIdx] at hk
  have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
  have hga : gateAt ⟨gs.mapIdx patch, 0⟩ k = patch k gs[k] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_mapIdx, hg0]
  rw [hga] at hu
  exact hp k gs[k] hg0 u hu

lemma mapIdx_eval_up (gs : List Gate) (patch : ℕ → Gate → Gate) (Bad : Finset ℕ) (top : ℕ)
    (hback : ReadsBack 26 ⟨gs, 0⟩) (_hback' : ReadsBack 26 ⟨gs.mapIdx patch, 0⟩)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hkeep : ∀ k g, k ∉ Bad → patch k g = g)
    (x : List Bool) (hx : x.length = 26)
    (htop_up : V gs x (26 + top) = true → V (gs.mapIdx patch) x (26 + top) = true) :
    ∀ w : ℕ, w < 26 + gs.length → reachesBadOnlyVia gs Bad top w →
      V gs x w = true → V (gs.mapIdx patch) x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hr hVw
    by_cases hw26 : w < 26
    · rw [V_in _ gs x w (by rw [hx]; exact hw26)]
      exact hVw
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      by_cases hkt : k = top
      · subst hkt; exact htop_up hVw
      · have hkBad : k ∉ Bad := by
          intro hmem
          exact hr k hmem hkt reachesAvoiding.base
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hg' : (gs.mapIdx patch)[k]? = some gs[k] := by
          simp [List.getElem?_mapIdx, hg0, hkeep k gs[k] hkBad]
        have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
        have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
        have hhop := hgs gs[k] (List.getElem_mem hk)
        rw [gate_val_aux gs x hx k gs[k] hg0 hb0] at hVw
        rw [gate_val_aux (gs.mapIdx patch) x hx k gs[k] hg' hb0]
        refine gateOp_mono hhop gs[k].inputs _ _ (fun u hu => ?_) hVw
        have hult : u < 26 + k := hb0 u hu
        exact ih u hult (by omega) (reachesBadOnlyVia_step gs Bad top k gs[k] hg0 hkt hb0 hr u hu)

lemma mapIdx_eval_down (gs : List Gate) (patch : ℕ → Gate → Gate) (Bad : Finset ℕ) (top : ℕ)
    (hback : ReadsBack 26 ⟨gs, 0⟩) (_hback' : ReadsBack 26 ⟨gs.mapIdx patch, 0⟩)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hkeep : ∀ k g, k ∉ Bad → patch k g = g)
    (x : List Bool) (hx : x.length = 26)
    (htop_dn : V (gs.mapIdx patch) x (26 + top) = true → V gs x (26 + top) = true) :
    ∀ w : ℕ, w < 26 + gs.length → reachesBadOnlyVia gs Bad top w →
      V (gs.mapIdx patch) x w = true → V gs x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hr hVw
    by_cases hw26 : w < 26
    · rw [V_in gs (gs.mapIdx patch) x w (by rw [hx]; exact hw26)]
      exact hVw
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      by_cases hkt : k = top
      · subst hkt; exact htop_dn hVw
      · have hkBad : k ∉ Bad := by
          intro hmem
          exact hr k hmem hkt reachesAvoiding.base
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hg' : (gs.mapIdx patch)[k]? = some gs[k] := by
          simp [List.getElem?_mapIdx, hg0, hkeep k gs[k] hkBad]
        have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
        have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
        have hhop := hgs gs[k] (List.getElem_mem hk)
        rw [gate_val_aux (gs.mapIdx patch) x hx k gs[k] hg' hb0] at hVw
        rw [gate_val_aux gs x hx k gs[k] hg0 hb0]
        refine gateOp_mono hhop gs[k].inputs _ _ (fun u hu => ?_) hVw
        have hult : u < 26 + k := hb0 u hu
        exact ih u hult (by omega) (reachesBadOnlyVia_step gs Bad top k gs[k] hg0 hkt hb0 hr u hu)

def shiftMoveInner (src w : ℕ) : ℕ :=
  if w < 26 + src then w else w - 1

def shiftMoveOuter (src dst w : ℕ) : ℕ :=
  if w < 26 + src then w else if w < 26 + dst then w - 1 else w

def gateMapInner (src : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftMoveInner src)⟩

def gateMapOuter (src dst : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftMoveOuter src dst)⟩

def gatesMoveAfter (gs : List Gate) (src dst : ℕ) (gNew : Gate) : List Gate :=
  gs.take src ++
  ((gs.drop (src + 1)).take (dst - src)).map (gateMapInner src) ++
  [gNew] ++
  (gs.drop (dst + 1)).map (gateMapOuter src dst)

lemma gatesMoveAfter_len (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length) :
    (gatesMoveAfter gs src dst gNew).length = gs.length := by
  unfold gatesMoveAfter
  simp [Nat.min_eq_left (by omega : src ≤ gs.length),
    Nat.min_eq_left (by omega : dst - src ≤ gs.length - (src + 1))]
  omega

lemma gatesMoveAfter_getElem_lt (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length) (k : ℕ) (hk : k < src) :
    (gatesMoveAfter gs src dst gNew)[k]? = gs[k]? := by
  unfold gatesMoveAfter
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk]

lemma gatesMoveAfter_getElem_mid (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length) (k : ℕ) (hk1 : src ≤ k) (hk2 : k < dst) :
    (gatesMoveAfter gs src dst gNew)[k]? = (gs[k + 1]?).map (gateMapInner src) := by
  unfold gatesMoveAfter
  have ht : (gs.take src).length = src := by simp [Nat.min_eq_left (by omega : src ≤ gs.length)]
  have hm : (((gs.drop (src + 1)).take (dst - src)).map (gateMapInner src)).length = dst - src := by
    simp [Nat.min_eq_left (by omega : dst - src ≤ gs.length - (src + 1))]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), ht]
  rw [List.getElem?_append_left (by rw [hm]; omega)]
  rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
  have ha : src + 1 + (k - src) = k + 1 := by omega
  rw [ha]

lemma gatesMoveAfter_getElem_dst (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length) :
    (gatesMoveAfter gs src dst gNew)[dst]? = some gNew := by
  unfold gatesMoveAfter
  have ht : (gs.take src).length = src := by simp [Nat.min_eq_left (by omega : src ≤ gs.length)]
  have hm : (((gs.drop (src + 1)).take (dst - src)).map (gateMapInner src)).length = dst - src := by
    simp [Nat.min_eq_left (by omega : dst - src ≤ gs.length - (src + 1))]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), ht]
  rw [List.getElem?_append_right (by rw [hm]), hm]
  have hsub : dst - src - (dst - src) = 0 := by omega
  rw [hsub]
  simp

lemma gatesMoveAfter_getElem_gt (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length) (k : ℕ) (hk1 : dst < k) :
    (gatesMoveAfter gs src dst gNew)[k]? = (gs[k]?).map (gateMapOuter src dst) := by
  unfold gatesMoveAfter
  have ht : (gs.take src).length = src := by simp [Nat.min_eq_left (by omega : src ≤ gs.length)]
  have hm : (((gs.drop (src + 1)).take (dst - src)).map (gateMapInner src)).length = dst - src := by
    simp [Nat.min_eq_left (by omega : dst - src ≤ gs.length - (src + 1))]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), ht]
  rw [List.getElem?_append_right (by rw [hm]; omega), hm]
  rw [List.getElem?_append_right (by simp; omega), List.length_singleton]
  rw [List.getElem?_map, List.getElem?_drop]
  have hsub2 : k - src - (dst - src) - 1 = k - (dst + 1) := by omega
  have hadd : dst + 1 + (k - (dst + 1)) = k := by omega
  rw [hsub2, hadd]

lemma gatesMoveAfter_mono (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hgNew : (gNew.op = GateOp.and ∨ gNew.op = GateOp.or) ∧ gNew.inputs.length ≤ 2) :
    ∀ g ∈ gatesMoveAfter gs src dst gNew, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  unfold gatesMoveAfter at hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with ((hg | ⟨g0, hg0, rfl⟩) | rfl) | ⟨g0, hg0, rfl⟩
  · exact hmon g (List.mem_of_mem_take hg)
  · have hm := hmon g0 (List.mem_of_mem_drop (List.mem_of_mem_take hg0))
    exact ⟨hm.1, by simp [gateMapInner, hm.2]⟩
  · exact hgNew
  · have hm := hmon g0 (List.mem_of_mem_drop hg0)
    exact ⟨hm.1, by simp [gateMapOuter, hm.2]⟩

lemma gatesMoveAfter_readsBack (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length)
    (hback : ReadsBack 26 ⟨gs, 0⟩) (hgNew : ∀ u ∈ gNew.inputs, u < 26 + dst) :
    ReadsBack 26 ⟨gatesMoveAfter gs src dst gNew, 0⟩ := by
  intro k hk u hu
  dsimp only at hk
  rw [gatesMoveAfter_len gs src dst gNew h1 h2] at hk
  by_cases hks : k < src
  · have hg := gatesMoveAfter_getElem_lt gs src dst gNew h1 h2 k hks
    have hga : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ k = gateAt ⟨gs, 0⟩ k := by
      simp [gateAt, List.getD_eq_getElem?_getD, hg]
    rw [hga] at hu
    exact hback k hk u hu
  · by_cases hkd : k < dst
    · have hg := gatesMoveAfter_getElem_mid gs src dst gNew h1 h2 k (by omega) hkd
      have hk1 : k + 1 < gs.length := by omega
      have hg0 : gs[k + 1]? = some gs[k + 1] := List.getElem?_eq_getElem hk1
      have hga : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ k = gateMapInner src gs[k + 1] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0]
      rw [hga] at hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
      have hbv := hback (k + 1) hk1 v (by rw [gateAt_eq ⟨gs, 0⟩ (k + 1) hk1]; exact hv)
      unfold shiftMoveInner; split_ifs <;> omega
    · by_cases hke : k = dst
      · have hg := gatesMoveAfter_getElem_dst gs src dst gNew h1 h2
        have hga : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ k = gNew := by
          rw [hke]; simp [gateAt, List.getD_eq_getElem?_getD, hg]
        rw [hga] at hu
        rw [hke]
        exact hgNew u hu
      · have hkgt : dst < k := by omega
        have hg := gatesMoveAfter_getElem_gt gs src dst gNew h1 h2 k hkgt
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hga : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ k = gateMapOuter src dst gs[k] := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0]
        rw [hga] at hu
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
        have hbv := hback k hk v (by rw [gateAt_eq ⟨gs, 0⟩ k hk]; exact hv)
        unfold shiftMoveOuter; split_ifs <;> omega

lemma gatesMoveAfter_eval_lt (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length)
    (hback : ReadsBack 26 ⟨gs, 0⟩) (hback' : ReadsBack 26 ⟨gatesMoveAfter gs src dst gNew, 0⟩)
    (hnoread : ∀ m, src < m → m ≤ dst → 26 + src ∉ (gateAt ⟨gs, 0⟩ m).inputs)
    (x : List Bool) (hx : x.length = 26) :
    ∀ w : ℕ, w < 26 + (dst + 1) → w ≠ 26 + src →
      V (gatesMoveAfter gs src dst gNew) x (shiftMoveInner src w) = V gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hws
    by_cases hw26 : w < 26
    · have hs : shiftMoveInner src w = w := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
      rw [hs, V_in _ gs x w (by rw [hx]; exact hw26)]
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hb0 : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga]; exact hu)
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      by_cases hks : k < src
      · have hs : shiftMoveInner src (26 + k) = 26 + k := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
        rw [hs]
        have hg' := gatesMoveAfter_getElem_lt gs src dst gNew h1 h2 k hks
        rw [hg0] at hg'
        rw [gate_val_aux gs x hx k gs[k] hg0 hb0, gate_val_aux _ x hx k gs[k] hg' hb0]
        congr 1
        apply List.map_inj_left.2
        intro u hu
        have hu' : u < 26 + k := hb0 u hu
        have hsu : shiftMoveInner src u = u := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
        conv_lhs => rw [← hsu]
        exact ih u hu' (by omega) (by omega)
      · have hkgt : src < k := by omega
        have hs : shiftMoveInner src (26 + k) = 26 + (k - 1) := by
          unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
        rw [hs]
        let g' : Gate := gateMapInner src gs[k]
        have hg' : (gatesMoveAfter gs src dst gNew)[k - 1]? = some g' := by
          have := gatesMoveAfter_getElem_mid gs src dst gNew h1 h2 (k - 1) (by omega) (by omega)
          have ha : k - 1 + 1 = k := by omega
          rw [ha, hg0] at this
          simpa [g'] using this
        have hb' : ∀ v ∈ g'.inputs, v < 26 + (k - 1) := by
          intro v hv
          have hgak : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ (k - 1) = g' := by
            simp [gateAt, List.getD_eq_getElem?_getD, hg']
          rw [← hgak] at hv
          exact hback' (k - 1) (by rw [gatesMoveAfter_len gs src dst gNew h1 h2]; omega) v hv
        rw [gate_val_aux gs x hx k gs[k] hg0 hb0, gate_val_aux _ x hx (k - 1) g' hg' hb']
        simp only [g', gateMapInner, List.map_map]
        congr 1
        apply List.map_inj_left.2
        intro u hu
        have hnr : u ≠ 26 + src := by
          intro heq; subst heq
          exact hnoread k hkgt (by omega) (by rw [hga]; exact hu)
        have hult : u < 26 + k := hb0 u hu
        exact ih u hult (by omega) hnr

end L1961


namespace L1961

lemma core_contra (gs : List Gate) (out : ℕ)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hnn : ¬ ∃ a b : ℕ, (gateAt ⟨gs, 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs, 0⟩ a b)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) out = false) : False := by
  have hle : 64 ≤ gs.length := by
    apply core gs out
    · intro g hg
      obtain ⟨hop, hlen⟩ := hmon g hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h <;> simp [h]
    · intro k hk u hu
      exact hback k hk u hu
    · exact hnn
    · exact hacc
    · intro Q h1 h2
      exact hrej Q ⟨h1, h2⟩
  omega

lemma andN_iff (gs : List Gate) (x : List Bool) (hx : x.length = 26)
    (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (hb : ∀ u ∈ g.inputs, u < 26 + k)
    (hop : g.op = GateOp.and) :
    V gs x (26 + k) = true ↔ ∀ u ∈ g.inputs, V gs x u = true := by
  rw [gate_val_aux gs x hx k g hg hb, hop]
  simp [GateOp.eval]

lemma inCone_reachesAvoiding (gs : List Gate) (a b : ℕ) (h : InCone 26 ⟨gs, 0⟩ a b) :
    reachesAvoiding gs gs.length (26 + a) (26 + b) := by
  have hb := (inCone_lt ⟨gs, 0⟩ a b h).2
  dsimp only at hb
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    rw [inCone_iff 26 ⟨gs, 0⟩ a b hb] at h
    obtain ⟨u, hu, hu26, hult, hrel⟩ := h
    have hga : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hb
    have hg0 : gs[b]? = some gs[b] := List.getElem?_eq_getElem hb
    rw [hga] at hu
    rcases hrel with hua | hic
    · have hueq : u = 26 + a := by omega
      rw [hueq] at hu
      exact reachesAvoiding.step hg0 (by omega) hu (by omega) reachesAvoiding.base
    · have hub : u - 26 < b := by omega
      have hulen : u - 26 < gs.length := by omega
      have hr := ih (u - 26) hub hic hulen
      have hueq : 26 + (u - 26) = u := by omega
      rw [hueq] at hr
      exact reachesAvoiding.step hg0 (by omega) hu hult hr

lemma inCone_avoid_or_via (gs : List Gate) (skip a b : ℕ) (h : InCone 26 ⟨gs, 0⟩ a b) :
    reachesAvoiding gs skip (26 + a) (26 + b) ∨
    (InCone 26 ⟨gs, 0⟩ a skip ∧ (b = skip ∨ InCone 26 ⟨gs, 0⟩ skip b)) := by
  have hb := (inCone_lt ⟨gs, 0⟩ a b h).2
  dsimp only at hb
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    by_cases hbs : b = skip
    · subst hbs; exact Or.inr ⟨h, Or.inl rfl⟩
    · rw [inCone_iff 26 ⟨gs, 0⟩ a b hb] at h
      obtain ⟨u, hu, hu26, hult, hrel⟩ := h
      have hga : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hb
      have hg0 : gs[b]? = some gs[b] := List.getElem?_eq_getElem hb
      rw [hga] at hu
      rcases hrel with hua | hic
      · have hueq : u = 26 + a := by omega
        rw [hueq] at hu
        exact Or.inl (reachesAvoiding.step hg0 hbs hu (by omega) reachesAvoiding.base)
      · have hub : u - 26 < b := by omega
        have hulen : u - 26 < gs.length := by omega
        rcases ih (u - 26) hub hic hulen with hr | ⟨has, hs⟩
        · have hueq : 26 + (u - 26) = u := by omega
          rw [hueq] at hr
          exact Or.inl (reachesAvoiding.step hg0 hbs hu hult hr)
        · refine Or.inr ⟨has, Or.inr ?_⟩
          exact (inCone_iff 26 ⟨gs, 0⟩ skip b hb).2 ⟨u, by rw [hga]; exact hu, hu26, hult, hs.imp Eq.symm id⟩

lemma inCone_gt_reachesAvoiding (gs : List Gate) (skip a b : ℕ) (hsa : skip < a)
    (h : InCone 26 ⟨gs, 0⟩ a b) : reachesAvoiding gs skip (26 + a) (26 + b) := by
  rcases inCone_avoid_or_via gs skip a b h with hr | ⟨has, _⟩
  · exact hr
  · have := (inCone_lt ⟨gs, 0⟩ a skip has).1; omega

lemma reachesOr_first_step (gs : List Gate) (avoid target w : ℕ)
    (hr : reachesOr gs avoid target w) (hne : w ≠ target) :
    ∃ k : ℕ, ∃ g : Gate, gs[k]? = some g ∧ k ≠ avoid ∧ g.op = GateOp.or ∧
      target ∈ g.inputs ∧ reachesOr gs avoid (26 + k) w := by
  induction hr with
  | base => exact absurd rfl hne
  | @step k g u hg hk hop hu hlt hru ih =>
    by_cases hut : u = target
    · subst hut
      exact ⟨k, g, hg, hk, hop, hu, reachesOr.base⟩
    · obtain ⟨k0, g0, hg0, hk0, hop0, hmem0, hreach0⟩ := ih hut
      exact ⟨k0, g0, hg0, hk0, hop0, hmem0, reachesOr.step hg hk hop hu hlt hreach0⟩

def preMove (src dst k : ℕ) : ℕ :=
  if k < src then k else if k < dst then k + 1 else k

lemma gatesMoveAfter_inCone (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hnoread : ∀ m, src < m → m < gs.length → 26 + src ∉ (gateAt ⟨gs, 0⟩ m).inputs) :
    ∀ b < gs.length, b ≠ dst → ¬ InCone 26 ⟨gs, 0⟩ dst (preMove src dst b) →
      ∀ a, InCone 26 ⟨gatesMoveAfter gs src dst gNew, 0⟩ a b →
        a ≠ dst ∧ InCone 26 ⟨gs, 0⟩ (preMove src dst a) (preMove src dst b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro hblen hbdst hndst a hab
    have hblen' : b < (gatesMoveAfter gs src dst gNew).length := by
      rw [gatesMoveAfter_len gs src dst gNew h1 h2]; exact hblen
    rw [inCone_iff 26 ⟨gatesMoveAfter gs src dst gNew, 0⟩ a b hblen'] at hab
    obtain ⟨v, hv, hv26, hvlt, hrel⟩ := hab
    by_cases hbs : b < src
    · have hpm_b : preMove src dst b = b := by unfold preMove; rw [ite_eq_left (by omega)]
      rw [hpm_b]
      have hg := gatesMoveAfter_getElem_lt gs src dst gNew h1 h2 b hbs
      have hg0 : gs[b]? = some gs[b] := List.getElem?_eq_getElem hblen
      have hga' : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ b = gs[b] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0]
      rw [hga'] at hv
      have hga : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hblen
      have hvbd : v < 26 + src := by omega
      have hpm_v : preMove src dst (v - 26) = v - 26 := by
        unfold preMove; rw [ite_eq_left (by omega)]
      have hnv_dst : ¬ InCone 26 ⟨gs, 0⟩ dst (v - 26) := by
        intro hic; have := (inCone_lt ⟨gs, 0⟩ dst (v - 26) hic).1; omega
      rcases hrel with rfl | hic
      · refine ⟨by omega, (inCone_iff 26 ⟨gs, 0⟩ (preMove src dst (v - 26)) b hblen).2 ?_⟩
        rw [hpm_v]
        exact ⟨v, by rw [hga]; exact hv, hv26, hvlt, Or.inl rfl⟩
      · obtain ⟨had, hinc⟩ := ih (v - 26) (by omega) (by omega) (by omega) (by rw [hpm_v]; exact hnv_dst) a hic
        refine ⟨had, (inCone_iff 26 ⟨gs, 0⟩ (preMove src dst a) b hblen).2 ?_⟩
        rw [hpm_v] at hinc
        exact ⟨v, by rw [hga]; exact hv, hv26, hvlt, Or.inr hinc⟩
    · by_cases hbd : b < dst
      · have hpm_b : preMove src dst b = b + 1 := by
          unfold preMove; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [hpm_b]
        have hg := gatesMoveAfter_getElem_mid gs src dst gNew h1 h2 b (by omega) hbd
        have hb1 : b + 1 < gs.length := by omega
        have hg0 : gs[b + 1]? = some gs[b + 1] := List.getElem?_eq_getElem hb1
        have hga' : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ b = gateMapInner src gs[b + 1] := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0]
        rw [hga'] at hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
        have hga : gateAt ⟨gs, 0⟩ (b + 1) = gs[b + 1] := gateAt_eq ⟨gs, 0⟩ (b + 1) hb1
        have hub : u < 26 + (b + 1) := hback (b + 1) hb1 u (by rw [hga]; exact hu)
        have hunr : u ≠ 26 + src := by
          intro heq; subst heq; exact hnoread (b + 1) (by omega) hb1 (by rw [hga]; exact hu)
        have hu26 : 26 ≤ u := by unfold shiftMoveInner at hv26; split_ifs at hv26 <;> omega
        have hpm_v : preMove src dst (shiftMoveInner src u - 26) = u - 26 := by
          unfold shiftMoveInner preMove
          split_ifs <;> omega
        have hvd : shiftMoveInner src u - 26 < dst := by
          unfold shiftMoveInner at hvlt ⊢; omega
        have hnv_dst : ¬ InCone 26 ⟨gs, 0⟩ dst (u - 26) := by
          intro hic; have := (inCone_lt ⟨gs, 0⟩ dst (u - 26) hic).1; omega
        rcases hrel with rfl | hic
        · refine ⟨by omega, (inCone_iff 26 ⟨gs, 0⟩ (preMove src dst (shiftMoveInner src u - 26)) (b + 1) hb1).2 ?_⟩
          rw [hpm_v]
          exact ⟨u, by rw [hga]; exact hu, hu26, hub, Or.inl rfl⟩
        · obtain ⟨had, hinc⟩ := ih (shiftMoveInner src u - 26) (by omega) (by omega) (by omega) (by rw [hpm_v]; exact hnv_dst) a hic
          refine ⟨had, (inCone_iff 26 ⟨gs, 0⟩ (preMove src dst a) (b + 1) hb1).2 ?_⟩
          rw [hpm_v] at hinc
          exact ⟨u, by rw [hga]; exact hu, hu26, hub, Or.inr hinc⟩
      · have hbgt : dst < b := by omega
        have hpm_b : preMove src dst b = b := by
          unfold preMove; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [hpm_b] at hndst ⊢
        have hg := gatesMoveAfter_getElem_gt gs src dst gNew h1 h2 b hbgt
        have hg0 : gs[b]? = some gs[b] := List.getElem?_eq_getElem hblen
        have hga' : gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ b = gateMapOuter src dst gs[b] := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0]
        rw [hga'] at hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
        have hga : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hblen
        have hub : u < 26 + b := hback b hblen u (by rw [hga]; exact hu)
        have hunr : u ≠ 26 + src := by
          intro heq; subst heq; exact hnoread b (by omega) hblen (by rw [hga]; exact hu)
        have hund : u ≠ 26 + dst := by
          intro heq; subst heq
          exact hndst (inCone_direct ⟨gs, 0⟩ dst b hblen (by rw [hga]; exact hu) hbgt)
        have hu26 : 26 ≤ u := by unfold shiftMoveOuter at hv26; split_ifs at hv26 <;> omega
        have hpm_v : preMove src dst (shiftMoveOuter src dst u - 26) = u - 26 := by
          unfold shiftMoveOuter preMove
          split_ifs <;> omega
        have hvd : shiftMoveOuter src dst u - 26 ≠ dst := by
          unfold shiftMoveOuter; split_ifs <;> omega
        have hnv_dst : ¬ InCone 26 ⟨gs, 0⟩ dst (u - 26) := by
          intro hic
          apply hndst
          exact (inCone_iff 26 ⟨gs, 0⟩ dst b hblen).2 ⟨u, by rw [hga]; exact hu, hu26, hub, Or.inr hic⟩
        rcases hrel with rfl | hic
        · refine ⟨hvd, (inCone_iff 26 ⟨gs, 0⟩ (preMove src dst (shiftMoveOuter src dst u - 26)) b hblen).2 ?_⟩
          rw [hpm_v]
          exact ⟨u, by rw [hga]; exact hu, hu26, hub, Or.inl rfl⟩
        · obtain ⟨had, hinc⟩ := ih (shiftMoveOuter src dst u - 26) (by omega) (by omega) hvd (by rw [hpm_v]; exact hnv_dst) a hic
          refine ⟨had, (inCone_iff 26 ⟨gs, 0⟩ (preMove src dst a) b hblen).2 ?_⟩
          rw [hpm_v] at hinc
          exact ⟨u, by rw [hga]; exact hu, hu26, hub, Or.inr hinc⟩

lemma gatesMoveAfter_no_nested_and (gs : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs.length)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hgNew : gNew.op = GateOp.or)
    (hnoread : ∀ m, src < m → m < gs.length → 26 + src ∉ (gateAt ⟨gs, 0⟩ m).inputs)
    (hndst : ∀ b, dst < b → b < gs.length → (gateAt ⟨gs, 0⟩ b).op = GateOp.and → ¬ InCone 26 ⟨gs, 0⟩ dst b)
    (hnn : ¬ ∃ a b : ℕ, (gateAt ⟨gs, 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs, 0⟩ a b) :
    ¬ ∃ a b : ℕ, (gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ b).op = GateOp.and ∧
      InCone 26 ⟨gatesMoveAfter gs src dst gNew, 0⟩ a b := by
  rintro ⟨a, b, ha, hb, hab⟩
  have hlt := inCone_lt ⟨gatesMoveAfter gs src dst gNew, 0⟩ a b hab
  dsimp only at hlt
  rw [gatesMoveAfter_len gs src dst gNew h1 h2] at hlt
  have hop_pre : ∀ k, k < gs.length → k ≠ dst →
      (gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ k).op = (gateAt ⟨gs, 0⟩ (preMove src dst k)).op := by
    intro k hk hkd
    by_cases hks : k < src
    · have hp : preMove src dst k = k := by unfold preMove; rw [ite_eq_left (by omega)]
      rw [hp]
      have hg := gatesMoveAfter_getElem_lt gs src dst gNew h1 h2 k hks
      simp [gateAt, List.getD_eq_getElem?_getD, hg]
    · by_cases hk2 : k < dst
      · have hp : preMove src dst k = k + 1 := by
          unfold preMove; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [hp]
        have hg := gatesMoveAfter_getElem_mid gs src dst gNew h1 h2 k (by omega) hk2
        have hg0 : gs[k + 1]? = some gs[k + 1] := List.getElem?_eq_getElem (by omega)
        simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0, gateMapInner]
      · have hkgt : dst < k := by omega
        have hp : preMove src dst k = k := by
          unfold preMove; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [hp]
        have hg := gatesMoveAfter_getElem_gt gs src dst gNew h1 h2 k hkgt
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        simp [gateAt, List.getD_eq_getElem?_getD, hg, hg0, gateMapOuter]
  have hbdst : b ≠ dst := by
    intro heq
    have hg := gatesMoveAfter_getElem_dst gs src dst gNew h1 h2
    have hgd : (gateAt ⟨gatesMoveAfter gs src dst gNew, 0⟩ b).op = gNew.op := by
      rw [heq]; simp [gateAt, List.getD_eq_getElem?_getD, hg]
    rw [hgd, hgNew] at hb
    cases hb
  have hpb : (gateAt ⟨gs, 0⟩ (preMove src dst b)).op = GateOp.and := by
    rw [← hop_pre b hlt.2 hbdst]; exact hb
  have hndst_b : ¬ InCone 26 ⟨gs, 0⟩ dst (preMove src dst b) := by
    by_cases hbs : b < src
    · have : preMove src dst b = b := by unfold preMove; rw [ite_eq_left (by omega)]
      rw [this]; intro hic; have := (inCone_lt ⟨gs, 0⟩ dst b hic).1; omega
    · by_cases hbd : b < dst
      · have : preMove src dst b = b + 1 := by
          unfold preMove; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rw [this]; intro hic; have := (inCone_lt ⟨gs, 0⟩ dst (b + 1) hic).1; omega
      · have hbgt : dst < b := by omega
        have : preMove src dst b = b := by
          unfold preMove; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [this] at hpb ⊢
        exact hndst b hbgt hlt.2 hpb
  obtain ⟨hadst, hinc⟩ := gatesMoveAfter_inCone gs src dst gNew h1 h2 hback hnoread b hlt.2 hbdst hndst_b a hab
  have hal : a < gs.length := by omega
  have hpa : (gateAt ⟨gs, 0⟩ (preMove src dst a)).op = GateOp.and := by
    rw [← hop_pre a hal hadst]; exact ha
  exact hnn ⟨preMove src dst a, preMove src dst b, hpa, hpb, hinc⟩

lemma gatesMoveAfter_eval_up_ge_rel (gs0 gs1 : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs1.length) (hlen : gs1.length = gs0.length)
    (hgs0 : ∀ g ∈ gs0, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hback0 : ReadsBack 26 ⟨gs0, 0⟩)
    (hback2 : ReadsBack 26 ⟨gatesMoveAfter gs1 src dst gNew, 0⟩)
    (hgt : ∀ k, dst < k → k < gs0.length → gs1[k]? = gs0[k]?)
    (x : List Bool) (hx : x.length = 26)
    (hlo : ∀ k, dst < k → k < gs0.length → ∀ u ∈ (gateAt ⟨gs0, 0⟩ k).inputs, u < 26 + dst →
      V gs0 x u = true → V (gatesMoveAfter gs1 src dst gNew) x (shiftMoveInner src u) = true)
    (hdst : V gs0 x (26 + dst) = true → V (gatesMoveAfter gs1 src dst gNew) x (26 + dst) = true) :
    ∀ k : ℕ, dst ≤ k → k < gs0.length →
      V gs0 x (26 + k) = true → V (gatesMoveAfter gs1 src dst gNew) x (26 + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hdk hk hVk
    by_cases hke : k = dst
    · subst hke; exact hdst hVk
    · have hkgt : dst < k := by omega
      have hga : gateAt ⟨gs0, 0⟩ k = gs0[k] := gateAt_eq ⟨gs0, 0⟩ k hk
      have hb0 : ∀ u ∈ gs0[k].inputs, u < 26 + k := fun u hu => hback0 k hk u (by rw [hga]; exact hu)
      have hg0 : gs0[k]? = some gs0[k] := List.getElem?_eq_getElem hk
      let g' : Gate := gateMapOuter src dst gs0[k]
      have hg' : (gatesMoveAfter gs1 src dst gNew)[k]? = some g' := by
        have := gatesMoveAfter_getElem_gt gs1 src dst gNew h1 h2 k hkgt
        rw [hgt k hkgt hk, hg0] at this
        simpa [g'] using this
      have hb' : ∀ v ∈ g'.inputs, v < 26 + k := by
        intro v hv
        have hgak : gateAt ⟨gatesMoveAfter gs1 src dst gNew, 0⟩ k = g' := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg']
        rw [← hgak] at hv
        exact hback2 k (by rw [gatesMoveAfter_len gs1 src dst gNew h1 h2, hlen]; omega) v hv
      have hhop := hgs0 gs0[k] (List.getElem_mem hk)
      rw [gate_val_aux gs0 x hx k gs0[k] hg0 hb0] at hVk
      rw [gate_val_aux _ x hx k g' hg' hb']
      simp only [g', gateMapOuter, List.map_map]
      refine gateOp_mono hhop gs0[k].inputs _ _ (fun u hu hVu => ?_) hVk
      dsimp only [Function.comp_apply]
      have hult : u < 26 + k := hb0 u hu
      by_cases hud : u < 26 + dst
      · have hsm : shiftMoveOuter src dst u = shiftMoveInner src u := by
          unfold shiftMoveOuter shiftMoveInner; split_ifs <;> rfl
        rw [hsm]
        exact hlo k hkgt hk u (by rw [hga]; exact hu) hud hVu
      · have hsm : shiftMoveOuter src dst u = u := by
          unfold shiftMoveOuter
          have hn1 : ¬ u < 26 + src := by omega
          have hn2 : ¬ u < 26 + dst := hud
          rw [ite_eq_right hn1, ite_eq_right hn2]
        rw [hsm]
        obtain ⟨m, rfl⟩ : ∃ m, u = 26 + m := ⟨u - 26, by omega⟩
        exact ih m (by omega) (by omega) (by omega) hVu

lemma gatesMoveAfter_eval_down_ge_rel (gs0 gs1 : List Gate) (src dst : ℕ) (gNew : Gate)
    (h1 : src < dst) (h2 : dst < gs1.length) (hlen : gs1.length = gs0.length)
    (hgs0 : ∀ g ∈ gs0, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hback0 : ReadsBack 26 ⟨gs0, 0⟩)
    (hback2 : ReadsBack 26 ⟨gatesMoveAfter gs1 src dst gNew, 0⟩)
    (hgt : ∀ k, dst < k → k < gs0.length → gs1[k]? = gs0[k]?)
    (x : List Bool) (hx : x.length = 26)
    (hlo : ∀ k, dst < k → k < gs0.length → ∀ u ∈ (gateAt ⟨gs0, 0⟩ k).inputs, u < 26 + dst →
      V (gatesMoveAfter gs1 src dst gNew) x (shiftMoveInner src u) = true → V gs0 x u = true)
    (hdst : V (gatesMoveAfter gs1 src dst gNew) x (26 + dst) = true → V gs0 x (26 + dst) = true) :
    ∀ k : ℕ, dst ≤ k → k < gs0.length →
      V (gatesMoveAfter gs1 src dst gNew) x (26 + k) = true → V gs0 x (26 + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hdk hk hVk
    by_cases hke : k = dst
    · subst hke; exact hdst hVk
    · have hkgt : dst < k := by omega
      have hga : gateAt ⟨gs0, 0⟩ k = gs0[k] := gateAt_eq ⟨gs0, 0⟩ k hk
      have hb0 : ∀ u ∈ gs0[k].inputs, u < 26 + k := fun u hu => hback0 k hk u (by rw [hga]; exact hu)
      have hg0 : gs0[k]? = some gs0[k] := List.getElem?_eq_getElem hk
      let g' : Gate := gateMapOuter src dst gs0[k]
      have hg' : (gatesMoveAfter gs1 src dst gNew)[k]? = some g' := by
        have := gatesMoveAfter_getElem_gt gs1 src dst gNew h1 h2 k hkgt
        rw [hgt k hkgt hk, hg0] at this
        simpa [g'] using this
      have hb' : ∀ v ∈ g'.inputs, v < 26 + k := by
        intro v hv
        have hgak : gateAt ⟨gatesMoveAfter gs1 src dst gNew, 0⟩ k = g' := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg']
        rw [← hgak] at hv
        exact hback2 k (by rw [gatesMoveAfter_len gs1 src dst gNew h1 h2, hlen]; omega) v hv
      have hhop := hgs0 gs0[k] (List.getElem_mem hk)
      rw [gate_val_aux _ x hx k g' hg' hb'] at hVk
      rw [gate_val_aux gs0 x hx k gs0[k] hg0 hb0]
      simp only [g', gateMapOuter, List.map_map] at hVk
      refine gateOp_mono hhop gs0[k].inputs _ _ (fun u hu hVu => ?_) hVk
      dsimp only [Function.comp_apply] at hVu
      have hult : u < 26 + k := hb0 u hu
      by_cases hud : u < 26 + dst
      · have hsm : shiftMoveOuter src dst u = shiftMoveInner src u := by
          unfold shiftMoveOuter shiftMoveInner; split_ifs <;> rfl
        rw [hsm] at hVu
        exact hlo k hkgt hk u (by rw [hga]; exact hu) hud hVu
      · have hsm : shiftMoveOuter src dst u = u := by
          unfold shiftMoveOuter
          have hn1 : ¬ u < 26 + src := by omega
          have hn2 : ¬ u < 26 + dst := hud
          rw [ite_eq_right hn1, ite_eq_right hn2]
        rw [hsm] at hVu
        obtain ⟨m, rfl⟩ : ∃ m, u = 26 + m := ⟨u - 26, by omega⟩
        exact ih m (by omega) (by omega) (by omega) hVu

def orList (S : Finset (Fin 26)) : List (Fin 26) :=
  (List.finRange 26).filter (fun z => decide (z ∈ S))

lemma orList_mem (S : Finset (Fin 26)) (z : Fin 26) : z ∈ orList S ↔ z ∈ S := by
  simp [orList]

lemma orList_length (S : Finset (Fin 26)) : (orList S).length = S.card := by
  have hnd : (orList S).Nodup := (List.nodup_finRange 26).filter _
  have hts : (orList S).toFinset = S := by
    ext z; simp [orList_mem]
  conv_rhs => rw [← hts]
  rw [List.toFinset_card_of_nodup hnd]

def orElem (S : Finset (Fin 26)) (idx : ℕ) : Fin 26 :=
  let L := orList S
  let a0 := L.getD 0 ⟨0, by omega⟩
  if idx = 0 then a0 else L.getD idx a0

lemma orElem_mem (S : Finset (Fin 26)) (hne : S.Nonempty) (idx : ℕ) : orElem S idx ∈ S := by
  have hlen : 0 < (orList S).length := by rw [orList_length]; exact Finset.Nonempty.card_pos hne
  have ha0 : (orList S).getD 0 ⟨0, by omega⟩ ∈ S := by
    rw [← orList_mem]
    have : (orList S).getD 0 ⟨0, by omega⟩ = (orList S)[0] := by
      simp [List.getD, List.getElem?_eq_getElem hlen]
    rw [this]
    exact List.getElem_mem hlen
  unfold orElem
  split_ifs with h0
  · exact ha0
  · by_cases hi : idx < (orList S).length
    · rw [← orList_mem]
      have : (orList S).getD idx ((orList S).getD 0 ⟨0, by omega⟩) = (orList S)[idx] := by
        simp [List.getD, List.getElem?_eq_getElem hi]
      rw [this]
      exact List.getElem_mem hi
    · have : (orList S).getD idx ((orList S).getD 0 ⟨0, by omega⟩) = (orList S).getD 0 ⟨0, by omega⟩ :=
        List.getD_eq_default _ _ (by omega)
      rw [this]
      exact ha0

lemma orElem_cover (S : Finset (Fin 26)) (hcard : S.card ≤ 4) (a : Fin 26) (ha : a ∈ S) :
    a = orElem S 0 ∨ a = orElem S 1 ∨ a = orElem S 2 ∨ a = orElem S 3 := by
  have hmem : a ∈ orList S := (orList_mem S a).2 ha
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hmem
  have hlen : (orList S).length ≤ 4 := by rw [orList_length]; exact hcard
  have h0123 : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases h0123 with rfl | rfl | rfl | rfl
  · left; simp [orElem, List.getD, List.getElem?_eq_getElem hidx]
  · right; left; simp [orElem, List.getD, List.getElem?_eq_getElem hidx]
  · right; right; left; simp [orElem, List.getD, List.getElem?_eq_getElem hidx]
  · right; right; right; simp [orElem, List.getD, List.getElem?_eq_getElem hidx]

def orGate1 (S : Finset (Fin 26)) : Gate :=
  ⟨GateOp.or, [(orElem S 0).1, (orElem S 1).1]⟩

def orGate2 (S : Finset (Fin 26)) : Gate :=
  ⟨GateOp.or, [(orElem S 2).1, (orElem S 3).1]⟩

lemma orChain3_spec (gs' : List Gate) (s1 s2 s3 : ℕ) (S : Finset (Fin 26))
    (hs12 : s1 < s2) (hs23 : s2 < s3) (hs3 : s3 < gs'.length)
    (hne : S.Nonempty) (hcard : S.card ≤ 4)
    (hg1 : gs'[s1]? = some (orGate1 S))
    (hg2 : gs'[s2]? = some (orGate2 S))
    (hg3 : gs'[s3]? = some ⟨GateOp.or, [26 + s1, 26 + s2]⟩) :
    pureOr gs' (26 + s1) ∧ pureOr gs' (26 + s2) ∧ pureOr gs' (26 + s3) ∧
    ∀ x : List Bool, x.length = 26 →
      (V gs' x (26 + s3) = true ↔ ∃ a ∈ S, x.getD a.1 false = true) := by
  have hga1 : gateAt ⟨gs', 0⟩ s1 = orGate1 S := by simp [gateAt, List.getD_eq_getElem?_getD, hg1]
  have hga2 : gateAt ⟨gs', 0⟩ s2 = orGate2 S := by simp [gateAt, List.getD_eq_getElem?_getD, hg2]
  have hga3 : gateAt ⟨gs', 0⟩ s3 = ⟨GateOp.or, [26 + s1, 26 + s2]⟩ := by
    simp [gateAt, List.getD_eq_getElem?_getD, hg3]
  have hp1 : pureOr gs' (26 + s1) := by
    apply pureOr_step gs' s1 (by omega) (by rw [hga1]; rfl)
    intro u hu hu26
    rw [hga1] at hu
    simp only [orGate1, List.mem_cons, List.not_mem_nil, or_false] at hu
    have h0 : (orElem S 0).1 < 26 := (orElem S 0).2
    have h1 : (orElem S 1).1 < 26 := (orElem S 1).2
    rcases hu with rfl | rfl <;> omega
  have hp2 : pureOr gs' (26 + s2) := by
    apply pureOr_step gs' s2 (by omega) (by rw [hga2]; rfl)
    intro u hu hu26
    rw [hga2] at hu
    simp only [orGate2, List.mem_cons, List.not_mem_nil, or_false] at hu
    have h2 : (orElem S 2).1 < 26 := (orElem S 2).2
    have h3 : (orElem S 3).1 < 26 := (orElem S 3).2
    rcases hu with rfl | rfl <;> omega
  have hp3 : pureOr gs' (26 + s3) := by
    apply pureOr_step gs' s3 hs3 (by rw [hga3])
    intro u hu
    rw [hga3] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact hp1
    · exact hp2
  refine ⟨hp1, hp2, hp3, ?_⟩
  intro x hx
  have hb1 : ∀ u ∈ (orGate1 S).inputs, u < 26 + s1 := by
    intro u hu; simp only [orGate1, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  have hb2 : ∀ u ∈ (orGate2 S).inputs, u < 26 + s2 := by
    intro u hu; simp only [orGate2, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  have hb3 : ∀ u ∈ ([26 + s1, 26 + s2] : List ℕ), u < 26 + s3 := by
    intro u hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> omega
  rw [orN gs' x hx s3 _ hg3 hb3 rfl]
  constructor
  · rintro ⟨w, hw, hVw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rw [orN gs' x hx s1 _ hg1 hb1 rfl] at hVw
      obtain ⟨v, hv, hVv⟩ := hVw
      simp only [orGate1, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · refine ⟨orElem S 0, orElem_mem S hne 0, ?_⟩
        unfold V at hVv; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 0).2)] at hVv; exact hVv
      · refine ⟨orElem S 1, orElem_mem S hne 1, ?_⟩
        unfold V at hVv; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 1).2)] at hVv; exact hVv
    · rw [orN gs' x hx s2 _ hg2 hb2 rfl] at hVw
      obtain ⟨v, hv, hVv⟩ := hVw
      simp only [orGate2, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · refine ⟨orElem S 2, orElem_mem S hne 2, ?_⟩
        unfold V at hVv; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 2).2)] at hVv; exact hVv
      · refine ⟨orElem S 3, orElem_mem S hne 3, ?_⟩
        unfold V at hVv; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 3).2)] at hVv; exact hVv
  · rintro ⟨a, ha, hxa⟩
    rcases orElem_cover S hcard a ha with rfl | rfl | rfl | rfl
    · refine ⟨26 + s1, by simp, ?_⟩
      rw [orN gs' x hx s1 _ hg1 hb1 rfl]
      refine ⟨(orElem S 0).1, by simp [orGate1], ?_⟩
      unfold V; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 0).2)]; exact hxa
    · refine ⟨26 + s1, by simp, ?_⟩
      rw [orN gs' x hx s1 _ hg1 hb1 rfl]
      refine ⟨(orElem S 1).1, by simp [orGate1], ?_⟩
      unfold V; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 1).2)]; exact hxa
    · refine ⟨26 + s2, by simp, ?_⟩
      rw [orN gs' x hx s2 _ hg2 hb2 rfl]
      refine ⟨(orElem S 2).1, by simp [orGate2], ?_⟩
      unfold V; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 2).2)]; exact hxa
    · refine ⟨26 + s2, by simp, ?_⟩
      rw [orN gs' x hx s2 _ hg2 hb2 rfl]
      refine ⟨(orElem S 3).1, by simp [orGate2], ?_⟩
      unfold V; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact (orElem S 3).2)]; exact hxa

lemma reach_reduction (gs : List Gate) (out : ℕ)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, out⟩)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) out = false) :
    (∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧
      (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V C'.gates (inp {p} {l}) C'.output = true) ∧
      (∀ Q : Finset (Fin 13), isQuad Q → V C'.gates (inp Q (TQ Q)) C'.output = false) ∧
      C'.size < gs.length) ∨
    (∃ outG : ℕ, out = 26 + outG ∧ outG + 1 = gs.length ∧
      ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, out⟩ k outG) := by
  obtain ⟨ho1, ho2⟩ := out_is_gate gs out hacc hrej
  obtain ⟨outG, rfl⟩ : ∃ outG, out = 26 + outG := ⟨out - 26, by omega⟩
  have houtG : outG < gs.length := by omega
  by_cases hex : ∃ d < gs.length, d ≠ outG ∧ ¬ InCone 26 ⟨gs, 26 + outG⟩ d outG
  · obtain ⟨d, hd, hdo, hnd⟩ := hex
    let gs' := gatesDel d gs
    let out' := shiftDel d (26 + outG)
    left
    refine ⟨⟨gs', out'⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      have hm := gatesDel_mono d gs hmon g hg
      refine ⟨?_, hm.2⟩
      rcases hm.1 with h | h <;> simp [h]
    · exact gatesDel_readsBack d gs hd (fun k hk u hu => hback k hk u hu)
    · intro p l hp
      have hev := gatesDel_eval d (26 + outG) gs hd hback (inp {p} {l}) (inp_len _ _)
        (26 + outG) (by omega) (by omega) (fun _ => by simpa [Nat.add_sub_cancel_left] using hnd)
      dsimp only [gs', out'] at hev ⊢
      rw [hev]
      exact hacc p l hp
    · intro Q hQ
      have hev := gatesDel_eval d (26 + outG) gs hd hback (inp Q (TQ Q)) (inp_len _ _)
        (26 + outG) (by omega) (by omega) (fun _ => by simpa [Nat.add_sub_cancel_left] using hnd)
      dsimp only [gs', out'] at hev ⊢
      rw [hev]
      exact hrej Q hQ
    · dsimp only [Circuit.size, gs']
      rw [gatesDel_len d gs hd]
      omega
  · right
    push Not at hex
    have hlast : outG + 1 = gs.length := by
      by_contra hne
      have hk : gs.length - 1 < gs.length := by omega
      have hne2 : gs.length - 1 ≠ outG := by omega
      have hic := hex (gs.length - 1) hk hne2
      have hlt := (inCone_lt ⟨gs, 26 + outG⟩ (gs.length - 1) outG hic).1
      omega
    exact ⟨outG, rfl, hlast, fun k hk => by_cases (fun h => Or.inl h) (fun h => Or.inr (hex k hk h))⟩

def case1Patch (i target k u outG : ℕ) (m : ℕ) (g : Gate) : Gate :=
  if m ≤ i then g
  else if m = k then
    if k = outG then ⟨GateOp.or, [u, 26 + i]⟩ else ⟨GateOp.or, []⟩
  else if m = target then ⟨GateOp.or, []⟩
  else
    let ins := (g.inputs.map (fun w => if w = 26 + k then u else w)).filter (· ≠ 26 + target)
    match g.op with
    | GateOp.and =>
      if 26 + target ∈ g.inputs then ⟨GateOp.or, []⟩
      else ⟨GateOp.and, g.inputs.map (fun w => if w = 26 + k then u else w)⟩
    | _ => ⟨GateOp.or, ins⟩

lemma case1_via_or_gate (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j target k u : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (ht_eq : target = i ∨ (target = j ∧ 26 + i ∈ (gateAt ⟨gs, 0⟩ j).inputs))
    (htk : target < k) (hkout : k ≤ outG)
    (hkop : (gateAt ⟨gs, 0⟩ k).op = GateOp.or)
    (hink : 26 + target ∈ (gateAt ⟨gs, 0⟩ k).inputs)
    (hu_ne : u ≠ 26 + target) (hu_lt : u < 26 + k)
    (hk_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ k).inputs ↔ w = 26 + target ∨ w = u)
    (hkill : ∀ x : List Bool, x.length = 26 → V gs x (26 + i) = false → V gs x (26 + target) = false)
    (hiQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + i) = false) :
    False := by
  have hi_le_t : i ≤ target := by
    rcases ht_eq with rfl | ⟨htj, _⟩
    · exact le_refl _
    · rw [htj]; exact (inCone_lt ⟨gs, 0⟩ i j hij).1.le
  have hi_lt_k : i < k := by omega
  have hlen : gs.length = outG + 1 := by omega
  let gs1 := gs.mapIdx (case1Patch i target k u outG)
  have hgs1_len : gs1.length = gs.length := List.length_mapIdx
  have hmon1 : ∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    apply mapIdx_mono
    intro m g hg
    have hm := hmon g (List.mem_of_getElem? hg)
    unfold case1Patch
    by_cases hm1 : m ≤ i
    · rw [ite_eq_left hm1]; exact hm
    · by_cases hm2 : m = k
      · rw [ite_eq_right hm1, ite_eq_left hm2]; split_ifs <;> simp
      · by_cases hm3 : m = target
        · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_left hm3]; simp
        · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_right hm3]
          cases hop : g.op with
          | and =>
            split_ifs
            · simp
            · exact ⟨Or.inl rfl, by simp [hm.2]⟩
          | or =>
            exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) (by simp [hm.2])⟩
          | _ => rcases hm.1 with h | h <;> rw [h] at hop <;> cases hop
  have hback1 : ReadsBack 26 ⟨gs1, 0⟩ := by
    apply mapIdx_readsBack
    intro m g hg v hv
    have hm_len : m < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hga : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
    have hbm : ∀ w ∈ g.inputs, w < 26 + m := fun w hw => hback m hm_len w (by rw [hga]; exact hw)
    unfold case1Patch at hv
    by_cases hm1 : m ≤ i
    · rw [ite_eq_left hm1] at hv; exact hbm v hv
    · by_cases hm2 : m = k
      · rw [ite_eq_right hm1, ite_eq_left hm2] at hv
        split_ifs at hv
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;> omega
        · simp at hv
      · by_cases hm3 : m = target
        · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_left hm3] at hv; simp at hv
        · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_right hm3] at hv
          cases hop : g.op with
          | and =>
            simp only [hop] at hv
            split_ifs at hv
            · simp at hv
            · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
              have := hbm w hw
              split_ifs <;> omega
          | or =>
            simp only [hop] at hv
            obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hv)
            have := hbm w hw
            split_ifs <;> omega
          | _ =>
            have hgm := (hmon g (List.mem_of_getElem? hg)).1
            rcases hgm with h | h <;> rw [h] at hop <;> cases hop
  have hgs1_le_i : ∀ x : List Bool, x.length = 26 → ∀ w ≤ 26 + i, V gs1 x w = V gs x w := by
    intro x hx w hw
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw26 : w < 26
      · exact V_in gs1 gs x w (by rw [hx]; exact hw26)
      · obtain ⟨m, rfl⟩ : ∃ m, w = 26 + m := ⟨w - 26, by omega⟩
        have hmi : m ≤ i := by omega
        have hm_len : m < gs.length := by omega
        have hg0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hm_len
        have hg1 : gs1[m]? = some gs[m] := by
          simp [gs1, List.getElem?_mapIdx, hg0, case1Patch, hmi]
        have hga : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hm_len
        have hbm : ∀ v ∈ gs[m].inputs, v < 26 + m := fun v hv => hback m hm_len v (by rw [hga]; exact hv)
        rw [gate_val_aux gs1 x hx m gs[m] hg1 hbm, gate_val_aux gs x hx m gs[m] hg0 hbm]
        congr 1
        apply List.map_inj_left.2
        intro v hv
        have hvm : v < 26 + m := hbm v hv
        exact ih v hvm (by omega)
  have hgs1_eq_off : ∀ x : List Bool, x.length = 26 → V gs x (26 + i) = false →
      ∀ w, w < 26 + gs.length → w ≠ 26 + k → V gs1 x w = V gs x w := by
    intro x hx hxi w hwlt hwk
    have hxt : V gs x (26 + target) = false := hkill x hx hxi
    have hxk : V gs x (26 + k) = V gs x u := by
      have hk_len : k < gs.length := by omega
      have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk_len
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk_len
      have hbk : ∀ v ∈ gs[k].inputs, v < 26 + k := fun v hv => hback k hk_len v (by rw [hga]; exact hv)
      have hop0 : gs[k].op = GateOp.or := by rw [← hga]; exact hkop
      cases hv : V gs x u
      · rw [Bool.eq_false_iff]; intro htr
        rw [orN gs x hx k gs[k] hg0 hbk hop0] at htr
        obtain ⟨w0, hw0, hVw0⟩ := htr
        rw [← hga, hk_inp] at hw0
        rcases hw0 with rfl | rfl
        · rw [hxt] at hVw0; cases hVw0
        · rw [hv] at hVw0; cases hVw0
      · rw [orN gs x hx k gs[k] hg0 hbk hop0]
        exact ⟨u, by rw [← hga, hk_inp]; right; rfl, hv⟩
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hw26 : w < 26
      · exact V_in gs1 gs x w (by rw [hx]; exact hw26)
      · obtain ⟨m, rfl⟩ : ∃ m, w = 26 + m := ⟨w - 26, by omega⟩
        have hm_len : m < gs.length := by omega
        have hmk : m ≠ k := by omega
        by_cases hmi : m ≤ i
        · exact hgs1_le_i x hx (26 + m) (by omega)
        · have hmgt : i < m := by omega
          have hga : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hm_len
          have hg0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hm_len
          have hbm : ∀ v ∈ gs[m].inputs, v < 26 + m := fun v hv => hback m hm_len v (by rw [hga]; exact hv)
          by_cases hmt : m = target
          · subst hmt
            have hg1 : gs1[m]? = some ⟨GateOp.or, []⟩ := by
              simp [gs1, List.getElem?_mapIdx, hg0, case1Patch, hmi, hmk]
            have hfl : V gs1 x (26 + m) = false := by
              rw [Bool.eq_false_iff]; intro htr
              rw [orN gs1 x hx m _ hg1 (by intro _ h; cases h) rfl] at htr
              obtain ⟨_, h, _⟩ := htr; cases h
            rw [hfl, hxt]
          · let gm' := case1Patch i target k u outG m gs[m]
            have hg1 : gs1[m]? = some gm' := by
              simp [gs1, List.getElem?_mapIdx, hg0, gm']
            have hga1 : gateAt ⟨gs1, 0⟩ m = gm' := by
              simp [gateAt, List.getD_eq_getElem?_getD, hg1]
            have hbm1 : ∀ v ∈ gm'.inputs, v < 26 + m := by
              intro v hv; rw [← hga1] at hv
              exact hback1 m (by rw [hgs1_len]; exact hm_len) v hv
            have hmop := (hmon gs[m] (List.getElem_mem hm_len)).1
            rcases hmop with hand | hor
            · by_cases hint : 26 + target ∈ gs[m].inputs
              · have hgm' : gm' = ⟨GateOp.or, []⟩ := by
                  simp [gm', case1Patch, hmi, hmk, hmt, hand, hint]
                rw [hgm'] at hg1
                have hfl : V gs1 x (26 + m) = false := by
                  rw [Bool.eq_false_iff]; intro htr
                  rw [orN gs1 x hx m _ hg1 (by intro _ h; cases h) rfl] at htr
                  obtain ⟨_, h, _⟩ := htr; cases h
                have hfr : V gs x (26 + m) = false := by
                  rw [Bool.eq_false_iff]; intro htr
                  rw [andN_iff gs x hx m gs[m] hg0 hbm hand] at htr
                  have := htr (26 + target) hint
                  rw [hxt] at this; cases this
                rw [hfl, hfr]
              · have hgm' : gm' = ⟨GateOp.and, gs[m].inputs.map (fun w0 => if w0 = 26 + k then u else w0)⟩ := by
                  simp [gm', case1Patch, hmi, hmk, hmt, hand, hint]
                rw [hgm'] at hg1
                rw [gate_val_aux gs1 x hx m _ hg1 (by rw [← hgm']; exact hbm1)]
                rw [gate_val_aux gs x hx m gs[m] hg0 hbm, hand]
                simp only [List.map_map]
                congr 1
                apply List.map_inj_left.2
                intro w0 hw0
                have hw0_lt : w0 < 26 + m := hbm w0 hw0
                dsimp only [Function.comp_apply]
                split_ifs with heq
                · rw [heq, hxk]
                  exact ih u (by rw [heq] at hw0_lt; omega) (by omega) (by omega)
                · exact ih w0 hw0_lt (by omega) heq
            · have hgm' : gm' = ⟨GateOp.or, (gs[m].inputs.map (fun w0 => if w0 = 26 + k then u else w0)).filter (· ≠ 26 + target)⟩ := by
                simp [gm', case1Patch, hmi, hmk, hmt, hor]
              rw [hgm'] at hg1
              apply Bool.eq_iff_iff.2
              rw [orN gs1 x hx m _ hg1 (by rw [← hgm']; exact hbm1) rfl]
              rw [orN gs x hx m gs[m] hg0 hbm hor]
              simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
              constructor
              · rintro ⟨v, ⟨⟨w0, hw0, rfl⟩, hnt⟩, hVv⟩
                have hw0_lt : w0 < 26 + m := hbm w0 hw0
                refine ⟨w0, hw0, ?_⟩
                split_ifs at hVv hnt with heq
                · rw [ih u (by rw [heq] at hw0_lt; omega) (by omega) (by omega)] at hVv
                  rw [heq, hxk, hVv]
                · rw [ih w0 hw0_lt (by omega) heq] at hVv
                  exact hVv
              · rintro ⟨w0, hw0, hVw0⟩
                have hw0_lt : w0 < 26 + m := hbm w0 hw0
                by_cases hwt : w0 = 26 + target
                · rw [hwt, hxt] at hVw0; cases hVw0
                · refine ⟨if w0 = 26 + k then u else w0, ⟨⟨w0, hw0, rfl⟩, ?_⟩, ?_⟩
                  · split_ifs; exact hu_ne; exact hwt
                  · split_ifs with heq
                    · rw [ih u (by rw [heq] at hw0_lt; omega) (by omega) (by omega)]
                      rw [heq, hxk] at hVw0; exact hVw0
                    · rw [ih w0 hw0_lt (by omega) heq]
                      exact hVw0
  have hgs1_inCone : ∀ a b, InCone 26 ⟨gs1, 0⟩ a b → InCone 26 ⟨gs, 0⟩ a b := by
    intro a b hab
    have hblen := (inCone_lt ⟨gs1, 0⟩ a b hab).2
    dsimp only at hblen
    rw [hgs1_len] at hblen
    induction b using Nat.strong_induction_on with
    | ind b ih =>
      rw [inCone_iff 26 ⟨gs1, 0⟩ a b (by rw [hgs1_len]; exact hblen)] at hab
      obtain ⟨v, hv, hv26, hvlt, hrel⟩ := hab
      have hga1 : gateAt ⟨gs1, 0⟩ b = gs1[b] := gateAt_eq ⟨gs1, 0⟩ b (by rw [hgs1_len]; exact hblen)
      have hga0 : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hblen
      have hgs1b : gs1[b] = case1Patch i target k u outG b gs[b] := by
        simp [gs1, List.getElem_mapIdx]
      rw [hga1, hgs1b] at hv
      have hstep : ∃ w ∈ (gateAt ⟨gs, 0⟩ b).inputs, 26 ≤ w ∧ w < 26 + b ∧
          (w - 26 = v - 26 ∨ InCone 26 ⟨gs, 0⟩ (v - 26) (w - 26)) := by
        unfold case1Patch at hv
        by_cases hm1 : b ≤ i
        · rw [ite_eq_left hm1] at hv
          exact ⟨v, by rw [hga0]; exact hv, hv26, hvlt, Or.inl rfl⟩
        · by_cases hm2 : b = k
          · rw [ite_eq_right hm1, ite_eq_left hm2] at hv
            split_ifs at hv
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with hvu | hvi
              · rw [hvu] at hv26 hvlt ⊢
                exact ⟨u, by rw [hm2]; exact (hk_inp u).2 (Or.inr rfl), hv26, hvlt, Or.inl rfl⟩
              · rw [hvi] at hv26 hvlt ⊢
                have hbi : InCone 26 ⟨gs, 0⟩ i b := by
                  rw [hm2]
                  have hik_t : InCone 26 ⟨gs, 0⟩ target k :=
                    inCone_direct ⟨gs, 0⟩ target k (by dsimp; omega) hink htk
                  rcases ht_eq with rfl | ⟨htj, _⟩
                  · exact hik_t
                  · rw [htj] at hik_t; exact inCone_trans ⟨gs, 0⟩ i j k hij hik_t
                rw [inCone_iff 26 ⟨gs, 0⟩ i b hblen] at hbi
                obtain ⟨w, hw, hw26, hwlt, hwrel⟩ := hbi
                refine ⟨w, hw, hw26, hwlt, ?_⟩
                simpa [Nat.add_sub_cancel_left] using (hwrel.imp Eq.symm id)
            · simp at hv
          · by_cases hm3 : b = target
            · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_left hm3] at hv; simp at hv
            · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_right hm3] at hv
              cases hop : gs[b].op with
              | and =>
                simp only [hop] at hv
                split_ifs at hv
                · simp at hv
                · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
                  have hwlt : w < 26 + b := hback b hblen w (by rw [hga0]; exact hw)
                  by_cases hwk : w = 26 + k
                  · rw [ite_eq_left hwk] at hv26 hvlt ⊢
                    have hu_eq : 26 + (u - 26) = u := by omega
                    refine ⟨26 + k, by rw [hga0, ← hwk]; exact hw, by omega, by rw [← hwk]; exact hwlt, Or.inr ?_⟩
                    rw [Nat.add_sub_cancel_left]
                    exact inCone_direct ⟨gs, 0⟩ (u - 26) k (by dsimp; omega) (by rw [hu_eq]; exact (hk_inp u).2 (Or.inr rfl)) (by omega)
                  · rw [ite_eq_right hwk] at hv26 hvlt ⊢
                    exact ⟨w, by rw [hga0]; exact hw, hv26, hvlt, Or.inl rfl⟩
              | or =>
                simp only [hop] at hv
                obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hv)
                have hwlt : w < 26 + b := hback b hblen w (by rw [hga0]; exact hw)
                by_cases hwk : w = 26 + k
                · rw [ite_eq_left hwk] at hv26 hvlt ⊢
                  have hu_eq : 26 + (u - 26) = u := by omega
                  refine ⟨26 + k, by rw [hga0, ← hwk]; exact hw, by omega, by rw [← hwk]; exact hwlt, Or.inr ?_⟩
                  rw [Nat.add_sub_cancel_left]
                  exact inCone_direct ⟨gs, 0⟩ (u - 26) k (by dsimp; omega) (by rw [hu_eq]; exact (hk_inp u).2 (Or.inr rfl)) (by omega)
                · rw [ite_eq_right hwk] at hv26 hvlt ⊢
                  exact ⟨w, by rw [hga0]; exact hw, hv26, hvlt, Or.inl rfl⟩
              | _ =>
                have hgm := (hmon gs[b] (List.getElem_mem hblen)).1
                rcases hgm with h | h <;> rw [h] at hop <;> cases hop
      obtain ⟨w, hw, hw26, hwlt, hwrel⟩ := hstep
      rcases hrel with hav | hic
      · rw [hav]
        rcases hwrel with hweq | hwic
        · exact (inCone_iff 26 ⟨gs, 0⟩ (v - 26) b hblen).2 ⟨w, hw, hw26, hwlt, Or.inl hweq.symm⟩
        · exact (inCone_iff 26 ⟨gs, 0⟩ (v - 26) b hblen).2 ⟨w, hw, hw26, hwlt, Or.inr hwic⟩
      · have hinc := ih (v - 26) (by omega) hic (by omega)
        rcases hwrel with hweq | hwic
        · rw [← hweq] at hinc
          exact (inCone_iff 26 ⟨gs, 0⟩ a b hblen).2 ⟨w, hw, hw26, hwlt, Or.inr hinc⟩
        · exact (inCone_iff 26 ⟨gs, 0⟩ a b hblen).2 ⟨w, hw, hw26, hwlt, Or.inr (inCone_trans ⟨gs, 0⟩ a (v - 26) (w - 26) hinc hwic)⟩
  have hgs1_no_target : ∀ m, target < m → m < gs1.length → m ≠ k →
      26 + target ∉ (gateAt ⟨gs1, 0⟩ m).inputs := by
    intro m htm hmlen hmk hmem
    rw [hgs1_len] at hmlen
    have hga1 : gateAt ⟨gs1, 0⟩ m = gs1[m] := gateAt_eq ⟨gs1, 0⟩ m (by rw [hgs1_len]; exact hmlen)
    have hgs1m : gs1[m] = case1Patch i target k u outG m gs[m] := by simp [gs1, List.getElem_mapIdx]
    rw [hga1, hgs1m] at hmem
    have hm1 : ¬ m ≤ i := by omega
    have hm3 : ¬ m = target := by omega
    unfold case1Patch at hmem
    simp only [hm1, ↓reduceIte, hmk, hm3] at hmem
    cases hop : gs[m].op with
    | and =>
      simp only [hop] at hmem
      split_ifs at hmem with hint
      · simp at hmem
      · obtain ⟨w, hw, heqw⟩ := List.mem_map.1 hmem
        split_ifs at heqw with hwk
        · exact hu_ne heqw
        · rw [heqw] at hw; exact hint hw
    | or =>
      simp only [hop] at hmem
      have hf := (List.mem_filter.1 hmem).2
      simp at hf
    | _ =>
      have hgm := (hmon gs[m] (List.getElem_mem hmlen)).1
      rcases hgm with h | h <;> rw [h] at hop <;> cases hop
  have hgs1_no_k : ∀ m, k < m → m < gs1.length → 26 + k ∉ (gateAt ⟨gs1, 0⟩ m).inputs := by
    intro m hkm hmlen hmem
    rw [hgs1_len] at hmlen
    have hga1 : gateAt ⟨gs1, 0⟩ m = gs1[m] := gateAt_eq ⟨gs1, 0⟩ m (by rw [hgs1_len]; exact hmlen)
    have hgs1m : gs1[m] = case1Patch i target k u outG m gs[m] := by simp [gs1, List.getElem_mapIdx]
    rw [hga1, hgs1m] at hmem
    have hm1 : ¬ m ≤ i := by omega
    have hm2 : ¬ m = k := by omega
    have hm3 : ¬ m = target := by omega
    unfold case1Patch at hmem
    simp only [hm1, ↓reduceIte, hm2, hm3] at hmem
    cases hop : gs[m].op with
    | and =>
      simp only [hop] at hmem
      split_ifs at hmem
      · simp at hmem
      · obtain ⟨w, hw, heqw⟩ := List.mem_map.1 hmem
        split_ifs at heqw <;> omega
    | or =>
      simp only [hop] at hmem
      obtain ⟨w, hw, heqw⟩ := List.mem_map.1 (List.mem_of_mem_filter hmem)
      split_ifs at heqw <;> omega
    | _ =>
      have hgm := (hmon gs[m] (List.getElem_mem hmlen)).1
      rcases hgm with h | h <;> rw [h] at hop <;> cases hop
  have hnn1 : ¬ ∃ a b : ℕ, (gateAt ⟨gs1, 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs1, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs1, 0⟩ a b := by
    rintro ⟨a, b, ha1, hb1, hab1⟩
    have hlt := inCone_lt ⟨gs1, 0⟩ a b hab1
    dsimp only at hlt
    rw [hgs1_len] at hlt
    have hop_gs : ∀ m, m < gs.length → (gateAt ⟨gs1, 0⟩ m).op = GateOp.and → (gateAt ⟨gs, 0⟩ m).op = GateOp.and := by
      intro m hmlen hm1
      have hga1 : gateAt ⟨gs1, 0⟩ m = gs1[m] := gateAt_eq ⟨gs1, 0⟩ m (by rw [hgs1_len]; exact hmlen)
      have hga0 : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hmlen
      have hgs1m : gs1[m] = case1Patch i target k u outG m gs[m] := by simp [gs1, List.getElem_mapIdx]
      rw [hga1, hgs1m] at hm1
      rw [hga0]
      unfold case1Patch at hm1
      by_cases h1 : m ≤ i
      · rw [ite_eq_left h1] at hm1; exact hm1
      · by_cases h2 : m = k
        · rw [ite_eq_right h1, ite_eq_left h2] at hm1; split_ifs at hm1
        · by_cases h3 : m = target
          · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] at hm1; cases hm1
          · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hm1
            cases hop : gs[m].op with
            | and => rfl
            | or => simp [hop] at hm1
            | _ =>
              have hgm := (hmon gs[m] (List.getElem_mem hmlen)).1
              rcases hgm with h | h <;> rw [h] at hop <;> cases hop
    have ha0 := hop_gs a (by omega) ha1
    have hb0 := hop_gs b hlt.2 hb1
    have hab0 := hgs1_inCone a b hab1
    obtain ⟨hai, hbj⟩ := andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij ha0 hb0 hab0
    rw [hai] at ha1 hlt; rw [hbj] at hb1 hlt; rw [hai, hbj] at hab1
    rcases ht_eq with hti | ⟨htj, _⟩
    · have hij_in : InCone 26 ⟨gs1, 0⟩ i j := hab1
      have hj_len : j < gs1.length := by rw [hgs1_len]; exact hlt.2
      have hno_from_i : ∀ m, i < m → m < gs1.length → m ≠ k → InCone 26 ⟨gs1, 0⟩ i m → False := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          intro him hmlen hmk himc
          rw [inCone_iff 26 ⟨gs1, 0⟩ i m hmlen] at himc
          obtain ⟨v, hv, hv26, hvlt, hrel⟩ := himc
          rcases hrel with hvi | hvic
          · have hveq : 26 + i = v := by omega
            rw [← hveq] at hv
            exact hgs1_no_target m (by omega) hmlen hmk (by rw [hti]; exact hv)
          · have hvk : v - 26 ≠ k := by
              intro heq
              have hvm : k < m := by omega
              have hveq : 26 + k = v := by omega
              rw [← hveq] at hv
              exact hgs1_no_k m hvm hmlen hv
            have hvic_lt := (inCone_lt ⟨gs1, 0⟩ i (v - 26) hvic).1
            exact ih (v - 26) (by omega) hvic_lt (by omega) hvk hvic
      have hjk : j ≠ k := by
        intro heq
        have hj_not : (gateAt ⟨gs1, 0⟩ j).op ≠ GateOp.and := by
          have hga1 : gateAt ⟨gs1, 0⟩ j = gs1[j] := gateAt_eq ⟨gs1, 0⟩ j (by dsimp; rw [hgs1_len]; exact hlt.2)
          have hgs1j : gs1[j] = case1Patch i target k u outG j gs[j] := by simp [gs1, List.getElem_mapIdx]
          rw [hga1, hgs1j]
          unfold case1Patch
          have h1 : ¬ j ≤ i := by omega
          rw [ite_eq_right h1, ite_eq_left heq]; split_ifs <;> simp
        exact hj_not hb1
      exact hno_from_i j hlt.1 hj_len hjk hij_in
    · have hga1 : gateAt ⟨gs1, 0⟩ j = gs1[j] := gateAt_eq ⟨gs1, 0⟩ j (by dsimp; rw [hgs1_len]; exact hlt.2)
      have hgs1j : gs1[j] = case1Patch i target k u outG j gs[j] := by simp [gs1, List.getElem_mapIdx]
      rw [hga1, hgs1j] at hb1
      unfold case1Patch at hb1
      have h1 : ¬ j ≤ i := by omega
      have h2 : ¬ j = k := by omega
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left htj.symm] at hb1
      cases hb1
  by_cases hko : k = outG
  · subst hko
    apply core_contra gs1 (26 + k) (by rw [hgs1_len]; exact hsz) hmon1 hback1 hnn1
    · intro p l hp
      have hk_len1 : k < gs1.length := by rw [hgs1_len]; omega
      have hg1k : gs1[k]? = some ⟨GateOp.or, [u, 26 + i]⟩ := by
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem (by omega)
        simp [gs1, List.getElem?_mapIdx, hg0, case1Patch, show ¬ k ≤ i by omega]
      rw [orN gs1 _ (inp_len _ _) k _ hg1k (by intro _ hv; simp at hv; rcases hv with rfl | rfl <;> omega) rfl]
      cases hpi : V gs (inp {p} {l}) (26 + i)
      · refine ⟨u, by simp, ?_⟩
        rw [hgs1_eq_off (inp {p} {l}) (inp_len _ _) hpi u (by omega) (by omega)]
        have hacc0 := hacc p l hp
        have hk_len0 : k < gs.length := by omega
        have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk_len0
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk_len0
        have hbk0 : ∀ w ∈ gs[k].inputs, w < 26 + k := fun w hw => hback k hk_len0 w (by rw [hga0]; exact hw)
        have hop0 : gs[k].op = GateOp.or := by rw [← hga0]; exact hkop
        rw [orN gs _ (inp_len _ _) k gs[k] hg0 hbk0 hop0] at hacc0
        obtain ⟨w0, hw0, hVw0⟩ := hacc0
        rw [← hga0, hk_inp] at hw0
        rcases hw0 with rfl | rfl
        · have := hkill _ (inp_len _ _) hpi
          rw [this] at hVw0; cases hVw0
        · exact hVw0
      · refine ⟨26 + i, by simp, ?_⟩
        rw [hgs1_le_i _ (inp_len _ _) (26 + i) (le_refl _), hpi]
    · intro Q hQ
      have hqi := hiQ Q hQ
      have hk_len1 : k < gs1.length := by rw [hgs1_len]; omega
      have hg1k : gs1[k]? = some ⟨GateOp.or, [u, 26 + i]⟩ := by
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem (by omega)
        simp [gs1, List.getElem?_mapIdx, hg0, case1Patch, show ¬ k ≤ i by omega]
      rw [Bool.eq_false_iff]; intro htr
      rw [orN gs1 _ (inp_len _ _) k _ hg1k (by intro _ hv; simp at hv; rcases hv with rfl | rfl <;> omega) rfl] at htr
      obtain ⟨v, hv, hVv⟩ := htr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hvu | hvi
      · rw [hvu, hgs1_eq_off _ (inp_len _ _) hqi u (by omega) (by omega)] at hVv
        have hrej0 := hrej Q hQ
        have hk_len0 : k < gs.length := by omega
        have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk_len0
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk_len0
        have hbk0 : ∀ w ∈ gs[k].inputs, w < 26 + k := fun w hw => hback k hk_len0 w (by rw [hga0]; exact hw)
        have hop0 : gs[k].op = GateOp.or := by rw [← hga0]; exact hkop
        have htr0 : V gs (inp Q (TQ Q)) (26 + k) = true := by
          rw [orN gs _ (inp_len _ _) k gs[k] hg0 hbk0 hop0]
          exact ⟨u, by rw [← hga0, hk_inp]; right; rfl, hVv⟩
        rw [hrej0] at htr0; cases htr0
      · rw [hvi, hgs1_le_i _ (inp_len _ _) (26 + i) (le_refl _), hqi] at hVv
        cases hVv
  · have hklt : k < outG := by omega
    let gNew : Gate := ⟨GateOp.or, [26 + (outG - 1), 26 + i]⟩
    let gs2 := gatesMoveAfter gs1 k outG gNew
    have hgs2_len : gs2.length = gs.length := by
      rw [gatesMoveAfter_len gs1 k outG gNew hklt (by rw [hgs1_len]; omega), hgs1_len]
    have hmon2 : ∀ g ∈ gs2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      gatesMoveAfter_mono gs1 k outG gNew hmon1 (by simp [gNew])
    have hback2 : ReadsBack 26 ⟨gs2, 0⟩ :=
      gatesMoveAfter_readsBack gs1 k outG gNew hklt (by rw [hgs1_len]; omega) hback1 (by
        intro w hw; simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega)
    have hnn2 : ¬ ∃ a b : ℕ, (gateAt ⟨gs2, 0⟩ a).op = GateOp.and ∧
        (gateAt ⟨gs2, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs2, 0⟩ a b := by
      apply gatesMoveAfter_no_nested_and gs1 k outG gNew hklt (by rw [hgs1_len]; omega) hback1 rfl
        hgs1_no_k (fun b hb hb2 _ => by rw [hgs1_len] at hb2; omega) hnn1
    have hgs2_i : ∀ x : List Bool, x.length = 26 → V gs2 x (26 + i) = V gs x (26 + i) := by
      intro x hx
      have hev := gatesMoveAfter_eval_lt gs1 k outG gNew hklt (by rw [hgs1_len]; omega) hback1 hback2
        (fun m hm1 _ => hgs1_no_k m hm1 (by rw [hgs1_len]; omega)) x hx (26 + i) (by omega) (by omega)
      have hsi : shiftMoveInner k (26 + i) = 26 + i := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
      rw [hsi] at hev
      rw [hev, hgs1_le_i x hx (26 + i) (le_refl _)]
    have hgs2_out : ∀ x : List Bool, x.length = 26 →
        (V gs2 x (26 + outG) = true ↔ (V gs x (26 + outG) = true ∨ V gs x (26 + i) = true)) := by
      intro x hx
      have hg2 : gs2[outG]? = some gNew := gatesMoveAfter_getElem_dst gs1 k outG gNew hklt (by rw [hgs1_len]; omega)
      have hb_gnew : ∀ w ∈ gNew.inputs, w < 26 + outG := by
        intro w hw; simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
      rw [orN gs2 x hx outG gNew hg2 hb_gnew rfl]
      constructor
      · rintro ⟨w, hw, hVw⟩
        simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · cases hxi : V gs x (26 + i)
          · left
            have hev := gatesMoveAfter_eval_lt gs1 k outG gNew hklt (by rw [hgs1_len]; omega) hback1 hback2
              (fun m hm1 _ => hgs1_no_k m hm1 (by rw [hgs1_len]; omega)) x hx (26 + outG) (by omega) (by omega)
            have hs : shiftMoveInner k (26 + outG) = 26 + (outG - 1) := by
              unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
            rw [hs] at hev
            rw [hev, hgs1_eq_off x hx hxi (26 + outG) (by omega) (by omega)] at hVw
            exact hVw
          · right; rfl
        · right; rw [← hgs2_i x hx]; exact hVw
      · rintro (hvo | hvi)
        · cases hxi : V gs x (26 + i)
          · refine ⟨26 + (outG - 1), by simp [gNew], ?_⟩
            have hev := gatesMoveAfter_eval_lt gs1 k outG gNew hklt (by rw [hgs1_len]; omega) hback1 hback2
              (fun m hm1 _ => hgs1_no_k m hm1 (by rw [hgs1_len]; omega)) x hx (26 + outG) (by omega) (by omega)
            have hs : shiftMoveInner k (26 + outG) = 26 + (outG - 1) := by
              unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
            rw [hs] at hev
            rw [hev, hgs1_eq_off x hx hxi (26 + outG) (by omega) (by omega), hvo]
          · refine ⟨26 + i, by simp [gNew], ?_⟩
            rw [hgs2_i x hx, hxi]
        · refine ⟨26 + i, by simp [gNew], ?_⟩
          rw [hgs2_i x hx, hvi]
    apply core_contra gs2 (26 + outG) (by rw [hgs2_len]; exact hsz) hmon2 hback2 hnn2
    · intro p l hp
      exact (hgs2_out (inp {p} {l}) (inp_len _ _)).2 (Or.inl (hacc p l hp))
    · intro Q hQ
      rw [Bool.eq_false_iff]; intro htr
      rcases (hgs2_out (inp Q (TQ Q)) (inp_len _ _)).1 htr with h | h
      · rw [hrej Q hQ] at h; cases h
      · rw [hiQ Q hQ] at h; cases h

lemma case1_contradiction (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and) (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hiQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + i) = false) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  by_cases hk_ex : ∃ k, i < k ∧ k < gs.length ∧ (gateAt ⟨gs, 0⟩ k).op = GateOp.or ∧ 26 + i ∈ (gateAt ⟨gs, 0⟩ k).inputs
  · obtain ⟨k, hik, hklen, hkop, hink⟩ := hk_ex
    have hga : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
    obtain ⟨hl2, hne⟩ := htwo gs[k] (List.getElem_mem hklen)
    obtain ⟨a0, a1, ha_eq⟩ : ∃ a0 a1, gs[k].inputs = [a0, a1] := by
      cases h : gs[k].inputs with
      | nil => simp [h] at hl2
      | cons x xs => cases h2 : xs with
        | nil => simp [h, h2] at hl2
        | cons y ys => cases h3 : ys with
          | nil => exact ⟨x, y, by simp⟩
          | cons _ _ => simp [h, h2, h3] at hl2
    have hne01 : a0 ≠ a1 := by simpa [ha_eq] using hne
    rw [hga, ha_eq] at hink
    have hmem : a0 = 26 + i ∨ a1 = 26 + i := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hink
      rcases hink with rfl | rfl <;> tauto
    let u := if a0 = 26 + i then a1 else a0
    have hu_ne : u ≠ 26 + i := by dsimp only [u]; split_ifs <;> omega
    have hkin : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ k).inputs ↔ w = 26 + i ∨ w = u := by
      intro w; rw [hga, ha_eq]; dsimp only [u]; rcases hmem with rfl | rfl
      · simp [eq_comm]
      · simp [hne01]; tauto
    have hu_mem : u ∈ (gateAt ⟨gs, 0⟩ k).inputs := (hkin u).2 (Or.inr rfl)
    have hu_lt : u < 26 + k := hback k hklen u hu_mem
    exact case1_via_or_gate gs outG hout hsz hmon hback hacc hrej i j i k u hiA hjA hij hAP
      (Or.inl rfl) hik (by omega) hkop ((hkin (26 + i)).2 (Or.inl rfl)) hu_ne hu_lt hkin
      (fun _ _ h => h) hiQ
  · have hij_in : 26 + i ∈ (gateAt ⟨gs, 0⟩ j).inputs := by
      rcases reachesAvoiding_split gs gs.length (26 + i) hgs_eq (26 + j) (inCone_reachesAvoiding gs i j hij) with hOr | hAnd
      · obtain ⟨k, g, hg, _, hkop, hmem, _⟩ := reachesOr_first_step gs gs.length (26 + i) (26 + j) hOr (by omega)
        have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        have hga : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
        have hik : i < k := by
          have := hback k hklen (26 + i) (by rw [hga]; exact hmem); omega
        exact absurd ⟨k, hik, hklen, by rw [hga]; exact hkop, by rw [hga]; exact hmem⟩ hk_ex
      · obtain ⟨a, ga, hga, haop, _, _, u, hu, hult, hOr⟩ := hAnd
        have halen : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
        have hga_eq : gateAt ⟨gs, 0⟩ a = ga := by simp [gateAt, List.getD_eq_getElem?_getD, hga]
        by_cases hui : u = 26 + i
        · rw [hui] at hu
          have hia : i < a := by have := hback a halen (26 + i) (by rw [hga_eq]; exact hu); omega
          have hica : InCone 26 ⟨gs, 0⟩ i a := inCone_direct ⟨gs, 0⟩ i a halen (by rw [hga_eq]; exact hu) hia
          have haj := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA (by rw [hga_eq]; exact haop) hica).2
          subst haj
          rw [hga_eq]; exact hu
        · obtain ⟨k, g, hg, _, hkop, hmem, _⟩ := reachesOr_first_step gs gs.length (26 + i) u hOr hui
          have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
          have hga_k : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
          have hik : i < k := by have := hback k hklen (26 + i) (by rw [hga_k]; exact hmem); omega
          exact absurd ⟨k, hik, hklen, by rw [hga_k]; exact hkop, by rw [hga_k]; exact hmem⟩ hk_ex
    have hjkill : ∀ x : List Bool, x.length = 26 → V gs x (26 + i) = false → V gs x (26 + j) = false := by
      intro x hx hxi
      rw [Bool.eq_false_iff]; intro htr
      have hga : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
      have hg0 : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
      have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga]; exact hw)
      have hopj : gs[j].op = GateOp.and := by rw [← hga]; exact hjA
      rw [andN_iff gs x hx j gs[j] hg0 hbj hopj] at htr
      have := htr (26 + i) (by rw [← hga]; exact hij_in)
      rw [hxi] at this; cases this
    by_cases hjo : j = outG
    · subst hjo
      let gs1 := gs.mapIdx (fun m g => if m = j then ⟨GateOp.or, [26 + i]⟩ else g)
      have hgs1_len : gs1.length = gs.length := List.length_mapIdx
      have hmon1 : ∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        apply mapIdx_mono
        intro m g hg
        split_ifs
        · simp
        · exact hmon g (List.mem_of_getElem? hg)
      have hback1 : ReadsBack 26 ⟨gs1, 0⟩ := by
        apply mapIdx_readsBack
        intro m g hg v hv
        split_ifs at hv with hm
        · subst hm; simp at hv; subst hv; omega
        · have hm_len : m < gs.length := (List.getElem?_eq_some_iff.1 hg).1
          have hga : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
          exact hback m hm_len v (by rw [hga]; exact hv)
      have hgs1_lt : ∀ x : List Bool, x.length = 26 → ∀ w, w < 26 + j → V gs1 x w = V gs x w := by
        intro x hx w hw
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases hw26 : w < 26
          · exact V_in gs1 gs x w (by rw [hx]; exact hw26)
          · obtain ⟨m, rfl⟩ : ∃ m, w = 26 + m := ⟨w - 26, by omega⟩
            have hmj : m < j := by omega
            have hm_len : m < gs.length := by omega
            have hg0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hm_len
            have hg1 : gs1[m]? = some gs[m] := by simp [gs1, List.getElem?_mapIdx, hg0, show m ≠ j by omega]
            have hga : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hm_len
            have hbm : ∀ v ∈ gs[m].inputs, v < 26 + m := fun v hv => hback m hm_len v (by rw [hga]; exact hv)
            rw [gate_val_aux gs1 x hx m gs[m] hg1 hbm, gate_val_aux gs x hx m gs[m] hg0 hbm]
            congr 1
            apply List.map_inj_left.2
            intro v hv
            have hvlt : v < 26 + m := hbm v hv
            exact ih v hvlt (by omega)
      have hnn1 : ¬ ∃ a b : ℕ, (gateAt ⟨gs1, 0⟩ a).op = GateOp.and ∧
          (gateAt ⟨gs1, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs1, 0⟩ a b := by
        rintro ⟨a, b, ha1, hb1, hab1⟩
        have hlt1 := inCone_lt ⟨gs1, 0⟩ a b hab1
        dsimp only at hlt1
        rw [hgs1_len] at hlt1
        have hbj : b < j := by
          have hbne : b ≠ j := by
            intro heq; subst heq
            have hga1 : gateAt ⟨gs1, 0⟩ b = gs1[b] := gateAt_eq ⟨gs1, 0⟩ b (by rw [hgs1_len]; exact hlt1.2)
            have hgs1b : gs1[b] = ⟨GateOp.or, [26 + i]⟩ := by simp [gs1, List.getElem_mapIdx]
            rw [hga1, hgs1b] at hb1; cases hb1
          omega
        have hlt_eq : ∀ m, m < j → gateAt ⟨gs1, 0⟩ m = gateAt ⟨gs, 0⟩ m := by
          intro m hmj
          have hg0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem (by omega)
          have hg1 : gs1[m]? = some gs[m] := by simp [gs1, List.getElem?_mapIdx, hg0, show m ≠ j by omega]
          simp [gateAt, List.getD_eq_getElem?_getD, hg0, hg1]
        have hlt_in : ∀ c d, d < j → InCone 26 ⟨gs1, 0⟩ c d → InCone 26 ⟨gs, 0⟩ c d := by
          intro c d hd hcd
          induction d using Nat.strong_induction_on generalizing c with
          | ind d ih =>
            have hdlen : d < gs.length := by omega
            rw [inCone_iff 26 ⟨gs1, 0⟩ c d (by rw [hgs1_len]; exact hdlen)] at hcd
            obtain ⟨v, hv, hv26, hvlt, hrel⟩ := hcd
            rw [hlt_eq d hd] at hv
            rcases hrel with rfl | hic
            · have hveq : 26 + (v - 26) = v := by omega
              exact inCone_direct ⟨gs, 0⟩ (v - 26) d hdlen (by rw [hveq]; exact hv) (by omega)
            · exact (inCone_iff 26 ⟨gs, 0⟩ c d hdlen).2 ⟨v, hv, hv26, hvlt, Or.inr (ih (v - 26) (by omega) c (by omega) hic)⟩
        have ha0 : (gateAt ⟨gs, 0⟩ a).op = GateOp.and := by rw [← hlt_eq a (by omega)]; exact ha1
        have hb0 : (gateAt ⟨gs, 0⟩ b).op = GateOp.and := by rw [← hlt_eq b hbj]; exact hb1
        have hab0 := hlt_in a b hbj hab1
        have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij ha0 hb0 hab0).2
        omega
      have hj1 : gs1[j]? = some ⟨GateOp.or, [26 + i]⟩ := by
        have hg0 : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
        simp [gs1, List.getElem?_mapIdx, hg0]
      have hbj1 : ∀ v ∈ ([26 + i] : List ℕ), v < 26 + j := by intro v hv; simp at hv; subst hv; omega
      apply core_contra gs1 (26 + j) (by rw [hgs1_len]; exact hsz) hmon1 hback1 hnn1
      · intro p l hp
        rw [orN gs1 _ (inp_len _ _) j _ hj1 hbj1 rfl]
        refine ⟨26 + i, by simp, ?_⟩
        rw [hgs1_lt _ (inp_len _ _) (26 + i) (by omega)]
        have hacc0 := hacc p l hp
        have hga : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
        have hg0 : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
        have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga]; exact hw)
        have hopj : gs[j].op = GateOp.and := by rw [← hga]; exact hjA
        rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0 hbj hopj] at hacc0
        exact hacc0 (26 + i) (by rw [← hga]; exact hij_in)
      · intro Q hQ
        rw [Bool.eq_false_iff]; intro htr
        rw [orN gs1 _ (inp_len _ _) j _ hj1 hbj1 rfl] at htr
        obtain ⟨v, hv, hVv⟩ := htr
        simp at hv; subst hv
        rw [hgs1_lt _ (inp_len _ _) (26 + i) (by omega), hiQ Q hQ] at hVv
        cases hVv
    · have hjout : j < outG := by omega
      have hinc_jo : InCone 26 ⟨gs, 0⟩ j outG := (hreach j hlt.2).resolve_left hjo
      have hj_or_out : reachesOr gs gs.length (26 + j) (26 + outG) := by
        rcases reachesAvoiding_split gs gs.length (26 + j) hgs_eq (26 + outG) (inCone_reachesAvoiding gs j outG hinc_jo) with hOr | hAnd
        · exact hOr
        · obtain ⟨a, ga, hga, haop, _, _, u, hu, hult, hOr⟩ := hAnd
          have halen : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
          have hga_eq : gateAt ⟨gs, 0⟩ a = ga := by simp [gateAt, List.getD_eq_getElem?_getD, hga]
          have hja : InCone 26 ⟨gs, 0⟩ j a := by
            rcases reachesOr_inCone gs gs.length (26 + j) u (by omega) hOr with heq | ⟨hu26, hic⟩
            · rw [heq] at hu
              have hltja : j < a := by have := hback a halen (26 + j) (by rw [hga_eq]; exact hu); omega
              exact inCone_direct ⟨gs, 0⟩ j a halen (by rw [hga_eq]; exact hu) hltja
            · exact (inCone_iff 26 ⟨gs, 0⟩ j a halen).2 ⟨u, by rw [hga_eq]; exact hu, hu26, hult, Or.inr (by simpa [Nat.add_sub_cancel_left] using hic)⟩
          have haj := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA (by rw [hga_eq]; exact haop) hja).1
          omega
      obtain ⟨k, g, hg, _, hkop, hmem, _⟩ := reachesOr_first_step gs gs.length (26 + j) (26 + outG) hj_or_out (by omega)
      have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      have hga : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
      have hjk : j < k := by have := hback k hklen (26 + j) (by rw [hga]; exact hmem); omega
      obtain ⟨hl2, hne⟩ := htwo gs[k] (List.getElem_mem hklen)
      obtain ⟨a0, a1, ha_eq⟩ : ∃ a0 a1, gs[k].inputs = [a0, a1] := by
        cases h : gs[k].inputs with
        | nil => simp [h] at hl2
        | cons x xs => cases h2 : xs with
          | nil => simp [h, h2] at hl2
          | cons y ys => cases h3 : ys with
            | nil => exact ⟨x, y, by simp⟩
            | cons _ _ => simp [h, h2, h3] at hl2
      have hne01 : a0 ≠ a1 := by simpa [ha_eq] using hne
      have hgs_k : g = gs[k] := by
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        rw [hg0] at hg; exact (Option.some.inj hg).symm
      rw [hgs_k, ha_eq] at hmem
      have hmem2 : a0 = 26 + j ∨ a1 = 26 + j := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl <;> tauto
      let u := if a0 = 26 + j then a1 else a0
      have hu_ne : u ≠ 26 + j := by dsimp only [u]; split_ifs <;> omega
      have hkin : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ k).inputs ↔ w = 26 + j ∨ w = u := by
        intro w; rw [hga, hgs_k, ha_eq]; dsimp only [u]; rcases hmem2 with rfl | rfl
        · simp [eq_comm]
        · simp [hne01]; tauto
      have hu_lt : u < 26 + k := hback k hklen u ((hkin u).2 (Or.inr rfl))
      exact case1_via_or_gate gs outG hout hsz hmon hback hacc hrej i j j k u hiA hjA hij hAP
        (Or.inr ⟨rfl, hij_in⟩) hjk (by omega) (by rw [hga]; exact hkop) ((hkin (26 + j)).2 (Or.inl rfl))
        hu_ne hu_lt hkin hjkill hiQ

end L1961


namespace L1961

def okQuad (S T : Finset (Fin 26)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ T, isInc26 a b = true

def okQuad3 (S T U : Finset (Fin 26)) : Prop :=
  ∀ Q : Finset (Fin 13), isQuad Q →
    ¬ ((∃ a ∈ S, qHit Q a = true) ∧ (∃ b ∈ T, qHit Q b = true) ∧ (∃ c ∈ U, qHit Q c = true))

lemma okQuad_of_okQuad3_inter (A B R : Finset (Fin 26)) (h3 : okQuad3 A B R) :
    okQuad (A ∩ B) R := by
  intro x hx r hr
  simp only [Finset.mem_inter] at hx
  by_contra hne
  have hfl : isInc26 x r = false := by cases h : isInc26 x r <;> simp_all
  obtain ⟨Q, hQ, hqx, hqr⟩ := pair_in_quad x r hfl
  exact h3 Q hQ ⟨⟨x, hx.1, hqx⟩, ⟨x, hx.2, hqx⟩, ⟨r, hr, hqr⟩⟩

lemma okQuad_of_okQuad3_interL (A B R : Finset (Fin 26)) (h3 : okQuad3 A B R) :
    okQuad (A ∩ R) B := by
  intro y hy b hb
  simp only [Finset.mem_inter] at hy
  by_contra hne
  have hfl : isInc26 y b = false := by cases h : isInc26 y b <;> simp_all
  obtain ⟨Q, hQ, hqy, hqb⟩ := pair_in_quad y b hfl
  exact h3 Q hQ ⟨⟨y, hy.1, hqy⟩, ⟨b, hb, hqb⟩, ⟨y, hy.2, hqy⟩⟩

lemma okQuad_of_okQuad3_interR (A B R : Finset (Fin 26)) (h3 : okQuad3 A B R) :
    okQuad (B ∩ R) A := by
  intro z hz a ha
  simp only [Finset.mem_inter] at hz
  by_contra hne
  have hfl : isInc26 z a = false := by cases h : isInc26 z a <;> simp_all
  obtain ⟨Q, hQ, hqz, hqa⟩ := pair_in_quad z a hfl
  exact h3 Q hQ ⟨⟨a, ha, hqa⟩, ⟨z, hz.1, hqz⟩, ⟨z, hz.2, hqz⟩⟩

lemma inp_pair_hit (p l : Fin 13) (w : Fin 26)
    (hw : (inp {p} {l}).getD w.1 false = true) :
    w.1 = p.1 ∨ w.1 = 13 + l.1 := by
  have hv : V [] (inp {p} {l}) w.1 = (inp {p} {l}).getD w.1 false := by
    unfold V; exact getD_wiresFrom [] (inp {p} {l}) w.1 (by rw [inp_len]; exact w.2)
  rw [hw] at hv
  by_cases h13 : w.1 < 13
  · left
    have vp := V_point [] {p} {l} w.1 h13
    rw [hv] at vp
    have vp' := vp.symm
    simp only [decide_eq_true_eq, Finset.mem_singleton] at vp'
    exact congrArg Fin.val vp'
  · right
    have vl := V_line [] {p} {l} w.1 (by omega) w.2
    rw [hv] at vl
    have vl' := vl.symm
    simp only [decide_eq_true_eq, Finset.mem_singleton] at vl'
    have hval := congrArg Fin.val vl'
    dsimp at hval
    omega

lemma inp_pair_eq_cases (p l : Fin 13) (a : Fin 26)
    (ha : (inp {p} {l}).getD a.1 false = true) :
    a = ⟨p.1, by omega⟩ ∨ a = ⟨13 + l.1, by omega⟩ := by
  rcases inp_pair_hit p l a ha with h | h
  · left; ext; exact h
  · right; ext; exact h

lemma pigeonhole_hit (A B R : Finset (Fin 26)) (p l : Fin 13)
    (hA : ∃ a ∈ A, (inp {p} {l}).getD a.1 false = true)
    (hB : ∃ b ∈ B, (inp {p} {l}).getD b.1 false = true)
    (hR : ∃ r ∈ R, (inp {p} {l}).getD r.1 false = true) :
    ∃ c ∈ (A ∩ B) ∪ (A ∩ R) ∪ (B ∩ R), (inp {p} {l}).getD c.1 false = true := by
  obtain ⟨a, haA, ha⟩ := hA
  obtain ⟨b, hbB, hb⟩ := hB
  obtain ⟨r, hrR, hr⟩ := hR
  rcases inp_pair_eq_cases p l a ha with ha1 | ha2 <;>
    rcases inp_pair_eq_cases p l b hb with hb1 | hb2 <;>
    rcases inp_pair_eq_cases p l r hr with hr1 | hr2
  · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨haA, by rw [ha1, ← hb1]; exact hbB⟩)), ha⟩
  · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨haA, by rw [ha1, ← hb1]; exact hbB⟩)), ha⟩
  · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨haA, by rw [ha1, ← hr1]; exact hrR⟩)), ha⟩
  · exact ⟨b, Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hbB, by rw [hb2, ← hr2]; exact hrR⟩), hb⟩
  · exact ⟨b, Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hbB, by rw [hb1, ← hr1]; exact hrR⟩), hb⟩
  · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨haA, by rw [ha2, ← hr2]; exact hrR⟩)), ha⟩
  · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨haA, by rw [ha2, ← hb2]; exact hbB⟩)), ha⟩
  · exact ⟨a, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨haA, by rw [ha2, ← hb2]; exact hbB⟩)), ha⟩

lemma qHit_eq_inp_getD (Q : Finset (Fin 13)) (a : Fin 26) :
    (inp Q (TQ Q)).getD a.1 false = qHit Q a := by
  have hv1 : V [] (inp Q (TQ Q)) a.1 = (inp Q (TQ Q)).getD a.1 false := by
    unfold V; exact getD_wiresFrom [] (inp Q (TQ Q)) a.1 (by rw [inp_len]; exact a.2)
  rw [← hv1, qHit_eq_V [] Q a]

lemma pureOr_V_orSet (gs : List Gate) (hback : ReadsBack 26 ⟨gs, 0⟩)
    (w : ℕ) (hw : w < 26 + gs.length) (hpo : pureOr gs w) (x : List Bool) (hx : x.length = 26) :
    (V gs x w = true ↔ ∃ a ∈ orSetAvoid gs gs.length w, x.getD a.1 false = true) := by
  constructor
  · intro hVw
    apply orSetAvoid_complete gs gs.length hback x hx (V_out gs x (26 + gs.length) (by rw [hx]))
      w hw (fun _ => by omega) _ hVw
    intro m hw26 hrel _
    have hpo' := hpo hw26
    rcases hrel with rfl | hic
    · exact hpo'.2.1
    · exact hpo'.2.2 m hic
  · exact orSetAvoid_sound gs gs.length hback x hx w hw

lemma orSetAvoid_eq_of_lt (gs : List Gate) (avoid : ℕ) (ha : avoid ≤ gs.length)
    (w : ℕ) (hw : w < 26 + avoid) :
    orSetAvoid gs avoid w = orSetAvoid gs gs.length w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw26 : w < 26
    · rw [orSetAvoid_lt gs avoid w hw26, orSetAvoid_lt gs gs.length w hw26]
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      rw [orSetAvoid, orSetAvoid]
      have h1 : ¬ 26 + k < 26 := by omega
      have h2 : ¬ 26 + k = 26 + avoid := by omega
      have h3 : ¬ 26 + k = 26 + gs.length := by omega
      simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left]
      cases hg : gs[k]? with
      | none => rfl
      | some g =>
        dsimp only
        cases hop : g.op with
        | or =>
          ext a
          simp only [Finset.mem_biUnion, List.mem_toFinset]
          constructor <;> rintro ⟨u, hu, hau⟩ <;> refine ⟨u, hu, ?_⟩
          · split_ifs at hau with hlt
            · rw [ih u hlt (by omega)] at hau; simp [hlt, hau]
            · simp at hau
          · split_ifs at hau with hlt
            · rw [← ih u hlt (by omega)] at hau; simp [hlt, hau]
            · simp at hau
        | _ => rfl

lemma orSetAvoid_eq_of_agree (gs gs' : List Gate) (avoid : ℕ)
    (hagree : ∀ k < gs.length, k ≠ avoid → gs'[k]? = gs[k]?)
    (w : ℕ) (hw : w < 26 + gs.length) :
    orSetAvoid gs avoid w = orSetAvoid gs' avoid w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw26 : w < 26
    · rw [orSetAvoid_lt gs avoid w hw26, orSetAvoid_lt gs' avoid w hw26]
    · by_cases hwa : w = 26 + avoid
      · rw [hwa, orSetAvoid_self, orSetAvoid_self]
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hklen : k < gs.length := by omega
        have hka : k ≠ avoid := by omega
        have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        have hg1 : gs'[k]? = some gs[k] := (hagree k hklen hka).trans hg0
        rw [orSetAvoid, orSetAvoid]
        have h1 : ¬ 26 + k < 26 := by omega
        have h2 : ¬ 26 + k = 26 + avoid := by omega
        simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left, hg0, hg1]
        cases hop : gs[k].op with
        | or =>
          ext a
          simp only [Finset.mem_biUnion, List.mem_toFinset]
          constructor <;> rintro ⟨u, hu, hau⟩ <;> refine ⟨u, hu, ?_⟩
          · split_ifs at hau with hlt
            · rw [ih u hlt (by omega)] at hau; simp [hlt, hau]
            · simp at hau
          · split_ifs at hau with hlt
            · rw [← ih u hlt (by omega)] at hau; simp [hlt, hau]
            · simp at hau
        | _ => rfl

lemma reachesOr_gt_inputs (gs : List Gate) (avoid t w : ℕ) (_ht : 26 ≤ t)
    (hr : reachesOr gs avoid t w) : t ≤ w := by
  induction hr with
  | base => exact le_refl _
  | @step _ _ _ _ _ _ _ hlt _ ih =>
    omega

lemma reachesOr_map_above (gs gs' : List Gate) (avoid a w : ℕ)
    (hmap : ∀ k, a < k → k < gs.length → gs'[k]? = gs[k]?)
    (hr : reachesOr gs avoid (26 + a) w) :
    reachesOr gs' avoid (26 + a) w := by
  induction hr with
  | base => exact reachesOr.base
  | @step k g u hg hk hop hu hlt hr_u ih =>
    have hge := reachesOr_gt_inputs gs avoid (26 + a) u (by omega) hr_u
    have hlen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hga : gs'[k]? = some g := by rw [hmap k (by omega) hlen, hg]
    exact reachesOr.step hga hk hop hu hlt ih

lemma reachesOr_of_inCone_pureOr (gs : List Gate) (a b : ℕ)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hinc : InCone 26 ⟨gs, 0⟩ a b) (hpo : pureOr gs (26 + b)) :
    reachesOr gs gs.length (26 + a) (26 + b) := by
  rcases reachesAvoiding_split gs gs.length (26 + a) hgs (26 + b) (inCone_reachesAvoiding gs a b hinc) with hOr | hAnd
  · exact hOr
  · obtain ⟨c, gc, hgc, hcop, _, hcw, _⟩ := hAnd
    have hga : gateAt ⟨gs, 0⟩ c = gc := by simp [gateAt, List.getD_eq_getElem?_getD, hgc]
    have hpo' := hpo (by omega)
    rw [Nat.add_sub_cancel_left] at hpo'
    rcases reachesAvoiding_inCone gs gs.length (26 + c) (26 + b) (by omega) hcw with heq | ⟨_, hic⟩
    · have hcb : c = b := by omega
      subst hcb
      have hor := hpo'.2.1
      rw [hga, hcop] at hor; cases hor
    · rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at hic
      have hor := hpo'.2.2 c hic
      rw [hga, hcop] at hor; cases hor

lemma orSetAvoid_sub_of_hit (gs : List Gate)
    (hgs : ∀ g0 ∈ gs, g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (g w : ℕ) (hpo : pureOr gs w)
    (hhit : w = 26 + g ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ g (w - 26))) :
    orSetAvoid gs gs.length (26 + g) ⊆ orSetAvoid gs gs.length w := by
  rcases hhit with rfl | ⟨hw26, hic⟩
  · exact Finset.Subset.rfl
  · have hweq : 26 + (w - 26) = w := by omega
    rw [← hweq]
    exact reachesOr_orSet gs gs.length (26 + g) (26 + (w - 26))
      (reachesOr_of_inCone_pureOr gs g (w - 26) hgs hic (by rw [hweq]; exact hpo))

lemma two_inputs_distinct {g : Gate} (htwo : g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) :
    ∃ a b : ℕ, a ≠ b ∧ g.inputs = [a, b] := by
  obtain ⟨hl, hne⟩ := htwo
  cases h1 : g.inputs with
  | nil => simp [h1] at hl
  | cons x xs => cases h2 : xs with
    | nil => simp [h1, h2] at hl
    | cons y ys => cases h3 : ys with
      | nil => exact ⟨x, y, by simpa [h1, h2, h3] using hne, by simp⟩
      | cons _ _ => simp [h1, h2, h3] at hl

lemma other_and_inputs_pureOr (gs : List Gate)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (i j : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (k : ℕ) (hk : k < gs.length) (hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and) (hkj : k ≠ j) :
    ∀ u ∈ (gateAt ⟨gs, 0⟩ k).inputs, pureOr gs u := by
  intro u hu hu26
  have hu_lt : u < 26 + k := hback k hk u hu
  have hno : ∀ m, (m = u - 26 ∨ InCone 26 ⟨gs, 0⟩ m (u - 26)) → (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
    intro m hm
    have hmk : InCone 26 ⟨gs, 0⟩ m k := by
      rcases hm with rfl | hic
      · have hueq : 26 + (u - 26) = u := by omega
        exact inCone_direct ⟨gs, 0⟩ (u - 26) k hk (by rw [hueq]; exact hu) (by omega)
      · exact (inCone_iff 26 ⟨gs, 0⟩ m k hk).2 ⟨u, hu, hu26, hu_lt, Or.inr hic⟩
    have hm_len : m < gs.length := by have := (inCone_lt ⟨gs, 0⟩ m k hmk).1; omega
    cases hop : (gateAt ⟨gs, 0⟩ m).op with
    | or => rfl
    | and =>
      have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hop hkA hmk).2
      exact absurd this hkj
    | _ =>
      have hgm := (hmon gs[m] (List.getElem_mem hm_len)).1
      have hga : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hm_len
      rw [← hga] at hgm
      rcases hgm with h | h <;> rw [h] at hop <;> cases hop
  exact ⟨by omega, hno (u - 26) (Or.inl rfl), fun a ha => hno a (Or.inr ha)⟩

lemma reachesAvoiding_wL_sub_orSet (gs : List Gate)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i j wL : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hwL_mem : wL ∈ (gateAt ⟨gs, 0⟩ j).inputs) (hwL_lt : wL < 26 + j)
    (g : ℕ) (hgi : g < i)
    (hr : reachesAvoiding gs i (26 + g) wL) :
    orSetAvoid gs gs.length (26 + g) ⊆ orSetAvoid gs i wL := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hgs_eq : ∀ g0 ∈ gs, g0.op = GateOp.and ∨ g0.op = GateOp.or := fun g0 hg0 => (hmon g0 hg0).1
  rcases reachesAvoiding_split gs i (26 + g) hgs_eq wL hr with hOr | hAnd
  · rw [← orSetAvoid_eq_of_lt gs i (hlt.1.trans hlt.2).le (26 + g) (by omega)]
    exact reachesOr_orSet gs i (26 + g) wL hOr
  · obtain ⟨a, ga, hga, haop, hai, haw, _⟩ := hAnd
    have halen : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
    have hga_eq : gateAt ⟨gs, 0⟩ a = ga := by simp [gateAt, List.getD_eq_getElem?_getD, hga]
    have haj : InCone 26 ⟨gs, 0⟩ a j := by
      rcases reachesAvoiding_inCone gs i (26 + a) wL (by omega) haw with heq | ⟨hw26, hic⟩
      · have : 26 + a = wL := heq.symm
        exact inCone_direct ⟨gs, 0⟩ a j hlt.2 (by rw [this]; exact hwL_mem) (by omega)
      · rw [Nat.add_sub_cancel_left] at hic
        exact (inCone_iff 26 ⟨gs, 0⟩ a j hlt.2).2 ⟨wL, hwL_mem, hw26, hwL_lt, Or.inr hic⟩
    have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij (by rw [hga_eq]; exact haop) hjA haj).1
    exact absurd this hai

lemma nonStar_no_bypass (gs : List Gate) (outG : ℕ) (_hout : outG + 1 = gs.length)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and) (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (g : ℕ) (hg : g < gs.length) (hpo : pureOr gs (26 + g))
    (hns : ¬ ∃ z : Fin 26, ∀ a ∈ orSetAvoid gs gs.length (26 + g), isInc26 a z = true) :
    (∀ a < gs.length, (gateAt ⟨gs, 0⟩ a).op = GateOp.and → a ≠ i → a ≠ j → ¬ InCone 26 ⟨gs, 0⟩ g a) ∧
    ¬ reachesAvoiding gs j (26 + g) (26 + outG) := by
  have hgs_eq : ∀ g0 ∈ gs, g0.op = GateOp.and ∨ g0.op = GateOp.or := fun g0 hg0 => (hmon g0 hg0).1
  have hpos : ∀ g0 ∈ gs, 0 < g0.inputs.length := fun g0 hg0 => by rw [(htwo g0 hg0).1]; omega
  have hSg_ne : (orSetAvoid gs gs.length (26 + g)).Nonempty :=
    orSetAvoid_nonempty gs hback hpos (26 + g) (by omega) hpo
  have hno_and : ∀ a < gs.length, (gateAt ⟨gs, 0⟩ a).op = GateOp.and → a ≠ i → a ≠ j → ¬ InCone 26 ⟨gs, 0⟩ g a := by
    intro a halen haA hai haj hga_inc
    have hga_eq : gateAt ⟨gs, 0⟩ a = gs[a] := gateAt_eq ⟨gs, 0⟩ a halen
    have ha_rej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + a) = false := by
      intro Q hQ
      by_cases hao : a = outG
      · subst hao; exact hrej Q hQ
      · have hinc_ao := (hreach a halen).resolve_left hao
        rcases reachesAvoiding_split gs gs.length (26 + a) hgs_eq (26 + outG) (inCone_reachesAvoiding gs a outG hinc_ao) with hOr | hAnd
        · rw [Bool.eq_false_iff]; intro htr
          have := reachesOr_V gs gs.length (26 + a) hback (inp Q (TQ Q)) (inp_len _ _) (26 + outG) hOr htr
          rw [hrej Q hQ] at this; cases this
        · obtain ⟨b, gb, hgb, hbop, _, _, u, hu, hult, hOr⟩ := hAnd
          have hblen : b < gs.length := (List.getElem?_eq_some_iff.1 hgb).1
          have hgb_eq : gateAt ⟨gs, 0⟩ b = gb := by simp [gateAt, List.getD_eq_getElem?_getD, hgb]
          have hab : InCone 26 ⟨gs, 0⟩ a b := by
            rcases reachesOr_inCone gs gs.length (26 + a) u (by omega) hOr with heq | ⟨hu26, hic⟩
            · rw [heq] at hu
              have hltab : a < b := by have := hback b hblen (26 + a) (by rw [hgb_eq]; exact hu); omega
              exact inCone_direct ⟨gs, 0⟩ a b hblen (by rw [hgb_eq]; exact hu) hltab
            · exact (inCone_iff 26 ⟨gs, 0⟩ a b hblen).2
                ⟨u, by rw [hgb_eq]; exact hu, hu26, hult, Or.inr (by simpa [Nat.add_sub_cancel_left] using hic)⟩
          have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij haA (by rw [hgb_eq]; exact hbop) hab).1
          exact absurd this hai
    obtain ⟨v1, v2, hv12, hva_eq⟩ := two_inputs_distinct (htwo gs[a] (List.getElem_mem halen))
    have ha_inc := hga_inc
    rw [inCone_iff 26 ⟨gs, 0⟩ g a halen, hga_eq, hva_eq] at ha_inc
    obtain ⟨u, hu, hu26, hult, hrel⟩ := ha_inc
    let other := if u = v1 then v2 else v1
    have hpo_u : pureOr gs u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP a halen haA haj u (by rw [hga_eq, hva_eq]; exact hu)
    have hoth_mem : other ∈ gs[a].inputs := by
      rw [hva_eq]; dsimp only [other]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
      rcases hu with rfl | rfl
      · rw [ite_eq_left rfl]; right; rfl
      · rw [ite_eq_right hv12.symm]; left; rfl
    have hpo_oth : pureOr gs other := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP a halen haA haj other (by rw [hga_eq]; exact hoth_mem)
    have holt : other < 26 + a := hback a halen other (by rw [hga_eq]; exact hoth_mem)
    have hsub_g : orSetAvoid gs gs.length (26 + g) ⊆ orSetAvoid gs gs.length u := by
      rcases hrel with hgu | hgic
      · have hueq : u = 26 + g := by omega
        rw [hueq]
      · have hueq : 26 + (u - 26) = u := by omega
        rw [← hueq]
        exact reachesOr_orSet gs gs.length (26 + g) (26 + (u - 26))
          (reachesOr_of_inCone_pureOr gs g (u - 26) hgs_eq hgic (by rw [hueq]; exact hpo_u))
    have hoth_ne : (orSetAvoid gs gs.length other).Nonempty :=
      orSetAvoid_nonempty gs hback hpos other (by omega) hpo_oth
    obtain ⟨z, hz⟩ := hoth_ne
    apply hns
    refine ⟨z, fun c hc => ?_⟩
    by_contra hinc_ne
    have hfl : isInc26 c z = false := by cases h : isInc26 c z <;> simp_all
    obtain ⟨Q, hQ, hqc, hqz⟩ := pair_in_quad c z hfl
    have hg0 : gs[a]? = some gs[a] := List.getElem?_eq_getElem halen
    have hba : ∀ w ∈ gs[a].inputs, w < 26 + a := fun w hw => hback a halen w (by rw [hga_eq]; exact hw)
    have hopa : gs[a].op = GateOp.and := by rw [← hga_eq]; exact haA
    have hVu : V gs (inp Q (TQ Q)) u = true :=
      orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) u (by omega)
        ⟨c, hsub_g hc, by rw [qHit_eq_inp_getD, hqc]⟩
    have hVoth : V gs (inp Q (TQ Q)) other = true :=
      orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) other (by omega)
        ⟨z, hz, by rw [qHit_eq_inp_getD, hqz]⟩
    have htr : V gs (inp Q (TQ Q)) (26 + a) = true := by
      rw [andN_iff gs _ (inp_len _ _) a gs[a] hg0 hba hopa]
      intro w hw
      rw [hva_eq] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hw
      rcases hw with hw1 | hw2
      · rcases hu with hu1 | hu2
        · rw [hw1, ← hu1]; exact hVu
        · have hoth1 : other = v1 := by dsimp only [other]; rw [hu2, ite_eq_right hv12.symm]
          rw [hw1, ← hoth1]; exact hVoth
      · rcases hu with hu1 | hu2
        · have hoth2 : other = v2 := by dsimp only [other]; rw [ite_eq_left hu1]
          rw [hw2, ← hoth2]; exact hVoth
        · rw [hw2, ← hu2]; exact hVu
    rw [ha_rej Q hQ] at htr; cases htr
  refine ⟨hno_and, ?_⟩
  intro hreach_g
  rcases reachesAvoiding_split gs j (26 + g) hgs_eq (26 + outG) hreach_g with hOr | hAnd
  · obtain ⟨a, ha⟩ := hSg_ne
    obtain ⟨Q, hQ, hqa⟩ := single_in_quad a
    have htr := reachesOr_V gs j (26 + g) hback (inp Q (TQ Q)) (inp_len _ _) (26 + outG) hOr
      (orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) (26 + g) (by omega) ⟨a, ha, by rw [qHit_eq_inp_getD, hqa]⟩)
    rw [hrej Q hQ] at htr; cases htr
  · obtain ⟨a, ga, hga, haop, haj, haw, u, hu, hult, hOr⟩ := hAnd
    have halen : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
    have hga_eq : gateAt ⟨gs, 0⟩ a = ga := by simp [gateAt, List.getD_eq_getElem?_getD, hga]
    by_cases hai : a = i
    · subst hai; exact hi_no_bypass haw
    · have hinc_ga : InCone 26 ⟨gs, 0⟩ g a := by
        rcases reachesOr_inCone gs j (26 + g) u (by omega) hOr with heq | ⟨hu26, hic⟩
        · rw [heq] at hu
          have hltga : g < a := by have := hback a halen (26 + g) (by rw [hga_eq]; exact hu); omega
          exact inCone_direct ⟨gs, 0⟩ g a halen (by rw [hga_eq]; exact hu) hltga
        · exact (inCone_iff 26 ⟨gs, 0⟩ g a halen).2
            ⟨u, by rw [hga_eq]; exact hu, hu26, hult, Or.inr (by simpa [Nat.add_sub_cancel_left] using hic)⟩
      exact hno_and a halen (by rw [hga_eq]; exact haop) hai haj hinc_ga

lemma pureOr_mapIdx (gs : List Gate) (patch : ℕ → Gate → Gate) (Bad : Finset ℕ)
    (hkeep : ∀ k g, k ∉ Bad → patch k g = g)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (w : ℕ) (hw : w < 26 + gs.length)
    (hor : ∀ m, (w = 26 + m ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ m (w - 26))) → m ∉ Bad →
      (gateAt ⟨gs, 0⟩ m).op = GateOp.or)
    (hbad : ∀ b ∈ Bad, b < gs.length →
      (w = 26 + b ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ b (w - 26))) →
      pureOr (gs.mapIdx patch) (26 + b)) :
    pureOr (gs.mapIdx patch) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw26
    obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
    have hklen : k < gs.length := by omega
    by_cases hkBad : k ∈ Bad
    · exact hbad k hkBad hklen (Or.inl rfl) hw26
    · have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
      have hg1 : (gs.mapIdx patch)[k]? = some gs[k] := by
        simp [List.getElem?_mapIdx, hg0, hkeep k gs[k] hkBad]
      have hga1 : gateAt ⟨gs.mapIdx patch, 0⟩ k = gs[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hg1]
      have hop1 : (gateAt ⟨gs.mapIdx patch, 0⟩ k).op = GateOp.or := by
        rw [hga1, ← hga0]; exact hor k (Or.inl rfl) hkBad
      apply pureOr_step (gs.mapIdx patch) k (by rw [List.length_mapIdx]; exact hklen) hop1 _ (by omega)
      intro u hu
      rw [hga1] at hu
      have hu_lt : u < 26 + k := hback k hklen u (by rw [hga0]; exact hu)
      apply ih u hu_lt (by omega)
      · intro m hm hmBad
        have hm_inc : InCone 26 ⟨gs, 0⟩ m k := by
          rcases hm with rfl | ⟨hu26, hic⟩
          · exact inCone_direct ⟨gs, 0⟩ m k hklen (by rw [hga0]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ m k hklen).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩
        exact hor m (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hm_inc⟩) hmBad
      · intro b hb hblen hrel
        have hic_b : InCone 26 ⟨gs, 0⟩ b k := by
          rcases hrel with rfl | ⟨hu26, hic⟩
          · exact inCone_direct ⟨gs, 0⟩ b k hklen (by rw [hga0]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ b k hklen).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩
        exact hbad b hb hblen (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hic_b⟩)

lemma mapIdx_eval_avoid (gs : List Gate) (patch : ℕ → Gate → Gate) (Bad : Finset ℕ)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hkeep : ∀ k g, k ∉ Bad → patch k g = g)
    (x : List Bool) (hx : x.length = 26) :
    ∀ w : ℕ, w < 26 + gs.length →
      (∀ b ∈ Bad, w ≠ 26 + b ∧ (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ b (w - 26))) →
      V (gs.mapIdx patch) x w = V gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hav
    by_cases hw26 : w < 26
    · exact V_in _ gs x w (by rw [hx]; exact hw26)
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hk : k < gs.length := by omega
      have hkBad : k ∉ Bad := fun hmem => (hav k hmem).1 rfl
      have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have hg1 : (gs.mapIdx patch)[k]? = some gs[k] := by
        simp [List.getElem?_mapIdx, hg0, hkeep k gs[k] hkBad]
      have hbm : ∀ u ∈ gs[k].inputs, u < 26 + k := fun u hu => hback k hk u (by rw [hga0]; exact hu)
      rw [gate_val_aux _ x hx k gs[k] hg1 hbm, gate_val_aux gs x hx k gs[k] hg0 hbm]
      congr 1; apply List.map_inj_left.2
      intro u hu
      have hu_lt := hbm u hu
      apply ih u hu_lt (by omega)
      intro b hb
      have h1 : u ≠ 26 + b := by
        intro heq
        have hnb := (hav b hb).2 (by omega)
        rw [Nat.add_sub_cancel_left] at hnb
        exact hnb (inCone_direct ⟨gs, 0⟩ b k hk (by rw [hga0, ← heq]; exact hu) (by omega))
      refine ⟨h1, fun hu26 hic => ?_⟩
      have hnb := (hav b hb).2 (by omega)
      rw [Nat.add_sub_cancel_left] at hnb
      exact hnb ((inCone_iff 26 ⟨gs, 0⟩ b k hk).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩)

lemma reachesBadOnlyVia_of_singleton_avoid (gs : List Gate) (skip target w : ℕ)
    (havoid : ¬ reachesAvoiding gs skip (26 + target) w) :
    reachesBadOnlyVia gs {target} skip w := by
  intro b hb _ hr
  simp only [Finset.mem_singleton] at hb; subst hb
  exact havoid hr

lemma gateAt_below_j_or_eq (gs : List Gate)
    (i j : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m : ℕ) (hm : m < gs.length) (hinc : InCone 26 ⟨gs, 0⟩ m j) (hmi : m ≠ i) :
    (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
  cases hop : (gateAt ⟨gs, 0⟩ m).op with
  | or => rfl
  | and =>
    have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hop hjA hinc).1
    exact absurd this hmi
  | _ =>
    have hgm := (hmon gs[m] (List.getElem_mem hm)).1
    have hga : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hm
    rw [← hga] at hgm
    rcases hgm with h | h <;> rw [h] at hop <;> cases hop

lemma pureOr_wR (gs : List Gate)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (i j wR : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hwR_mem : wR ∈ (gateAt ⟨gs, 0⟩ j).inputs)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26))) :
    pureOr gs wR := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hwR_lt : wR < 26 + j := hback j hlt.2 wR hwR_mem
  intro hw26
  have hm : ∀ m, (m = wR - 26 ∨ InCone 26 ⟨gs, 0⟩ m (wR - 26)) → (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
    intro m hrel
    have hmj : InCone 26 ⟨gs, 0⟩ m j := by
      rcases hrel with rfl | hic
      · have hwr : 26 + (wR - 26) = wR := by omega
        exact inCone_direct ⟨gs, 0⟩ (wR - 26) j hlt.2 (by rw [hwr]; exact hwR_mem) (by omega)
      · exact (inCone_iff 26 ⟨gs, 0⟩ m j hlt.2).2 ⟨wR, hwR_mem, hw26, hwR_lt, Or.inr hic⟩
    have hmi : m ≠ i := fun heq => by
      subst heq
      rcases hrel with hm0 | hic
      · apply hwR_no_i.1; omega
      · exact hwR_no_i.2 hw26 hic
    exact gateAt_below_j_or_eq gs i j hiA hjA hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m j hmj).1; omega) hmj hmi
  exact ⟨by omega, hm (wR - 26) (Or.inl rfl), fun a ha => hm a (Or.inr ha)⟩

lemma gate_mk_or_eq (g : Gate) (hop : g.op = GateOp.or) (l : List ℕ) (hl : l = g.inputs) :
    (⟨GateOp.or, l⟩ : Gate) = g := by
  subst hl; cases g; simp only [Gate.mk.injEq, and_true]; exact hop.symm

lemma case2_replace_i_or (gs : List Gate) (outG : ℕ) (_hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j wL wR : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (hwR_lt : wR < 26 + j)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26)))
    (hwj_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR)
    (hwL_lt : wL < 26 + j)
    (gI : Gate) (hgI_op : gI.op = GateOp.or) (hgI_len : gI.inputs.length ≤ 2)
    (hgI_back : ∀ v ∈ gI.inputs, v < 26 + i) (hgI_pure : ∀ v ∈ gI.inputs, pureOr gs v)
    (hacc_L : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) (26 + j) = true →
      V (gs.mapIdx (fun m g => if m = i then gI else g)) (inp {p} {l}) wL = true)
    (hrej_i : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) wR = true →
      ¬ (∃ v ∈ gI.inputs, V gs (inp Q (TQ Q)) v = true)) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  let patch : ℕ → Gate → Gate := fun m g => if m = i then gI else g
  let gs' := gs.mapIdx patch
  have hgs'_len : gs'.length = gs.length := List.length_mapIdx
  have hmon' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    apply mapIdx_mono
    intro m g hg
    dsimp only [patch]; split_ifs
    · exact ⟨Or.inr hgI_op, hgI_len⟩
    · exact hmon g (List.mem_of_getElem? hg)
  have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
    apply mapIdx_readsBack
    intro m g hg u hu
    dsimp only [patch] at hu; split_ifs at hu with hm
    · rw [hm]; exact hgI_back u hu
    · have hmlen : m < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      have hga : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
      exact hback m hmlen u (by rw [hga]; exact hu)
  have hkeep : ∀ k g, k ∉ ({i} : Finset ℕ) → patch k g = g := by
    intro k g hk; simp only [Finset.mem_singleton] at hk; simp [patch, hk]
  have hp_i : pureOr gs' (26 + i) := by
    have hg0 : gs[i]? = some gs[i] := List.getElem?_eq_getElem (by omega)
    have hgi' : gs'[i]? = some gI := by simp [gs', List.getElem?_mapIdx, hg0, patch]
    have hga' : gateAt ⟨gs', 0⟩ i = gI := by simp [gateAt, List.getD_eq_getElem?_getD, hgi']
    apply pureOr_step gs' i (by rw [hgs'_len]; omega) (by rw [hga']; exact hgI_op)
    intro v hv
    rw [hga'] at hv
    have hvlt := hgI_back v hv
    apply pureOr_mapIdx gs patch {i} hkeep hback v (by omega)
    · intro m hm _
      have hv26 : 26 ≤ v := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
      have hpo := hgI_pure v hv hv26
      rcases hm with heq | ⟨_, hic⟩
      · have hm_eq : m = v - 26 := by omega
        rw [hm_eq]; exact hpo.2.1
      · exact hpo.2.2 m hic
    · intro b hb _ hrel
      have hbi : b = i := Finset.mem_singleton.1 hb
      rcases hrel with hvb | ⟨_, hic⟩
      · omega
      · have := (inCone_lt ⟨gs, 0⟩ i (v - 26) (hbi ▸ hic)).1; omega
  have hgs'_lt_i : ∀ x : List Bool, x.length = 26 → ∀ w < 26 + i, V gs' x w = V gs x w := by
    intro x hx w hw
    apply mapIdx_eval_avoid gs patch {i} hback hkeep x hx w (by omega)
    intro b hb
    have hbi : b = i := Finset.mem_singleton.1 hb
    refine ⟨by omega, fun hw26 hic => ?_⟩
    have := (inCone_lt ⟨gs, 0⟩ i (w - 26) (hbi ▸ hic)).1; omega
  have hwR_eval : ∀ x : List Bool, x.length = 26 → V gs' x wR = V gs x wR := by
    intro x hx
    apply mapIdx_eval_avoid gs patch {i} hback hkeep x hx wR (by omega)
    intro b hb; have hbi : b = i := Finset.mem_singleton.1 hb; rw [hbi]; exact hwR_no_i
  have hbad_out : reachesBadOnlyVia gs {i} j (26 + outG) :=
    reachesBadOnlyVia_of_singleton_avoid gs j i (26 + outG) hi_no_bypass
  have hbad_wL : reachesBadOnlyVia gs {i} i wL := by
    intro b hb hbi; simp only [Finset.mem_singleton] at hb; exact absurd hb hbi
  have hnn' : ¬ ∃ a b : ℕ, (gateAt ⟨gs', 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs', 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs', 0⟩ a b := by
    apply no_nested_and_of_all_and_pureOr gs' 0
    intro k hk hkA u hu
    rw [hgs'_len] at hk
    have hki : k ≠ i := by
      intro heq; subst heq
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have hg' : gs'[k]? = some gI := by simp [gs', List.getElem?_mapIdx, hg0, patch]
      have hga' : gateAt ⟨gs', 0⟩ k = gI := by simp [gateAt, List.getD_eq_getElem?_getD, hg']
      rw [hga', hgI_op] at hkA; cases hkA
    have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    have hg' : gs'[k]? = some gs[k] := by simp [gs', List.getElem?_mapIdx, hg0, patch, hki]
    have hga' : gateAt ⟨gs', 0⟩ k = gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hg']
    have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
    have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0, ← hga']; exact hkA
    rw [hga'] at hu
    have hu_lt : u < 26 + k := hback k hk u (by rw [hga0]; exact hu)
    by_cases hkj : k = j
    · subst hkj
      apply pureOr_mapIdx gs patch {i} hkeep hback u (by omega)
      · intro m hm hmi
        simp only [Finset.mem_singleton] at hmi
        have hmj : InCone 26 ⟨gs, 0⟩ m k := by
          rcases hm with heq | ⟨hu26, hic⟩
          · have hm_eq : u - 26 = m := by omega
            have hueq : 26 + (u - 26) = u := by omega
            rw [← hm_eq]
            exact inCone_direct ⟨gs, 0⟩ (u - 26) k hk (by rw [hga0, hueq]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ m k hk).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩
        exact gateAt_below_j_or_eq gs i k hiA hkA0 hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m k hmj).1; omega) hmj hmi
      · intro b hb _ _; have hbi : b = i := Finset.mem_singleton.1 hb; rw [hbi]; exact hp_i
    · have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0]; exact hu)
      apply pureOr_mapIdx gs patch {i} hkeep hback u (by omega)
      · intro m hm _
        have hu26 : 26 ≤ u := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
        have := hpo_u hu26
        rcases hm with heq | ⟨_, hic⟩
        · have hm_eq : m = u - 26 := by omega
          rw [hm_eq]; exact this.2.1
        · exact this.2.2 m hic
      · intro b hb _ hrel
        have hbi : b = i := Finset.mem_singleton.1 hb
        have hib : InCone 26 ⟨gs, 0⟩ i k := by
          rcases hrel with heq | ⟨hu26, hic⟩
          · have hueq : 26 + i = u := by omega
            exact inCone_direct ⟨gs, 0⟩ i k hk (by rw [hga0, hueq]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ i k hk).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr (hbi ▸ hic)⟩
        have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 hib).2
        exact absurd this hkj
  have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
  have hg'j : gs'[j]? = some gs[j] := by simp [gs', List.getElem?_mapIdx, hg0j, patch, show j ≠ i by omega]
  have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
  have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
  have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
  apply core_contra gs' (26 + outG) (by rw [hgs'_len]; exact hsz) hmon' hback' hnn'
  · intro p l hp
    apply mapIdx_eval_up gs patch {i} j hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _) _ (26 + outG) (by omega) hbad_out (hacc p l hp)
    intro hVj
    have hacc_wL := hacc_L p l hp hVj
    rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
    have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
    rw [andN_iff gs' _ (inp_len _ _) j gs[j] hg'j hbj hopj]
    intro w hw; rw [← hga0j, hwj_inp] at hw
    rcases hw with rfl | rfl
    · exact hacc_wL
    · rw [hwR_eval _ (inp_len _ _)]; exact hVwR
  · intro Q hQ
    rw [Bool.eq_false_iff]; intro htr
    have hdn : V gs' (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
      intro hVj'
      rw [andN_iff gs' _ (inp_len _ _) j gs[j] hg'j hbj hopj] at hVj'
      have hVwL' := hVj' wL (by rw [← hga0j, hwj_inp]; left; rfl)
      have hVwR' := hVj' wR (by rw [← hga0j, hwj_inp]; right; rfl)
      rw [hwR_eval _ (inp_len _ _)] at hVwR'
      have hVi' : V gs' (inp Q (TQ Q)) (26 + i) = false := by
        rw [Bool.eq_false_iff]; intro hti'
        have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem (by omega)
        have hgi' : gs'[i]? = some gI := by simp [gs', List.getElem?_mapIdx, hg0i, patch]
        rw [orN gs' _ (inp_len _ _) i gI hgi' hgI_back hgI_op] at hti'
        obtain ⟨v, hv, hVv'⟩ := hti'
        rw [hgs'_lt_i _ (inp_len _ _) v (hgI_back v hv)] at hVv'
        exact hrej_i Q hQ hVwR' ⟨v, hv, hVv'⟩
      have hVwL : V gs (inp Q (TQ Q)) wL = true :=
        mapIdx_eval_down gs patch {i} i hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _)
          (fun h => by rw [hVi'] at h; cases h) wL (by omega) hbad_wL hVwL'
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj]
      intro w hw; rw [← hga0j, hwj_inp] at hw
      rcases hw with rfl | rfl; exact hVwL; exact hVwR'
    have htr0 := mapIdx_eval_down gs patch {i} j hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _) hdn (26 + outG) (by omega) hbad_out htr
    rw [hrej Q hQ] at htr0; cases htr0

set_option maxHeartbeats 800000 in
lemma case2_sub3 (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j uA uB wL wR : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (hu_ne : uA ≠ uB) (hu_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ i).inputs ↔ w = uA ∨ w = uB)
    (hwL_reach : reachesOr gs gs.length (26 + i) wL)
    (hwR_lt : wR < 26 + j)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26)))
    (hwj_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR)
    (hX2 : 2 ≤ (orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length uB).card)
    (hAR_empty : orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length wR = ∅)
    (hBR_empty : orSetAvoid gs gs.length uB ∩ orSetAvoid gs gs.length wR = ∅)
    (hnok_AR : ¬ okQuad (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length wR))
    (hnok_BR : ¬ okQuad (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR))
    (h3 : okQuad3 (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR)) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hil : i < gs.length := by omega
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  have hpos : ∀ g ∈ gs, 0 < g.inputs.length := fun g hg => by rw [(htwo g hg).1]; omega
  let A := orSetAvoid gs gs.length uA
  let B := orSetAvoid gs gs.length uB
  let R := orSetAvoid gs gs.length wR
  let S_L := orSetAvoid gs i wL
  let X := A ∩ B
  have hX2' : 2 ≤ X.card := hX2
  have hX2'' : 2 ≤ (A ∩ B).card := hX2
  have huA_lt : uA < 26 + i := hback i hil uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_lt : uB < 26 + i := hback i hil uB ((hu_inp uB).2 (Or.inr rfl))
  have hwL_lt : wL < 26 + j := hback j hlt.2 wL ((hwj_inp wL).2 (Or.inl rfl))
  have huA_po : pureOr gs uA := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_po : pureOr gs uB := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uB ((hu_inp uB).2 (Or.inr rfl))
  have hwR_po : pureOr gs wR :=
    pureOr_wR gs hmon hback i j wR hiA hjA hij hAP ((hwj_inp wR).2 (Or.inr rfl)) hwR_no_i
  have hR_ne : R.Nonempty := orSetAvoid_nonempty gs hback hpos wR (by omega) hwR_po
  have hok_XR : okQuad X R := okQuad_of_okQuad3_inter A B R h3
  obtain ⟨x1, hx1, x2, hx2, hx12⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  obtain ⟨r0, hr0⟩ := hR_ne
  have hR_sing : ∀ r ∈ R, r = r0 := fun r hr => unique_common_inc x1 x2 r r0 hx12
    (hok_XR x1 hx1 r hr) (hok_XR x2 hx2 r hr) (hok_XR x1 hx1 r0 hr0) (hok_XR x2 hx2 r0 hr0)
  have hX_le4 : X.card ≤ 4 := by
    have hsub : X ⊆ Finset.univ.filter (fun a : Fin 26 => isInc26 a r0 = true) := by
      intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hok_XR x hx r0 hr0
    exact le_trans (Finset.card_le_card hsub) (star_card_le_4 r0)
  have hX_ne : X.Nonempty := ⟨x1, hx1⟩
  have huA26 : 26 ≤ uA := by
    by_contra hlt26
    have hcard : A.card = 1 := by simp [A, orSetAvoid_lt gs gs.length uA (by omega)]
    have hle : X.card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
    omega
  have huB26 : 26 ≤ uB := by
    by_contra hlt26
    have hcard : B.card = 1 := by simp [B, orSetAvoid_lt gs gs.length uB (by omega)]
    have hle : X.card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    omega
  obtain ⟨gA, rfl⟩ : ∃ gA, uA = 26 + gA := ⟨uA - 26, by omega⟩
  obtain ⟨gB, rfl⟩ : ∃ gB, uB = 26 + gB := ⟨uB - 26, by omega⟩
  have hA_ns : ¬ ∃ z : Fin 26, ∀ a ∈ A, isInc26 a z = true := by
    rintro ⟨z, hz⟩
    apply hnok_AR
    intro a ha r hr
    rw [hR_sing r hr]
    have hzeq : z = r0 := unique_common_inc x1 x2 z r0 hx12
      (hz x1 (Finset.mem_inter.1 hx1).1) (hz x2 (Finset.mem_inter.1 hx2).1)
      (hok_XR x1 hx1 r0 hr0) (hok_XR x2 hx2 r0 hr0)
    rw [← hzeq]; exact hz a ha
  have hB_ns : ¬ ∃ z : Fin 26, ∀ b ∈ B, isInc26 b z = true := by
    rintro ⟨z, hz⟩
    apply hnok_BR
    intro b hb r hr
    rw [hR_sing r hr]
    have hzeq : z = r0 := unique_common_inc x1 x2 z r0 hx12
      (hz x1 (Finset.mem_inter.1 hx1).2) (hz x2 (Finset.mem_inter.1 hx2).2)
      (hok_XR x1 hx1 r0 hr0) (hok_XR x2 hx2 r0 hr0)
    rw [← hzeq]; exact hz b hb
  have hgA_nb := nonStar_no_bypass gs outG hout hmon hback htwo hreach hrej i j hiA hjA hij hAP hi_no_bypass gA (by omega) huA_po hA_ns
  have hgB_nb := nonStar_no_bypass gs outG hout hmon hback htwo hreach hrej i j hiA hjA hij hAP hi_no_bypass gB (by omega) huB_po hB_ns
  have hok_SL_R : okQuad S_L R := by
    intro s hs r hr
    by_contra hne
    have hfl : isInc26 s r = false := by cases h : isInc26 s r <;> simp_all
    obtain ⟨Q, hQ, hqs, hqr⟩ := pair_in_quad s r hfl
    have hViQ : V gs (inp Q (TQ Q)) (26 + i) = false := by
      rw [Bool.eq_false_iff]; intro htr
      have hhg0 : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
      have hga0 : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
      have hbi : ∀ w ∈ gs[i].inputs, w < 26 + i := fun w hw => hback i hil w (by rw [hga0]; exact hw)
      have hopi : gs[i].op = GateOp.and := by rw [← hga0]; exact hiA
      rw [andN_iff gs _ (inp_len _ _) i gs[i] hhg0 hbi hopi] at htr
      have hVA := htr (26 + gA) (by rw [← hga0, hu_inp]; left; rfl)
      have hVB := htr (26 + gB) (by rw [← hga0, hu_inp]; right; rfl)
      obtain ⟨a, ha, hqa⟩ := (pureOr_V_orSet gs hback (26 + gA) (by omega) huA_po (inp Q (TQ Q)) (inp_len _ _)).1 hVA
      obtain ⟨b, hb, hqb⟩ := (pureOr_V_orSet gs hback (26 + gB) (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVB
      rw [qHit_eq_inp_getD] at hqa hqb
      exact h3 Q hQ ⟨⟨a, ha, hqa⟩, ⟨b, hb, hqb⟩, ⟨r, hr, hqr⟩⟩
    have hVwL : V gs (inp Q (TQ Q)) wL = true :=
      orSetAvoid_sound gs i hback (inp Q (TQ Q)) (inp_len _ _) wL (by omega) ⟨s, hs, by rw [qHit_eq_inp_getD, hqs]⟩
    have hVwR : V gs (inp Q (TQ Q)) wR = true :=
      orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) wR (by omega) ⟨r, hr, by rw [qHit_eq_inp_getD, hqr]⟩
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
    have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hVj := (andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj).2 (fun w hw => by
      rw [← hga0j, hwj_inp] at hw; rcases hw with rfl | rfl; exact hVwL; exact hVwR)
    rw [hjQ Q hQ] at hVj; cases hVj
  let s1 := min gA gB
  let s2 := max gA gB
  have hs12 : s1 < s2 := by dsimp only [s1, s2]; omega
  have hs2i : s2 < i := by dsimp only [s2]; omega
  let patch : ℕ → Gate → Gate := fun m g =>
    if m = s1 then orGate1 X
    else if m = s2 then orGate2 X
    else if m = i then ⟨GateOp.or, [26 + s1, 26 + s2]⟩
    else g
  let gs' := gs.mapIdx patch
  have hgs'_len : gs'.length = gs.length := List.length_mapIdx
  let Bad : Finset ℕ := {s1, s2, i}
  have hkeep : ∀ k g, k ∉ Bad → patch k g = g := by
    intro k g hk
    simp only [Bad, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    dsimp only [patch]
    rw [ite_eq_right hk.1, ite_eq_right hk.2.1, ite_eq_right hk.2.2]
  have hmon' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    apply mapIdx_mono; intro m g hg; dsimp only [patch]; split_ifs
    · simp [orGate1]
    · simp [orGate2]
    · simp
    · exact hmon g (List.mem_of_getElem? hg)
  have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
    apply mapIdx_readsBack; intro m g hg u hu; dsimp only [patch] at hu
    by_cases hm1 : m = s1
    · rw [ite_eq_left hm1] at hu; simp only [orGate1, List.mem_cons, List.not_mem_nil, or_false] at hu
      have h0 := (orElem X 0).2; have h1 := (orElem X 1).2
      rcases hu with rfl | rfl <;> omega
    · by_cases hm2 : m = s2
      · rw [ite_eq_right hm1, ite_eq_left hm2] at hu; simp only [orGate2, List.mem_cons, List.not_mem_nil, or_false] at hu
        have h2 := (orElem X 2).2; have h3 := (orElem X 3).2
        rcases hu with rfl | rfl <;> omega
      · by_cases hm3 : m = i
        · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_left hm3] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;> omega
        · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_right hm3] at hu
          have hmlen : m < gs.length := (List.getElem?_eq_some_iff.1 hg).1
          have hga : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
          exact hback m hmlen u (by rw [hga]; exact hu)
  have hg_s1 : gs'[s1]? = some (orGate1 X) := by
    have hg0 : gs[s1]? = some gs[s1] := List.getElem?_eq_getElem (by omega)
    simp [gs', List.getElem?_mapIdx, hg0, patch]
  have hg_s2 : gs'[s2]? = some (orGate2 X) := by
    have hg0 : gs[s2]? = some gs[s2] := List.getElem?_eq_getElem (by omega)
    simp [gs', List.getElem?_mapIdx, hg0, patch, show s2 ≠ s1 by omega]
  have hg_i : gs'[i]? = some ⟨GateOp.or, [26 + s1, 26 + s2]⟩ := by
    have hg0 : gs[i]? = some gs[i] := List.getElem?_eq_getElem (by omega)
    simp [gs', List.getElem?_mapIdx, hg0, patch, show i ≠ s1 by omega, show i ≠ s2 by omega]
  obtain ⟨hp_s1, hp_s2, hp_i, hX_eval⟩ :=
    orChain3_spec gs' s1 s2 i X hs12 hs2i (by rw [hgs'_len]; exact hil) hX_ne hX_le4 hg_s1 hg_s2 hg_i
  have hBad_mem : ∀ b ∈ Bad, b = gA ∨ b = gB ∨ b = i := by
    intro b hb; simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · dsimp only [s1]; by_cases h : gA ≤ gB
      · left; exact min_eq_left h
      · right; left; exact min_eq_right (le_of_not_ge h)
    · dsimp only [s2]; by_cases h : gA ≤ gB
      · right; left; exact max_eq_right h
      · left; exact max_eq_left (le_of_not_ge h)
    · right; right; rfl
  have hsub_R_no_A : ¬ (A ⊆ R) := fun hsub => by
    have : 2 ≤ R.card := by
      have : X.card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      exact le_trans hX2 (le_trans this (Finset.card_le_card hsub))
    have hR1 : R.card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by rw [hR_sing a ha, hR_sing b hb])
    omega
  have hsub_R_no_B : ¬ (B ⊆ R) := fun hsub => by
    have : 2 ≤ R.card := by
      have : X.card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      exact le_trans hX2 (le_trans this (Finset.card_le_card hsub))
    have hR1 : R.card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by rw [hR_sing a ha, hR_sing b hb])
    omega
  have hwR_av : ∀ b ∈ Bad, wR ≠ 26 + b ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ b (wR - 26)) := by
    intro b hb
    rcases hBad_mem b hb with hb1 | hb2 | hb3
    · rw [hb1]; refine ⟨fun heq => hsub_R_no_A (orSetAvoid_sub_of_hit gs hgs_eq gA wR hwR_po (Or.inl heq)),
        fun hw26 hic => hsub_R_no_A (orSetAvoid_sub_of_hit gs hgs_eq gA wR hwR_po (Or.inr ⟨hw26, hic⟩))⟩
    · rw [hb2]; refine ⟨fun heq => hsub_R_no_B (orSetAvoid_sub_of_hit gs hgs_eq gB wR hwR_po (Or.inl heq)),
        fun hw26 hic => hsub_R_no_B (orSetAvoid_sub_of_hit gs hgs_eq gB wR hwR_po (Or.inr ⟨hw26, hic⟩))⟩
    · rw [hb3]; exact hwR_no_i
  have hwR_eval : ∀ x : List Bool, x.length = 26 → V gs' x wR = V gs x wR := fun x hx =>
    mapIdx_eval_avoid gs patch Bad hback hkeep x hx wR (by omega) hwR_av
  have hbad_out : reachesBadOnlyVia gs Bad j (26 + outG) := by
    intro b hb _ hrb
    rcases hBad_mem b hb with hb1 | hb2 | hb3
    · rw [hb1] at hrb; exact hgA_nb.2 hrb
    · rw [hb2] at hrb; exact hgB_nb.2 hrb
    · rw [hb3] at hrb; exact hi_no_bypass hrb
  have hbad_wL : reachesBadOnlyVia gs Bad i wL := by
    intro b hb hbi hrb
    rcases hBad_mem b hb with hb1 | hb2 | hb3
    · rw [hb1] at hrb
      have hsub : A ⊆ S_L := reachesAvoiding_wL_sub_orSet gs hmon i j wL hiA hjA hij hAP ((hwj_inp wL).2 (Or.inl rfl)) hwL_lt gA (by omega) hrb
      exact hnok_AR (fun a ha r hr => hok_SL_R a (hsub ha) r hr)
    · rw [hb2] at hrb
      have hsub : B ⊆ S_L := reachesAvoiding_wL_sub_orSet gs hmon i j wL hiA hjA hij hAP ((hwj_inp wL).2 (Or.inl rfl)) hwL_lt gB (by omega) hrb
      exact hnok_BR (fun b' hb' r hr => hok_SL_R b' (hsub hb') r hr)
    · exact hbi hb3
  have hp_bad : ∀ b ∈ Bad, b < gs.length → pureOr gs' (26 + b) := by
    intro b hb _
    simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb1 | hb2 | hb3
    · rw [hb1]; exact hp_s1
    · rw [hb2]; exact hp_s2
    · rw [hb3]; exact hp_i
  have hnn' : ¬ ∃ a b : ℕ, (gateAt ⟨gs', 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs', 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs', 0⟩ a b := by
    apply no_nested_and_of_all_and_pureOr gs' 0
    intro k hk hkA u hu
    rw [hgs'_len] at hk
    have hkBad : k ∉ Bad := by
      intro hmem
      have hk_po := hp_bad k hmem hk (by omega)
      rw [Nat.add_sub_cancel_left] at hk_po
      rw [hk_po.2.1] at hkA; cases hkA
    have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    have hg' : gs'[k]? = some gs[k] := by simp [gs', List.getElem?_mapIdx, hg0, hkeep k gs[k] hkBad]
    have hga' : gateAt ⟨gs', 0⟩ k = gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hg']
    have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
    have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0, ← hga']; exact hkA
    rw [hga'] at hu
    have hu_lt : u < 26 + k := hback k hk u (by rw [hga0]; exact hu)
    by_cases hkj : k = j
    · subst hkj
      apply pureOr_mapIdx gs patch Bad hkeep hback u (by omega)
      · intro m hm hmBad
        have hmi : m ≠ i := fun h => hmBad (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self i)))
        have hmj : InCone 26 ⟨gs, 0⟩ m k := by
          rcases hm with heq | ⟨hu26, hic⟩
          · have hm_eq : u - 26 = m := by omega
            have hueq : 26 + (u - 26) = u := by omega
            rw [← hm_eq]
            exact inCone_direct ⟨gs, 0⟩ (u - 26) k hk (by rw [hga0, hueq]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ m k hk).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩
        exact gateAt_below_j_or_eq gs i k hiA hkA0 hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m k hmj).1; omega) hmj hmi
      · intro b hb hblen _; exact hp_bad b hb hblen
    · have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0]; exact hu)
      apply pureOr_mapIdx gs patch Bad hkeep hback u (by omega)
      · intro m hm _
        have hu26 : 26 ≤ u := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
        have := hpo_u hu26
        rcases hm with heq | ⟨_, hic⟩
        · have hm_eq : m = u - 26 := by omega
          rw [hm_eq]; exact this.2.1
        · exact this.2.2 m hic
      · intro b hb _ hrel
        have hbk : InCone 26 ⟨gs, 0⟩ b k := by
          rcases hrel with heq | ⟨hu26, hic⟩
          · have hueq : 26 + b = u := by omega
            exact inCone_direct ⟨gs, 0⟩ b k hk (by rw [hga0, hueq]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ b k hk).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩
        rcases hBad_mem b hb with rfl | rfl | rfl
        · exact absurd hbk (hgA_nb.1 k hk hkA0 (fun h => hkBad (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self i)))) hkj)
        · exact absurd hbk (hgB_nb.1 k hk hkA0 (fun h => hkBad (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self i)))) hkj)
        · exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 hbk).2) hkj
  have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
  have hg'j : gs'[j]? = some gs[j] := by
    simp [gs', List.getElem?_mapIdx, hg0j, hkeep j gs[j] (by simp [Bad]; omega)]
  have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
  have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
  have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
  apply core_contra gs' (26 + outG) (by rw [hgs'_len]; exact hsz) hmon' hback' hnn'
  · intro p l hp
    apply mapIdx_eval_up gs patch Bad j hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _) _ (26 + outG) (by omega) hbad_out (hacc p l hp)
    intro hVj
    rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
    have hVwL0 := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
    have hVwR0 := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
    have hVwL' : V gs' (inp {p} {l}) wL = true := by
      cases hVi0 : V gs (inp {p} {l}) (26 + i)
      · exact mapIdx_eval_up gs patch Bad i hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _)
          (fun h => by rw [hVi0] at h; cases h) wL (by omega) hbad_wL hVwL0
      · have hhg0 : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
        have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
        have hbi : ∀ w ∈ gs[i].inputs, w < 26 + i := fun w hw => hback i hil w (by rw [hga0i]; exact hw)
        have hopi : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
        rw [andN_iff gs _ (inp_len _ _) i gs[i] hhg0 hbi hopi] at hVi0
        have hVA := hVi0 (26 + gA) (by rw [← hga0i, hu_inp]; left; rfl)
        have hVB := hVi0 (26 + gB) (by rw [← hga0i, hu_inp]; right; rfl)
        obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback (26 + gA) (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 hVA
        obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback (26 + gB) (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
        obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR0
        obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
        have hcX : c ∈ X := by
          simp only [Finset.mem_union] at hc
          rcases hc with (hc | hc) | hc
          · exact hc
          · have hmem : c ∈ A ∩ R := hc
            rw [hAR_empty] at hmem; cases hmem
          · have hmem : c ∈ B ∩ R := hc
            rw [hBR_empty] at hmem; cases hmem
        have hVi' := (hX_eval (inp {p} {l}) (inp_len _ _)).2 ⟨c, hcX, hpc⟩
        have hr' := reachesOr_map_above gs gs' gs.length i wL (fun k hki hkl => by
          have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hkl
          simp [gs', List.getElem?_mapIdx, hg0k, hkeep k gs[k] (by simp [Bad]; omega)]) hwL_reach
        exact reachesOr_V gs' gs'.length (26 + i) hback' (inp {p} {l}) (inp_len _ _) wL (by rwa [hgs'_len]) hVi'
    rw [andN_iff gs' _ (inp_len _ _) j gs[j] hg'j hbj hopj]
    intro w hw; rw [← hga0j, hwj_inp] at hw
    rcases hw with rfl | rfl; exact hVwL'; rw [hwR_eval _ (inp_len _ _)]; exact hVwR0
  · intro Q hQ
    rw [Bool.eq_false_iff]; intro htr
    have hdn : V gs' (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
      intro hVj'
      rw [andN_iff gs' _ (inp_len _ _) j gs[j] hg'j hbj hopj] at hVj'
      have hVwL' := hVj' wL (by rw [← hga0j, hwj_inp]; left; rfl)
      have hVwR' := hVj' wR (by rw [← hga0j, hwj_inp]; right; rfl)
      rw [hwR_eval _ (inp_len _ _)] at hVwR'
      obtain ⟨r, hr, hqr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp Q (TQ Q)) (inp_len _ _)).1 hVwR'
      rw [qHit_eq_inp_getD] at hqr
      have hVi' : V gs' (inp Q (TQ Q)) (26 + i) = false := by
        rw [Bool.eq_false_iff]; intro hti'
        obtain ⟨x, hxX, hqx⟩ := (hX_eval (inp Q (TQ Q)) (inp_len _ _)).1 hti'
        rw [qHit_eq_inp_getD] at hqx
        exact inc_false_on_quad x r (hok_XR x hxX r hr) Q ⟨hqx, hqr⟩
      have hVwL : V gs (inp Q (TQ Q)) wL = true :=
        mapIdx_eval_down gs patch Bad i hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _)
          (fun h => by rw [hVi'] at h; cases h) wL (by omega) hbad_wL hVwL'
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj]
      intro w hw; rw [← hga0j, hwj_inp] at hw
      rcases hw with rfl | rfl; exact hVwL; exact hVwR'
    have htr0 := mapIdx_eval_down gs patch Bad j hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _) hdn (26 + outG) (by omega) hbad_out htr
    rw [hrej Q hQ] at htr0; cases htr0

set_option maxHeartbeats 800000 in
lemma case2_sub5 (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j uA uB wL wR : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (hu_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ i).inputs ↔ w = uA ∨ w = uB)
    (hwL_reach : reachesOr gs gs.length (26 + i) wL)
    (hwR_lt : wR < 26 + j)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26)))
    (hwj_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR)
    (hY2 : 2 ≤ (orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length wR).card)
    (hXZ_empty : orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length uB = ∅ ∧
                 orSetAvoid gs gs.length uB ∩ orSetAvoid gs gs.length wR = ∅)
    (hnok_AB : ¬ okQuad (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length uB))
    (hnok_AR : ¬ okQuad (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length wR))
    (hnok_BR : ¬ okQuad (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR))
    (h3 : okQuad3 (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR)) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hil : i < gs.length := by omega
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  have hpos : ∀ g ∈ gs, 0 < g.inputs.length := fun g hg => by rw [(htwo g hg).1]; omega
  let A := orSetAvoid gs gs.length uA
  let B := orSetAvoid gs gs.length uB
  let R := orSetAvoid gs gs.length wR
  let S_L := orSetAvoid gs i wL
  let Y := A ∩ R
  have hY2' : 2 ≤ Y.card := hY2
  have hY2'' : 2 ≤ (A ∩ R).card := hY2
  have huA_lt : uA < 26 + i := hback i hil uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_lt : uB < 26 + i := hback i hil uB ((hu_inp uB).2 (Or.inr rfl))
  have hwL_lt : wL < 26 + j := hback j hlt.2 wL ((hwj_inp wL).2 (Or.inl rfl))
  have huA_po : pureOr gs uA := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_po : pureOr gs uB := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uB ((hu_inp uB).2 (Or.inr rfl))
  have hwR_po : pureOr gs wR :=
    pureOr_wR gs hmon hback i j wR hiA hjA hij hAP ((hwj_inp wR).2 (Or.inr rfl)) hwR_no_i
  have hB_ne : B.Nonempty := orSetAvoid_nonempty gs hback hpos uB (by omega) huB_po
  have hR_ne : R.Nonempty := orSetAvoid_nonempty gs hback hpos wR (by omega) hwR_po
  have hok_YB : okQuad Y B := okQuad_of_okQuad3_interL A B R h3
  obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.1 (by omega : 1 < Y.card)
  obtain ⟨b0, hb0⟩ := hB_ne
  have hB_sing : ∀ b ∈ B, b = b0 := fun b hb => unique_common_inc y1 y2 b b0 hy12
    (hok_YB y1 hy1 b hb) (hok_YB y2 hy2 b hb) (hok_YB y1 hy1 b0 hb0) (hok_YB y2 hy2 b0 hb0)
  have hY_le4 : Y.card ≤ 4 := by
    have hsub : Y ⊆ Finset.univ.filter (fun a : Fin 26 => isInc26 a b0 = true) := by
      intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hok_YB y hy b0 hb0
    exact le_trans (Finset.card_le_card hsub) (star_card_le_4 b0)
  have hY_ne : Y.Nonempty := ⟨y1, hy1⟩
  have hok_SL_R : okQuad S_L R := by
    intro s hs r hr
    by_contra hne
    have hfl : isInc26 s r = false := by cases h : isInc26 s r <;> simp_all
    obtain ⟨Q, hQ, hqs, hqr⟩ := pair_in_quad s r hfl
    have hViQ : V gs (inp Q (TQ Q)) (26 + i) = false := by
      rw [Bool.eq_false_iff]; intro htr
      have hhg0 : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
      have hga0 : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
      have hbi : ∀ w ∈ gs[i].inputs, w < 26 + i := fun w hw => hback i hil w (by rw [hga0]; exact hw)
      have hopi : gs[i].op = GateOp.and := by rw [← hga0]; exact hiA
      rw [andN_iff gs _ (inp_len _ _) i gs[i] hhg0 hbi hopi] at htr
      have hVA := htr uA (by rw [← hga0, hu_inp]; left; rfl)
      have hVB := htr uB (by rw [← hga0, hu_inp]; right; rfl)
      obtain ⟨a, ha, hqa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp Q (TQ Q)) (inp_len _ _)).1 hVA
      obtain ⟨b, hb, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVB
      rw [qHit_eq_inp_getD] at hqa hqb
      exact h3 Q hQ ⟨⟨a, ha, hqa⟩, ⟨b, hb, hqb⟩, ⟨r, hr, hqr⟩⟩
    have hVwL : V gs (inp Q (TQ Q)) wL = true :=
      orSetAvoid_sound gs i hback (inp Q (TQ Q)) (inp_len _ _) wL (by omega) ⟨s, hs, by rw [qHit_eq_inp_getD, hqs]⟩
    have hVwR : V gs (inp Q (TQ Q)) wR = true :=
      orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) wR (by omega) ⟨r, hr, by rw [qHit_eq_inp_getD, hqr]⟩
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
    have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hVj := (andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj).2 (fun w hw => by
      rw [← hga0j, hwj_inp] at hw; rcases hw with rfl | rfl; exact hVwL; exact hVwR)
    rw [hjQ Q hQ] at hVj; cases hVj
  by_cases hSL : S_L.Nonempty
  · have hSL_sing : ∀ s ∈ S_L, s = b0 := fun s hs => by
      have hs1 := hok_SL_R s hs y1 (Finset.mem_inter.1 hy1).2
      have hs2 := hok_SL_R s hs y2 (Finset.mem_inter.1 hy2).2
      exact unique_common_inc y1 y2 s b0 hy12 (by rw [isInc26_symm]; exact hs1) (by rw [isInc26_symm]; exact hs2)
        (hok_YB y1 hy1 b0 hb0) (hok_YB y2 hy2 b0 hb0)
    obtain ⟨s0, hs0⟩ := hSL
    have hb0_SL : b0 ∈ S_L := by rw [← hSL_sing s0 hs0]; exact hs0
    apply case2_replace_i_or gs outG hout hsz hmon hback hacc hrej i j wL wR hiA hjA hij hAP hjQ hi_no_bypass
      hwR_lt hwR_no_i hwj_inp hwL_lt ⟨GateOp.or, []⟩ rfl (by simp) (by intro _ h; cases h) (by intro _ h; cases h)
    · intro p l _ hVj
      have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
      have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
      have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
      have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
      have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
      let gs' := gs.mapIdx (fun m g => if m = i then ⟨GateOp.or, []⟩ else g)
      have hgs'_len : gs'.length = gs.length := List.length_mapIdx
      have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
        apply mapIdx_readsBack; intro m g hg u hu; split_ifs at hu with hm
        · simp at hu
        · have hmlen : m < gs.length := (List.getElem?_eq_some_iff.1 hg).1
          have hga : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
          exact hback m hmlen u (by rw [hga]; exact hu)
      cases hVi : V gs (inp {p} {l}) (26 + i)
      · have hkeep : ∀ k g, k ∉ ({i} : Finset ℕ) → (if k = i then (⟨GateOp.or, []⟩ : Gate) else g) = g := by
          intro k g hk; simp only [Finset.mem_singleton] at hk; simp [hk]
        exact mapIdx_eval_up gs _ {i} i hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _)
          (fun h => by rw [hVi] at h; cases h) wL (by omega)
          (fun b hb hbi => by simp only [Finset.mem_singleton] at hb; exact absurd hb hbi) hVwL
      · have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
        have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
        have hbi : ∀ w ∈ gs[i].inputs, w < 26 + i := fun w hw => hback i hil w (by rw [hga0i]; exact hw)
        have hopi : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
        rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hVi
        have hVB := hVi uB (by rw [← hga0i, hu_inp]; right; rfl)
        obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
        rw [hB_sing b hb] at hpb
        have hSL_sub : orSetAvoid gs i wL ⊆ orSetAvoid gs' i wL := by
          rw [orSetAvoid_eq_of_agree gs gs' i (fun k hk hki => by
            have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
            simp [gs', List.getElem?_mapIdx, hg0k, hki]) wL (by omega)]
        exact orSetAvoid_sound gs' i hback' (inp {p} {l}) (inp_len _ _) wL (by rw [hgs'_len]; omega)
          ⟨b0, hSL_sub hb0_SL, hpb⟩
    · intro Q _ _ ⟨v, hv, _⟩; simp at hv
  · have hSL_eq : S_L = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSL
    have huA26 : 26 ≤ uA := by
      by_contra hlt26
      have hcard : A.card = 1 := by simp [A, orSetAvoid_lt gs gs.length uA (by omega)]
      have hle : Y.card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
      omega
    have hwR26 : 26 ≤ wR := by
      by_contra hlt26
      have hcard : R.card = 1 := by simp [R, orSetAvoid_lt gs gs.length wR (by omega)]
      have hle : Y.card ≤ R.card := Finset.card_le_card Finset.inter_subset_right
      omega
    obtain ⟨gA, rfl⟩ : ∃ gA, uA = 26 + gA := ⟨uA - 26, by omega⟩
    obtain ⟨gR, rfl⟩ : ∃ gR, wR = 26 + gR := ⟨wR - 26, by omega⟩
    have hgAR : gA ≠ gR := by
      intro heq; subst heq
      apply hnok_AB
      intro a ha b hb
      have haY : a ∈ Y := Finset.mem_inter.2 ⟨ha, ha⟩
      exact hok_YB a haY b hb
    have hgiR : gR ≠ i := by intro heq; apply hwR_no_i.1; omega
    have hA_ns : ¬ ∃ z : Fin 26, ∀ a ∈ A, isInc26 a z = true := by
      rintro ⟨z, hz⟩
      apply hnok_AB
      intro a ha b hb
      rw [hB_sing b hb]
      have hzeq : z = b0 := unique_common_inc y1 y2 z b0 hy12
        (hz y1 (Finset.mem_inter.1 hy1).1) (hz y2 (Finset.mem_inter.1 hy2).1)
        (hok_YB y1 hy1 b0 hb0) (hok_YB y2 hy2 b0 hb0)
      rw [← hzeq]; exact hz a ha
    have hR_ns : ¬ ∃ z : Fin 26, ∀ r ∈ R, isInc26 r z = true := by
      rintro ⟨z, hz⟩
      apply hnok_BR
      intro b hb r hr
      rw [hB_sing b hb, isInc26_symm]
      have hzeq : z = b0 := unique_common_inc y1 y2 z b0 hy12
        (hz y1 (Finset.mem_inter.1 hy1).2) (hz y2 (Finset.mem_inter.1 hy2).2)
        (hok_YB y1 hy1 b0 hb0) (hok_YB y2 hy2 b0 hb0)
      rw [← hzeq]; exact hz r hr
    have hgA_nb := nonStar_no_bypass gs outG hout hmon hback htwo hreach hrej i j hiA hjA hij hAP hi_no_bypass gA (by omega) huA_po hA_ns
    have hgR_nb := nonStar_no_bypass gs outG hout hmon hback htwo hreach hrej i j hiA hjA hij hAP hi_no_bypass gR (by omega) hwR_po hR_ns
    let s1 := if gR < gA then gR else gA
    let s2 := if gR < gA then gA else if gR < i then gR else i
    let s3 := if gR < i then i else gR
    have hs12 : s1 < s2 := by dsimp only [s1, s2]; split_ifs <;> omega
    have hs23 : s2 < s3 := by dsimp only [s2, s3]; split_ifs <;> omega
    have hs3j : s3 < j := by dsimp only [s3]; split_ifs <;> omega
    let patch : ℕ → Gate → Gate := fun m g =>
      if m = s1 then orGate1 Y
      else if m = s2 then orGate2 Y
      else if m = s3 then ⟨GateOp.or, [26 + s1, 26 + s2]⟩
      else if m = j then ⟨GateOp.and, [b0.1, 26 + s3]⟩
      else g
    let gs' := gs.mapIdx patch
    have hgs'_len : gs'.length = gs.length := List.length_mapIdx
    let Bad : Finset ℕ := {s1, s2, s3, j}
    have hkeep : ∀ k g, k ∉ Bad → patch k g = g := by
      intro k g hk
      simp only [Bad, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      dsimp only [patch]
      rw [ite_eq_right hk.1, ite_eq_right hk.2.1, ite_eq_right hk.2.2.1, ite_eq_right hk.2.2.2]
    have hmon' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      apply mapIdx_mono; intro m g hg; dsimp only [patch]; split_ifs
      · simp [orGate1]
      · simp [orGate2]
      · simp
      · simp
      · exact hmon g (List.mem_of_getElem? hg)
    have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
      apply mapIdx_readsBack; intro m g hg u hu; dsimp only [patch] at hu
      by_cases hm1 : m = s1
      · rw [ite_eq_left hm1] at hu; simp only [orGate1, List.mem_cons, List.not_mem_nil, or_false] at hu
        have h0 := (orElem Y 0).2; have h1 := (orElem Y 1).2
        rcases hu with rfl | rfl <;> omega
      · by_cases hm2 : m = s2
        · rw [ite_eq_right hm1, ite_eq_left hm2] at hu; simp only [orGate2, List.mem_cons, List.not_mem_nil, or_false] at hu
          have h2 := (orElem Y 2).2; have h3 := (orElem Y 3).2
          rcases hu with rfl | rfl <;> omega
        · by_cases hm3 : m = s3
          · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_left hm3] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl <;> omega
          · by_cases hm4 : m = j
            · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_right hm3, ite_eq_left hm4] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              have hb0lt := b0.2
              rcases hu with rfl | rfl <;> omega
            · rw [ite_eq_right hm1, ite_eq_right hm2, ite_eq_right hm3, ite_eq_right hm4] at hu
              have hmlen : m < gs.length := (List.getElem?_eq_some_iff.1 hg).1
              have hga : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
              exact hback m hmlen u (by rw [hga]; exact hu)
    have hg_s1 : gs'[s1]? = some (orGate1 Y) := by
      have hg0 : gs[s1]? = some gs[s1] := List.getElem?_eq_getElem (by omega)
      simp [gs', List.getElem?_mapIdx, hg0, patch]
    have hg_s2 : gs'[s2]? = some (orGate2 Y) := by
      have hg0 : gs[s2]? = some gs[s2] := List.getElem?_eq_getElem (by omega)
      simp [gs', List.getElem?_mapIdx, hg0, patch, show s2 ≠ s1 by omega]
    have hg_s3 : gs'[s3]? = some ⟨GateOp.or, [26 + s1, 26 + s2]⟩ := by
      have hg0 : gs[s3]? = some gs[s3] := List.getElem?_eq_getElem (by omega)
      simp [gs', List.getElem?_mapIdx, hg0, patch, show s3 ≠ s1 by omega, show s3 ≠ s2 by omega]
    obtain ⟨hp_s1, hp_s2, hp_s3, hY_eval⟩ :=
      orChain3_spec gs' s1 s2 s3 Y hs12 hs23 (by rw [hgs'_len]; omega) hY_ne hY_le4 hg_s1 hg_s2 hg_s3
    have hBad_mem : ∀ b ∈ Bad, b = gA ∨ b = gR ∨ b = i ∨ b = j := by
      intro b hb; simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · dsimp only [s1]; split_ifs <;> first | (left; rfl) | (right; left; rfl)
      · dsimp only [s2]; split_ifs <;> first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl)
      · dsimp only [s3]; split_ifs <;> first | (right; left; rfl) | (right; right; left; rfl)
      · right; right; right; rfl
    have hbad_out : reachesBadOnlyVia gs Bad j (26 + outG) := by
      intro b hb hbj hrb
      rcases hBad_mem b hb with hb1 | hb2 | hb3 | hb4
      · rw [hb1] at hrb; exact hgA_nb.2 hrb
      · rw [hb2] at hrb; exact hgR_nb.2 hrb
      · rw [hb3] at hrb; exact hi_no_bypass hrb
      · exact hbj hb4
    have hnn' : ¬ ∃ a b : ℕ, (gateAt ⟨gs', 0⟩ a).op = GateOp.and ∧
        (gateAt ⟨gs', 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs', 0⟩ a b := by
      apply no_nested_and_of_all_and_pureOr gs' 0
      intro k hk hkA u hu
      rw [hgs'_len] at hk
      by_cases hkj : k = j
      · subst hkj
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hg'k : gs'[k]? = some ⟨GateOp.and, [b0.1, 26 + s3]⟩ := by
          simp [gs', List.getElem?_mapIdx, hg0k, patch, show k ≠ s1 by omega, show k ≠ s2 by omega, show k ≠ s3 by omega]
        have hga'k : gateAt ⟨gs', 0⟩ k = ⟨GateOp.and, [b0.1, 26 + s3]⟩ := by
          simp [gateAt, List.getD_eq_getElem?_getD, hg'k]
        rw [hga'k] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · intro h; have := b0.2; omega
        · exact hp_s3
      · have hk_not_123 : k ≠ s1 ∧ k ≠ s2 ∧ k ≠ s3 := by
          refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
          · have h0 : (gateAt ⟨gs', 0⟩ k).op = GateOp.or := by rw [heq]; simp [gateAt, List.getD_eq_getElem?_getD, hg_s1, orGate1]
            rw [h0] at hkA; cases hkA
          · have h0 : (gateAt ⟨gs', 0⟩ k).op = GateOp.or := by rw [heq]; simp [gateAt, List.getD_eq_getElem?_getD, hg_s2, orGate2]
            rw [h0] at hkA; cases hkA
          · have h0 : (gateAt ⟨gs', 0⟩ k).op = GateOp.or := by rw [heq]; simp [gateAt, List.getD_eq_getElem?_getD, hg_s3]
            rw [h0] at hkA; cases hkA
        have hkBad : k ∉ Bad := by
          simp only [Bad, Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hk_not_123.1, hk_not_123.2.1, hk_not_123.2.2, hkj⟩
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hg'k : gs'[k]? = some gs[k] := by simp [gs', List.getElem?_mapIdx, hg0k, hkeep k gs[k] hkBad]
        have hga'k : gateAt ⟨gs', 0⟩ k = gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hg'k]
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
        have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, ← hga'k]; exact hkA
        rw [hga'k] at hu
        have hu_lt : u < 26 + k := hback k hk u (by rw [hga0k]; exact hu)
        have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0k]; exact hu)
        apply pureOr_mapIdx gs patch Bad hkeep hback u (by omega)
        · intro m hm _
          have hu26 : 26 ≤ u := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
          have := hpo_u hu26
          rcases hm with heq | ⟨_, hic⟩
          · have hm_eq : m = u - 26 := by omega
            rw [hm_eq]; exact this.2.1
          · exact this.2.2 m hic
        · intro b hb _ hrel
          have hbk : InCone 26 ⟨gs, 0⟩ b k := by
            rcases hrel with heq | ⟨hu26, hic⟩
            · have hueq : 26 + b = u := by omega
              exact inCone_direct ⟨gs, 0⟩ b k hk (by rw [hga0k, hueq]; exact hu) (by omega)
            · exact (inCone_iff 26 ⟨gs, 0⟩ b k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr hic⟩
          have hki : k ≠ i := fun h => hkBad (by
            rw [h]; dsimp only [Bad, s2, s3]
            simp only [Finset.mem_insert, Finset.mem_singleton]
            by_cases h2 : gR < i
            · right; right; left; simp [h2]
            · right; left; simp [show ¬ gR < gA by omega, h2])
          rcases hBad_mem b hb with hb1 | hb2 | hb3 | hb4
          · rw [hb1] at hbk; exact absurd hbk (hgA_nb.1 k hk hkA0 hki hkj)
          · rw [hb2] at hbk; exact absurd hbk (hgR_nb.1 k hk hkA0 hki hkj)
          · rw [hb3] at hbk; exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 hbk).2) hkj
          · rw [hb4] at hbk; exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA hkA0 hbk).1) (by omega)
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hg'j : gs'[j]? = some ⟨GateOp.and, [b0.1, 26 + s3]⟩ := by
      simp [gs', List.getElem?_mapIdx, hg0j, patch, show j ≠ s1 by omega, show j ≠ s2 by omega, show j ≠ s3 by omega]
    have hbj' : ∀ w ∈ ([b0.1, 26 + s3] : List ℕ), w < 26 + j := fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hb0lt := b0.2
      rcases hw with rfl | rfl <;> omega
    apply core_contra gs' (26 + outG) (by rw [hgs'_len]; exact hsz) hmon' hback' hnn'
    · intro p l hp
      apply mapIdx_eval_up gs patch Bad j hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _) _ (26 + outG) (by omega) hbad_out (hacc p l hp)
      intro hVj
      have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
      have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
      have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
      have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
      have hVwR := hVj (26 + gR) (by rw [← hga0j, hwj_inp]; right; rfl)
      have hVi : V gs (inp {p} {l}) (26 + i) = true := by
        by_contra hfl
        have hfl' : V gs (inp {p} {l}) (26 + i) = false := by cases h : V gs (inp {p} {l}) (26 + i) <;> simp_all
        have hor_L : ∀ m : ℕ, 26 ≤ wL → (m = wL - 26 ∨ InCone 26 ⟨gs, 0⟩ m (wL - 26)) → m ≠ i → (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
          intro m hwL26 hrel hmi
          have hmj : InCone 26 ⟨gs, 0⟩ m j := by
            rcases hrel with rfl | hic
            · have hwl26 : 26 + (wL - 26) = wL := by omega
              exact inCone_direct ⟨gs, 0⟩ (wL - 26) j hlt.2 (by rw [hwl26]; exact (hwj_inp wL).2 (Or.inl rfl)) (by omega)
            · exact (inCone_iff 26 ⟨gs, 0⟩ m j hlt.2).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hwL26, hwL_lt, Or.inr hic⟩
          exact gateAt_below_j_or_eq gs i j hiA hjA hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m j hmj).1; omega) hmj hmi
        obtain ⟨a, ha, _⟩ := orSetAvoid_complete gs i hback (inp {p} {l}) (inp_len _ _) hfl' wL (by omega)
          (fun hwL26 heq => by rw [heq, hfl'] at hVwL; cases hVwL) hor_L hVwL
        rw [show orSetAvoid gs i wL = S_L from rfl, hSL_eq] at ha; cases ha
      have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
      have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
      have hbi : ∀ w ∈ gs[i].inputs, w < 26 + i := fun w hw => hback i hil w (by rw [hga0i]; exact hw)
      have hopi : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
      rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hVi
      have hVA := hVi (26 + gA) (by rw [← hga0i, hu_inp]; left; rfl)
      have hVB := hVi uB (by rw [← hga0i, hu_inp]; right; rfl)
      obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback (26 + gA) (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 hVA
      obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
      obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback (26 + gR) (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
      obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
      have hcY : c ∈ Y := by
        simp only [Finset.mem_union] at hc
        rcases hc with (hc | hc) | hc
        · have hmem : c ∈ A ∩ B := hc; rw [hXZ_empty.1] at hmem; cases hmem
        · exact hc
        · have hmem : c ∈ B ∩ R := hc; rw [hXZ_empty.2] at hmem; cases hmem
      rw [hB_sing b hb] at hpb
      rw [andN_iff gs' _ (inp_len _ _) j _ hg'j hbj' rfl]
      intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact b0.2)]; exact hpb
      · exact (hY_eval (inp {p} {l}) (inp_len _ _)).2 ⟨c, hcY, hpc⟩
    · intro Q hQ
      rw [Bool.eq_false_iff]; intro htr
      have hdn : V gs' (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
        intro hVj'
        rw [andN_iff gs' _ (inp_len _ _) j _ hg'j hbj' rfl] at hVj'
        have hVb0 := hVj' b0.1 (by simp)
        have hVs3 := hVj' (26 + s3) (by simp)
        have hqb0 : qHit Q b0 = true := by
          unfold V at hVb0; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact b0.2), qHit_eq_inp_getD] at hVb0; exact hVb0
        obtain ⟨y, hyY, hqy⟩ := (hY_eval (inp Q (TQ Q)) (inp_len _ _)).1 hVs3
        rw [qHit_eq_inp_getD] at hqy
        exact absurd ⟨hqy, hqb0⟩ (inc_false_on_quad y b0 (hok_YB y hyY b0 hb0) Q)
      have htr0 := mapIdx_eval_down gs patch Bad j hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _) hdn (26 + outG) (by omega) hbad_out htr
      rw [hrej Q hQ] at htr0; cases htr0

end L1961


namespace L1961

lemma inCone_of_eq_above (gs gs1 : List Gate) (dst b : ℕ)
    (hlen : gs1.length = gs.length)
    (hgt : ∀ m, dst < m → m < gs.length → gs1[m]? = gs[m]?)
    (hdb : dst < b) (hb : b < gs.length) (hinc : InCone 26 ⟨gs1, 0⟩ dst b) :
    InCone 26 ⟨gs, 0⟩ dst b := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    rw [inCone_iff 26 ⟨gs1, 0⟩ dst b (by dsimp; rw [hlen]; exact hb)] at hinc
    obtain ⟨u, hu, hu26, hult, hrel⟩ := hinc
    have hg0 : gs[b]? = some gs[b] := List.getElem?_eq_getElem hb
    have hg1 : gs1[b]? = some gs[b] := by rw [hgt b hdb hb, hg0]
    have hga1 : gateAt ⟨gs1, 0⟩ b = gs[b] := by simp [gateAt, List.getD_eq_getElem?_getD, hg1]
    have hga0 : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hb
    rw [hga1] at hu
    rcases hrel with rfl | hic
    · have hueq : 26 + (u - 26) = u := by omega
      exact inCone_direct ⟨gs, 0⟩ (u - 26) b hb (by rw [hga0, hueq]; exact hu) (by omega)
    · have hlt_du := (inCone_lt ⟨gs1, 0⟩ dst (u - 26) hic).1
      have hic0 := ih (u - 26) (by omega) (by omega) (by omega) hic
      exact (inCone_iff 26 ⟨gs, 0⟩ dst b hb).2 ⟨u, by rw [hga0]; exact hu, hu26, hult, Or.inr hic0⟩

lemma pureOr_of_agree_cone (gs gs1 : List Gate) (hback : ReadsBack 26 ⟨gs, 0⟩)
    (hlen : gs1.length = gs.length)
    (w : ℕ) (hw : w < 26 + gs.length) (hpo : pureOr gs w)
    (hag : ∀ c, (w = 26 + c ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ c (w - 26))) → gs1[c]? = gs[c]?) :
    pureOr gs1 w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw26
    obtain ⟨c, rfl⟩ : ∃ c, w = 26 + c := ⟨w - 26, by omega⟩
    have hclen : c < gs.length := by omega
    have hg0 : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
    have hg1 : gs1[c]? = some gs[c] := by rw [hag c (Or.inl rfl), hg0]
    have hga1 : gateAt ⟨gs1, 0⟩ c = gs[c] := by simp [gateAt, List.getD_eq_getElem?_getD, hg1]
    have hga0 : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
    have hpo' := hpo hw26
    rw [Nat.add_sub_cancel_left] at hpo'
    have hop1 : (gateAt ⟨gs1, 0⟩ c).op = GateOp.or := by rw [hga1, ← hga0]; exact hpo'.2.1
    apply pureOr_step gs1 c (by rw [hlen]; exact hclen) hop1 _ hw26
    intro u hu
    rw [hga1] at hu
    have hu_lt : u < 26 + c := hback c hclen u (by rw [hga0]; exact hu)
    apply ih u hu_lt (by omega)
    · intro hu26
      have hu_eq : 26 + (u - 26) = u := by omega
      have huc := inCone_direct ⟨gs, 0⟩ (u - 26) c hclen (by rw [hga0, hu_eq]; exact hu) (by omega)
      exact ⟨by omega, hpo'.2.2 (u - 26) huc, fun a ha => hpo'.2.2 a (inCone_trans ⟨gs, 0⟩ a (u - 26) c ha huc)⟩
    · intro d hd
      apply hag d
      right
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      rcases hd with rfl | ⟨hu26, hic⟩
      · exact inCone_direct ⟨gs, 0⟩ d c hclen (by rw [hga0]; exact hu) (by omega)
      · exact (inCone_iff 26 ⟨gs, 0⟩ d c hclen).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩

lemma reachesAvoiding_trans (gs : List Gate) (skip t : ℕ) :
    ∀ m w : ℕ, reachesAvoiding gs skip t m → reachesAvoiding gs skip m w → reachesAvoiding gs skip t w := by
  intro m w hr1 hr2
  induction hr2 with
  | base => exact hr1
  | @step k g u hg hk hu hlt _ ih => exact reachesAvoiding.step hg hk hu hlt ih

lemma reachesAvoiding_below_skip (gs : List Gate) (skip a b : ℕ)
    (hbs : b < skip) (hic : InCone 26 ⟨gs, 0⟩ a b) :
    reachesAvoiding gs skip (26 + a) (26 + b) := by
  induction b using Nat.strong_induction_on generalizing a with
  | ind b ih =>
    have hblen : b < gs.length := (inCone_lt ⟨gs, 0⟩ a b hic).2
    rw [inCone_iff 26 ⟨gs, 0⟩ a b hblen] at hic
    obtain ⟨u, hu, hu26, hult, hrel⟩ := hic
    have hg0 : gs[b]? = some gs[b] := List.getElem?_eq_getElem hblen
    have hga0 : gateAt ⟨gs, 0⟩ b = gs[b] := gateAt_eq ⟨gs, 0⟩ b hblen
    rcases hrel with rfl | hic_u
    · have hueq : 26 + (u - 26) = u := by omega
      exact reachesAvoiding.step hg0 (by omega) (by rw [← hga0, hueq]; exact hu) (by omega) reachesAvoiding.base
    · have hu_lt_b := (inCone_lt ⟨gs, 0⟩ a (u - 26) hic_u).1
      have hueq : 26 + (u - 26) = u := by omega
      exact reachesAvoiding.step hg0 (by omega) (by rw [← hga0]; exact hu) (by omega)
        (by rw [← hueq]; exact ih (u - 26) (by omega) a (by omega) hic_u)

lemma V_eq_of_agree_cone (gs0 gs1 : List Gate) (hback : ReadsBack 26 ⟨gs0, 0⟩)
    (_hlen : gs1.length = gs0.length) (x : List Bool) (hx : x.length = 26) :
    ∀ w : ℕ, w < 26 + gs0.length →
      (∀ c, (w = 26 + c ∨ (26 ≤ w ∧ InCone 26 ⟨gs0, 0⟩ c (w - 26))) → gs1[c]? = gs0[c]?) →
      V gs1 x w = V gs0 x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hag
    by_cases hw26 : w < 26
    · exact V_in gs1 gs0 x w (by rw [hx]; exact hw26)
    · obtain ⟨c, rfl⟩ : ∃ c, w = 26 + c := ⟨w - 26, by omega⟩
      have hc : c < gs0.length := by omega
      have hg0 : gs0[c]? = some gs0[c] := List.getElem?_eq_getElem hc
      have hg1 : gs1[c]? = some gs0[c] := by rw [hag c (Or.inl rfl), hg0]
      have hga0 : gateAt ⟨gs0, 0⟩ c = gs0[c] := gateAt_eq ⟨gs0, 0⟩ c hc
      have hbc : ∀ u ∈ gs0[c].inputs, u < 26 + c := fun u hu => hback c hc u (by rw [hga0]; exact hu)
      rw [gate_val_aux gs1 x hx c gs0[c] hg1 hbc, gate_val_aux gs0 x hx c gs0[c] hg0 hbc]
      congr 1
      apply List.map_inj_left.2
      intro u hu
      have hu_lt := hbc u hu
      apply ih u hu_lt (by omega)
      intro d hd
      apply hag d
      right
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      rcases hd with rfl | ⟨hu26, hic⟩
      · exact inCone_direct ⟨gs0, 0⟩ d c hc (by rw [hga0]; exact hu) (by omega)
      · exact (inCone_iff 26 ⟨gs0, 0⟩ d c hc).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩

set_option maxHeartbeats 800000 in
lemma case2_sub4 (gs : List Gate) (outG : ℕ) (_hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j uA uB wL wR : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (hu_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ i).inputs ↔ w = uA ∨ w = uB)
    (hwL_reach : reachesOr gs gs.length (26 + i) wL)
    (hwR_lt : wR < 26 + j)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26)))
    (hwj_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR)
    (y0 : Fin 26)
    (hY_sing : ∀ c ∈ orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length wR, c = y0)
    (hy0Y : y0 ∈ orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length wR)
    (hXZ_empty : orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length uB = ∅ ∧
                 orSetAvoid gs gs.length uB ∩ orSetAvoid gs gs.length wR = ∅)
    (h3 : okQuad3 (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR)) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hil : i < gs.length := by omega
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  let A := orSetAvoid gs gs.length uA
  let B := orSetAvoid gs gs.length uB
  let R := orSetAvoid gs gs.length wR
  let S_L := orSetAvoid gs i wL
  have hy0A : y0 ∈ A := (Finset.mem_inter.1 hy0Y).1
  have hy0R : y0 ∈ R := (Finset.mem_inter.1 hy0Y).2
  have huA_lt : uA < 26 + i := hback i hil uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_lt : uB < 26 + i := hback i hil uB ((hu_inp uB).2 (Or.inr rfl))
  have hwL_lt : wL < 26 + j := hback j hlt.2 wL ((hwj_inp wL).2 (Or.inl rfl))
  have huA_po : pureOr gs uA := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_po : pureOr gs uB := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uB ((hu_inp uB).2 (Or.inr rfl))
  have hwR_po : pureOr gs wR :=
    pureOr_wR gs hmon hback i j wR hiA hjA hij hAP ((hwj_inp wR).2 (Or.inr rfl)) hwR_no_i
  by_cases hSL : S_L.Nonempty
  · have hwL_ne_i : wL ≠ 26 + i := by
      intro heq; dsimp only [S_L] at hSL; rw [heq, orSetAvoid_self] at hSL; exact absurd hSL Finset.not_nonempty_empty
    obtain ⟨m, gm, hgm, _, hmop, hmin, hm_reach⟩ := reachesOr_first_step gs gs.length (26 + i) wL hwL_reach hwL_ne_i
    have hmlen : m < gs.length := (List.getElem?_eq_some_iff.1 hgm).1
    have hga_m : gateAt ⟨gs, 0⟩ m = gm := by simp [gateAt, List.getD_eq_getElem?_getD, hgm]
    have him : i < m := by have := hback m hmlen (26 + i) (by rw [hga_m]; exact hmin); omega
    have hmj : m < j := by
      have hm_le := reachesOr_gt_inputs gs gs.length (26 + m) wL (by omega) hm_reach
      omega
    have hgm_eq : gm = gs[m] := by
      have hg0m : gs[m]? = some gs[m] := List.getElem?_eq_getElem hmlen
      rw [hg0m] at hgm; exact (Option.some.inj hgm).symm
    obtain ⟨a0, a1, ha01, ha_eq⟩ := two_inputs_distinct (htwo gs[m] (List.getElem_mem hmlen))
    rw [hgm_eq, ha_eq] at hmin
    have hmem : a0 = 26 + i ∨ a1 = 26 + i := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmin
      simpa only [eq_comm] using hmin
    let v := if a0 = 26 + i then a1 else a0
    have hv_ne : v ≠ 26 + i := by dsimp only [v]; split_ifs <;> omega
    have hmin_eq : ∀ w, w ∈ gs[m].inputs ↔ w = 26 + i ∨ w = v := by
      intro w; rw [ha_eq]; dsimp only [v]; rcases hmem with rfl | rfl
      · simp [eq_comm]
      · simp [ha01, or_comm]
    have hv_lt : v < 26 + m := hback m hmlen v (by rw [hga_m, hgm_eq]; exact (hmin_eq v).2 (Or.inr rfl))
    let wL' := if wL = 26 + m then v else wL
    have hwL'_ne_m : wL' ≠ 26 + m := by dsimp only [wL']; split_ifs; omega; assumption
    have hwL'_lt : wL' < 26 + j := by dsimp only [wL']; split_ifs <;> omega
    let patch1 : ℕ → Gate → Gate := fun k g =>
      if k < i then g
      else if k = i then ⟨GateOp.and, [y0.1, uB]⟩
      else if k = m then ⟨GateOp.or, []⟩
      else if k < j then
        match g.op with
        | GateOp.and => g
        | _ => ⟨GateOp.or, (g.inputs.map (fun w => if w = 26 + m then v else w)).filter (· ≠ 26 + i)⟩
      else if k = j then ⟨GateOp.and, [wL', wR]⟩
      else g
    let gs1 := gs.mapIdx patch1
    have hgs1_len : gs1.length = gs.length := List.length_mapIdx
    have hmon1 : ∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      apply mapIdx_mono; intro k g hg
      have hk := hmon g (List.mem_of_getElem? hg)
      dsimp only [patch1]
      by_cases h1 : k < i; · rw [ite_eq_left h1]; exact hk
      · by_cases h2 : k = i; · rw [ite_eq_right h1, ite_eq_left h2]; simp
        · by_cases h3 : k = m; · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]; simp
          · by_cases h4 : k < j
            · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
              cases hop : g.op with
              | and => exact hk
              | or => exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) (by simp [hk.2])⟩
              | _ => rcases hk.1 with h | h <;> rw [h] at hop <;> cases hop
            · by_cases h5 : k = j
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left h5]; simp
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5]; exact hk
    have hback1 : ReadsBack 26 ⟨gs1, 0⟩ := by
      apply mapIdx_readsBack; intro k g hg u hu
      have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      have hga0 : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
      have hbk : ∀ w ∈ g.inputs, w < 26 + k := fun w hw => hback k hklen w (by rw [hga0]; exact hw)
      dsimp only [patch1] at hu
      by_cases h1 : k < i; · rw [ite_eq_left h1] at hu; exact hbk u hu
      · by_cases h2 : k = i
        · rw [ite_eq_right h1, ite_eq_left h2] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          have hy0lt := y0.2; rcases hu with rfl | rfl <;> omega
        · by_cases h3 : k = m; · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] at hu; simp at hu
          · by_cases h4 : k < j
            · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4] at hu
              cases hop : g.op with
              | and => simp only [hop] at hu; exact hbk u hu
              | or =>
                simp only [hop] at hu
                obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hu)
                have := hbk w hw; split_ifs <;> omega
              | _ =>
                have hgm' := (hmon g (List.mem_of_getElem? hg)).1
                rcases hgm' with h | h <;> rw [h] at hop <;> cases hop
            · by_cases h5 : k = j
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_left h5] at hu
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl <;> omega
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5] at hu
                exact hbk u hu
    have hno_in_and : ∀ k, k < gs.length → k ≠ j → (gateAt ⟨gs, 0⟩ k).op = GateOp.and →
        26 + i ∉ (gateAt ⟨gs, 0⟩ k).inputs ∧ 26 + m ∉ (gateAt ⟨gs, 0⟩ k).inputs := by
      intro k hklen hkj hkA
      refine ⟨fun hmem => ?_, fun hmem => ?_⟩
      · have hik : i < k := by have := hback k hklen (26 + i) hmem; omega
        exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA (inCone_direct ⟨gs, 0⟩ i k hklen hmem hik)).2) hkj
      · have hmk : m < k := by have := hback k hklen (26 + m) hmem; omega
        have him_inc : InCone 26 ⟨gs, 0⟩ i m := inCone_direct ⟨gs, 0⟩ i m hmlen (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him
        have hik_inc : InCone 26 ⟨gs, 0⟩ i k := inCone_trans ⟨gs, 0⟩ i m k him_inc (inCone_direct ⟨gs, 0⟩ m k hklen hmem hmk)
        exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA hik_inc).2) hkj
    have hgt_j_noread : ∀ k, j < k → k < gs.length →
        26 + i ∉ (gateAt ⟨gs, 0⟩ k).inputs ∧ 26 + m ∉ (gateAt ⟨gs, 0⟩ k).inputs := by
      intro k hjk hklen
      have hreach_k : reachesAvoiding gs j (26 + k) (26 + outG) := by
        by_cases hko : k = outG
        · subst hko; exact reachesAvoiding.base
        · exact inCone_gt_reachesAvoiding gs j k outG hjk ((hreach k hklen).resolve_left hko)
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
      have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
      refine ⟨fun hmem => ?_, fun hmem => ?_⟩
      · have hik : 26 + i < 26 + k := by have := hback k hklen (26 + i) hmem; omega
        exact hi_no_bypass (reachesAvoiding_trans gs j (26 + i) (26 + k) (26 + outG)
          (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hmem) hik reachesAvoiding.base) hreach_k)
      · have hmk : 26 + m < 26 + k := by have := hback k hklen (26 + m) hmem; omega
        have hm_reach_out : reachesAvoiding gs j (26 + m) (26 + outG) :=
          reachesAvoiding_trans gs j (26 + m) (26 + k) (26 + outG)
            (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hmem) hmk reachesAvoiding.base) hreach_k
        have hg0m : gs[m]? = some gs[m] := List.getElem?_eq_getElem hmlen
        exact hi_no_bypass (reachesAvoiding_trans gs j (26 + i) (26 + m) (26 + outG)
          (reachesAvoiding.step hg0m (by omega) ((hmin_eq (26 + i)).2 (Or.inl rfl)) (by omega) reachesAvoiding.base) hm_reach_out)
    have hgs1_nom : ∀ k, m < k → k < gs1.length → 26 + m ∉ (gateAt ⟨gs1, 0⟩ k).inputs := by
      intro k hmk hklen hmem
      rw [hgs1_len] at hklen
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
      have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
      rw [hga1k] at hmem
      dsimp only [patch1] at hmem
      have h1 : ¬ k < i := by omega
      have h2 : ¬ k = i := by omega
      have h3 : ¬ k = m := by omega
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hmem
      by_cases h4 : k < j
      · rw [ite_eq_left h4] at hmem
        cases hop : gs[k].op with
        | and =>
          simp only [hop] at hmem
          have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [gateAt_eq ⟨gs, 0⟩ k hklen, hop]
          exact (hno_in_and k hklen (by omega) hkA).2 (by rw [gateAt_eq ⟨gs, 0⟩ k hklen]; exact hmem)
        | or =>
          simp only [hop] at hmem
          obtain ⟨w, _, heq⟩ := List.mem_map.1 (List.mem_of_mem_filter hmem)
          split_ifs at heq <;> omega
        | _ =>
          have hgm' := (hmon gs[k] (List.getElem_mem hklen)).1
          rcases hgm' with h | h <;> rw [h] at hop <;> cases hop
      · by_cases h5 : k = j
        · rw [ite_eq_right h4, ite_eq_left h5] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with heq | heq
          · exact hwL'_ne_m heq.symm
          · rw [← heq] at hwR_no_i
            apply hwR_no_i.2 (by omega)
            rw [Nat.add_sub_cancel_left]
            exact inCone_direct ⟨gs, 0⟩ i m hmlen (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him
        · rw [ite_eq_right h4, ite_eq_right h5] at hmem
          exact (hgt_j_noread k (by omega) hklen).2 (by rw [gateAt_eq ⟨gs, 0⟩ k hklen]; exact hmem)
    have hgs1_noi : ∀ k, i < k → k < j → 26 + i ∉ (gateAt ⟨gs1, 0⟩ k).inputs := by
      intro k hik hkj hmem
      have hklen : k < gs.length := hkj.trans hlt.2
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
      have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
      rw [hga1k] at hmem
      dsimp only [patch1] at hmem
      have h1 : ¬ k < i := by omega
      have h2 : ¬ k = i := by omega
      rw [ite_eq_right h1, ite_eq_right h2] at hmem
      by_cases h3 : k = m
      · rw [ite_eq_left h3] at hmem; simp at hmem
      · rw [ite_eq_right h3, ite_eq_left hkj] at hmem
        cases hop : gs[k].op with
        | and =>
          simp only [hop] at hmem
          have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [gateAt_eq ⟨gs, 0⟩ k hklen, hop]
          exact (hno_in_and k hklen (by omega) hkA).1 (by rw [gateAt_eq ⟨gs, 0⟩ k hklen]; exact hmem)
        | or =>
          simp only [hop] at hmem
          have hf := (List.mem_filter.1 hmem).2; simp at hf
        | _ =>
          have hgm' := (hmon gs[k] (List.getElem_mem hklen)).1
          rcases hgm' with h | h <;> rw [h] at hop <;> cases hop
    have hpo_below_j : ∀ w : ℕ, w < 26 + j → w ≠ 26 + i →
        (∀ a < j, (gateAt ⟨gs, 0⟩ a).op = GateOp.and → a ≠ i → w ≠ 26 + a ∧ (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ a (w - 26))) →
        pureOr gs1 w := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt hwi hno hw26
        obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hklen : k < gs.length := by omega
        have hki : k ≠ i := by omega
        have hnotA : (gateAt ⟨gs, 0⟩ k).op ≠ GateOp.and := by
          intro hka; exact (hno k (by omega) hka hki).1 rfl
        have hkop0 : gs[k].op = GateOp.or := by
          have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
          rcases (hmon gs[k] (List.getElem_mem hklen)).1 with h | h
          · rw [hga0, h] at hnotA; exact absurd rfl hnotA
          · exact h
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by
          simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
        by_cases hkm : k = m
        · subst hkm
          have hpk : patch1 k gs[k] = ⟨GateOp.or, []⟩ := by
            dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_right hki, ite_eq_left rfl]
          apply pureOr_step gs1 k (by rw [hgs1_len]; exact hklen) (by rw [hga1k, hpk]) _ hw26
          intro u hu; rw [hga1k, hpk] at hu; simp at hu
        · have hpk_op : (patch1 k gs[k]).op = GateOp.or := by
            dsimp only [patch1]
            by_cases h1 : k < i; · rw [ite_eq_left h1]; exact hkop0
            · rw [ite_eq_right h1, ite_eq_right hki, ite_eq_right hkm, ite_eq_left (by omega : k < j)]; simp [hkop0]
          apply pureOr_step gs1 k (by rw [hgs1_len]; exact hklen) (by rw [hga1k]; exact hpk_op) _ hw26
          intro u hu
          have hu_lt1 : u < 26 + k := hback1 k (by rw [hgs1_len]; exact hklen) u hu
          have hu_ni : u ≠ 26 + i := by
            by_cases h1 : k < i; · omega
            · intro heq; rw [heq] at hu; exact hgs1_noi k (by omega) (by omega) hu
          have hno_u : ∀ a < j, (gateAt ⟨gs, 0⟩ a).op = GateOp.and → a ≠ i →
              u ≠ 26 + a ∧ (26 ≤ u → ¬ InCone 26 ⟨gs, 0⟩ a (u - 26)) := by
            intro a ha haA hai
            rw [hga1k] at hu; dsimp only [patch1] at hu
            by_cases h1 : k < i
            · rw [ite_eq_left h1] at hu
              have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
              have hu_lt0 : u < 26 + k := hback k hklen u (by rw [hga0]; exact hu)
              refine ⟨fun heq => (hno a ha haA hai).2 (by omega) (by
                rw [Nat.add_sub_cancel_left]; exact inCone_direct ⟨gs, 0⟩ a k hklen (by rw [hga0, ← heq]; exact hu) (by omega)),
                fun hu26 hic => (hno a ha haA hai).2 (by omega) (by
                  rw [Nat.add_sub_cancel_left]; exact (inCone_iff 26 ⟨gs, 0⟩ a k hklen).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt0, Or.inr hic⟩)⟩
            · rw [ite_eq_right h1, ite_eq_right hki, ite_eq_right hkm, ite_eq_left (by omega : k < j), hkop0] at hu
              obtain ⟨w, hw, heqw⟩ := List.mem_map.1 (List.mem_of_mem_filter hu)
              have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
              have hw_lt : w < 26 + k := hback k hklen w (by rw [hga0]; exact hw)
              by_cases hwm : w = 26 + m
              · rw [ite_eq_left hwm] at heqw
                rw [← heqw]
                have hga0m : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hmlen
                have hm_inc : InCone 26 ⟨gs, 0⟩ m k := inCone_direct ⟨gs, 0⟩ m k hklen (by rw [hga0, ← hwm]; exact hw) (by omega)
                refine ⟨fun heq => (hno a ha haA hai).2 (by omega) (by
                  rw [Nat.add_sub_cancel_left]
                  have := inCone_direct ⟨gs, 0⟩ a m hmlen (by rw [hga0m, ← heq]; exact (hmin_eq v).2 (Or.inr rfl)) (by omega)
                  exact inCone_trans ⟨gs, 0⟩ a m k this hm_inc),
                  fun hu26 hic => (hno a ha haA hai).2 (by omega) (by
                    rw [Nat.add_sub_cancel_left]
                    have := (inCone_iff 26 ⟨gs, 0⟩ a m hmlen).2 ⟨v, by rw [hga0m]; exact (hmin_eq v).2 (Or.inr rfl), hu26, hv_lt, Or.inr hic⟩
                    exact inCone_trans ⟨gs, 0⟩ a m k this hm_inc)⟩
              · rw [ite_eq_right hwm] at heqw
                rw [← heqw]
                refine ⟨fun heq => (hno a ha haA hai).2 (by omega) (by
                  rw [Nat.add_sub_cancel_left]; exact inCone_direct ⟨gs, 0⟩ a k hklen (by rw [hga0, ← heq]; exact hw) (by omega)),
                  fun hu26 hic => (hno a ha haA hai).2 (by omega) (by
                    rw [Nat.add_sub_cancel_left]; exact (inCone_iff 26 ⟨gs, 0⟩ a k hklen).2 ⟨w, by rw [hga0]; exact hw, hu26, hw_lt, Or.inr hic⟩)⟩
          exact ih u hu_lt1 (by omega) hu_ni hno_u
    let gNew : Gate := ⟨GateOp.or, [26 + (j - 1), 26 + i]⟩
    let gs2 := gatesMoveAfter gs1 m j gNew
    have hgs2_len : gs2.length = gs.length := by
      rw [gatesMoveAfter_len gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2), hgs1_len]
    have hmon2 : ∀ g ∈ gs2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      gatesMoveAfter_mono gs1 m j gNew hmon1 (by simp [gNew])
    have hback2 : ReadsBack 26 ⟨gs2, 0⟩ :=
      gatesMoveAfter_readsBack gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) hback1 (by
        intro u hu; simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega)
    have hnn1 : ¬ ∃ a b : ℕ, (gateAt ⟨gs1, 0⟩ a).op = GateOp.and ∧
        (gateAt ⟨gs1, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs1, 0⟩ a b := by
      apply no_nested_and_of_all_and_pureOr gs1 0
      intro k hk hkA u hu
      rw [hgs1_len] at hk
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
      have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      by_cases hki : k = i
      · subst hki
        have hpk : patch1 k gs[k] = ⟨GateOp.and, [y0.1, uB]⟩ := by
          dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_left rfl]
        rw [hga1k, hpk] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hu1 | hu2
        · rw [hu1]; intro h; have := y0.2; omega
        · rw [hu2]; exact hpo_below_j uB (by omega) (by omega) (fun a _ haA _ => by
            refine ⟨(fun heq => by have := huB_po (by omega); rw [heq, Nat.add_sub_cancel_left] at this; rw [this.2.1] at haA; cases haA),
              (fun hu26 hic => by have := huB_po hu26; rw [this.2.2 a hic] at haA; cases haA)⟩)
      · by_cases hkj : k = j
        · subst hkj
          have hpk : patch1 k gs[k] = ⟨GateOp.and, [wL', wR]⟩ := by
            dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_right hki, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
          rw [hga1k, hpk] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with hu1 | hu2
          · rw [hu1]; have hwL'_ni : wL' ≠ 26 + i := by dsimp only [wL']; split_ifs; exact hv_ne; exact hwL_ne_i
            exact hpo_below_j wL' hwL'_lt hwL'_ni (fun a ha haA hai => by
              refine ⟨(fun heq => ?_), (fun hu26 hic => ?_)⟩
              · have haj : InCone 26 ⟨gs, 0⟩ a k := by
                  dsimp only [wL'] at heq; split_ifs at heq
                  · have := inCone_direct ⟨gs, 0⟩ a m hmlen (by rw [hga_m, hgm_eq, ← heq]; exact (hmin_eq v).2 (Or.inr rfl)) (by omega)
                    exact inCone_trans ⟨gs, 0⟩ a m k this (by
                      rcases reachesOr_inCone gs gs.length (26 + m) wL (by omega) hm_reach with heqm | ⟨hwL26, hicm⟩
                      · exact inCone_direct ⟨gs, 0⟩ m k hk (by rw [← heqm]; exact (hwj_inp wL).2 (Or.inl rfl)) hmj
                      · rw [Nat.add_sub_cancel_left] at hicm
                        exact (inCone_iff 26 ⟨gs, 0⟩ m k hk).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hwL26, hwL_lt, Or.inr hicm⟩)
                  · exact inCone_direct ⟨gs, 0⟩ a k hk (by rw [← heq]; exact (hwj_inp wL).2 (Or.inl rfl)) (by omega)
                exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij haA hjA haj).1) hai
              · have haj : InCone 26 ⟨gs, 0⟩ a k := by
                  dsimp only [wL'] at hu26 hic; split_ifs at hu26 hic
                  · have := (inCone_iff 26 ⟨gs, 0⟩ a m hmlen).2 ⟨v, by rw [hga_m, hgm_eq]; exact (hmin_eq v).2 (Or.inr rfl), hu26, hv_lt, Or.inr hic⟩
                    exact inCone_trans ⟨gs, 0⟩ a m k this (by
                      rcases reachesOr_inCone gs gs.length (26 + m) wL (by omega) hm_reach with heqm | ⟨hwL26, hicm⟩
                      · exact inCone_direct ⟨gs, 0⟩ m k hk (by rw [← heqm]; exact (hwj_inp wL).2 (Or.inl rfl)) hmj
                      · rw [Nat.add_sub_cancel_left] at hicm
                        exact (inCone_iff 26 ⟨gs, 0⟩ m k hk).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hwL26, hwL_lt, Or.inr hicm⟩)
                  · exact (inCone_iff 26 ⟨gs, 0⟩ a k hk).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hu26, hwL_lt, Or.inr hic⟩
                exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij haA hjA haj).1) hai)
          · rw [hu2]; exact hpo_below_j wR hwR_lt hwR_no_i.1 (fun a _ haA _ => by
              refine ⟨(fun heq => by have := hwR_po (by omega); rw [heq, Nat.add_sub_cancel_left] at this; rw [this.2.1] at haA; cases haA),
                (fun hu26 hic => by have := hwR_po hu26; rw [this.2.2 a hic] at haA; cases haA)⟩)
        · have hkm_ne : k ≠ m := by
            intro heq; subst heq
            have hpk : patch1 k gs[k] = ⟨GateOp.or, []⟩ := by
              dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_right hki, ite_eq_left rfl]
            rw [hga1k, hpk] at hkA; cases hkA
          have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by
            rw [hga1k] at hkA; dsimp only [patch1] at hkA
            by_cases h1 : k < i; · rw [ite_eq_left h1] at hkA; rw [hga0k]; exact hkA
            · by_cases h4 : k < j
              · rw [ite_eq_right h1, ite_eq_right hki, ite_eq_right hkm_ne, ite_eq_left h4] at hkA
                cases hop : gs[k].op with
                | and => rw [hga0k]; exact hop
                | or => simp [hop] at hkA
                | _ => rcases (hmon gs[k] (List.getElem_mem hk)).1 with h | h <;> rw [h] at hop <;> cases hop
              · rw [ite_eq_right h1, ite_eq_right hki, ite_eq_right hkm_ne, ite_eq_right h4, ite_eq_right hkj] at hkA
                rw [hga0k]; exact hkA
          have hpk_eq : patch1 k gs[k] = gs[k] := by
            dsimp only [patch1]
            by_cases h1 : k < i; · rw [ite_eq_left h1]
            · by_cases h4 : k < j
              · rw [ite_eq_right h1, ite_eq_right hki, ite_eq_right hkm_ne, ite_eq_left h4]
                have hop : gs[k].op = GateOp.and := by rw [← hga0k]; exact hkA0
                simp [hop]
              · rw [ite_eq_right h1, ite_eq_right hki, ite_eq_right hkm_ne, ite_eq_right h4, ite_eq_right hkj]
          rw [hga1k, hpk_eq] at hu
          have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0k]; exact hu)
          have hu_lt : u < 26 + k := hback k hk u (by rw [hga0k]; exact hu)
          apply pureOr_of_agree_cone gs gs1 hback hgs1_len u (by omega) hpo_u
          intro c hc
          have hck : InCone 26 ⟨gs, 0⟩ c k := by
            rcases hc with heq | ⟨hu26, hic⟩
            · have hueq : 26 + c = u := heq.symm
              exact inCone_direct ⟨gs, 0⟩ c k hk (by rw [hga0k, hueq]; exact hu) (by omega)
            · exact (inCone_iff 26 ⟨gs, 0⟩ c k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr hic⟩
          have hci : c ≠ i := fun heq => by
            subst heq; exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 hck).2) hkj
          have hcj : c ≠ j := fun heq => by
            subst heq; exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA hkA0 hck).1) (by omega)
          have hcm : c ≠ m := fun heq => by
            subst heq
            have him_c : InCone 26 ⟨gs, 0⟩ i c := inCone_direct ⟨gs, 0⟩ i c (by omega) (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him
            exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i c k him_c hck)).2) hkj
          have hclen : c < gs.length := by have := (inCone_lt ⟨gs, 0⟩ c k hck).1; omega
          have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
          have hga0c : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
          have hcop0 : gs[c].op = GateOp.or := by
            have hu26 : 26 ≤ u := by rcases hc with heq | ⟨hu26, _⟩ <;> omega
            have := hpo_u hu26
            rcases hc with heq | ⟨_, hic⟩
            · have hce : c = u - 26 := by omega
              have hpo1 := this.2.1; rw [← hce, hga0c] at hpo1; exact hpo1
            · have hpo2 := this.2.2 c hic; rw [hga0c] at hpo2; exact hpo2
          have hpc : patch1 c gs[c] = gs[c] := by
            dsimp only [patch1]
            by_cases hc1 : c < i; · rw [ite_eq_left hc1]
            · by_cases hc4 : c < j
              · rw [ite_eq_right hc1, ite_eq_right hci, ite_eq_right hcm, ite_eq_left hc4, hcop0]
                have hc_no_m : 26 + m ∉ gs[c].inputs := fun hmem => by
                  have hmc : m < c := by have := hback c hclen (26 + m) (by rw [hga0c]; exact hmem); omega
                  have him_c := inCone_trans ⟨gs, 0⟩ i m c
                    (inCone_direct ⟨gs, 0⟩ i m hmlen (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him)
                    (inCone_direct ⟨gs, 0⟩ m c hclen (by rw [hga0c]; exact hmem) hmc)
                  exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i c k him_c hck)).2) hkj
                have hc_no_i : 26 + i ∉ gs[c].inputs := fun hmem => by
                  have hic' : i < c := by have := hback c hclen (26 + i) (by rw [hga0c]; exact hmem); omega
                  have := inCone_trans ⟨gs, 0⟩ i c k (inCone_direct ⟨gs, 0⟩ i c hclen (by rw [hga0c]; exact hmem) hic') hck
                  exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 this).2) hkj
                have hmap : gs[c].inputs.map (fun w => if w = 26 + m then v else w) = gs[c].inputs := by
                  trans gs[c].inputs.map (fun a => a)
                  · exact List.map_inj_left.2 (fun w hw => ite_eq_right (fun (heq : w = 26 + m) => hc_no_m (heq ▸ hw)))
                  · exact List.map_id' _
                exact gate_mk_or_eq gs[c] hcop0 _ (by
                  rw [hmap]
                  exact List.filter_eq_self.2 (fun w hw => by simp only [decide_eq_true_eq]; exact fun heq => hc_no_i (heq ▸ hw)))
              · rw [ite_eq_right hc1, ite_eq_right hci, ite_eq_right hcm, ite_eq_right hc4, ite_eq_right hcj]
          simp [gs1, List.getElem?_mapIdx, hg0c, hpc]
    have hnn2 : ¬ ∃ a b : ℕ, (gateAt ⟨gs2, 0⟩ a).op = GateOp.and ∧
        (gateAt ⟨gs2, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs2, 0⟩ a b := by
      apply gatesMoveAfter_no_nested_and gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) hback1 rfl hgs1_nom
      · intro b hjb hblen hbA hic
        rw [hgs1_len] at hblen
        have hinc0 := inCone_of_eq_above gs gs1 j b hgs1_len (fun c hjc hc => by
          have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hc
          simp [gs1, List.getElem?_mapIdx, hg0c, patch1, show ¬ c < i by omega, show c ≠ i by omega,
            show c ≠ m by omega, show ¬ c < j by omega, show c ≠ j by omega]) hjb hblen hic
        have hb0 : (gateAt ⟨gs, 0⟩ b).op = GateOp.and := by
          have hg0b : gs[b]? = some gs[b] := List.getElem?_eq_getElem hblen
          have hgb1 : gs1[b]? = some gs[b] := by
            simp [gs1, List.getElem?_mapIdx, hg0b, patch1, show ¬ b < i by omega, show b ≠ i by omega,
              show b ≠ m by omega, show ¬ b < j by omega, show b ≠ j by omega]
          have : gateAt ⟨gs1, 0⟩ b = gs[b] := by simp [gateAt, List.getD_eq_getElem?_getD, hgb1]
          rw [gateAt_eq ⟨gs, 0⟩ b hblen, ← this]; exact hbA
        have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA hb0 hinc0).1
        omega
      · exact hnn1
    have hgt_agree : ∀ k, j < k → k < gs.length → gs1[k]? = gs[k]? := fun k hjk hk => by
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      simp [gs1, List.getElem?_mapIdx, hg0k, patch1, show ¬ k < i by omega, show k ≠ i by omega,
        show k ≠ m by omega, show ¬ k < j by omega, show k ≠ j by omega]
    have hgs1_eq_w : ∀ x : List Bool, x.length = 26 → ∀ w < 26 + j, w ≠ 26 + m →
        (w ≠ 26 + i ∧ (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ i (w - 26))) → V gs1 x w = V gs x w := by
      intro x hx w hw_lt hwm hno_i
      apply V_eq_of_agree_cone gs gs1 hback hgs1_len x hx w (by omega)
      intro c hc
      have hclen : c < gs.length := by
        rcases hc with heq | ⟨hu26, hic⟩
        · omega
        · exact (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).1.trans (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).2
      have hcj : c < j := by
        rcases hc with heq | ⟨hu26, hic⟩
        · omega
        · have := (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).1; omega
      have hci : c ≠ i := fun heq => by
        subst heq; rcases hc with heq | ⟨hu26, hic⟩
        · exact hno_i.1 heq
        · exact hno_i.2 hu26 hic
      have hcm : c ≠ m := fun heq => by
        subst heq
        have him_c : InCone 26 ⟨gs, 0⟩ i c := inCone_direct ⟨gs, 0⟩ i c hmlen (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him
        rcases hc with heq | ⟨hu26, hic⟩
        · exact hwm heq
        · exact hno_i.2 hu26 (inCone_trans ⟨gs, 0⟩ i c (w - 26) him_c hic)
      have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
      have hga0c : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
      have hi_in_c : InCone 26 ⟨gs, 0⟩ i c → False := fun hic_c => by
        rcases hc with heq | ⟨hu26, hic⟩
        · exact hno_i.2 (by omega) (by rw [heq, Nat.add_sub_cancel_left]; exact hic_c)
        · exact hno_i.2 hu26 (inCone_trans ⟨gs, 0⟩ i c (w - 26) hic_c hic)
      have hpc : patch1 c gs[c] = gs[c] := by
        dsimp only [patch1]
        by_cases hc1 : c < i; · rw [ite_eq_left hc1]
        · rw [ite_eq_right hc1, ite_eq_right hci, ite_eq_right hcm, ite_eq_left hcj]
          cases hop : gs[c].op with
          | and => rfl
          | or =>
            have hc_no_m : 26 + m ∉ gs[c].inputs := fun hmem => by
              have hmc : m < c := by have := hback c hclen (26 + m) (by rw [hga0c]; exact hmem); omega
              exact hi_in_c (inCone_trans ⟨gs, 0⟩ i m c
                (inCone_direct ⟨gs, 0⟩ i m hmlen (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him)
                (inCone_direct ⟨gs, 0⟩ m c hclen (by rw [hga0c]; exact hmem) hmc))
            have hc_no_i : 26 + i ∉ gs[c].inputs := fun hmem => by
              have hic' : i < c := by have := hback c hclen (26 + i) (by rw [hga0c]; exact hmem); omega
              exact hi_in_c (inCone_direct ⟨gs, 0⟩ i c hclen (by rw [hga0c]; exact hmem) hic')
            have hmap : gs[c].inputs.map (fun z => if z = 26 + m then v else z) = gs[c].inputs := by
              trans gs[c].inputs.map (fun a => a)
              · exact List.map_inj_left.2 (fun z hz => ite_eq_right (fun (heq : z = 26 + m) => hc_no_m (heq ▸ hz)))
              · exact List.map_id' _
            exact gate_mk_or_eq gs[c] hop _ (by
              rw [hmap]
              exact List.filter_eq_self.2 (fun z hz => by simp only [decide_eq_true_eq]; exact fun heq => hc_no_i (heq ▸ hz)))
          | _ => rcases (hmon gs[c] (List.getElem_mem hclen)).1 with h | h <;> rw [h] at hop <;> cases hop
      simp [gs1, List.getElem?_mapIdx, hg0c, hpc]
    have hgs1_no_m : ∀ k, m < k → k < gs.length → 26 + m ∉ (gateAt ⟨gs1, 0⟩ k).inputs := by
      intro k hmk hk; exact hgs1_nom k hmk (by rw [hgs1_len]; exact hk)
    have hgs2_uB : ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner m uB) = V gs x uB := by
      intro x hx
      rw [gatesMoveAfter_eval_lt gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
        (fun k hk _ => hgs1_nom k hk (by rw [hgs1_len]; omega)) x hx uB (by omega) (by omega)]
      exact hgs1_eq_w x hx uB (by omega) (by omega) ⟨by omega, fun hu26 hic => by
        have := (inCone_lt ⟨gs, 0⟩ i (uB - 26) hic).1; omega⟩
    have hwR_no_m : wR ≠ 26 + m := fun heq => hwR_no_i.2 (by omega) (by
      rw [heq, Nat.add_sub_cancel_left]
      exact inCone_direct ⟨gs, 0⟩ i m hmlen (by rw [hga_m, hgm_eq]; exact (hmin_eq (26 + i)).2 (Or.inl rfl)) him)
    have hwR_eq1 : ∀ x : List Bool, x.length = 26 → V gs1 x wR = V gs x wR := fun x hx =>
      hgs1_eq_w x hx wR hwR_lt hwR_no_m hwR_no_i
    have hlo_lt_j : ∀ k, j < k → k < gs.length → ∀ u ∈ (gateAt ⟨gs, 0⟩ k).inputs, u < 26 + j →
        ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner m u) = V gs x u := by
      intro k hjk hk u hu hu_lt x hx
      have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hreach_k : reachesAvoiding gs j (26 + k) (26 + outG) := by
        by_cases hko : k = outG
        · subst hko; exact reachesAvoiding.base
        · exact inCone_gt_reachesAvoiding gs j k outG hjk ((hreach k hk).resolve_left hko)
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have huk : u < 26 + k := hback k hk u hu
      have hum : u ≠ 26 + m := fun heq => (hgt_j_noread k hjk hk).2 (by rw [← heq]; exact hu)
      have hno_i_u : u ≠ 26 + i ∧ (26 ≤ u → ¬ InCone 26 ⟨gs, 0⟩ i (u - 26)) := by
        refine ⟨fun heq => (hgt_j_noread k hjk hk).1 (by rw [← heq]; exact hu), fun hu26 hic => ?_⟩
        apply hi_no_bypass
        have hueq : 26 + (u - 26) = u := by omega
        have h1 : reachesAvoiding gs j (26 + i) u := by
          rw [← hueq]; exact reachesAvoiding_below_skip gs j i (u - 26) (by omega) hic
        have h2 : reachesAvoiding gs j u (26 + k) :=
          reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hu) huk reachesAvoiding.base
        exact reachesAvoiding_trans gs j (26 + i) (26 + k) (26 + outG)
          (reachesAvoiding_trans gs j (26 + i) u (26 + k) h1 h2) hreach_k
      rw [gatesMoveAfter_eval_lt gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
        (fun c hc _ => hgs1_no_m c hc (by omega)) x hx u (by omega) hum]
      exact hgs1_eq_w x hx u hu_lt hum hno_i_u
    have hgs1_up : ∀ x : List Bool, x.length = 26 → V gs x (26 + i) = false →
        ∀ w : ℕ, w < 26 + j → w ≠ 26 + i → w ≠ 26 + m → V gs x w = true → V gs1 x w = true := by
      intro x hx hVi0 w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_lt hwi hwm hVw
        by_cases hw26 : w < 26
        · rw [V_in gs1 gs x w (by rw [hx]; exact hw26)]; exact hVw
        · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
          have hklen : k < gs.length := by omega
          have hki : k ≠ i := by omega
          have hkm : k ≠ m := by omega
          have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
          have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
          have hbk : ∀ z ∈ gs[k].inputs, z < 26 + k := fun z hz => hback k hklen z (by rw [hga0k]; exact hz)
          have hpk1 : gs1[k]? = some (patch1 k gs[k]) := by simp [gs1, List.getElem?_mapIdx, hg0k]
          have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hpk1]
          have hbk1 : ∀ z ∈ (patch1 k gs[k]).inputs, z < 26 + k := fun z hz =>
            hback1 k (by rw [hgs1_len]; exact hklen) z (by rw [hga1k]; exact hz)
          by_cases hk1 : k < i
          · have hpk : patch1 k gs[k] = gs[k] := by dsimp only [patch1]; rw [ite_eq_left hk1]
            have hpk1' : gs1[k]? = some gs[k] := by rw [← hpk]; exact hpk1
            rw [gate_val_aux gs x hx k gs[k] hg0k hbk] at hVw
            rw [gate_val_aux gs1 x hx k gs[k] hpk1' hbk]
            exact gateOp_mono (hgs_eq gs[k] (List.getElem_mem hklen)) gs[k].inputs _ _
              (fun z hz hVz => by have hzk := hbk z hz; exact ih z hzk (by omega) (by omega) (by omega) hVz) hVw
          · have hkj : k < j := by omega
            cases hop : gs[k].op with
            | and =>
              have hpk : patch1 k gs[k] = gs[k] := by
                dsimp only [patch1]; rw [ite_eq_right hk1, ite_eq_right hki, ite_eq_right hkm, ite_eq_left hkj, hop]
              have hpk1' : gs1[k]? = some gs[k] := by rw [← hpk]; exact hpk1
              have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, hop]
              rw [andN_iff gs x hx k gs[k] hg0k hbk hop] at hVw
              rw [andN_iff gs1 x hx k gs[k] hpk1' hbk hop]
              intro z hz
              have hzk := hbk z hz
              have hzm := hno_in_and k hklen (by omega) hkA
              have hzi : z ≠ 26 + i := fun heq => hzm.1 (by rw [hga0k, ← heq]; exact hz)
              have hz_m : z ≠ 26 + m := fun heq => hzm.2 (by rw [hga0k, ← heq]; exact hz)
              exact ih z hzk (by omega) hzi hz_m (hVw z hz)
            | or =>
              have hpk : patch1 k gs[k] = ⟨GateOp.or, (gs[k].inputs.map (fun w => if w = 26 + m then v else w)).filter (· ≠ 26 + i)⟩ := by
                dsimp only [patch1]; rw [ite_eq_right hk1, ite_eq_right hki, ite_eq_right hkm, ite_eq_left hkj, hop]
              rw [hpk] at hpk1 hbk1
              rw [orN gs x hx k gs[k] hg0k hbk hop] at hVw
              obtain ⟨z, hz, hVz⟩ := hVw
              rw [orN gs1 x hx k _ hpk1 hbk1 rfl]
              by_cases hzi : z = 26 + i
              · rw [hzi, hVi0] at hVz; cases hVz
              · by_cases hzm : z = 26 + m
                · subst hzm
                  have hmk : m < k := by have := hbk (26 + m) hz; omega
                  have hgm_0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hmlen
                  have hga0m : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hmlen
                  have hbm : ∀ w0 ∈ gs[m].inputs, w0 < 26 + m := fun w0 hw0 => hback m hmlen w0 (by rw [hga0m]; exact hw0)
                  have hmop0 : gs[m].op = GateOp.or := by rw [← hgm_eq]; exact hmop
                  rw [orN gs x hx m gs[m] hgm_0 hbm hmop0] at hVz
                  obtain ⟨w0, hw0, hVw0⟩ := hVz
                  rw [hmin_eq w0] at hw0
                  rcases hw0 with rfl | rfl
                  · rw [hVi0] at hVw0; cases hVw0
                  · refine ⟨v, List.mem_filter.2 ⟨List.mem_map.2 ⟨26 + m, hz, by simp⟩, by simpa using hv_ne⟩, ?_⟩
                    exact ih v (by omega) (by omega) hv_ne (by omega) hVw0
                · refine ⟨z, List.mem_filter.2 ⟨List.mem_map.2 ⟨z, hz, by simp [hzm]⟩, by simpa using hzi⟩, ?_⟩
                  have hzk := hbk z hz
                  exact ih z hzk (by omega) hzi hzm hVz
            | _ => rcases (hgs_eq gs[k] (List.getElem_mem hklen)) with h | h <;> rw [h] at hop <;> cases hop
    have hgs1_down : ∀ x : List Bool, x.length = 26 →
        ∀ w : ℕ, w < 26 + j → w ≠ 26 + i → w ≠ 26 + m → V gs1 x w = true → V gs x w = true := by
      intro x hx w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_lt hwi hwm hVw1
        by_cases hw26 : w < 26
        · rw [← V_in gs1 gs x w (by rw [hx]; exact hw26)]; exact hVw1
        · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
          have hklen : k < gs.length := by omega
          have hki : k ≠ i := by omega
          have hkm : k ≠ m := by omega
          have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
          have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
          have hbk : ∀ z ∈ gs[k].inputs, z < 26 + k := fun z hz => hback k hklen z (by rw [hga0k]; exact hz)
          have hpk1 : gs1[k]? = some (patch1 k gs[k]) := by simp [gs1, List.getElem?_mapIdx, hg0k]
          have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hpk1]
          have hbk1 : ∀ z ∈ (patch1 k gs[k]).inputs, z < 26 + k := fun z hz =>
            hback1 k (by rw [hgs1_len]; exact hklen) z (by rw [hga1k]; exact hz)
          by_cases hk1 : k < i
          · have hpk : patch1 k gs[k] = gs[k] := by dsimp only [patch1]; rw [ite_eq_left hk1]
            have hpk1' : gs1[k]? = some gs[k] := by rw [← hpk]; exact hpk1
            rw [gate_val_aux gs1 x hx k gs[k] hpk1' hbk] at hVw1
            rw [gate_val_aux gs x hx k gs[k] hg0k hbk]
            exact gateOp_mono (hgs_eq gs[k] (List.getElem_mem hklen)) gs[k].inputs _ _
              (fun z hz hVz1 => by have hzk := hbk z hz; exact ih z hzk (by omega) (by omega) (by omega) hVz1) hVw1
          · have hkj : k < j := by omega
            cases hop : gs[k].op with
            | and =>
              have hpk : patch1 k gs[k] = gs[k] := by
                dsimp only [patch1]; rw [ite_eq_right hk1, ite_eq_right hki, ite_eq_right hkm, ite_eq_left hkj, hop]
              have hpk1' : gs1[k]? = some gs[k] := by rw [← hpk]; exact hpk1
              have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, hop]
              rw [andN_iff gs1 x hx k gs[k] hpk1' hbk hop] at hVw1
              rw [andN_iff gs x hx k gs[k] hg0k hbk hop]
              intro z hz
              have hzk := hbk z hz
              have hzm := hno_in_and k hklen (by omega) hkA
              have hzi : z ≠ 26 + i := fun heq => hzm.1 (by rw [hga0k, ← heq]; exact hz)
              have hz_m : z ≠ 26 + m := fun heq => hzm.2 (by rw [hga0k, ← heq]; exact hz)
              exact ih z hzk (by omega) hzi hz_m (hVw1 z hz)
            | or =>
              have hpk : patch1 k gs[k] = ⟨GateOp.or, (gs[k].inputs.map (fun w => if w = 26 + m then v else w)).filter (· ≠ 26 + i)⟩ := by
                dsimp only [patch1]; rw [ite_eq_right hk1, ite_eq_right hki, ite_eq_right hkm, ite_eq_left hkj, hop]
              rw [hpk] at hpk1 hbk1
              rw [orN gs1 x hx k _ hpk1 hbk1 rfl] at hVw1
              obtain ⟨z', hz', hVz'⟩ := hVw1
              rw [List.mem_filter] at hz'
              have hz'_ni : z' ≠ 26 + i := by simpa using hz'.2
              obtain ⟨z, hz, heqz⟩ := List.mem_map.1 hz'.1
              rw [orN gs x hx k gs[k] hg0k hbk hop]
              by_cases hzm : z = 26 + m
              · rw [ite_eq_left hzm] at heqz
                rw [← heqz] at hz'_ni hVz'
                have hmk : m < k := by have := hbk z hz; omega
                have hVv : V gs x v = true := ih v (by omega) (by omega) hv_ne (by omega) hVz'
                have hgm_0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hmlen
                have hga0m : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hmlen
                have hbm : ∀ w0 ∈ gs[m].inputs, w0 < 26 + m := fun w0 hw0 => hback m hmlen w0 (by rw [hga0m]; exact hw0)
                have hmop0 : gs[m].op = GateOp.or := by rw [← hgm_eq]; exact hmop
                refine ⟨26 + m, by rw [← hzm]; exact hz, ?_⟩
                rw [orN gs x hx m gs[m] hgm_0 hbm hmop0]
                exact ⟨v, by rw [hmin_eq]; right; rfl, hVv⟩
              · rw [ite_eq_right hzm] at heqz
                rw [← heqz] at hz'_ni hVz'
                have hzk := hbk z hz
                exact ⟨z, hz, ih z hzk (by omega) hz'_ni hzm hVz'⟩
            | _ => rcases (hgs_eq gs[k] (List.getElem_mem hklen)) with h | h <;> rw [h] at hop <;> cases hop
    have hgi2 : gs2[i]? = some ⟨GateOp.and, [y0.1, uB]⟩ := by
      have hg := gatesMoveAfter_getElem_lt gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) i him
      have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
      have h1i : gs1[i]? = some ⟨GateOp.and, [y0.1, uB]⟩ := by
        simp [gs1, List.getElem?_mapIdx, hg0i, patch1]
      rw [h1i] at hg; exact hg
    have hgj2 : gs2[j]? = some gNew := gatesMoveAfter_getElem_dst gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2)
    have hbj2 : ∀ z ∈ gNew.inputs, z < 26 + j := fun z hz => by
      simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega
    have hbi2 : ∀ z ∈ ([y0.1, uB] : List ℕ), z < 26 + i := fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; have hy26 := y0.2; rcases hz with rfl | rfl <;> omega
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj0 : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
    have hopj0 : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hg1j : gs1[j]? = some ⟨GateOp.and, [wL', wR]⟩ := by
      simp [gs1, List.getElem?_mapIdx, hg0j, patch1, show ¬ j < i by omega, show j ≠ i by omega,
        show j ≠ m by omega]
    have hbj1 : ∀ z ∈ ([wL', wR] : List ℕ), z < 26 + j := fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega
    apply core_contra gs2 (26 + outG) (by rw [hgs2_len]; exact hsz) hmon2 hback2 hnn2
    · intro p l hp
      refine gatesMoveAfter_eval_up_ge_rel gs gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2)
        hgs1_len hgs_eq hback hback2 hgt_agree (inp {p} {l}) (inp_len _ _)
        (fun k hjk hk u hu hult hv => by rw [hlo_lt_j k hjk hk u hu hult _ (inp_len _ _)]; exact hv)
        ?_ outG (by omega) (by omega) (hacc p l hp)
      intro hVj
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0] at hVj
      have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
      have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
      rw [orN gs2 _ (inp_len _ _) j gNew hgj2 hbj2 rfl]
      cases hVi0 : V gs (inp {p} {l}) (26 + i)
      · have hVwR1 : V gs1 (inp {p} {l}) wR = true := by rw [hwR_eq1 _ (inp_len _ _)]; exact hVwR
        have hVwL1 : V gs1 (inp {p} {l}) wL' = true := by
          by_cases hwm : wL = 26 + m
          · have hwL'eq : wL' = v := by dsimp only [wL']; rw [ite_eq_left hwm]
            rw [hwL'eq]
            rw [hwm] at hVwL
            have hgm_0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hmlen
            have hga0m : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hmlen
            have hbm : ∀ w0 ∈ gs[m].inputs, w0 < 26 + m := fun w0 hw0 => hback m hmlen w0 (by rw [hga0m]; exact hw0)
            have hmop0 : gs[m].op = GateOp.or := by rw [← hgm_eq]; exact hmop
            rw [orN gs _ (inp_len _ _) m gs[m] hgm_0 hbm hmop0] at hVwL
            obtain ⟨w0, hw0, hVw0⟩ := hVwL
            rw [hmin_eq w0] at hw0
            rcases hw0 with rfl | rfl
            · rw [hVi0] at hVw0; cases hVw0
            · exact hgs1_up _ (inp_len _ _) hVi0 v (by omega) hv_ne (by omega) hVw0
          · have hwL'eq : wL' = wL := by dsimp only [wL']; rw [ite_eq_right hwm]
            rw [hwL'eq]
            exact hgs1_up _ (inp_len _ _) hVi0 wL hwL_lt hwL_ne_i hwm hVwL
        have hVj1 : V gs1 (inp {p} {l}) (26 + j) = true := by
          rw [andN_iff gs1 _ (inp_len _ _) j _ hg1j hbj1 rfl]
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl; exact hVwL1; exact hVwR1
        have hVj2 : V gs2 (inp {p} {l}) (26 + (j - 1)) = true := by
          have hev := gatesMoveAfter_eval_lt gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
            (fun k hk _ => hgs1_no_m k hk (by omega)) (inp {p} {l}) (inp_len _ _) (26 + j) (by omega) (by omega)
          have hsh : shiftMoveInner m (26 + j) = 26 + (j - 1) := by
            unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
          rw [hsh] at hev; rw [hev]; exact hVj1
        exact ⟨26 + (j - 1), by simp [gNew], hVj2⟩
      · have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
        have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
        have hbi0 : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
        have hopi0 : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
        rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi0 hopi0] at hVi0
        have hVA := hVi0 uA (by rw [← hga0i, hu_inp]; left; rfl)
        have hVB := hVi0 uB (by rw [← hga0i, hu_inp]; right; rfl)
        obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 hVA
        obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
        obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
        obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
        have hcY : c ∈ A ∩ R := by
          simp only [Finset.mem_union] at hc
          rcases hc with (hc | hc) | hc
          · rw [hXZ_empty.1] at hc; cases hc
          · exact hc
          · rw [hXZ_empty.2] at hc; cases hc
        rw [hY_sing c hcY] at hpc
        have hVy0 : V gs2 (inp {p} {l}) y0.1 = true := by
          unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact y0.2)]; exact hpc
        have hVuB2 : V gs2 (inp {p} {l}) uB = true := by
          have hsh : shiftMoveInner m uB = uB := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
          have := hgs2_uB (inp {p} {l}) (inp_len _ _)
          rw [hsh] at this; rw [this]; exact hVB
        have hVi2 : V gs2 (inp {p} {l}) (26 + i) = true := by
          rw [andN_iff gs2 _ (inp_len _ _) i _ hgi2 hbi2 rfl]
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl; exact hVy0; exact hVuB2
        exact ⟨26 + i, by simp [gNew], hVi2⟩
    · intro Q hQ
      rw [Bool.eq_false_iff]; intro htr
      have hdn : V gs2 (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
        intro hVj2
        rw [orN gs2 _ (inp_len _ _) j gNew hgj2 hbj2 rfl] at hVj2
        rcases hVj2 with ⟨z, hz, hVz2⟩
        simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · have hev := gatesMoveAfter_eval_lt gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
            (fun k hk _ => hgs1_no_m k hk (by omega)) (inp Q (TQ Q)) (inp_len _ _) (26 + j) (by omega) (by omega)
          have hsh : shiftMoveInner m (26 + j) = 26 + (j - 1) := by
            unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
          rw [hsh] at hev
          have hVj1 : V gs1 (inp Q (TQ Q)) (26 + j) = true := by rw [← hev]; exact hVz2
          rw [andN_iff gs1 _ (inp_len _ _) j _ hg1j hbj1 rfl] at hVj1
          have hVwL1 := hVj1 wL' (by simp)
          have hVwR1 := hVj1 wR (by simp)
          have hVwR : V gs (inp Q (TQ Q)) wR = true := by rw [← hwR_eq1 _ (inp_len _ _)]; exact hVwR1
          have hVwL : V gs (inp Q (TQ Q)) wL = true := by
            by_cases hwm : wL = 26 + m
            · have hwL'eq : wL' = v := by dsimp only [wL']; rw [ite_eq_left hwm]
              rw [hwL'eq] at hVwL1
              have hVv := hgs1_down _ (inp_len _ _) v (by omega) hv_ne (by omega) hVwL1
              rw [hwm]
              have hgm_0 : gs[m]? = some gs[m] := List.getElem?_eq_getElem hmlen
              have hga0m : gateAt ⟨gs, 0⟩ m = gs[m] := gateAt_eq ⟨gs, 0⟩ m hmlen
              have hbm : ∀ w0 ∈ gs[m].inputs, w0 < 26 + m := fun w0 hw0 => hback m hmlen w0 (by rw [hga0m]; exact hw0)
              have hmop0 : gs[m].op = GateOp.or := by rw [← hgm_eq]; exact hmop
              rw [orN gs _ (inp_len _ _) m gs[m] hgm_0 hbm hmop0]
              exact ⟨v, by rw [hmin_eq]; right; rfl, hVv⟩
            · have hwL'eq : wL' = wL := by dsimp only [wL']; rw [ite_eq_right hwm]
              rw [hwL'eq] at hVwL1
              exact hgs1_down _ (inp_len _ _) wL hwL_lt hwL_ne_i hwm hVwL1
          rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0]
          intro z hz; rw [← hga0j, hwj_inp] at hz
          rcases hz with rfl | rfl; exact hVwL; exact hVwR
        · rw [andN_iff gs2 _ (inp_len _ _) i _ hgi2 hbi2 rfl] at hVz2
          have hVy0 := hVz2 y0.1 (by simp)
          have hVuB := hVz2 uB (by simp)
          have hqy0 : qHit Q y0 = true := by
            have hv0 : V gs2 (inp Q (TQ Q)) y0.1 = (inp Q (TQ Q)).getD y0.1 false := by
              unfold V; exact getD_wiresFrom gs2 _ _ (by rw [inp_len]; exact y0.2)
            rw [← qHit_eq_inp_getD, ← hv0, hVy0]
          have hVuB0 : V gs (inp Q (TQ Q)) uB = true := by
            have hsh : shiftMoveInner m uB = uB := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
            have := hgs2_uB (inp Q (TQ Q)) (inp_len _ _)
            rw [hsh] at this; rw [← this]; exact hVuB
          obtain ⟨b, hbB, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVuB0
          rw [qHit_eq_inp_getD] at hqb
          exact absurd ⟨⟨y0, hy0A, hqy0⟩, ⟨b, hbB, hqb⟩, ⟨y0, hy0R, hqy0⟩⟩ (h3 Q hQ)
      have htr0 := gatesMoveAfter_eval_down_ge_rel gs gs1 m j gNew hmj (by rw [hgs1_len]; exact hlt.2)
        hgs1_len hgs_eq hback hback2 hgt_agree (inp Q (TQ Q)) (inp_len _ _)
        (fun k hjk hk u hu hult hv => by rw [← hlo_lt_j k hjk hk u hu hult _ (inp_len _ _)]; exact hv)
        hdn outG (by omega) (by omega) htr
      rw [hrej Q hQ] at htr0; cases htr0
  · have hSL_empty : S_L = ∅ := Finset.not_nonempty_iff_eq_empty.1 hSL
    have hwL_imp_i : ∀ x : List Bool, x.length = 26 → V gs x wL = true → V gs x (26 + i) = true := by
      intro x hx hVwL
      by_contra hni
      have hVi_f : V gs x (26 + i) = false := Bool.eq_false_iff.2 hni
      have hwL_ni : 26 ≤ wL → wL ≠ 26 + i := fun _ heq => by rw [heq, hVi_f] at hVwL; cases hVwL
      have hor_wL : ∀ m : ℕ, 26 ≤ wL → (m = wL - 26 ∨ InCone 26 ⟨gs, 0⟩ m (wL - 26)) → m ≠ i →
          (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
        intro m hw26 hrel hmi
        have hmj : InCone 26 ⟨gs, 0⟩ m j := by
          rcases hrel with rfl | hic
          · exact inCone_direct ⟨gs, 0⟩ (wL - 26) j hlt.2 (by
              have : 26 + (wL - 26) = wL := by omega
              rw [this]; exact (hwj_inp wL).2 (Or.inl rfl)) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ m j hlt.2).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hw26, hwL_lt, Or.inr hic⟩
        exact gateAt_below_j_or_eq gs i j hiA hjA hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m j hmj).1; omega) hmj hmi
      obtain ⟨s, hs, _⟩ := orSetAvoid_complete gs i hback x hx hVi_f wL (by omega) hwL_ni hor_wL hVwL
      change s ∈ S_L at hs; rw [hSL_empty] at hs; cases hs
    let patch : ℕ → Gate → Gate := fun k g =>
      if k = i then ⟨GateOp.and, [y0.1, uB]⟩
      else if k = j then ⟨GateOp.or, [26 + i]⟩
      else g
    let gs' := gs.mapIdx patch
    have hgs'_len : gs'.length = gs.length := List.length_mapIdx
    let Bad : Finset ℕ := {i, j}
    have hkeep : ∀ k g, k ∉ Bad → patch k g = g := fun k g hk => by
      simp only [Bad, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      dsimp only [patch]; rw [ite_eq_right hk.1, ite_eq_right hk.2]
    have hmon' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      apply mapIdx_mono; intro k g hg; dsimp only [patch]; split_ifs
      · simp
      · simp
      · exact hmon g (List.mem_of_getElem? hg)
    have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
      apply mapIdx_readsBack; intro k g hg u hu; dsimp only [patch] at hu
      by_cases hk1 : k = i
      · rw [ite_eq_left hk1] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        have hy26 := y0.2; rcases hu with rfl | rfl <;> omega
      · by_cases hk2 : k = j
        · rw [ite_eq_right hk1, ite_eq_left hk2] at hu; simp at hu; omega
        · rw [ite_eq_right hk1, ite_eq_right hk2] at hu
          have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
          have hgak : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
          exact hback k hklen u (by rw [hgak]; exact hu)
    have hnn' : ¬ ∃ a b : ℕ, (gateAt ⟨gs', 0⟩ a).op = GateOp.and ∧
        (gateAt ⟨gs', 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs', 0⟩ a b := by
      apply no_nested_and_of_all_and_pureOr gs' 0
      intro k hk hkA u hu
      rw [hgs'_len] at hk
      have hkj : k ≠ j := by
        intro heq; subst heq
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hpk : gs'[k]? = some ⟨GateOp.or, [26 + i]⟩ := by simp [gs', List.getElem?_mapIdx, hg0k, patch, show k ≠ i by omega]
        have hga' : gateAt ⟨gs', 0⟩ k = ⟨GateOp.or, [26 + i]⟩ := by simp [gateAt, List.getD_eq_getElem?_getD, hpk]
        rw [hga'] at hkA; cases hkA
      by_cases hki : k = i
      · subst hki
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hpk : gs'[k]? = some ⟨GateOp.and, [y0.1, uB]⟩ := by simp [gs', List.getElem?_mapIdx, hg0k, patch]
        have hga' : gateAt ⟨gs', 0⟩ k = ⟨GateOp.and, [y0.1, uB]⟩ := by simp [gateAt, List.getD_eq_getElem?_getD, hpk]
        rw [hga'] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hu1 | hu2
        · rw [hu1]; intro h; have := y0.2; omega
        · rw [hu2]; apply pureOr_mapIdx gs patch Bad hkeep hback uB (by omega)
          · intro m hm _
            have huB26 : 26 ≤ uB := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
            have := huB_po huB26
            rcases hm with heq | ⟨_, hic⟩
            · have hm_eq : m = uB - 26 := by omega
              rw [hm_eq]; exact this.2.1
            · exact this.2.2 m hic
          · intro b hb _ hrel
            simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
            rcases hb with hbi_eq | hbj_eq
            · rw [hbi_eq] at hrel; rcases hrel with heq | ⟨_, hic⟩
              · omega
              · have := (inCone_lt ⟨gs, 0⟩ k (uB - 26) hic).1; omega
            · rw [hbj_eq] at hrel; rcases hrel with heq | ⟨_, hic⟩
              · omega
              · have := (inCone_lt ⟨gs, 0⟩ j (uB - 26) hic).1; omega
      · have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
        have hpk : gs'[k]? = some gs[k] := by simp [gs', List.getElem?_mapIdx, hg0k, hkeep k gs[k] (by simp [Bad, hki, hkj])]
        have hga' : gateAt ⟨gs', 0⟩ k = gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hpk]
        have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, ← hga']; exact hkA
        rw [hga'] at hu
        have hu_lt : u < 26 + k := hback k hk u (by rw [hga0k]; exact hu)
        have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0k]; exact hu)
        apply pureOr_mapIdx gs patch Bad hkeep hback u (by omega)
        · intro m hm _
          have hu26 : 26 ≤ u := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
          have := hpo_u hu26
          rcases hm with heq | ⟨_, hic⟩
          · have hm_eq : m = u - 26 := by omega
            rw [hm_eq]; exact this.2.1
          · exact this.2.2 m hic
        · intro b hb _ hrel
          simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with hbi_eq | hbj_eq
          · have hbk : InCone 26 ⟨gs, 0⟩ i k := by
              rcases hrel with heq | ⟨hu26, hic⟩
              · have hueq : 26 + i = u := by omega
                exact inCone_direct ⟨gs, 0⟩ i k hk (by rw [hga0k, hueq]; exact hu) (by omega)
              · exact (inCone_iff 26 ⟨gs, 0⟩ i k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr (hbi_eq ▸ hic)⟩
            exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 hbk).2) hkj
          · have hbk : InCone 26 ⟨gs, 0⟩ j k := by
              rcases hrel with heq | ⟨hu26, hic⟩
              · have hueq : 26 + j = u := by omega
                exact inCone_direct ⟨gs, 0⟩ j k hk (by rw [hga0k, hueq]; exact hu) (by omega)
              · exact (inCone_iff 26 ⟨gs, 0⟩ j k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr (hbj_eq ▸ hic)⟩
            exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i j k hij hbk)).2) hkj
    have hbad_out : reachesBadOnlyVia gs Bad j (26 + outG) := by
      intro b hb hbj hrb
      simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact hi_no_bypass hrb
      · exact hbj rfl
    have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
    have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
    have hbi0 : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
    have hopi0 : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj0 : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
    have hopj0 : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hgi' : gs'[i]? = some ⟨GateOp.and, [y0.1, uB]⟩ := by simp [gs', List.getElem?_mapIdx, hg0i, patch]
    have hgj' : gs'[j]? = some ⟨GateOp.or, [26 + i]⟩ := by simp [gs', List.getElem?_mapIdx, hg0j, patch, show j ≠ i by omega]
    have hbi' : ∀ z ∈ ([y0.1, uB] : List ℕ), z < 26 + i := fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; have := y0.2; rcases hz with rfl | rfl <;> omega
    have hbj' : ∀ z ∈ ([26 + i] : List ℕ), z < 26 + j := fun z hz => by simp at hz; omega
    have huB_eval' : ∀ x : List Bool, x.length = 26 → V gs' x uB = V gs x uB := fun x hx =>
      mapIdx_eval_avoid gs patch Bad hback hkeep x hx uB (by omega) (fun b hb => by
        simp only [Bad, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with hb1 | hb2
        · rw [hb1]; exact ⟨by omega, fun hu26 hic => by have := (inCone_lt ⟨gs, 0⟩ i (uB - 26) hic).1; omega⟩
        · rw [hb2]; exact ⟨by omega, fun hu26 hic => by have := (inCone_lt ⟨gs, 0⟩ j (uB - 26) hic).1; omega⟩)
    apply core_contra gs' (26 + outG) (by rw [hgs'_len]; exact hsz) hmon' hback' hnn'
    · intro p l hp
      apply mapIdx_eval_up gs patch Bad j hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _) _ (26 + outG) (by omega) hbad_out (hacc p l hp)
      intro hVj
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0] at hVj
      have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
      have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
      have hVi0 := hwL_imp_i (inp {p} {l}) (inp_len _ _) hVwL
      rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi0 hopi0] at hVi0
      have hVA := hVi0 uA (by rw [← hga0i, hu_inp]; left; rfl)
      have hVB := hVi0 uB (by rw [← hga0i, hu_inp]; right; rfl)
      obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 hVA
      obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
      obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
      obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
      have hcY : c ∈ A ∩ R := by
        simp only [Finset.mem_union] at hc
        rcases hc with (hc | hc) | hc
        · rw [hXZ_empty.1] at hc; cases hc
        · exact hc
        · rw [hXZ_empty.2] at hc; cases hc
      rw [hY_sing c hcY] at hpc
      have hVy0 : V gs' (inp {p} {l}) y0.1 = true := by
        unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact y0.2)]; exact hpc
      have hVi' : V gs' (inp {p} {l}) (26 + i) = true := by
        rw [andN_iff gs' _ (inp_len _ _) i _ hgi' hbi' rfl]
        intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl; exact hVy0; rw [huB_eval' _ (inp_len _ _)]; exact hVB
      rw [orN gs' _ (inp_len _ _) j _ hgj' hbj' rfl]
      exact ⟨26 + i, by simp, hVi'⟩
    · intro Q hQ
      rw [Bool.eq_false_iff]; intro htr
      have hdn : V gs' (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
        intro hVj'
        rw [orN gs' _ (inp_len _ _) j _ hgj' hbj' rfl] at hVj'
        obtain ⟨z, hz, hVz'⟩ := hVj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rw [hz] at hVz'
        rw [andN_iff gs' _ (inp_len _ _) i _ hgi' hbi' rfl] at hVz'
        have hVy0 := hVz' y0.1 (by simp)
        have hVuB := hVz' uB (by simp)
        have hqy0 : qHit Q y0 = true := by
          have hv0 : V gs' (inp Q (TQ Q)) y0.1 = (inp Q (TQ Q)).getD y0.1 false := by
            unfold V; exact getD_wiresFrom gs' _ _ (by rw [inp_len]; exact y0.2)
          rw [← qHit_eq_inp_getD, ← hv0, hVy0]
        rw [huB_eval' _ (inp_len _ _)] at hVuB
        obtain ⟨b, hbB, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVuB
        rw [qHit_eq_inp_getD] at hqb
        exact absurd ⟨⟨y0, hy0A, hqy0⟩, ⟨b, hbB, hqb⟩, ⟨y0, hy0R, hqy0⟩⟩ (h3 Q hQ)
      have htr0 := mapIdx_eval_down gs patch Bad j hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _) hdn (26 + outG) (by omega) hbad_out htr
      rw [hrej Q hQ] at htr0; cases htr0

set_option maxHeartbeats 800000 in
lemma case2_sub6 (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j uA uB wL wR : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (hu_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ i).inputs ↔ w = uA ∨ w = uB)
    (hwL_reach : reachesOr gs gs.length (26 + i) wL)
    (hwR_lt : wR < 26 + j)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26)))
    (hwj_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR)
    (y0 z0 : Fin 26)
    (hy0Y : y0 ∈ orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length wR)
    (hz0Z : z0 ∈ orSetAvoid gs gs.length uB ∩ orSetAvoid gs gs.length wR)
    (hX_empty : orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length uB = ∅)
    (h3 : okQuad3 (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR)) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hil : i < gs.length := by omega
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  have hpos : ∀ g ∈ gs, 0 < g.inputs.length := fun g hg => by rw [(htwo g hg).1]; omega
  let A := orSetAvoid gs gs.length uA
  let B := orSetAvoid gs gs.length uB
  let R := orSetAvoid gs gs.length wR
  let Y := A ∩ R
  let Z := B ∩ R
  let S_L := orSetAvoid gs i wL
  have hy0A : y0 ∈ A := (Finset.mem_inter.1 hy0Y).1
  have hy0R : y0 ∈ R := (Finset.mem_inter.1 hy0Y).2
  have hz0B : z0 ∈ B := (Finset.mem_inter.1 hz0Z).1
  have hz0R : z0 ∈ R := (Finset.mem_inter.1 hz0Z).2
  have huA_lt : uA < 26 + i := hback i hil uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_lt : uB < 26 + i := hback i hil uB ((hu_inp uB).2 (Or.inr rfl))
  have hwL_lt : wL < 26 + j := hback j hlt.2 wL ((hwj_inp wL).2 (Or.inl rfl))
  have huA_po : pureOr gs uA := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_po : pureOr gs uB := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uB ((hu_inp uB).2 (Or.inr rfl))
  have hwR_po : pureOr gs wR :=
    pureOr_wR gs hmon hback i j wR hiA hjA hij hAP ((hwj_inp wR).2 (Or.inr rfl)) hwR_no_i
  have hok_YB : okQuad Y B := okQuad_of_okQuad3_interL A B R h3
  have hok_ZA : okQuad Z A := okQuad_of_okQuad3_interR A B R h3
  have hy0z0 : isInc26 y0 z0 = true := hok_YB y0 hy0Y z0 hz0B
  have hok_SL_R : okQuad S_L R := by
    intro s hs r hr; by_contra hne
    have hfl : isInc26 s r = false := by cases h : isInc26 s r <;> simp_all
    obtain ⟨Q, hQ, hqs, hqr⟩ := pair_in_quad s r hfl
    have hVwL : V gs (inp Q (TQ Q)) wL = true :=
      orSetAvoid_sound gs i hback (inp Q (TQ Q)) (inp_len _ _) wL (by omega) ⟨s, hs, by rw [qHit_eq_inp_getD, hqs]⟩
    have hVwR : V gs (inp Q (TQ Q)) wR = true :=
      orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) wR (by omega) ⟨r, hr, by rw [qHit_eq_inp_getD, hqr]⟩
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
    have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hVj := (andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj).2 (fun z hz => by
      rw [← hga0j, hwj_inp] at hz; rcases hz with rfl | rfl; exact hVwL; exact hVwR)
    rw [hjQ Q hQ] at hVj; cases hVj
  have hSL_empty : S_L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro s hs
    have hsy := hok_SL_R s hs y0 hy0R
    have hsz := hok_SL_R s hs z0 hz0R
    rw [isInc26_symm] at hsy
    have hfl := isInc26_bipartite y0 s z0 hsy hsz
    rw [hy0z0] at hfl; cases hfl
  have hwL_imp_i : ∀ x : List Bool, x.length = 26 → V gs x wL = true → V gs x (26 + i) = true := by
    intro x hx hVwL
    by_contra hni
    have hVi_f : V gs x (26 + i) = false := by cases h : V gs x (26 + i) <;> simp_all
    have hwL_ni : 26 ≤ wL → wL ≠ 26 + i := fun _ heq => by rw [heq, hVi_f] at hVwL; cases hVwL
    have hor_wL : ∀ m : ℕ, 26 ≤ wL → (m = wL - 26 ∨ InCone 26 ⟨gs, 0⟩ m (wL - 26)) → m ≠ i →
        (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
      intro m hw26 hrel hmi
      have hmj : InCone 26 ⟨gs, 0⟩ m j := by
        rcases hrel with rfl | hic
        · exact inCone_direct ⟨gs, 0⟩ (wL - 26) j hlt.2 (by
            have : 26 + (wL - 26) = wL := by omega
            rw [this]; exact (hwj_inp wL).2 (Or.inl rfl)) (by omega)
        · exact (inCone_iff 26 ⟨gs, 0⟩ m j hlt.2).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hw26, hwL_lt, Or.inr hic⟩
      exact gateAt_below_j_or_eq gs i j hiA hjA hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m j hmj).1; omega) hmj hmi
    obtain ⟨s, hs, _⟩ := orSetAvoid_complete gs i hback x hx hVi_f wL (by omega) hwL_ni hor_wL hVwL
    change s ∈ S_L at hs; rw [hSL_empty] at hs; cases hs
  have collapse_j_to_i : (∀ x : List Bool, x.length = 26 → V gs x (26 + i) = true → V gs x wR = true) → False := by
    intro himpR
    let patch : ℕ → Gate → Gate := fun k g => if k = j then ⟨GateOp.or, [26 + i]⟩ else g
    let gs' := gs.mapIdx patch
    have hgs'_len : gs'.length = gs.length := List.length_mapIdx
    have hkeep : ∀ k g, k ∉ ({j} : Finset ℕ) → patch k g = g := fun k g hk => by
      simp only [Finset.mem_singleton] at hk; dsimp only [patch]; rw [ite_eq_right hk]
    have hmon' : ∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      apply mapIdx_mono; intro k g hg; dsimp only [patch]; split_ifs
      · simp
      · exact hmon g (List.mem_of_getElem? hg)
    have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
      apply mapIdx_readsBack; intro k g hg u hu; dsimp only [patch] at hu; split_ifs at hu with hk
      · simp at hu; omega
      · have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        have hga0 : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
        exact hback k hklen u (by rw [hga0]; exact hu)
    have hnn' : ¬ ∃ a b : ℕ, (gateAt ⟨gs', 0⟩ a).op = GateOp.and ∧
        (gateAt ⟨gs', 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs', 0⟩ a b := by
      apply no_nested_and_of_all_and_pureOr gs' 0
      intro k hk hkA u hu
      rw [hgs'_len] at hk
      have hkj : k ≠ j := by
        intro heq; subst heq
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hpk : gs'[k]? = some ⟨GateOp.or, [26 + i]⟩ := by simp [gs', List.getElem?_mapIdx, hg0k, patch]
        have hga' : gateAt ⟨gs', 0⟩ k = ⟨GateOp.or, [26 + i]⟩ := by simp [gateAt, List.getD_eq_getElem?_getD, hpk]
        rw [hga'] at hkA; cases hkA
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
      have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
      have hpk : gs'[k]? = some gs[k] := by simp [gs', List.getElem?_mapIdx, hg0k, patch, hkj]
      have hga' : gateAt ⟨gs', 0⟩ k = gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hpk]
      have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, ← hga']; exact hkA
      rw [hga'] at hu
      have hu_lt : u < 26 + k := hback k hk u (by rw [hga0k]; exact hu)
      have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0k]; exact hu)
      apply pureOr_mapIdx gs patch {j} hkeep hback u (by omega)
      · intro m hm _
        have hu26 : 26 ≤ u := by rcases hm with heq | ⟨hu26, _⟩ <;> omega
        have := hpo_u hu26
        rcases hm with heq | ⟨_, hic⟩
        · have hm_eq : m = u - 26 := by omega
          rw [hm_eq]; exact this.2.1
        · exact this.2.2 m hic
      · intro b hb _ hrel
        have hbj_eq : b = j := Finset.mem_singleton.1 hb
        have hbk : InCone 26 ⟨gs, 0⟩ j k := by
          rcases hrel with heq | ⟨hu26, hic⟩
          · have hueq : 26 + j = u := by omega
            exact inCone_direct ⟨gs, 0⟩ j k hk (by rw [hga0k, hueq]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ j k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr (hbj_eq ▸ hic)⟩
        exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i j k hij hbk)).2) hkj
    have hbad_out : reachesBadOnlyVia gs {j} j (26 + outG) := fun b hb hbj _ => by
      simp only [Finset.mem_singleton] at hb; exact absurd hb hbj
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj0 : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
    have hopj0 : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hgj' : gs'[j]? = some ⟨GateOp.or, [26 + i]⟩ := by simp [gs', List.getElem?_mapIdx, hg0j, patch]
    have hbj' : ∀ z ∈ ([26 + i] : List ℕ), z < 26 + j := fun z hz => by simp at hz; omega
    have hVi_eval' : ∀ x : List Bool, x.length = 26 → V gs' x (26 + i) = V gs x (26 + i) := fun x hx =>
      mapIdx_eval_avoid gs patch {j} hback hkeep x hx (26 + i) (by omega) (fun b hb => by
        have hbj_eq : b = j := Finset.mem_singleton.1 hb
        rw [hbj_eq]
        exact ⟨by omega, fun _ hic => by rw [Nat.add_sub_cancel_left] at hic; have := (inCone_lt ⟨gs, 0⟩ j i hic).1; omega⟩)
    apply core_contra gs' (26 + outG) (by rw [hgs'_len]; exact hsz) hmon' hback' hnn'
    · intro p l hp
      apply mapIdx_eval_up gs patch {j} j hback hback' hgs_eq hkeep (inp {p} {l}) (inp_len _ _) _ (26 + outG) (by omega) hbad_out (hacc p l hp)
      intro hVj
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0] at hVj
      have hVi0 := hwL_imp_i (inp {p} {l}) (inp_len _ _) (hVj wL (by rw [← hga0j, hwj_inp]; left; rfl))
      rw [orN gs' _ (inp_len _ _) j _ hgj' hbj' rfl]
      exact ⟨26 + i, by simp, by rw [hVi_eval' _ (inp_len _ _)]; exact hVi0⟩
    · intro Q hQ
      rw [Bool.eq_false_iff]; intro htr
      have hdn : V gs' (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
        intro hVj'
        rw [orN gs' _ (inp_len _ _) j _ hgj' hbj' rfl] at hVj'
        obtain ⟨z, hz, hVz'⟩ := hVj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rw [hz, hVi_eval' _ (inp_len _ _)] at hVz'
        have hVwL := reachesOr_V gs gs.length (26 + i) hback (inp Q (TQ Q)) (inp_len _ _) wL hwL_reach hVz'
        have hVwR := himpR (inp Q (TQ Q)) (inp_len _ _) hVz'
        rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0]
        intro z hz; rw [← hga0j, hwj_inp] at hz
        rcases hz with rfl | rfl; exact hVwL; exact hVwR
      have htr0 := mapIdx_eval_down gs patch {j} j hback hback' hgs_eq hkeep (inp Q (TQ Q)) (inp_len _ _) hdn (26 + outG) (by omega) hbad_out htr
      rw [hrej Q hQ] at htr0; cases htr0
  by_cases hY2 : 2 ≤ Y.card
  · obtain ⟨y1, hy1, y2, hy2, hy12⟩ := Finset.one_lt_card.1 (by omega : 1 < Y.card)
    have hB_sing : ∀ b ∈ B, b = z0 := fun b hb => unique_common_inc y1 y2 b z0 hy12
      (hok_YB y1 hy1 b hb) (hok_YB y2 hy2 b hb) (hok_YB y1 hy1 z0 hz0B) (hok_YB y2 hy2 z0 hz0B)
    apply collapse_j_to_i
    intro x hx hVi
    have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
    have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
    have hbi0 : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
    have hopi0 : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
    rw [andN_iff gs x hx i gs[i] hg0i hbi0 hopi0] at hVi
    have hVB := hVi uB (by rw [← hga0i, hu_inp]; right; rfl)
    obtain ⟨b, hbB, hxb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po x hx).1 hVB
    rw [hB_sing b hbB] at hxb
    exact orSetAvoid_sound gs gs.length hback x hx wR (by omega) ⟨z0, hz0R, hxb⟩
  · by_cases hZ2 : 2 ≤ Z.card
    · obtain ⟨z1, hz1, z2, hz2, hz12⟩ := Finset.one_lt_card.1 (by omega : 1 < Z.card)
      have hA_sing : ∀ a ∈ A, a = y0 := fun a ha => unique_common_inc z1 z2 a y0 hz12
        (hok_ZA z1 hz1 a ha) (hok_ZA z2 hz2 a ha) (hok_ZA z1 hz1 y0 hy0A) (hok_ZA z2 hz2 y0 hy0A)
      apply collapse_j_to_i
      intro x hx hVi
      have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
      have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
      have hbi0 : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
      have hopi0 : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
      rw [andN_iff gs x hx i gs[i] hg0i hbi0 hopi0] at hVi
      have hVA := hVi uA (by rw [← hga0i, hu_inp]; left; rfl)
      obtain ⟨a, haA, hxa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po x hx).1 hVA
      rw [hA_sing a haA] at hxa
      exact orSetAvoid_sound gs gs.length hback x hx wR (by omega) ⟨y0, hy0R, hxa⟩
    · have hY_sing : ∀ y ∈ Y, y = y0 := fun y hy => Finset.card_le_one.1 (by omega : Y.card ≤ 1) y hy y0 hy0Y
      have hZ_sing : ∀ z ∈ Z, z = z0 := fun z hz => Finset.card_le_one.1 (by omega : Z.card ≤ 1) z hz z0 hz0Z
      have hy0z0_ne : y0 ≠ z0 := fun heq => by
        have : y0 ∈ A ∩ B := Finset.mem_inter.2 ⟨hy0A, by rw [heq]; exact hz0B⟩
        rw [hX_empty] at this; cases this
      have hwR26 : 26 ≤ wR := by
        by_contra hlt26
        have hRc : R.card = 1 := by simp [R, orSetAvoid_lt gs gs.length wR (by omega)]
        have : 2 ≤ R.card := Finset.one_lt_card.2 ⟨y0, hy0R, z0, hz0R, hy0z0_ne⟩
        omega
      obtain ⟨gR, rfl⟩ : ∃ gR, wR = 26 + gR := ⟨wR - 26, by omega⟩
      have hgRj : gR < j := by omega
      have hgRi : gR ≠ i := fun heq => hwR_no_i.1 (by rw [heq])
      have hR_ns : ¬ ∃ z : Fin 26, ∀ r ∈ R, isInc26 r z = true := fun ⟨z, hz⟩ => by
        have h1 := hz y0 hy0R
        have h2 := hz z0 hz0R
        rw [isInc26_symm] at h2
        have hfl := isInc26_bipartite y0 z z0 h1 h2
        rw [hy0z0] at hfl; cases hfl
      have hgR_nb := nonStar_no_bypass gs outG hout hmon hback htwo hreach hrej i j hiA hjA hij hAP hi_no_bypass gR (by omega) hwR_po hR_ns
      have hgR_not_uA : uA ≠ 26 + gR ∧ (26 ≤ uA → ¬ InCone 26 ⟨gs, 0⟩ gR (uA - 26)) := by
        have hno_sub : ¬ (R ⊆ A) := fun hsub => by
          have hzA : z0 ∈ A := hsub hz0R
          have hzX : z0 ∈ A ∩ B := Finset.mem_inter.2 ⟨hzA, hz0B⟩
          rw [hX_empty] at hzX; cases hzX
        exact ⟨fun heq => hno_sub (orSetAvoid_sub_of_hit gs hgs_eq gR uA huA_po (Or.inl heq)),
          fun hu26 hic => hno_sub (orSetAvoid_sub_of_hit gs hgs_eq gR uA huA_po (Or.inr ⟨hu26, hic⟩))⟩
      have hgR_not_uB : uB ≠ 26 + gR ∧ (26 ≤ uB → ¬ InCone 26 ⟨gs, 0⟩ gR (uB - 26)) := by
        have hno_sub : ¬ (R ⊆ B) := fun hsub => by
          have hyB : y0 ∈ B := hsub hy0R
          have hyX : y0 ∈ A ∩ B := Finset.mem_inter.2 ⟨hy0A, hyB⟩
          rw [hX_empty] at hyX; cases hyX
        exact ⟨fun heq => hno_sub (orSetAvoid_sub_of_hit gs hgs_eq gR uB huB_po (Or.inl heq)),
          fun hu26 hic => hno_sub (orSetAvoid_sub_of_hit gs hgs_eq gR uB huB_po (Or.inr ⟨hu26, hic⟩))⟩
      let patch1 : ℕ → Gate → Gate := fun k g =>
        if k = gR then ⟨GateOp.or, []⟩
        else if k = i then ⟨GateOp.and, [y0.1, uB]⟩
        else if k = j then ⟨GateOp.and, [z0.1, uA]⟩
        else if gR < k ∧ k < j then
          match g.op with
          | GateOp.and => g
          | _ => ⟨GateOp.or, g.inputs.filter (· ≠ 26 + gR)⟩
        else g
      let gs1 := gs.mapIdx patch1
      have hgs1_len : gs1.length = gs.length := List.length_mapIdx
      have hmon1 : ∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        apply mapIdx_mono; intro k g hg
        have hk := hmon g (List.mem_of_getElem? hg)
        dsimp only [patch1]
        by_cases h1 : k = gR; · rw [ite_eq_left h1]; simp
        · by_cases h2 : k = i; · rw [ite_eq_right h1, ite_eq_left h2]; simp
          · by_cases h3' : k = j; · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3']; simp
            · by_cases h4 : gR < k ∧ k < j
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_left h4]
                cases hop : g.op with
                | and => exact hk
                | or => exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) (by simp [hk.2])⟩
                | _ => rcases hk.1 with h | h <;> rw [h] at hop <;> cases hop
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4]; exact hk
      have hback1 : ReadsBack 26 ⟨gs1, 0⟩ := by
        apply mapIdx_readsBack; intro k g hg u hu
        have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        have hga0 : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
        have hbk : ∀ z ∈ g.inputs, z < 26 + k := fun z hz => hback k hklen z (by rw [hga0]; exact hz)
        dsimp only [patch1] at hu
        by_cases h1 : k = gR; · rw [ite_eq_left h1] at hu; simp at hu
        · by_cases h2 : k = i
          · rw [ite_eq_right h1, ite_eq_left h2] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            have := y0.2; rcases hu with rfl | rfl <;> omega
          · by_cases h3' : k = j
            · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3'] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              have := z0.2; rcases hu with rfl | rfl <;> omega
            · by_cases h4 : gR < k ∧ k < j
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_left h4] at hu
                cases hop : g.op with
                | and => simp only [hop] at hu; exact hbk u hu
                | or => simp only [hop] at hu; exact hbk u (List.mem_of_mem_filter hu)
                | _ => rcases (hmon g (List.mem_of_getElem? hg)).1 with h | h <;> rw [h] at hop <;> cases hop
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4] at hu; exact hbk u hu
      have hgt_j_noread : ∀ k, j < k → k < gs.length → 26 + i ∉ (gateAt ⟨gs, 0⟩ k).inputs ∧ 26 + gR ∉ (gateAt ⟨gs, 0⟩ k).inputs := by
        intro k hjk hklen
        have hreach_k : reachesAvoiding gs j (26 + k) (26 + outG) := by
          by_cases hko : k = outG
          · subst hko; exact reachesAvoiding.base
          · exact inCone_gt_reachesAvoiding gs j k outG hjk ((hreach k hklen).resolve_left hko)
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
        refine ⟨fun hmem => ?_, fun hmem => ?_⟩
        · have := hback k hklen (26 + i) hmem
          exact hi_no_bypass (reachesAvoiding_trans gs j (26 + i) (26 + k) (26 + outG)
            (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hmem) this reachesAvoiding.base) hreach_k)
        · have := hback k hklen (26 + gR) hmem
          exact hgR_nb.2 (reachesAvoiding_trans gs j (26 + gR) (26 + k) (26 + outG)
            (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hmem) this reachesAvoiding.base) hreach_k)
      have hgs1_no_gR : ∀ k, gR < k → k < gs.length → 26 + gR ∉ (gateAt ⟨gs1, 0⟩ k).inputs := by
        intro k hgk hklen hmem
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
        have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
        rw [hga1k] at hmem
        dsimp only [patch1] at hmem
        rw [ite_eq_right (by omega)] at hmem
        by_cases hki : k = i
        · subst hki; rw [ite_eq_left rfl] at hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          have := y0.2; rcases hmem with heq | heq
          · omega
          · exact hgR_not_uB.1 heq.symm
        · rw [ite_eq_right hki] at hmem
          by_cases hkj : k = j
          · subst hkj; rw [ite_eq_left rfl] at hmem; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            have := z0.2; rcases hmem with heq | heq
            · omega
            · exact hgR_not_uA.1 heq.symm
          · rw [ite_eq_right hkj] at hmem
            by_cases hklt : k < j
            · rw [ite_eq_left ⟨hgk, hklt⟩] at hmem
              cases hop : gs[k].op with
              | and =>
                simp only [hop] at hmem
                have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, hop]
                exact hgR_nb.1 k hklen hkA (by omega) (by omega)
                  (inCone_direct ⟨gs, 0⟩ gR k hklen (by rw [hga0k]; exact hmem) hgk)
              | or => simp only [hop] at hmem; have := (List.mem_filter.1 hmem).2; simp at this
              | _ => rcases (hmon gs[k] (List.getElem_mem hklen)).1 with h | h <;> rw [h] at hop <;> cases hop
            · rw [ite_eq_right (fun h => hklt h.2)] at hmem
              exact (hgt_j_noread k (by omega) hklen).2 (by rw [hga0k]; exact hmem)
      have hagree_w : ∀ x : List Bool, x.length = 26 → ∀ w < 26 + gs.length, w ≠ 26 + gR → w ≠ 26 + i → w ≠ 26 + j →
          (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ gR (w - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ i (w - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ j (w - 26)) →
          V gs1 x w = V gs x w := by
        intro x hx w hw_lt hwg hwi hwj hno
        apply V_eq_of_agree_cone gs gs1 hback hgs1_len x hx w hw_lt
        intro c hc
        have hclen : c < gs.length := by
          rcases hc with heq | ⟨_, hic⟩
          · omega
          · exact (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).1.trans (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).2
        have hno_c : c ≠ gR ∧ c ≠ i ∧ c ≠ j := by
          rcases hc with heq | ⟨hu26, hic⟩
          · refine ⟨by omega, by omega, by omega⟩
          · refine ⟨fun e => by subst e; exact (hno hu26).1 hic, fun e => by subst e; exact (hno hu26).2.1 hic, fun e => by subst e; exact (hno hu26).2.2 hic⟩
        have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
        have hga0c : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
        have hpc : patch1 c gs[c] = gs[c] := by
          dsimp only [patch1]; rw [ite_eq_right hno_c.1, ite_eq_right hno_c.2.1, ite_eq_right hno_c.2.2]
          by_cases h4 : gR < c ∧ c < j
          · rw [ite_eq_left h4]
            cases hop : gs[c].op with
            | and => rfl
            | or =>
              have hc_no_gR : 26 + gR ∉ gs[c].inputs := fun hmem => by
                have hgc : gR < c := h4.1
                have hic_g := inCone_direct ⟨gs, 0⟩ gR c hclen (by rw [hga0c]; exact hmem) hgc
                rcases hc with heq | ⟨hu26, hic⟩
                · exact (hno (by omega)).1 (by rw [show w - 26 = c by omega]; exact hic_g)
                · exact (hno hu26).1 (inCone_trans ⟨gs, 0⟩ gR c (w - 26) hic_g hic)
              exact gate_mk_or_eq gs[c] hop _ (List.filter_eq_self.2 (fun z hz => by simp; intro heq; subst heq; exact hc_no_gR hz))
            | _ => rcases (hmon gs[c] (List.getElem_mem hclen)).1 with h | h <;> rw [h] at hop <;> cases hop
          · rw [ite_eq_right h4]
        simp [gs1, List.getElem?_mapIdx, hg0c, hpc]
      have hnn1 : ¬ ∃ a b : ℕ, (gateAt ⟨gs1, 0⟩ a).op = GateOp.and ∧
          (gateAt ⟨gs1, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs1, 0⟩ a b := by
        apply no_nested_and_of_all_and_pureOr gs1 0
        intro k hk hkA u hu
        rw [hgs1_len] at hk
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
        have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
        have hk_ngR : k ≠ gR := fun e => by
          subst e; rw [hga1k] at hkA; dsimp only [patch1] at hkA; rw [ite_eq_left rfl] at hkA; cases hkA
        have agree_cone_po : ∀ w < 26 + gs.length, pureOr gs w →
            (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ gR (w - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ i (w - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ j (w - 26)) →
            w ≠ 26 + gR → w ≠ 26 + i → w ≠ 26 + j → pureOr gs1 w := by
          intro w hw hpo hno hw1 hw2 hw3
          apply pureOr_of_agree_cone gs gs1 hback hgs1_len w hw hpo
          intro c hc
          have hclen : c < gs.length := by
            rcases hc with heq | ⟨_, hic⟩; omega; exact (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).1.trans (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).2
          have hnc : c ≠ gR ∧ c ≠ i ∧ c ≠ j := by
            rcases hc with heq | ⟨hu26, hic⟩
            · exact ⟨by omega, by omega, by omega⟩
            · exact ⟨fun e => by subst e; exact (hno hu26).1 hic, fun e => by subst e; exact (hno hu26).2.1 hic, fun e => by subst e; exact (hno hu26).2.2 hic⟩
          have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
          have hga0c : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
          have hpc : patch1 c gs[c] = gs[c] := by
            dsimp only [patch1]; rw [ite_eq_right hnc.1, ite_eq_right hnc.2.1, ite_eq_right hnc.2.2]
            by_cases h4 : gR < c ∧ c < j
            · rw [ite_eq_left h4]
              cases hop : gs[c].op with
              | and => rfl
              | or =>
                have hc_no_gR : 26 + gR ∉ gs[c].inputs := fun hmem => by
                  have hic_g := inCone_direct ⟨gs, 0⟩ gR c hclen (by rw [hga0c]; exact hmem) h4.1
                  rcases hc with heq | ⟨hu26, hic⟩
                  · have hc_eq : w - 26 = c := by omega
                    exact (hno (by omega)).1 (hc_eq ▸ hic_g)
                  · exact (hno hu26).1 (inCone_trans ⟨gs, 0⟩ gR c (w - 26) hic_g hic)
                exact gate_mk_or_eq gs[c] hop _ (List.filter_eq_self.2 (fun z hz => by simp only [decide_eq_true_eq]; exact fun heq => hc_no_gR (heq ▸ hz)))
              | _ => rcases (hmon gs[c] (List.getElem_mem hclen)).1 with h | h <;> rw [h] at hop <;> cases hop
            · rw [ite_eq_right h4]
          simp [gs1, List.getElem?_mapIdx, hg0c, hpc]
        by_cases hki : k = i
        · subst hki
          have hpk : patch1 k gs[k] = ⟨GateOp.and, [y0.1, uB]⟩ := by
            dsimp only [patch1]; rw [ite_eq_right hk_ngR, ite_eq_left rfl]
          rw [hga1k, hpk] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with hu1 | hu2
          · rw [hu1]; intro h; have := y0.2; omega
          · rw [hu2]; exact agree_cone_po uB (by omega) huB_po (fun hu26 => ⟨hgR_not_uB.2 hu26,
              fun hic => by have := (inCone_lt ⟨gs, 0⟩ k (uB - 26) hic).1; omega,
              fun hic => by have := (inCone_lt ⟨gs, 0⟩ j (uB - 26) hic).1; omega⟩) hgR_not_uB.1 (by omega) (by omega)
        · by_cases hkj : k = j
          · subst hkj
            have hpk : patch1 k gs[k] = ⟨GateOp.and, [z0.1, uA]⟩ := by
              dsimp only [patch1]; rw [ite_eq_right hk_ngR, ite_eq_right hki, ite_eq_left rfl]
            rw [hga1k, hpk] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with hu1 | hu2
            · rw [hu1]; intro h; have := z0.2; omega
            · rw [hu2]; exact agree_cone_po uA (by omega) huA_po (fun hu26 => ⟨hgR_not_uA.2 hu26,
                fun hic => by have := (inCone_lt ⟨gs, 0⟩ i (uA - 26) hic).1; omega,
                fun hic => by have := (inCone_lt ⟨gs, 0⟩ k (uA - 26) hic).1; omega⟩) hgR_not_uA.1 (by omega) (by omega)
          · have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by
              rw [hga1k] at hkA; dsimp only [patch1] at hkA
              rw [ite_eq_right hk_ngR, ite_eq_right hki, ite_eq_right hkj] at hkA
              by_cases h4 : gR < k ∧ k < j
              · rw [ite_eq_left h4] at hkA
                cases hop : gs[k].op with
                | and => rw [hga0k]; exact hop
                | or => simp [hop] at hkA
                | _ => rcases (hmon gs[k] (List.getElem_mem hk)).1 with h | h <;> rw [h] at hop <;> cases hop
              · rw [ite_eq_right h4] at hkA; rw [hga0k]; exact hkA
            have hpk : patch1 k gs[k] = gs[k] := by
              dsimp only [patch1]; rw [ite_eq_right hk_ngR, ite_eq_right hki, ite_eq_right hkj]
              by_cases h4 : gR < k ∧ k < j
              · rw [ite_eq_left h4]; have hop : gs[k].op = GateOp.and := (by rw [← hga0k]; exact hkA0); simp [hop]
              · rw [ite_eq_right h4]
            rw [hga1k, hpk] at hu
            have hu_lt : u < 26 + k := hback k hk u (by rw [hga0k]; exact hu)
            have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0k]; exact hu)
            have hno_u : (26 ≤ u → ¬ InCone 26 ⟨gs, 0⟩ gR (u - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ i (u - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ j (u - 26)) ∧
                u ≠ 26 + gR ∧ u ≠ 26 + i ∧ u ≠ 26 + j := by
              refine ⟨fun hu26 => ⟨fun hic => hgR_nb.1 k hk hkA0 hki hkj ((inCone_iff 26 ⟨gs, 0⟩ gR k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr hic⟩),
                fun hic => absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 ((inCone_iff 26 ⟨gs, 0⟩ i k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr hic⟩)).2) hkj,
                fun hic => absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i j k hij ((inCone_iff 26 ⟨gs, 0⟩ j k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr hic⟩))).2) hkj⟩,
                fun heq => hgR_nb.1 k hk hkA0 hki hkj (inCone_direct ⟨gs, 0⟩ gR k hk (by rw [hga0k, ← heq]; exact hu) (by omega)),
                fun heq => absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_direct ⟨gs, 0⟩ i k hk (by rw [hga0k, ← heq]; exact hu) (by omega))).2) hkj,
                fun heq => absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i j k hij (inCone_direct ⟨gs, 0⟩ j k hk (by rw [hga0k, ← heq]; exact hu) (by omega)))).2) hkj⟩
            exact agree_cone_po u (by omega) hpo_u hno_u.1 hno_u.2.1 hno_u.2.2.1 hno_u.2.2.2
      let i2 := if gR < i then i - 1 else i
      have hi2_lt : i2 < j := by dsimp only [i2]; split_ifs <;> omega
      let gNew : Gate := ⟨GateOp.or, [26 + i2, 26 + (j - 1)]⟩
      let gs2 := gatesMoveAfter gs1 gR j gNew
      have hgs2_len : gs2.length = gs.length := by rw [gatesMoveAfter_len gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2), hgs1_len]
      have hmon2 : ∀ g ∈ gs2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
        gatesMoveAfter_mono gs1 gR j gNew hmon1 (by simp [gNew])
      have hback2 : ReadsBack 26 ⟨gs2, 0⟩ :=
        gatesMoveAfter_readsBack gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) hback1 (fun z hz => by
          simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega)
      have hnn2 : ¬ ∃ a b : ℕ, (gateAt ⟨gs2, 0⟩ a).op = GateOp.and ∧
          (gateAt ⟨gs2, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs2, 0⟩ a b := by
        apply gatesMoveAfter_no_nested_and gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) hback1 rfl
          (fun m hm1 hm2 => hgs1_no_gR m hm1 (by rw [← hgs1_len]; exact hm2))
        · intro b hjb hblen hbA hic
          rw [hgs1_len] at hblen
          have hinc0 := inCone_of_eq_above gs gs1 j b hgs1_len (fun c hjc hc => by
            have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hc
            simp [gs1, List.getElem?_mapIdx, hg0c, patch1, show c ≠ gR by omega, show c ≠ i by omega,
              show c ≠ j by omega, show ¬ (gR < c ∧ c < j) by omega]) hjb hblen hic
          have hb0 : (gateAt ⟨gs, 0⟩ b).op = GateOp.and := by
            have hg0b : gs[b]? = some gs[b] := List.getElem?_eq_getElem hblen
            have hgb1 : gs1[b]? = some gs[b] := by
              simp [gs1, List.getElem?_mapIdx, hg0b, patch1, show b ≠ gR by omega, show b ≠ i by omega,
                show b ≠ j by omega, show ¬ (gR < b ∧ b < j) by omega]
            have : gateAt ⟨gs1, 0⟩ b = gs[b] := by simp [gateAt, List.getD_eq_getElem?_getD, hgb1]
            rw [gateAt_eq ⟨gs, 0⟩ b hblen, ← this]; exact hbA
          have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA hb0 hinc0).1
          omega
        · exact hnn1
      have hgt_agree : ∀ k, j < k → k < gs.length → gs1[k]? = gs[k]? := fun k hjk hk => by
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        simp [gs1, List.getElem?_mapIdx, hg0k, patch1, show k ≠ gR by omega, show k ≠ i by omega,
          show k ≠ j by omega, show ¬ (gR < k ∧ k < j) by omega]
      have hlo_lt_j : ∀ k, j < k → k < gs.length → ∀ u ∈ (gateAt ⟨gs, 0⟩ k).inputs, u < 26 + j →
          ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner gR u) = V gs x u := by
        intro k hjk hk u hu hu_lt x hx
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
        have hreach_k : reachesAvoiding gs j (26 + k) (26 + outG) := by
          by_cases hko : k = outG; subst hko; exact reachesAvoiding.base
          exact inCone_gt_reachesAvoiding gs j k outG hjk ((hreach k hk).resolve_left hko)
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
        have huk : u < 26 + k := hback k hk u hu
        have hug : u ≠ 26 + gR := fun e => (hgt_j_noread k hjk hk).2 (by rw [← e]; exact hu)
        have hui : u ≠ 26 + i := fun e => (hgt_j_noread k hjk hk).1 (by rw [← e]; exact hu)
        have hno_u : 26 ≤ u → ¬ InCone 26 ⟨gs, 0⟩ gR (u - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ i (u - 26) ∧ ¬ InCone 26 ⟨gs, 0⟩ j (u - 26) := fun hu26 =>
          ⟨fun hic => hgR_nb.2 (reachesAvoiding_trans gs j (26 + gR) (26 + k) (26 + outG)
            (reachesAvoiding_trans gs j (26 + gR) u (26 + k)
              (by have hueq : 26 + (u - 26) = u := (by omega); rw [← hueq]; exact reachesAvoiding_below_skip gs j gR (u - 26) (by omega) hic)
              (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hu) huk reachesAvoiding.base)) hreach_k),
           fun hic => hi_no_bypass (reachesAvoiding_trans gs j (26 + i) (26 + k) (26 + outG)
            (reachesAvoiding_trans gs j (26 + i) u (26 + k)
              (by have hueq : 26 + (u - 26) = u := (by omega); rw [← hueq]; exact reachesAvoiding_below_skip gs j i (u - 26) (by omega) hic)
              (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hu) huk reachesAvoiding.base)) hreach_k),
           fun hic => by have := (inCone_lt ⟨gs, 0⟩ j (u - 26) hic).1; omega⟩
        rw [gatesMoveAfter_eval_lt gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
          (fun c hc _ => hgs1_no_gR c hc (by omega)) x hx u (by omega) hug]
        exact hagree_w x hx u (by omega) hug hui (by omega) hno_u
      have hgs2_uA : ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner gR uA) = V gs x uA := fun x hx => by
        rw [gatesMoveAfter_eval_lt gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
          (fun c hc _ => hgs1_no_gR c hc (by omega)) x hx uA (by omega) hgR_not_uA.1]
        exact hagree_w x hx uA (by omega) hgR_not_uA.1 (by omega) (by omega) (fun hu26 =>
          ⟨hgR_not_uA.2 hu26, fun hic => by have := (inCone_lt ⟨gs, 0⟩ i (uA - 26) hic).1; omega,
           fun hic => by have := (inCone_lt ⟨gs, 0⟩ j (uA - 26) hic).1; omega⟩)
      have hgs2_uB : ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner gR uB) = V gs x uB := fun x hx => by
        rw [gatesMoveAfter_eval_lt gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) hback1 hback2
          (fun c hc _ => hgs1_no_gR c hc (by omega)) x hx uB (by omega) hgR_not_uB.1]
        exact hagree_w x hx uB (by omega) hgR_not_uB.1 (by omega) (by omega) (fun hu26 =>
          ⟨hgR_not_uB.2 hu26, fun hic => by have := (inCone_lt ⟨gs, 0⟩ i (uB - 26) hic).1; omega,
           fun hic => by have := (inCone_lt ⟨gs, 0⟩ j (uB - 26) hic).1; omega⟩)
      have hg2_i2 : gs2[i2]? = some ⟨GateOp.and, [y0.1, shiftMoveInner gR uB]⟩ := by
        have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
        have hg1i : gs1[i]? = some ⟨GateOp.and, [y0.1, uB]⟩ := by
          simp [gs1, List.getElem?_mapIdx, hg0i, patch1, show i ≠ gR by omega]
        by_cases hgRi' : gR < i
        · have hi2e : i2 = i - 1 := by dsimp only [i2]; rw [ite_eq_left hgRi']
          have hm := gatesMoveAfter_getElem_mid gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) i2 (by omega) (by omega)
          have hadd : i2 + 1 = i := by omega
          rw [hadd, hg1i] at hm
          have hsy : shiftMoveInner gR y0.1 = y0.1 := by unfold shiftMoveInner; rw [ite_eq_left (by have := y0.2; omega)]
          simpa [gateMapInner, hsy] using hm
        · have hi2e : i2 = i := by dsimp only [i2]; rw [ite_eq_right hgRi']
          have hg1 := gatesMoveAfter_getElem_lt gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) i (by omega)
          have hsb : shiftMoveInner gR uB = uB := by unfold shiftMoveInner; rw [ite_eq_left (by omega)]
          rw [hi2e, hsb]; rw [hg1i] at hg1; exact hg1
      have hg2_jm1 : gs2[j - 1]? = some ⟨GateOp.and, [z0.1, shiftMoveInner gR uA]⟩ := by
        have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
        have hg1j : gs1[j]? = some ⟨GateOp.and, [z0.1, uA]⟩ := by
          simp [gs1, List.getElem?_mapIdx, hg0j, patch1, show j ≠ gR by omega, show j ≠ i by omega]
        have hm := gatesMoveAfter_getElem_mid gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2) (j - 1) (by omega) (by omega)
        have hadd : j - 1 + 1 = j := by omega
        rw [hadd, hg1j] at hm
        have hsz0 : shiftMoveInner gR z0.1 = z0.1 := by unfold shiftMoveInner; rw [ite_eq_left (by have := z0.2; omega)]
        simpa [gateMapInner, hsz0] using hm
      have hgj2 : gs2[j]? = some gNew := gatesMoveAfter_getElem_dst gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2)
      have hbj2 : ∀ z ∈ gNew.inputs, z < 26 + j := fun z hz => by
        simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega
      have hbi2 : ∀ z ∈ ([y0.1, shiftMoveInner gR uB] : List ℕ), z < 26 + i2 := fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        have := y0.2; rcases hz with rfl | rfl
        · omega
        · unfold shiftMoveInner; dsimp only [i2]; split_ifs <;> omega
      have hbjm1 : ∀ z ∈ ([z0.1, shiftMoveInner gR uA] : List ℕ), z < 26 + (j - 1) := fun z hz => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        have := z0.2; rcases hz with rfl | rfl
        · omega
        · unfold shiftMoveInner; split_ifs <;> omega
      have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
      have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
      have hbj0 : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
      have hopj0 : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
      have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
      have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
      have hbi0 : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
      have hopi0 : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
      apply core_contra gs2 (26 + outG) (by rw [hgs2_len]; exact hsz) hmon2 hback2 hnn2
      · intro p l hp
        refine gatesMoveAfter_eval_up_ge_rel gs gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2)
          hgs1_len hgs_eq hback hback2 hgt_agree (inp {p} {l}) (inp_len _ _)
          (fun k hjk hk u hu hult hv => by rw [hlo_lt_j k hjk hk u hu hult _ (inp_len _ _)]; exact hv)
          ?_ outG (by omega) (by omega) (hacc p l hp)
        intro hVj
        rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0] at hVj
        have hVi0 := hwL_imp_i (inp {p} {l}) (inp_len _ _) (hVj wL (by rw [← hga0j, hwj_inp]; left; rfl))
        have hVwR := hVj (26 + gR) (by rw [← hga0j, hwj_inp]; right; rfl)
        rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi0 hopi0] at hVi0
        have hVA := hVi0 uA (by rw [← hga0i, hu_inp]; left; rfl)
        have hVB := hVi0 uB (by rw [← hga0i, hu_inp]; right; rfl)
        obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 hVA
        obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
        obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback (26 + gR) (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
        obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
        rw [orN gs2 _ (inp_len _ _) j gNew hgj2 hbj2 rfl]
        simp only [Finset.mem_union] at hc
        rcases hc with (hc | hc) | hc
        · rw [hX_empty] at hc; cases hc
        · rw [hY_sing c hc] at hpc
          refine ⟨26 + i2, by simp [gNew], ?_⟩
          rw [andN_iff gs2 _ (inp_len _ _) i2 _ hg2_i2 hbi2 rfl]
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact y0.2)]; exact hpc
          · rw [hgs2_uB _ (inp_len _ _)]; exact hVB
        · rw [hZ_sing c hc] at hpc
          refine ⟨26 + (j - 1), by simp [gNew], ?_⟩
          rw [andN_iff gs2 _ (inp_len _ _) (j - 1) _ hg2_jm1 hbjm1 rfl]
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact z0.2)]; exact hpc
          · rw [hgs2_uA _ (inp_len _ _)]; exact hVA
      · intro Q hQ
        rw [Bool.eq_false_iff]; intro htr
        have hdn : V gs2 (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
          intro hVj2
          rw [orN gs2 _ (inp_len _ _) j gNew hgj2 hbj2 rfl] at hVj2
          obtain ⟨z, hz, hVz2⟩ := hVj2
          simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · rw [andN_iff gs2 _ (inp_len _ _) i2 _ hg2_i2 hbi2 rfl] at hVz2
            have hVy0 := hVz2 y0.1 (by simp)
            have hVuB := hVz2 (shiftMoveInner gR uB) (by simp)
            have hqy0 : qHit Q y0 = true := by
              have hv0 : V gs2 (inp Q (TQ Q)) y0.1 = (inp Q (TQ Q)).getD y0.1 false := by
                unfold V; exact getD_wiresFrom gs2 _ _ (by rw [inp_len]; exact y0.2)
              rw [← qHit_eq_inp_getD, ← hv0, hVy0]
            rw [hgs2_uB _ (inp_len _ _)] at hVuB
            obtain ⟨b, hbB, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVuB
            rw [qHit_eq_inp_getD] at hqb
            exact absurd ⟨hqy0, hqb⟩ (inc_false_on_quad y0 b (hok_YB y0 hy0Y b hbB) Q)
          · rw [andN_iff gs2 _ (inp_len _ _) (j - 1) _ hg2_jm1 hbjm1 rfl] at hVz2
            have hVz0 := hVz2 z0.1 (by simp)
            have hVuA := hVz2 (shiftMoveInner gR uA) (by simp)
            have hqz0 : qHit Q z0 = true := by
              have hv0 : V gs2 (inp Q (TQ Q)) z0.1 = (inp Q (TQ Q)).getD z0.1 false := by
                unfold V; exact getD_wiresFrom gs2 _ _ (by rw [inp_len]; exact z0.2)
              rw [← qHit_eq_inp_getD, ← hv0, hVz0]
            rw [hgs2_uA _ (inp_len _ _)] at hVuA
            obtain ⟨a, haA, hqa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp Q (TQ Q)) (inp_len _ _)).1 hVuA
            rw [qHit_eq_inp_getD] at hqa
            exact absurd ⟨hqz0, hqa⟩ (inc_false_on_quad z0 a (hok_ZA z0 hz0Z a haA) Q)
        have htr0 := gatesMoveAfter_eval_down_ge_rel gs gs1 gR j gNew hgRj (by rw [hgs1_len]; exact hlt.2)
          hgs1_len hgs_eq hback hback2 hgt_agree (inp Q (TQ Q)) (inp_len _ _)
          (fun k hjk hk u hu hult hv => by rw [← hlo_lt_j k hjk hk u hu hult _ (inp_len _ _)]; exact hv)
          hdn outG (by omega) (by omega) htr
        rw [hrej Q hQ] at htr0; cases htr0

end L1961


namespace L1961

set_option maxHeartbeats 800000 in
lemma case2_sub7 (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j uA uB wL wR : ℕ)
    (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG))
    (hu_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ i).inputs ↔ w = uA ∨ w = uB)
    (hwL_reach : reachesOr gs gs.length (26 + i) wL)
    (hwR_lt : wR < 26 + j)
    (hwR_no_i : wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26)))
    (hwj_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR)
    (p0 l0 : Fin 26)
    (hp0X : p0 ∈ orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length uB)
    (hl0Y : l0 ∈ orSetAvoid gs gs.length uA ∩ orSetAvoid gs gs.length wR)
    (hZ_empty : orSetAvoid gs gs.length uB ∩ orSetAvoid gs gs.length wR = ∅)
    (hnok_AR : ¬ okQuad (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length wR))
    (hnok_BR : ¬ okQuad (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR))
    (h3 : okQuad3 (orSetAvoid gs gs.length uA) (orSetAvoid gs gs.length uB) (orSetAvoid gs gs.length wR)) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hil : i < gs.length := by omega
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  have hpos : ∀ g ∈ gs, 0 < g.inputs.length := fun g hg => by rw [(htwo g hg).1]; omega
  let A := orSetAvoid gs gs.length uA
  let B := orSetAvoid gs gs.length uB
  let R := orSetAvoid gs gs.length wR
  let X := A ∩ B
  let Y := A ∩ R
  let S_L := orSetAvoid gs i wL
  have hp0A : p0 ∈ A := (Finset.mem_inter.1 hp0X).1
  have hp0B : p0 ∈ B := (Finset.mem_inter.1 hp0X).2
  have hl0A : l0 ∈ A := (Finset.mem_inter.1 hl0Y).1
  have hl0R : l0 ∈ R := (Finset.mem_inter.1 hl0Y).2
  have huA_lt : uA < 26 + i := hback i hil uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_lt : uB < 26 + i := hback i hil uB ((hu_inp uB).2 (Or.inr rfl))
  have hwL_lt : wL < 26 + j := hback j hlt.2 wL ((hwj_inp wL).2 (Or.inl rfl))
  have huA_po : pureOr gs uA := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_po : pureOr gs uB := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uB ((hu_inp uB).2 (Or.inr rfl))
  have hwR_po : pureOr gs wR :=
    pureOr_wR gs hmon hback i j wR hiA hjA hij hAP ((hwj_inp wR).2 (Or.inr rfl)) hwR_no_i
  have hB_ne : B.Nonempty := orSetAvoid_nonempty gs hback hpos uB (by omega) huB_po
  have hR_ne : R.Nonempty := orSetAvoid_nonempty gs hback hpos wR (by omega) hwR_po
  have hok_XR : okQuad X R := okQuad_of_okQuad3_inter A B R h3
  have hok_YB : okQuad Y B := okQuad_of_okQuad3_interL A B R h3
  have hX_sing : ∀ x ∈ X, x = p0 := by
    intro x hx
    by_contra hxne
    have hR_sing : ∀ r ∈ R, r = l0 := fun r hr => unique_common_inc x p0 r l0 hxne
      (hok_XR x hx r hr) (hok_XR p0 hp0X r hr) (hok_XR x hx l0 hl0R) (hok_XR p0 hp0X l0 hl0R)
    apply hnok_BR
    intro b hb r hr
    rw [hR_sing r hr, isInc26_symm]
    exact hok_YB l0 hl0Y b hb
  have hY_sing : ∀ y ∈ Y, y = l0 := by
    intro y hy
    by_contra hyne
    have hB_sing : ∀ b ∈ B, b = p0 := fun b hb => unique_common_inc y l0 b p0 hyne
      (hok_YB y hy b hb) (hok_YB l0 hl0Y b hb) (hok_YB y hy p0 hp0B) (hok_YB l0 hl0Y p0 hp0B)
    apply hnok_BR
    intro b hb r hr
    rw [hB_sing b hb]
    exact hok_XR p0 hp0X r hr
  have hp0l0 : isInc26 p0 l0 = true := hok_XR p0 hp0X l0 hl0R
  have hp0l0_ne : p0 ≠ l0 := fun heq => by
    have : p0 ∈ B ∩ R := Finset.mem_inter.2 ⟨hp0B, by rw [heq]; exact hl0R⟩
    rw [hZ_empty] at this; cases this
  have huA26 : 26 ≤ uA := by
    by_contra hlt26
    have hAc : A.card = 1 := by simp [A, orSetAvoid_lt gs gs.length uA (by omega)]
    have : 2 ≤ A.card := Finset.one_lt_card.2 ⟨p0, hp0A, l0, hl0A, hp0l0_ne⟩
    omega
  obtain ⟨gA, rfl⟩ : ∃ gA, uA = 26 + gA := ⟨uA - 26, by omega⟩
  have hgAi : gA < i := by omega
  have hA_ns : ¬ ∃ z : Fin 26, ∀ a ∈ A, isInc26 a z = true := fun ⟨z, hz⟩ => by
    have h1 := hz p0 hp0A
    have h2 := hz l0 hl0A
    rw [isInc26_symm] at h2
    have hfl := isInc26_bipartite p0 z l0 h1 h2
    rw [hp0l0] at hfl; cases hfl
  have hgA_nb := nonStar_no_bypass gs outG hout hmon hback htwo hreach hrej i j hiA hjA hij hAP hi_no_bypass gA (by omega) huA_po hA_ns
  have hok_SL_R : okQuad S_L R := by
    intro s hs r hr; by_contra hne
    have hfl : isInc26 s r = false := by cases h : isInc26 s r <;> simp_all
    obtain ⟨Q, hQ, hqs, hqr⟩ := pair_in_quad s r hfl
    have hVwL : V gs (inp Q (TQ Q)) wL = true :=
      orSetAvoid_sound gs i hback (inp Q (TQ Q)) (inp_len _ _) wL (by omega) ⟨s, hs, by rw [qHit_eq_inp_getD, hqs]⟩
    have hVwR : V gs (inp Q (TQ Q)) wR = true :=
      orSetAvoid_sound gs gs.length hback (inp Q (TQ Q)) (inp_len _ _) wR (by omega) ⟨r, hr, by rw [qHit_eq_inp_getD, hqr]⟩
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
    have hbj : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
    have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
    have hVj := (andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj).2 (fun z hz => by
      rw [← hga0j, hwj_inp] at hz; rcases hz with rfl | rfl; exact hVwL; exact hVwR)
    rw [hjQ Q hQ] at hVj; cases hVj
  have hgA_not_wL : ¬ reachesAvoiding gs i (26 + gA) wL := by
    intro hr
    have hsub := reachesAvoiding_wL_sub_orSet gs hmon i j wL hiA hjA hij hAP ((hwj_inp wL).2 (Or.inl rfl)) hwL_lt gA (by omega) hr
    exact hnok_AR (fun a ha r hrR => hok_SL_R a (hsub ha) r hrR)
  have hwL_ne_gA : wL ≠ 26 + gA := fun heq => hgA_not_wL (by rw [heq]; exact reachesAvoiding.base)
  let wL' := if wL = 26 + i then p0.1 else wL
  have hwL'_ne_gA : wL' ≠ 26 + gA := by dsimp only [wL']; split_ifs; have := p0.2; omega; exact hwL_ne_gA
  have hwL'_lt : wL' < 26 + j := by dsimp only [wL']; split_ifs; have := p0.2; omega; exact hwL_lt
  let patch1 : ℕ → Gate → Gate := fun k g =>
    if k < gA then g
    else if k = gA then ⟨GateOp.or, []⟩
    else if k < i then
      match g.op with
      | GateOp.and => g
      | _ => ⟨GateOp.or, g.inputs.filter (· ≠ 26 + gA)⟩
    else if k = i then ⟨GateOp.and, [l0.1, uB]⟩
    else if k < j then
      match g.op with
      | GateOp.and => g
      | _ => ⟨GateOp.or, (g.inputs.map (fun w => if w = 26 + i then p0.1 else w)).filter (· ≠ 26 + gA)⟩
    else if k = j then ⟨GateOp.and, [wL', wR]⟩
    else g
  let gs1 := gs.mapIdx patch1
  have hgs1_len : gs1.length = gs.length := List.length_mapIdx
  have hmon1 : ∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    apply mapIdx_mono; intro k g hg
    have hk := hmon g (List.mem_of_getElem? hg)
    dsimp only [patch1]
    by_cases h1 : k < gA; · rw [ite_eq_left h1]; exact hk
    · by_cases h2 : k = gA; · rw [ite_eq_right h1, ite_eq_left h2]; simp
      · by_cases h3' : k < i
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3']
          cases hop : g.op with
          | and => exact hk
          | or => exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) (by simp [hk.2])⟩
          | _ => rcases hk.1 with h | h <;> rw [h] at hop <;> cases hop
        · by_cases h4 : k = i; · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_left h4]; simp
          · by_cases h5 : k < j
            · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4, ite_eq_left h5]
              cases hop : g.op with
              | and => exact hk
              | or => exact ⟨Or.inr rfl, le_trans (List.length_filter_le _ _) (by simp [hk.2])⟩
              | _ => rcases hk.1 with h | h <;> rw [h] at hop <;> cases hop
            · by_cases h6 : k = j
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4, ite_eq_right h5, ite_eq_left h6]; simp
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4, ite_eq_right h5, ite_eq_right h6]; exact hk
  have hback1 : ReadsBack 26 ⟨gs1, 0⟩ := by
    apply mapIdx_readsBack; intro k g hg u hu
    have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hga0 : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
    have hbk : ∀ z ∈ g.inputs, z < 26 + k := fun z hz => hback k hklen z (by rw [hga0]; exact hz)
    dsimp only [patch1] at hu
    by_cases h1 : k < gA; · rw [ite_eq_left h1] at hu; exact hbk u hu
    · by_cases h2 : k = gA; · rw [ite_eq_right h1, ite_eq_left h2] at hu; simp at hu
      · by_cases h3' : k < i
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3'] at hu
          cases hop : g.op with
          | and => simp only [hop] at hu; exact hbk u hu
          | or => simp only [hop] at hu; exact hbk u (List.mem_of_mem_filter hu)
          | _ => rcases (hmon g (List.mem_of_getElem? hg)).1 with h | h <;> rw [h] at hop <;> cases hop
        · by_cases h4 : k = i
          · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_left h4] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            have := l0.2; rcases hu with rfl | rfl <;> omega
          · by_cases h5 : k < j
            · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4, ite_eq_left h5] at hu
              cases hop : g.op with
              | and => simp only [hop] at hu; exact hbk u hu
              | or =>
                simp only [hop] at hu
                obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hu)
                have := hbk w hw; have := p0.2; split_ifs <;> omega
              | _ => rcases (hmon g (List.mem_of_getElem? hg)).1 with h | h <;> rw [h] at hop <;> cases hop
            · by_cases h6 : k = j
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4, ite_eq_right h5, ite_eq_left h6] at hu
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl <;> omega
              · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right h4, ite_eq_right h5, ite_eq_right h6] at hu
                exact hbk u hu
  have hgt_j_noread : ∀ k, j < k → k < gs.length → 26 + i ∉ (gateAt ⟨gs, 0⟩ k).inputs ∧ 26 + gA ∉ (gateAt ⟨gs, 0⟩ k).inputs := by
    intro k hjk hklen
    have hreach_k : reachesAvoiding gs j (26 + k) (26 + outG) := by
      by_cases hko : k = outG; subst hko; exact reachesAvoiding.base
      exact inCone_gt_reachesAvoiding gs j k outG hjk ((hreach k hklen).resolve_left hko)
    have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
    have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · have := hback k hklen (26 + i) hmem
      exact hi_no_bypass (reachesAvoiding_trans gs j (26 + i) (26 + k) (26 + outG)
        (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hmem) this reachesAvoiding.base) hreach_k)
    · have := hback k hklen (26 + gA) hmem
      exact hgA_nb.2 (reachesAvoiding_trans gs j (26 + gA) (26 + k) (26 + outG)
        (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hmem) this reachesAvoiding.base) hreach_k)
  have hgs1_no_gA : ∀ k, gA < k → k < gs.length → 26 + gA ∉ (gateAt ⟨gs1, 0⟩ k).inputs := by
    intro k hgk hklen hmem
    have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
    have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
    have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
    rw [hga1k] at hmem; dsimp only [patch1] at hmem
    rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hmem
    by_cases hki : k < i
    · rw [ite_eq_left hki] at hmem
      cases hop : gs[k].op with
      | and =>
        simp only [hop] at hmem
        have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, hop]
        exact hgA_nb.1 k hklen hkA (by omega) (by omega)
          (inCone_direct ⟨gs, 0⟩ gA k hklen (by rw [hga0k]; exact hmem) hgk)
      | or => simp only [hop] at hmem; have := (List.mem_filter.1 hmem).2; simp at this
      | _ => rcases (hmon gs[k] (List.getElem_mem hklen)).1 with h | h <;> rw [h] at hop <;> cases hop
    · rw [ite_eq_right hki] at hmem
      by_cases hkie : k = i
      · subst hkie; rw [ite_eq_left rfl] at hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        have := l0.2; rcases hmem with heq | heq
        · omega
        · have hsub_AB : ¬ (A ⊆ B) := fun hsub => by
            have : l0 ∈ B ∩ R := Finset.mem_inter.2 ⟨hsub hl0A, hl0R⟩
            rw [hZ_empty] at this; cases this
          exact hsub_AB (orSetAvoid_sub_of_hit gs hgs_eq gA uB huB_po (Or.inl heq.symm))
      · rw [ite_eq_right hkie] at hmem
        by_cases hkj : k < j
        · rw [ite_eq_left hkj] at hmem
          cases hop : gs[k].op with
          | and =>
            simp only [hop] at hmem
            have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, hop]
            exact hgA_nb.1 k hklen hkA hkie (by omega)
              (inCone_direct ⟨gs, 0⟩ gA k hklen (by rw [hga0k]; exact hmem) hgk)
          | or => simp only [hop] at hmem; have := (List.mem_filter.1 hmem).2; simp at this
          | _ => rcases (hmon gs[k] (List.getElem_mem hklen)).1 with h | h <;> rw [h] at hop <;> cases hop
        · rw [ite_eq_right hkj] at hmem
          by_cases hkje : k = j
          · subst hkje; rw [ite_eq_left rfl] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
            rcases hmem with heq | heq
            · exact hwL'_ne_gA heq.symm
            · have hsub_AR : ¬ (A ⊆ R) := fun hsub => by
                have hp0R : p0 ∈ R := hsub hp0A
                have : p0 ∈ B ∩ R := Finset.mem_inter.2 ⟨hp0B, hp0R⟩
                rw [hZ_empty] at this; cases this
              exact hsub_AR (orSetAvoid_sub_of_hit gs hgs_eq gA wR hwR_po (Or.inl heq.symm))
          · rw [ite_eq_right hkje] at hmem
            exact (hgt_j_noread k (by omega) hklen).2 (by rw [hga0k]; exact hmem)
  have hsub_AR : ¬ (A ⊆ R) := fun hsub => by
    have : p0 ∈ B ∩ R := Finset.mem_inter.2 ⟨hp0B, hsub hp0A⟩
    rw [hZ_empty] at this; cases this
  have hwR_no_gA : wR ≠ 26 + gA ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ gA (wR - 26)) :=
    ⟨fun heq => hsub_AR (orSetAvoid_sub_of_hit gs hgs_eq gA wR hwR_po (Or.inl heq)),
     fun hw26 hic => hsub_AR (orSetAvoid_sub_of_hit gs hgs_eq gA wR hwR_po (Or.inr ⟨hw26, hic⟩))⟩
  have hgA_not_wL_lt : wL ≠ 26 + gA := hwL_ne_gA
  have hsub_AB : ¬ (A ⊆ B) := fun hsub => by
    have : l0 ∈ B ∩ R := Finset.mem_inter.2 ⟨hsub hl0A, hl0R⟩
    rw [hZ_empty] at this; cases this
  have hgA_not_uB : uB ≠ 26 + gA ∧ (26 ≤ uB → ¬ InCone 26 ⟨gs, 0⟩ gA (uB - 26)) :=
    ⟨fun heq => hsub_AB (orSetAvoid_sub_of_hit gs hgs_eq gA uB huB_po (Or.inl heq)),
     fun hu26 hic => hsub_AB (orSetAvoid_sub_of_hit gs hgs_eq gA uB huB_po (Or.inr ⟨hu26, hic⟩))⟩
  have hno_in_and : ∀ k, k < gs.length → k ≠ j → k ≠ i → (gateAt ⟨gs, 0⟩ k).op = GateOp.and →
      26 + gA ∉ (gateAt ⟨gs, 0⟩ k).inputs ∧ 26 + i ∉ (gateAt ⟨gs, 0⟩ k).inputs := by
    intro k hklen hkj hki hkA
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · have hgk : gA < k := by have := hback k hklen (26 + gA) hmem; omega
      exact hgA_nb.1 k hklen hkA hki hkj (inCone_direct ⟨gs, 0⟩ gA k hklen hmem hgk)
    · have hik : i < k := by have := hback k hklen (26 + i) hmem; omega
      exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA (inCone_direct ⟨gs, 0⟩ i k hklen hmem hik)).2) hkj
  have hpo_below_j : ∀ w : ℕ, w < 26 + j → w ≠ 26 + i →
      (∀ a < j, (gateAt ⟨gs, 0⟩ a).op = GateOp.and → a ≠ i → w ≠ 26 + a ∧ (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ a (w - 26))) →
      pureOr gs1 w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwlt hwi hno hw26
      obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      have hklen : k < gs.length := by omega
      have hki : k ≠ i := by omega
      have hnotA : (gateAt ⟨gs, 0⟩ k).op ≠ GateOp.and := fun hka => (hno k (by omega) hka hki).1 rfl
      have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
      have hkop0 : gs[k].op = GateOp.or := by
        rcases (hmon gs[k] (List.getElem_mem hklen)).1 with h | h
        · rw [hga0, h] at hnotA; exact absurd rfl hnotA
        · exact h
      have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
      have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
      by_cases h1 : k < gA
      · have hpk : patch1 k gs[k] = gs[k] := by dsimp only [patch1]; rw [ite_eq_left h1]
        apply pureOr_step gs1 k (by rw [hgs1_len]; exact hklen) (by rw [hga1k, hpk]; exact hkop0) _ hw26
        intro u hu; rw [hga1k, hpk] at hu
        have hu_lt := hback k hklen u (by rw [hga0]; exact hu)
        apply ih u hu_lt (by omega) (by omega)
        intro a ha haA hai
        refine ⟨fun heq => (hno a ha haA hai).2 (by omega) (by
          rw [Nat.add_sub_cancel_left]; exact inCone_direct ⟨gs, 0⟩ a k hklen (by rw [hga0, ← heq]; exact hu) (by omega)),
          fun hu26 hic => (hno a ha haA hai).2 (by omega) (by
            rw [Nat.add_sub_cancel_left]; exact (inCone_iff 26 ⟨gs, 0⟩ a k hklen).2 ⟨u, by rw [hga0]; exact hu, hu26, hu_lt, Or.inr hic⟩)⟩
      · by_cases h2 : k = gA
        · subst h2
          have hpk : patch1 k gs[k] = ⟨GateOp.or, []⟩ := by dsimp only [patch1]; rw [ite_eq_right h1, ite_eq_left rfl]
          apply pureOr_step gs1 k (by rw [hgs1_len]; exact hklen) (by rw [hga1k, hpk]) _ hw26
          intro u hu; rw [hga1k, hpk] at hu; simp at hu
        · by_cases h3' : k < i
          · have hpk : patch1 k gs[k] = ⟨GateOp.or, gs[k].inputs.filter (· ≠ 26 + gA)⟩ := by
              dsimp only [patch1]; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3', hkop0]
            apply pureOr_step gs1 k (by rw [hgs1_len]; exact hklen) (by rw [hga1k, hpk]) _ hw26
            intro u hu; rw [hga1k, hpk] at hu
            have hu_mem := List.mem_of_mem_filter hu
            have hu_lt := hback k hklen u (by rw [hga0]; exact hu_mem)
            apply ih u hu_lt (by omega) (by omega)
            intro a ha haA hai
            refine ⟨fun heq => (hno a ha haA hai).2 (by omega) (by
              rw [Nat.add_sub_cancel_left]; exact inCone_direct ⟨gs, 0⟩ a k hklen (by rw [hga0, ← heq]; exact hu_mem) (by omega)),
              fun hu26 hic => (hno a ha haA hai).2 (by omega) (by
                rw [Nat.add_sub_cancel_left]; exact (inCone_iff 26 ⟨gs, 0⟩ a k hklen).2 ⟨u, by rw [hga0]; exact hu_mem, hu26, hu_lt, Or.inr hic⟩)⟩
          · have hpk : patch1 k gs[k] = ⟨GateOp.or, (gs[k].inputs.map (fun w => if w = 26 + i then p0.1 else w)).filter (· ≠ 26 + gA)⟩ := by
              dsimp only [patch1]; rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3', ite_eq_right hki, ite_eq_left (by omega : k < j), hkop0]
            apply pureOr_step gs1 k (by rw [hgs1_len]; exact hklen) (by rw [hga1k, hpk]) _ hw26
            intro u hu; rw [hga1k, hpk] at hu
            obtain ⟨z, hz, heqz⟩ := List.mem_map.1 (List.mem_of_mem_filter hu)
            by_cases hzi : z = 26 + i
            · rw [ite_eq_left hzi] at heqz; rw [← heqz]; intro h; have := p0.2; omega
            · rw [ite_eq_right hzi] at heqz; rw [← heqz]
              have hz_lt := hback k hklen z (by rw [hga0]; exact hz)
              apply ih z hz_lt (by omega) hzi
              intro a ha haA hai
              refine ⟨fun heq => (hno a ha haA hai).2 (by omega) (by
                rw [Nat.add_sub_cancel_left]; exact inCone_direct ⟨gs, 0⟩ a k hklen (by rw [hga0, ← heq]; exact hz) (by omega)),
                fun hu26 hic => (hno a ha haA hai).2 (by omega) (by
                  rw [Nat.add_sub_cancel_left]; exact (inCone_iff 26 ⟨gs, 0⟩ a k hklen).2 ⟨z, by rw [hga0]; exact hz, hu26, hz_lt, Or.inr hic⟩)⟩
  have hnn1 : ¬ ∃ a b : ℕ, (gateAt ⟨gs1, 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs1, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs1, 0⟩ a b := by
    apply no_nested_and_of_all_and_pureOr gs1 0
    intro k hk hkA u hu
    rw [hgs1_len] at hk
    have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
    have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, gs1, List.getElem?_mapIdx, hg0k]
    by_cases hki : k = i
    · subst hki
      have hpk : patch1 k gs[k] = ⟨GateOp.and, [l0.1, uB]⟩ := by
        dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      rw [hga1k, hpk] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu1 | hu2
      · rw [hu1]; intro h; have := l0.2; omega
      · rw [hu2]; exact hpo_below_j uB (by omega) (by omega) (fun a _ haA _ =>
          ⟨(fun heq => by have := huB_po (by omega); rw [heq, Nat.add_sub_cancel_left] at this; rw [this.2.1] at haA; cases haA),
           (fun hu26 hic => by have := huB_po hu26; rw [this.2.2 a hic] at haA; cases haA)⟩)
    · by_cases hkj : k = j
      · subst hkj
        have hpk : patch1 k gs[k] = ⟨GateOp.and, [wL', wR]⟩ := by
          dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right hki, ite_eq_right (by omega), ite_eq_left rfl]
        rw [hga1k, hpk] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with hu1 | hu2
        · rw [hu1]; have hwL'_ni : wL' ≠ 26 + i := by dsimp only [wL']; split_ifs; have := p0.2; omega; assumption
          exact hpo_below_j wL' hwL'_lt hwL'_ni (fun a ha haA hai => by
            refine ⟨fun heq => ?_, fun hu26 hic => ?_⟩
            · dsimp only [wL'] at heq; split_ifs at heq
              · have := p0.2; omega
              · have := inCone_direct ⟨gs, 0⟩ a k hk (by rw [← heq]; exact (hwj_inp wL).2 (Or.inl rfl)) (by omega)
                exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij haA hjA this).1) hai
            · dsimp only [wL'] at hu26 hic; split_ifs at hu26 hic
              · have := p0.2; omega
              · have := (inCone_iff 26 ⟨gs, 0⟩ a k hk).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hu26, hwL_lt, Or.inr hic⟩
                exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij haA hjA this).1) hai)
        · rw [hu2]; exact hpo_below_j wR hwR_lt hwR_no_i.1 (fun a _ haA _ =>
            ⟨(fun heq => by have := hwR_po (by omega); rw [heq, Nat.add_sub_cancel_left] at this; rw [this.2.1] at haA; cases haA),
             (fun hu26 hic => by have := hwR_po hu26; rw [this.2.2 a hic] at haA; cases haA)⟩)
      · have hkgA : k ≠ gA := fun e => by
          subst e; rw [hga1k] at hkA; dsimp only [patch1] at hkA; rw [ite_eq_right (by omega), ite_eq_left rfl] at hkA; cases hkA
        have hkA0 : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by
          rw [hga1k] at hkA; dsimp only [patch1] at hkA
          by_cases h1 : k < gA; · rw [ite_eq_left h1] at hkA; rw [hga0k]; exact hkA
          · rw [ite_eq_right h1, ite_eq_right hkgA] at hkA
            by_cases h3' : k < i
            · rw [ite_eq_left h3'] at hkA
              cases hop : gs[k].op with
              | and => rw [hga0k]; exact hop
              | or => simp [hop] at hkA
              | _ => rcases (hmon gs[k] (List.getElem_mem hk)).1 with h | h <;> rw [h] at hop <;> cases hop
            · rw [ite_eq_right h3', ite_eq_right hki] at hkA
              by_cases h5 : k < j
              · rw [ite_eq_left h5] at hkA
                cases hop : gs[k].op with
                | and => rw [hga0k]; exact hop
                | or => simp [hop] at hkA
                | _ => rcases (hmon gs[k] (List.getElem_mem hk)).1 with h | h <;> rw [h] at hop <;> cases hop
              · rw [ite_eq_right h5, ite_eq_right hkj] at hkA; rw [hga0k]; exact hkA
        have hpk : patch1 k gs[k] = gs[k] := by
          dsimp only [patch1]
          by_cases h1 : k < gA; · rw [ite_eq_left h1]
          · rw [ite_eq_right h1, ite_eq_right hkgA]
            have hop : gs[k].op = GateOp.and := by rw [← hga0k]; exact hkA0
            by_cases h3' : k < i; · rw [ite_eq_left h3', hop]
            · rw [ite_eq_right h3', ite_eq_right hki]
              by_cases h5 : k < j; · rw [ite_eq_left h5, hop]
              · rw [ite_eq_right h5, ite_eq_right hkj]
        rw [hga1k, hpk] at hu
        have hu_lt : u < 26 + k := hback k hk u (by rw [hga0k]; exact hu)
        have hpo_u := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP k hk hkA0 hkj u (by rw [hga0k]; exact hu)
        apply pureOr_of_agree_cone gs gs1 hback hgs1_len u (by omega) hpo_u
        intro c hc
        have hck : InCone 26 ⟨gs, 0⟩ c k := by
          rcases hc with heq | ⟨hu26, hic⟩
          · have hueq : 26 + c = u := heq.symm
            exact inCone_direct ⟨gs, 0⟩ c k hk (by rw [hga0k, hueq]; exact hu) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ c k hk).2 ⟨u, by rw [hga0k]; exact hu, hu26, hu_lt, Or.inr hic⟩
        have hci : c ≠ i := fun e => by subst e; exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 hck).2) hkj
        have hcj : c ≠ j := fun e => by subst e; exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA hkA0 hck).1) (by omega)
        have hcgA : c ≠ gA := fun e => by subst e; exact hgA_nb.1 k hk hkA0 hki hkj hck
        have hclen : c < gs.length := (inCone_lt ⟨gs, 0⟩ c k hck).1.trans (inCone_lt ⟨gs, 0⟩ c k hck).2
        have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
        have hga0c : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
        have hpc : patch1 c gs[c] = gs[c] := by
          dsimp only [patch1]
          by_cases hc1 : c < gA; · rw [ite_eq_left hc1]
          · rw [ite_eq_right hc1, ite_eq_right hcgA]
            have hcop : gs[c].op = GateOp.or := by
              have hu26 : 26 ≤ u := by rcases hc with heq | ⟨hu26, _⟩ <;> omega
              have := hpo_u hu26
              rcases hc with heq | ⟨_, hic⟩
              · have hce : c = u - 26 := by omega
                have hpo1 := this.2.1; rw [← hce, hga0c] at hpo1; exact hpo1
              · have hpo2 := this.2.2 c hic; rw [hga0c] at hpo2; exact hpo2
            have hc_no_gA : 26 + gA ∉ gs[c].inputs := fun hmem => by
              have hgc : gA < c := by have := hback c hclen (26 + gA) (by rw [hga0c]; exact hmem); omega
              exact hgA_nb.1 k hk hkA0 hki hkj (inCone_trans ⟨gs, 0⟩ gA c k (inCone_direct ⟨gs, 0⟩ gA c hclen (by rw [hga0c]; exact hmem) hgc) hck)
            by_cases hc3 : c < i
            · rw [ite_eq_left hc3, hcop]
              exact gate_mk_or_eq gs[c] hcop _ (List.filter_eq_self.2 (fun z hz => by simp only [decide_eq_true_eq]; exact fun e => hc_no_gA (e ▸ hz)))
            · rw [ite_eq_right hc3, ite_eq_right hci]
              by_cases hc5 : c < j
              · rw [ite_eq_left hc5, hcop]
                have hc_no_i : 26 + i ∉ gs[c].inputs := fun hmem => by
                  have hic' : i < c := by have := hback c hclen (26 + i) (by rw [hga0c]; exact hmem); omega
                  exact absurd ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA hkA0 (inCone_trans ⟨gs, 0⟩ i c k (inCone_direct ⟨gs, 0⟩ i c hclen (by rw [hga0c]; exact hmem) hic') hck)).2) hkj
                have hmap : gs[c].inputs.map (fun w => if w = 26 + i then p0.1 else w) = gs[c].inputs := by
                  trans gs[c].inputs.map (fun a => a)
                  · exact List.map_inj_left.2 (fun z hz => ite_eq_right (fun (e : z = 26 + i) => hc_no_i (e ▸ hz)))
                  · exact List.map_id' _
                exact gate_mk_or_eq gs[c] hcop _ (by
                  rw [hmap]
                  exact List.filter_eq_self.2 (fun z hz => by simp only [decide_eq_true_eq]; exact fun e => hc_no_gA (e ▸ hz)))
              · rw [ite_eq_right hc5, ite_eq_right hcj]
        simp [gs1, List.getElem?_mapIdx, hg0c, hpc]
  let gNew : Gate := ⟨GateOp.or, [26 + (j - 1), 26 + (i - 1)]⟩
  let gs2 := gatesMoveAfter gs1 gA j gNew
  have hgs2_len : gs2.length = gs.length := by rw [gatesMoveAfter_len gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2), hgs1_len]
  have hmon2 : ∀ g ∈ gs2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    gatesMoveAfter_mono gs1 gA j gNew hmon1 (by simp [gNew])
  have hback2 : ReadsBack 26 ⟨gs2, 0⟩ :=
    gatesMoveAfter_readsBack gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 (fun z hz => by
      simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega)
  have hnn2 : ¬ ∃ a b : ℕ, (gateAt ⟨gs2, 0⟩ a).op = GateOp.and ∧
      (gateAt ⟨gs2, 0⟩ b).op = GateOp.and ∧ InCone 26 ⟨gs2, 0⟩ a b := by
    apply gatesMoveAfter_no_nested_and gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 rfl
      (fun m hm1 hm2 => hgs1_no_gA m hm1 (by rw [← hgs1_len]; exact hm2))
    · intro b hjb hblen hbA hic
      rw [hgs1_len] at hblen
      have hinc0 := inCone_of_eq_above gs gs1 j b hgs1_len (fun c hjc hc => by
        have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hc
        simp [gs1, List.getElem?_mapIdx, hg0c, patch1, show ¬ c < gA by omega, show c ≠ gA by omega,
          show ¬ c < i by omega, show c ≠ i by omega, show ¬ c < j by omega, show c ≠ j by omega]) hjb hblen hic
      have hb0 : (gateAt ⟨gs, 0⟩ b).op = GateOp.and := by
        have hg0b : gs[b]? = some gs[b] := List.getElem?_eq_getElem hblen
        have hgb1 : gs1[b]? = some gs[b] := by
          simp [gs1, List.getElem?_mapIdx, hg0b, patch1, show ¬ b < gA by omega, show b ≠ gA by omega,
            show ¬ b < i by omega, show b ≠ i by omega, show ¬ b < j by omega, show b ≠ j by omega]
        have : gateAt ⟨gs1, 0⟩ b = gs[b] := by simp [gateAt, List.getD_eq_getElem?_getD, hgb1]
        rw [gateAt_eq ⟨gs, 0⟩ b hblen, ← this]; exact hbA
      have := (andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hjA hb0 hinc0).1
      omega
    · exact hnn1
  have hgt_agree : ∀ k, j < k → k < gs.length → gs1[k]? = gs[k]? := fun k hjk hk => by
    have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    simp [gs1, List.getElem?_mapIdx, hg0k, patch1, show ¬ k < gA by omega, show k ≠ gA by omega,
      show ¬ k < i by omega, show k ≠ i by omega, show ¬ k < j by omega, show k ≠ j by omega]
  have hgs1_eq_w : ∀ x : List Bool, x.length = 26 → ∀ w < 26 + j,
      (w ≠ 26 + gA ∧ (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ gA (w - 26))) →
      (w ≠ 26 + i ∧ (26 ≤ w → ¬ InCone 26 ⟨gs, 0⟩ i (w - 26))) → V gs1 x w = V gs x w := by
    intro x hx w hw_lt hno_gA hno_i
    apply V_eq_of_agree_cone gs gs1 hback hgs1_len x hx w (by omega)
    intro c hc
    have hclen : c < gs.length := by
      rcases hc with heq | ⟨_, hic⟩; omega; exact (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).1.trans (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).2
    have hcj : c < j := by
      rcases hc with heq | ⟨_, hic⟩; omega; have := (inCone_lt ⟨gs, 0⟩ c (w - 26) hic).1; omega
    have hcgA : c ≠ gA := fun e => by
      subst e; rcases hc with heq | ⟨hu26, hic⟩; exact hno_gA.1 heq; exact hno_gA.2 hu26 hic
    have hci : c ≠ i := fun e => by
      subst e; rcases hc with heq | ⟨hu26, hic⟩; exact hno_i.1 heq; exact hno_i.2 hu26 hic
    have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hclen
    have hga0c : gateAt ⟨gs, 0⟩ c = gs[c] := gateAt_eq ⟨gs, 0⟩ c hclen
    have hgA_in_c : InCone 26 ⟨gs, 0⟩ gA c → False := fun hic_c => by
      rcases hc with heq | ⟨hu26, hic⟩
      · exact hno_gA.2 (by omega) (by rw [heq, Nat.add_sub_cancel_left]; exact hic_c)
      · exact hno_gA.2 hu26 (inCone_trans ⟨gs, 0⟩ gA c (w - 26) hic_c hic)
    have hi_in_c : InCone 26 ⟨gs, 0⟩ i c → False := fun hic_c => by
      rcases hc with heq | ⟨hu26, hic⟩
      · exact hno_i.2 (by omega) (by rw [heq, Nat.add_sub_cancel_left]; exact hic_c)
      · exact hno_i.2 hu26 (inCone_trans ⟨gs, 0⟩ i c (w - 26) hic_c hic)
    have hpc : patch1 c gs[c] = gs[c] := by
      dsimp only [patch1]
      by_cases hc1 : c < gA; · rw [ite_eq_left hc1]
      · rw [ite_eq_right hc1, ite_eq_right hcgA]
        cases hop : gs[c].op with
        | and =>
          by_cases hc3 : c < i
          · rw [ite_eq_left hc3]
          · rw [ite_eq_right hc3, ite_eq_right hci, ite_eq_left hcj]
        | or =>
          have hc_no_gA : 26 + gA ∉ gs[c].inputs := fun hmem => by
            have hgc : gA < c := by have := hback c hclen (26 + gA) (by rw [hga0c]; exact hmem); omega
            exact hgA_in_c (inCone_direct ⟨gs, 0⟩ gA c hclen (by rw [hga0c]; exact hmem) hgc)
          by_cases hc3 : c < i
          · rw [ite_eq_left hc3]; dsimp only
            exact gate_mk_or_eq gs[c] hop _ (List.filter_eq_self.2 (fun z hz => by simp only [decide_eq_true_eq]; exact fun e => hc_no_gA (e ▸ hz)))
          · rw [ite_eq_right hc3, ite_eq_right hci, ite_eq_left hcj]; dsimp only
            have hc_no_i : 26 + i ∉ gs[c].inputs := fun hmem => by
              have hic' : i < c := by have := hback c hclen (26 + i) (by rw [hga0c]; exact hmem); omega
              exact hi_in_c (inCone_direct ⟨gs, 0⟩ i c hclen (by rw [hga0c]; exact hmem) hic')
            have hmap : gs[c].inputs.map (fun w => if w = 26 + i then p0.1 else w) = gs[c].inputs := by
              trans gs[c].inputs.map (fun a => a)
              · exact List.map_inj_left.2 (fun z hz => ite_eq_right (fun (e : z = 26 + i) => hc_no_i (e ▸ hz)))
              · exact List.map_id' _
            exact gate_mk_or_eq gs[c] hop _ (by
              rw [hmap]
              exact List.filter_eq_self.2 (fun z hz => by simp only [decide_eq_true_eq]; exact fun e => hc_no_gA (e ▸ hz)))
        | _ => rcases (hmon gs[c] (List.getElem_mem hclen)).1 with h | h <;> rw [h] at hop <;> cases hop
    simp [gs1, List.getElem?_mapIdx, hg0c, hpc]
  have hgs1_no_gA' : ∀ k, gA < k → k < gs.length → 26 + gA ∉ (gateAt ⟨gs1, 0⟩ k).inputs := hgs1_no_gA
  have hlo_lt_j : ∀ k, j < k → k < gs.length → ∀ u ∈ (gateAt ⟨gs, 0⟩ k).inputs, u < 26 + j →
      ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner gA u) = V gs x u := by
    intro k hjk hk u hu hu_lt x hx
    have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hk
    have hreach_k : reachesAvoiding gs j (26 + k) (26 + outG) := by
      by_cases hko : k = outG; subst hko; exact reachesAvoiding.base
      exact inCone_gt_reachesAvoiding gs j k outG hjk ((hreach k hk).resolve_left hko)
    have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hk
    have huk : u < 26 + k := hback k hk u hu
    have hugA : u ≠ 26 + gA := fun e => (hgt_j_noread k hjk hk).2 (by rw [← e]; exact hu)
    have hui : u ≠ 26 + i := fun e => (hgt_j_noread k hjk hk).1 (by rw [← e]; exact hu)
    have hno_gA_u : u ≠ 26 + gA ∧ (26 ≤ u → ¬ InCone 26 ⟨gs, 0⟩ gA (u - 26)) :=
      ⟨hugA, fun hu26 hic => hgA_nb.2 (reachesAvoiding_trans gs j (26 + gA) (26 + k) (26 + outG)
        (reachesAvoiding_trans gs j (26 + gA) u (26 + k)
          (by have hueq : 26 + (u - 26) = u := (by omega); rw [← hueq]; exact reachesAvoiding_below_skip gs j gA (u - 26) (by omega) hic)
          (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hu) huk reachesAvoiding.base)) hreach_k)⟩
    have hno_i_u : u ≠ 26 + i ∧ (26 ≤ u → ¬ InCone 26 ⟨gs, 0⟩ i (u - 26)) :=
      ⟨hui, fun hu26 hic => hi_no_bypass (reachesAvoiding_trans gs j (26 + i) (26 + k) (26 + outG)
        (reachesAvoiding_trans gs j (26 + i) u (26 + k)
          (by have hueq : 26 + (u - 26) = u := (by omega); rw [← hueq]; exact reachesAvoiding_below_skip gs j i (u - 26) (by omega) hic)
          (reachesAvoiding.step hg0k (by omega) (by rw [← hga0k]; exact hu) huk reachesAvoiding.base)) hreach_k)⟩
    rw [gatesMoveAfter_eval_lt gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 hback2
      (fun c hc hcj => hgs1_no_gA c hc (by omega)) x hx u (by omega) hugA]
    exact hgs1_eq_w x hx u hu_lt hno_gA_u hno_i_u
  have hgs2_uB : ∀ x : List Bool, x.length = 26 → V gs2 x (shiftMoveInner gA uB) = V gs x uB := fun x hx => by
    rw [gatesMoveAfter_eval_lt gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 hback2
      (fun c hc hcj => hgs1_no_gA c hc (by omega)) x hx uB (by omega) hgA_not_uB.1]
    exact hgs1_eq_w x hx uB (by omega) hgA_not_uB
      ⟨by omega, fun _ hic => by have := (inCone_lt ⟨gs, 0⟩ i (uB - 26) hic).1; omega⟩
  have hwR_eq1 : ∀ x : List Bool, x.length = 26 → V gs1 x wR = V gs x wR := fun x hx =>
    hgs1_eq_w x hx wR hwR_lt hwR_no_gA hwR_no_i
  have hgs1_up_off : ∀ x : List Bool, x.length = 26 → V gs x (26 + i) = false →
      ∀ w : ℕ, w < 26 + j → w ≠ 26 + i → ¬ reachesAvoiding gs i (26 + gA) w →
      (∀ m, reachesAvoiding gs i (26 + m) w → m ≠ i → (gateAt ⟨gs, 0⟩ m).op = GateOp.or) →
      V gs x w = true → V gs1 x w = true := by
    intro x hx hVi0 w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw_lt hwi hwg hor hVw
      by_cases hw26 : w < 26
      · rw [V_in gs1 gs x w (by rw [hx]; exact hw26)]; exact hVw
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hklen : k < gs.length := by omega
        have hki : k ≠ i := by omega
        have hkgA : k ≠ gA := fun e => by subst e; exact hwg reachesAvoiding.base
        have hkop : (gateAt ⟨gs, 0⟩ k).op = GateOp.or := hor k reachesAvoiding.base hki
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
        have hbk : ∀ z ∈ gs[k].inputs, z < 26 + k := fun z hz => hback k hklen z (by rw [hga0k]; exact hz)
        have hkop0 : gs[k].op = GateOp.or := by rw [← hga0k]; exact hkop
        rw [orN gs x hx k gs[k] hg0k hbk hkop0] at hVw
        obtain ⟨z, hz, hVz⟩ := hVw
        have hz_lt := hbk z hz
        have hzi : z ≠ 26 + i := fun e => by rw [e, hVi0] at hVz; cases hVz
        have hzg : ¬ reachesAvoiding gs i (26 + gA) z := fun hr =>
          hwg (reachesAvoiding.step hg0k hki hz hz_lt hr)
        have hor_z : ∀ m, reachesAvoiding gs i (26 + m) z → m ≠ i → (gateAt ⟨gs, 0⟩ m).op = GateOp.or :=
          fun m hrm hmi => hor m (reachesAvoiding.step hg0k hki hz hz_lt hrm) hmi
        have hVz1 := ih z hz_lt (by omega) hzi hzg hor_z hVz
        have hzgA : z ≠ 26 + gA := fun e => hzg (by rw [e]; exact reachesAvoiding.base)
        have hpk1 : gs1[k]? = some (patch1 k gs[k]) := by simp [gs1, List.getElem?_mapIdx, hg0k]
        have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hpk1]
        have hbk1 : ∀ z0 ∈ (patch1 k gs[k]).inputs, z0 < 26 + k := fun z0 hz0 =>
          hback1 k (by rw [hgs1_len]; exact hklen) z0 (by rw [hga1k]; exact hz0)
        by_cases hk1 : k < gA
        · have hpk : patch1 k gs[k] = gs[k] := by dsimp only [patch1]; rw [ite_eq_left hk1]
          rw [hpk] at hpk1 hbk1
          rw [orN gs1 x hx k gs[k] hpk1 hbk1 hkop0]
          exact ⟨z, hz, hVz1⟩
        · by_cases hk3 : k < i
          · have hpk : patch1 k gs[k] = ⟨GateOp.or, gs[k].inputs.filter (· ≠ 26 + gA)⟩ := by
              dsimp only [patch1]; rw [ite_eq_right hk1, ite_eq_right hkgA, ite_eq_left hk3, hkop0]
            rw [hpk] at hpk1 hbk1
            rw [orN gs1 x hx k _ hpk1 hbk1 rfl]
            exact ⟨z, List.mem_filter.2 ⟨hz, by simpa using hzgA⟩, hVz1⟩
          · have hpk : patch1 k gs[k] = ⟨GateOp.or, (gs[k].inputs.map (fun w => if w = 26 + i then p0.1 else w)).filter (· ≠ 26 + gA)⟩ := by
              dsimp only [patch1]; rw [ite_eq_right hk1, ite_eq_right hkgA, ite_eq_right hk3, ite_eq_right hki, ite_eq_left (by omega : k < j), hkop0]
            rw [hpk] at hpk1 hbk1
            rw [orN gs1 x hx k _ hpk1 hbk1 rfl]
            exact ⟨z, List.mem_filter.2 ⟨List.mem_map.2 ⟨z, hz, by simp [hzi]⟩, by simpa using hzgA⟩, hVz1⟩
  have hgs1_up_reach : ∀ x : List Bool, x.length = 26 → x.getD p0.1 false = true →
      ∀ w : ℕ, w < 26 + j → reachesOr gs gs.length (26 + i) w →
      V gs1 x (if w = 26 + i then p0.1 else w) = true := by
    intro x hx hp0 w hw hr
    induction hr with
    | base =>
      simp only [↓reduceIte]; unfold V; rw [getD_wiresFrom _ _ _ (by rw [hx]; exact p0.2)]; exact hp0
    | @step k g u hg hk hkop hu hlt_u hr_u ih =>
      have hklen : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      have hga0k : gateAt ⟨gs, 0⟩ k = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
      have hiku : u = 26 + i ∨ 26 + i < u := by
        rcases reachesOr_inCone gs gs.length (26 + i) u (by omega) hr_u with heq | ⟨_, hic⟩
        · exact Or.inl heq
        · right; rw [Nat.add_sub_cancel_left] at hic; have := (inCone_lt ⟨gs, 0⟩ i (u - 26) hic).1; omega
      have hik : i < k := by omega
      have hki : k ≠ i := by omega
      have hkj : k < j := by omega
      have hg0k : gs[k]? = some g := hg
      have hpk : patch1 k g = ⟨GateOp.or, (g.inputs.map (fun w => if w = 26 + i then p0.1 else w)).filter (· ≠ 26 + gA)⟩ := by
        dsimp only [patch1]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hki, ite_eq_left hkj, hkop]
      have hpk1 : gs1[k]? = some (patch1 k g) := by simp [gs1, List.getElem?_mapIdx, hg0k]
      have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k g := by simp [gateAt, List.getD_eq_getElem?_getD, hpk1]
      have hbk1 : ∀ z ∈ (patch1 k g).inputs, z < 26 + k := fun z hz =>
        hback1 k (by rw [hgs1_len]; exact hklen) z (by rw [hga1k]; exact hz)
      rw [ite_eq_right (by omega)]
      rw [orN gs1 x hx k (patch1 k g) hpk1 hbk1 (by rw [hpk])]
      let u' := if u = 26 + i then p0.1 else u
      have hu'_gA : u' ≠ 26 + gA := by dsimp only [u']; split_ifs; have := p0.2; omega; omega
      exact ⟨u', by rw [hpk]; exact List.mem_filter.2 ⟨List.mem_map.2 ⟨u, hu, rfl⟩, by simpa using hu'_gA⟩, ih (by omega)⟩
  have hgs1_down : ∀ x : List Bool, x.length = 26 → V gs1 x p0.1 = false →
      ∀ w : ℕ, w < 26 + j → w ≠ 26 + i → w ≠ 26 + gA → V gs1 x w = true → V gs x w = true := by
    intro x hx hp0 w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw_lt hwi hwg hVw1
      by_cases hw26 : w < 26
      · rw [← V_in gs1 gs x w (by rw [hx]; exact hw26)]; exact hVw1
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        have hklen : k < gs.length := by omega
        have hki : k ≠ i := by omega
        have hkgA : k ≠ gA := by omega
        have hg0k : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
        have hga0k : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
        have hbk : ∀ z ∈ gs[k].inputs, z < 26 + k := fun z hz => hback k hklen z (by rw [hga0k]; exact hz)
        have hpk1 : gs1[k]? = some (patch1 k gs[k]) := by simp [gs1, List.getElem?_mapIdx, hg0k]
        have hga1k : gateAt ⟨gs1, 0⟩ k = patch1 k gs[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hpk1]
        have hbk1 : ∀ z ∈ (patch1 k gs[k]).inputs, z < 26 + k := fun z hz =>
          hback1 k (by rw [hgs1_len]; exact hklen) z (by rw [hga1k]; exact hz)
        by_cases h1 : k < gA
        · have hpk : patch1 k gs[k] = gs[k] := by dsimp only [patch1]; rw [ite_eq_left h1]
          rw [gate_val_aux gs1 x hx k gs[k] (by rw [← hpk]; exact hpk1) hbk] at hVw1
          rw [gate_val_aux gs x hx k gs[k] hg0k hbk]
          exact gateOp_mono (hgs_eq gs[k] (List.getElem_mem hklen)) gs[k].inputs _ _
            (fun z hz hVz1 => by have hzk := hbk z hz; exact ih z hzk (by omega) (by omega) (by omega) hVz1) hVw1
        · cases hop : gs[k].op with
          | and =>
            have hpk : patch1 k gs[k] = gs[k] := by
              dsimp only [patch1]; rw [ite_eq_right h1, ite_eq_right hkgA]
              by_cases h3' : k < i <;> [rw [ite_eq_left h3', hop]; rw [ite_eq_right h3', ite_eq_right hki, ite_eq_left (by omega : k < j), hop]]
            have hkA : (gateAt ⟨gs, 0⟩ k).op = GateOp.and := by rw [hga0k, hop]
            rw [andN_iff gs1 x hx k gs[k] (by rw [← hpk]; exact hpk1) hbk hop] at hVw1
            rw [andN_iff gs x hx k gs[k] hg0k hbk hop]
            intro z hz
            have hzk := hbk z hz
            have hzm := hno_in_and k hklen (by omega) hki hkA
            exact ih z hzk (by omega) (fun e => hzm.2 (by rw [hga0k, ← e]; exact hz))
              (fun e => hzm.1 (by rw [hga0k, ← e]; exact hz)) (hVw1 z hz)
          | or =>
            by_cases h3' : k < i
            · have hpk : patch1 k gs[k] = ⟨GateOp.or, gs[k].inputs.filter (· ≠ 26 + gA)⟩ := by
                dsimp only [patch1]; rw [ite_eq_right h1, ite_eq_right hkgA, ite_eq_left h3', hop]
              rw [hpk] at hpk1 hbk1
              rw [orN gs1 x hx k _ hpk1 hbk1 rfl] at hVw1
              obtain ⟨z, hz, hVz⟩ := hVw1
              rw [List.mem_filter] at hz
              have hzg : z ≠ 26 + gA := by simpa using hz.2
              have hzk := hbk z hz.1
              rw [orN gs x hx k gs[k] hg0k hbk hop]
              exact ⟨z, hz.1, ih z hzk (by omega) (by omega) hzg hVz⟩
            · have hpk : patch1 k gs[k] = ⟨GateOp.or, (gs[k].inputs.map (fun w => if w = 26 + i then p0.1 else w)).filter (· ≠ 26 + gA)⟩ := by
                dsimp only [patch1]; rw [ite_eq_right h1, ite_eq_right hkgA, ite_eq_right h3', ite_eq_right hki, ite_eq_left (by omega : k < j), hop]
              rw [hpk] at hpk1 hbk1
              rw [orN gs1 x hx k _ hpk1 hbk1 rfl] at hVw1
              obtain ⟨z', hz', hVz'⟩ := hVw1
              rw [List.mem_filter] at hz'
              have hz'g : z' ≠ 26 + gA := by simpa using hz'.2
              obtain ⟨z, hz, heqz⟩ := List.mem_map.1 hz'.1
              by_cases hzi : z = 26 + i
              · rw [ite_eq_left hzi] at heqz; rw [← heqz, hp0] at hVz'; cases hVz'
              · rw [ite_eq_right hzi] at heqz; rw [← heqz] at hz'g hVz'
                have hzk := hbk z hz
                rw [orN gs x hx k gs[k] hg0k hbk hop]
                exact ⟨z, hz, ih z hzk (by omega) hzi hz'g hVz'⟩
          | _ => rcases (hmon gs[k] (List.getElem_mem hklen)).1 with h | h <;> rw [h] at hop <;> cases hop
  have hg2_im1 : gs2[i - 1]? = some ⟨GateOp.and, [l0.1, shiftMoveInner gA uB]⟩ := by
    have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
    have hg1i : gs1[i]? = some ⟨GateOp.and, [l0.1, uB]⟩ := by
      simp [gs1, List.getElem?_mapIdx, hg0i, patch1, show ¬ i < gA by omega, show i ≠ gA by omega]
    have hm := gatesMoveAfter_getElem_mid gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) (i - 1) (by omega) (by omega)
    have hadd : i - 1 + 1 = i := by omega
    rw [hadd, hg1i] at hm
    have hsl : shiftMoveInner gA l0.1 = l0.1 := by unfold shiftMoveInner; rw [ite_eq_left (by have := l0.2; omega)]
    simpa [gateMapInner, hsl] using hm
  have hg2_jm1 : gs2[j - 1]? = some ⟨GateOp.and, [shiftMoveInner gA wL', shiftMoveInner gA wR]⟩ := by
    have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
    have hg1j : gs1[j]? = some ⟨GateOp.and, [wL', wR]⟩ := by
      simp [gs1, List.getElem?_mapIdx, hg0j, patch1, show ¬ j < gA by omega, show j ≠ gA by omega,
        show ¬ j < i by omega, show j ≠ i by omega]
    have hm := gatesMoveAfter_getElem_mid gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) (j - 1) (by omega) (by omega)
    have hadd : j - 1 + 1 = j := by omega
    rw [hadd, hg1j] at hm
    simpa [gateMapInner] using hm
  have hgj2 : gs2[j]? = some gNew := gatesMoveAfter_getElem_dst gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2)
  have hbj2 : ∀ z ∈ gNew.inputs, z < 26 + j := fun z hz => by
    simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega
  have hbim1 : ∀ z ∈ ([l0.1, shiftMoveInner gA uB] : List ℕ), z < 26 + (i - 1) := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; have := l0.2; rcases hz with rfl | rfl
    · omega
    · unfold shiftMoveInner; split_ifs <;> omega
  have hbjm1 : ∀ z ∈ ([shiftMoveInner gA wL', shiftMoveInner gA wR] : List ℕ), z < 26 + (j - 1) := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl
    · unfold shiftMoveInner; split_ifs <;> omega
    · unfold shiftMoveInner; split_ifs <;> omega
  have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
  have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
  have hbj0 : ∀ z ∈ gs[j].inputs, z < 26 + j := fun z hz => hback j hlt.2 z (by rw [hga0j]; exact hz)
  have hopj0 : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
  have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
  have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
  have hbi0 : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
  have hopi0 : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
  have hg1j : gs1[j]? = some ⟨GateOp.and, [wL', wR]⟩ := by
    simp [gs1, List.getElem?_mapIdx, hg0j, patch1, show ¬ j < gA by omega, show j ≠ gA by omega,
      show ¬ j < i by omega, show j ≠ i by omega]
  have hbj1 : ∀ z ∈ ([wL', wR] : List ℕ), z < 26 + j := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; rcases hz with rfl | rfl <;> omega
  apply core_contra gs2 (26 + outG) (by rw [hgs2_len]; exact hsz) hmon2 hback2 hnn2
  · intro p l hp
    refine gatesMoveAfter_eval_up_ge_rel gs gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2)
      hgs1_len hgs_eq hback hback2 hgt_agree (inp {p} {l}) (inp_len _ _)
      (fun k hjk hk u hu hult hv => by rw [hlo_lt_j k hjk hk u hu hult _ (inp_len _ _)]; exact hv)
      ?_ outG (by omega) (by omega) (hacc p l hp)
    intro hVj
    rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0] at hVj
    have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
    have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
    rw [orN gs2 _ (inp_len _ _) j gNew hgj2 hbj2 rfl]
    cases hVi0 : V gs (inp {p} {l}) (26 + i)
    · have hwL_ni : wL ≠ 26 + i := fun e => by rw [e, hVi0] at hVwL; cases hVwL
      have hwL'e : wL' = wL := by dsimp only [wL']; rw [ite_eq_right hwL_ni]
      have hor_wL : ∀ m, reachesAvoiding gs i (26 + m) wL → m ≠ i → (gateAt ⟨gs, 0⟩ m).op = GateOp.or := fun m hrm hmi => by
        have hmj : InCone 26 ⟨gs, 0⟩ m j := by
          rcases reachesAvoiding_inCone gs i (26 + m) wL (by omega) hrm with heqm | ⟨hw26, hic⟩
          · exact inCone_direct ⟨gs, 0⟩ m j hlt.2 (by rw [← heqm]; exact (hwj_inp wL).2 (Or.inl rfl)) (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ m j hlt.2).2 ⟨wL, (hwj_inp wL).2 (Or.inl rfl), hw26, hwL_lt, Or.inr (by simpa [Nat.add_sub_cancel_left] using hic)⟩
        exact gateAt_below_j_or_eq gs i j hiA hjA hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m j hmj).1; omega) hmj hmi
      have hVwL1 : V gs1 (inp {p} {l}) wL' = true := by
        rw [hwL'e]; exact hgs1_up_off _ (inp_len _ _) hVi0 wL hwL_lt hwL_ni hgA_not_wL hor_wL hVwL
      have hVwR1 : V gs1 (inp {p} {l}) wR = true := by rw [hwR_eq1 _ (inp_len _ _)]; exact hVwR
      have hVj1 : V gs1 (inp {p} {l}) (26 + j) = true := by
        rw [andN_iff gs1 _ (inp_len _ _) j _ hg1j hbj1 rfl]
        intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl; exact hVwL1; exact hVwR1
      have hVj2 : V gs2 (inp {p} {l}) (26 + (j - 1)) = true := by
        have hev := gatesMoveAfter_eval_lt gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 hback2
          (fun c hc hcj => hgs1_no_gA c hc (by omega)) (inp {p} {l}) (inp_len _ _) (26 + j) (by omega) (by omega)
        have hsh : shiftMoveInner gA (26 + j) = 26 + (j - 1) := by unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
        rw [hsh] at hev; rw [hev]; exact hVj1
      exact ⟨26 + (j - 1), by simp [gNew], hVj2⟩
    · rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi0 hopi0] at hVi0
      have hVA := hVi0 (26 + gA) (by rw [← hga0i, hu_inp]; left; rfl)
      have hVB := hVi0 uB (by rw [← hga0i, hu_inp]; right; rfl)
      obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback (26 + gA) (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 hVA
      obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 hVB
      obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
      obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
      simp only [Finset.mem_union] at hc
      rcases hc with (hc | hc) | hc
      · rw [hX_sing c hc] at hpc
        have hVwL1 : V gs1 (inp {p} {l}) wL' = true := hgs1_up_reach (inp {p} {l}) (inp_len _ _) hpc wL hwL_lt hwL_reach
        have hVwR1 : V gs1 (inp {p} {l}) wR = true := by rw [hwR_eq1 _ (inp_len _ _)]; exact hVwR
        have hVj1 : V gs1 (inp {p} {l}) (26 + j) = true := by
          rw [andN_iff gs1 _ (inp_len _ _) j _ hg1j hbj1 rfl]
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl; exact hVwL1; exact hVwR1
        have hVj2 : V gs2 (inp {p} {l}) (26 + (j - 1)) = true := by
          have hev := gatesMoveAfter_eval_lt gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 hback2
            (fun c hc hcj => hgs1_no_gA c hc (by omega)) (inp {p} {l}) (inp_len _ _) (26 + j) (by omega) (by omega)
          have hsh : shiftMoveInner gA (26 + j) = 26 + (j - 1) := by unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
          rw [hsh] at hev; rw [hev]; exact hVj1
        exact ⟨26 + (j - 1), by simp [gNew], hVj2⟩
      · rw [hY_sing c hc] at hpc
        have hVl0 : V gs2 (inp {p} {l}) l0.1 = true := by
          unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact l0.2)]; exact hpc
        have hVuB2 : V gs2 (inp {p} {l}) (shiftMoveInner gA uB) = true := by rw [hgs2_uB _ (inp_len _ _)]; exact hVB
        have Vim1 : V gs2 (inp {p} {l}) (26 + (i - 1)) = true := by
          rw [andN_iff gs2 _ (inp_len _ _) (i - 1) _ hg2_im1 hbim1 rfl]
          intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl; exact hVl0; exact hVuB2
        exact ⟨26 + (i - 1), by simp [gNew], Vim1⟩
      · rw [hZ_empty] at hc; cases hc
  · intro Q hQ
    rw [Bool.eq_false_iff]; intro htr
    have hdn : V gs2 (inp Q (TQ Q)) (26 + j) = true → V gs (inp Q (TQ Q)) (26 + j) = true := by
      intro hVj2
      rw [orN gs2 _ (inp_len _ _) j gNew hgj2 hbj2 rfl] at hVj2
      obtain ⟨z, hz, hVz2⟩ := hVj2
      simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · have hev := gatesMoveAfter_eval_lt gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2) hback1 hback2
          (fun c hc hcj => hgs1_no_gA c hc (by omega)) (inp Q (TQ Q)) (inp_len _ _) (26 + j) (by omega) (by omega)
        have hsh : shiftMoveInner gA (26 + j) = 26 + (j - 1) := by unfold shiftMoveInner; rw [ite_eq_right (by omega)]; omega
        rw [hsh] at hev
        have hVj1 : V gs1 (inp Q (TQ Q)) (26 + j) = true := by rw [← hev]; exact hVz2
        rw [andN_iff gs1 _ (inp_len _ _) j _ hg1j hbj1 rfl] at hVj1
        have hVwL1 := hVj1 wL' (by simp)
        have hVwR1 := hVj1 wR (by simp)
        have hVwR : V gs (inp Q (TQ Q)) wR = true := by rw [← hwR_eq1 _ (inp_len _ _)]; exact hVwR1
        obtain ⟨r, hrR, hqr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp Q (TQ Q)) (inp_len _ _)).1 hVwR
        rw [qHit_eq_inp_getD] at hqr
        have hp0_f : V gs1 (inp Q (TQ Q)) p0.1 = false := by
          rw [Bool.eq_false_iff]; intro htp0
          have hv0 : V gs1 (inp Q (TQ Q)) p0.1 = (inp Q (TQ Q)).getD p0.1 false := by
            unfold V; exact getD_wiresFrom gs1 _ _ (by rw [inp_len]; exact p0.2)
          rw [hv0, qHit_eq_inp_getD] at htp0
          exact absurd ⟨htp0, hqr⟩ (inc_false_on_quad p0 r (hok_XR p0 hp0X r hrR) Q)
        have hwL_ni : wL ≠ 26 + i := fun e => by
          have hwL'e : wL' = p0.1 := by dsimp only [wL']; rw [ite_eq_left e]
          rw [hwL'e, hp0_f] at hVwL1; cases hVwL1
        have hwL'e : wL' = wL := by dsimp only [wL']; rw [ite_eq_right hwL_ni]
        rw [hwL'e] at hVwL1
        have hVwL : V gs (inp Q (TQ Q)) wL = true :=
          hgs1_down _ (inp_len _ _) hp0_f wL hwL_lt hwL_ni hwL_ne_gA hVwL1
        rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj0 hopj0]
        intro z hz; rw [← hga0j, hwj_inp] at hz
        rcases hz with rfl | rfl; exact hVwL; exact hVwR
      · rw [andN_iff gs2 _ (inp_len _ _) (i - 1) _ hg2_im1 hbim1 rfl] at hVz2
        have hVl0 := hVz2 l0.1 (by simp)
        have hVuB := hVz2 (shiftMoveInner gA uB) (by simp)
        have hql0 : qHit Q l0 = true := by
          have hv0 : V gs2 (inp Q (TQ Q)) l0.1 = (inp Q (TQ Q)).getD l0.1 false := by
            unfold V; exact getD_wiresFrom gs2 _ _ (by rw [inp_len]; exact l0.2)
          rw [← qHit_eq_inp_getD, ← hv0, hVl0]
        rw [hgs2_uB _ (inp_len _ _)] at hVuB
        obtain ⟨b, hbB, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVuB
        rw [qHit_eq_inp_getD] at hqb
        exact absurd ⟨hql0, hqb⟩ (inc_false_on_quad l0 b (hok_YB l0 hl0Y b hbB) Q)
    have htr0 := gatesMoveAfter_eval_down_ge_rel gs gs1 gA j gNew (by omega) (by rw [hgs1_len]; exact hlt.2)
      hgs1_len hgs_eq hback hback2 hgt_agree (inp Q (TQ Q)) (inp_len _ _)
      (fun k hjk hk u hu hult hv => by rw [← hlo_lt_j k hjk hk u hu hult _ (inp_len _ _)]; exact hv)
      hdn outG (by omega) (by omega) htr
    rw [hrej Q hQ] at htr0; cases htr0

lemma reachesOr_of_inCone_below_j (gs : List Gate) (_hback : ReadsBack 26 ⟨gs, 0⟩)
    (i j : ℕ) (hj : j < gs.length) :
    ∀ w : ℕ, w < 26 + j → (w = 26 + i ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ i (w - 26))) →
      (∀ m, (w = 26 + m ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ m (w - 26))) → m ≠ i → (gateAt ⟨gs, 0⟩ m).op = GateOp.or) →
      reachesOr gs gs.length (26 + i) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hrel hor
    rcases hrel with rfl | ⟨hw26, hic⟩
    · exact reachesOr.base
    · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hic
      have hki : k ≠ i := (inCone_lt ⟨gs, 0⟩ i k hic).1.ne'
      have hklen : k < gs.length := by omega
      have hg0 : gs[k]? = some gs[k] := List.getElem?_eq_getElem hklen
      have hga0 : gateAt ⟨gs, 0⟩ k = gs[k] := gateAt_eq ⟨gs, 0⟩ k hklen
      have hkop : gs[k].op = GateOp.or := by rw [← hga0]; exact hor k (Or.inl rfl) hki
      rw [inCone_iff 26 ⟨gs, 0⟩ i k hklen] at hic
      obtain ⟨u, hu, hu26, hult, hurel⟩ := hic
      have hor_u : ∀ m, (u = 26 + m ∨ (26 ≤ u ∧ InCone 26 ⟨gs, 0⟩ m (u - 26))) → m ≠ i →
          (gateAt ⟨gs, 0⟩ m).op = GateOp.or := by
        intro m hmu hmi
        have hmk : InCone 26 ⟨gs, 0⟩ m k := by
          rcases hmu with rfl | ⟨_, hmic⟩
          · exact inCone_direct ⟨gs, 0⟩ m k hklen hu (by omega)
          · exact (inCone_iff 26 ⟨gs, 0⟩ m k hklen).2 ⟨u, hu, hu26, hult, Or.inr hmic⟩
        exact hor m (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hmk⟩) hmi
      have hur : reachesOr gs gs.length (26 + i) u := by
        apply ih u hult (by omega) _ hor_u
        rcases hurel with rfl | hic_u
        · left; omega
        · right; exact ⟨hu26, hic_u⟩
      exact reachesOr.step hg0 (by omega) hkop (by rw [← hga0]; exact hu) hult hur

set_option maxHeartbeats 800000 in
lemma case2_contradiction (gs : List Gate) (outG : ℕ) (hout : outG + 1 = gs.length)
    (hsz : gs.length < 64)
    (hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ReadsBack 26 ⟨gs, 0⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (hreach : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) (26 + outG) = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + outG) = false)
    (i j : ℕ) (hiA : (gateAt ⟨gs, 0⟩ i).op = GateOp.and) (hjA : (gateAt ⟨gs, 0⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, 0⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1)
    (hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false)
    (hQ0 : ∃ Q0 : Finset (Fin 13), isQuad Q0 ∧ V gs (inp Q0 (TQ Q0)) (26 + i) = true) :
    False := by
  have hlt := inCone_lt ⟨gs, 0⟩ i j hij
  dsimp only at hlt
  have hil : i < gs.length := by omega
  have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
  obtain ⟨Q0, hQ0q, hQ0_i⟩ := hQ0
  have hi_no_bypass : ¬ reachesAvoiding gs j (26 + i) (26 + outG) := by
    intro hr
    rcases reachesAvoiding_split gs j (26 + i) hgs_eq (26 + outG) hr with hOr | hAnd
    · have htr := reachesOr_V gs j (26 + i) hback (inp Q0 (TQ Q0)) (inp_len _ _) (26 + outG) hOr hQ0_i
      rw [hrej Q0 hQ0q] at htr; cases htr
    · obtain ⟨a, ga, hga, haop, haj, _, u, hu, hult, hOr⟩ := hAnd
      have halen : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
      have hga_eq : gateAt ⟨gs, 0⟩ a = ga := by simp [gateAt, List.getD_eq_getElem?_getD, hga]
      have hia : InCone 26 ⟨gs, 0⟩ i a := by
        rcases reachesOr_inCone gs j (26 + i) u (by omega) hOr with heq | ⟨hu26, hic⟩
        · rw [heq] at hu
          exact inCone_direct ⟨gs, 0⟩ i a halen (by rw [hga_eq]; exact hu)
            (by have := hback a halen (26 + i) (by rw [hga_eq]; exact hu); omega)
        · exact (inCone_iff 26 ⟨gs, 0⟩ i a halen).2 ⟨u, by rw [hga_eq]; exact hu, hu26, hult, Or.inr (by simpa [Nat.add_sub_cancel_left] using hic)⟩
      exact haj ((andPairs_unique ⟨gs, 0⟩ hAP hiA hjA hij hiA (by rw [hga_eq]; exact haop) hia).2)
  obtain ⟨w1, w2, hw12, hwj_eq⟩ := two_inputs_distinct (htwo gs[j] (List.getElem_mem hlt.2))
  have hga0j : gateAt ⟨gs, 0⟩ j = gs[j] := gateAt_eq ⟨gs, 0⟩ j hlt.2
  have hg0j : gs[j]? = some gs[j] := List.getElem?_eq_getElem hlt.2
  have hbj : ∀ w ∈ gs[j].inputs, w < 26 + j := fun w hw => hback j hlt.2 w (by rw [hga0j]; exact hw)
  have hopj : gs[j].op = GateOp.and := by rw [← hga0j]; exact hjA
  have hreaches_w_of_inCone : ∀ w ∈ gs[j].inputs, (w = 26 + i ∨ (26 ≤ w ∧ InCone 26 ⟨gs, 0⟩ i (w - 26))) →
      reachesOr gs gs.length (26 + i) w := by
    intro w hw hrel
    have hwlt := hbj w hw
    apply reachesOr_of_inCone_below_j gs hback i j hlt.2 w hwlt hrel
    intro m hm hmi
    have hmj : InCone 26 ⟨gs, 0⟩ m j := by
      rcases hm with rfl | ⟨hw26, hic⟩
      · exact inCone_direct ⟨gs, 0⟩ m j hlt.2 (by rw [hga0j]; exact hw) (by omega)
      · exact (inCone_iff 26 ⟨gs, 0⟩ m j hlt.2).2 ⟨w, by rw [hga0j]; exact hw, hw26, hbj w hw, Or.inr hic⟩
    exact gateAt_below_j_or_eq gs i j hiA hjA hij hAP hmon m (by have := (inCone_lt ⟨gs, 0⟩ m j hmj).1; omega) hmj hmi
  have hj_has_i : (w1 = 26 + i ∨ (26 ≤ w1 ∧ InCone 26 ⟨gs, 0⟩ i (w1 - 26))) ∨
      (w2 = 26 + i ∨ (26 ≤ w2 ∧ InCone 26 ⟨gs, 0⟩ i (w2 - 26))) := by
    have hij' := hij
    rw [inCone_iff 26 ⟨gs, 0⟩ i j hlt.2, hga0j, hwj_eq] at hij'
    obtain ⟨u, hu, hu26, _, hrel⟩ := hij'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · left; rcases hrel with h | h; exact Or.inl (by omega); exact Or.inr ⟨hu26, h⟩
    · right; rcases hrel with h | h; exact Or.inl (by omega); exact Or.inr ⟨hu26, h⟩
  have hnot_both : ¬ ((w1 = 26 + i ∨ (26 ≤ w1 ∧ InCone 26 ⟨gs, 0⟩ i (w1 - 26))) ∧
      (w2 = 26 + i ∨ (26 ≤ w2 ∧ InCone 26 ⟨gs, 0⟩ i (w2 - 26)))) := by
    rintro ⟨hr1, hr2⟩
    have h1 := reachesOr_V gs gs.length (26 + i) hback (inp Q0 (TQ Q0)) (inp_len _ _) w1
      (hreaches_w_of_inCone w1 (by rw [hwj_eq]; simp) hr1) hQ0_i
    have h2 := reachesOr_V gs gs.length (26 + i) hback (inp Q0 (TQ Q0)) (inp_len _ _) w2
      (hreaches_w_of_inCone w2 (by rw [hwj_eq]; simp) hr2) hQ0_i
    have hVj0 : V gs (inp Q0 (TQ Q0)) (26 + j) = true := by
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj]
      intro z hz; rw [hwj_eq] at hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl; exact h1; exact h2
    rw [hjQ Q0 hQ0q] at hVj0; cases hVj0
  obtain ⟨wL, wR, hwL_reach, hwR_lt, hwR_no_i, hwj_inp⟩ :
      ∃ wL wR, reachesOr gs gs.length (26 + i) wL ∧ wR < 26 + j ∧
        (wR ≠ 26 + i ∧ (26 ≤ wR → ¬ InCone 26 ⟨gs, 0⟩ i (wR - 26))) ∧
        (∀ w, w ∈ (gateAt ⟨gs, 0⟩ j).inputs ↔ w = wL ∨ w = wR) := by
    rcases hj_has_i with hr1 | hr2
    · have hno2 : w2 ≠ 26 + i ∧ (26 ≤ w2 → ¬ InCone 26 ⟨gs, 0⟩ i (w2 - 26)) :=
        ⟨fun e => hnot_both ⟨hr1, Or.inl e⟩, fun hw26 hic => hnot_both ⟨hr1, Or.inr ⟨hw26, hic⟩⟩⟩
      exact ⟨w1, w2, hreaches_w_of_inCone w1 (by rw [hwj_eq]; simp) hr1, hbj w2 (by rw [hwj_eq]; simp), hno2,
        fun w => by rw [hga0j, hwj_eq]; simp⟩
    · have hno1 : w1 ≠ 26 + i ∧ (26 ≤ w1 → ¬ InCone 26 ⟨gs, 0⟩ i (w1 - 26)) :=
        ⟨fun e => hnot_both ⟨Or.inl e, hr2⟩, fun hw26 hic => hnot_both ⟨Or.inr ⟨hw26, hic⟩, hr2⟩⟩
      exact ⟨w2, w1, hreaches_w_of_inCone w2 (by rw [hwj_eq]; simp) hr2, hbj w1 (by rw [hwj_eq]; simp), hno1,
        fun w => by rw [hga0j, hwj_eq]; simp [or_comm]⟩
  obtain ⟨uA, uB, hu_ne, hui_eq⟩ := two_inputs_distinct (htwo gs[i] (List.getElem_mem hil))
  have hga0i : gateAt ⟨gs, 0⟩ i = gs[i] := gateAt_eq ⟨gs, 0⟩ i hil
  have hg0i : gs[i]? = some gs[i] := List.getElem?_eq_getElem hil
  have hbi : ∀ z ∈ gs[i].inputs, z < 26 + i := fun z hz => hback i hil z (by rw [hga0i]; exact hz)
  have hopi : gs[i].op = GateOp.and := by rw [← hga0i]; exact hiA
  have hu_inp : ∀ w, w ∈ (gateAt ⟨gs, 0⟩ i).inputs ↔ w = uA ∨ w = uB := fun w => by rw [hga0i, hui_eq]; simp
  have huA_lt : uA < 26 + i := hbi uA (by rw [hui_eq]; simp)
  have huB_lt : uB < 26 + i := hbi uB (by rw [hui_eq]; simp)
  have huA_po : pureOr gs uA := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uA ((hu_inp uA).2 (Or.inl rfl))
  have huB_po : pureOr gs uB := other_and_inputs_pureOr gs hmon hback i j hiA hjA hij hAP i hil hiA (by omega) uB ((hu_inp uB).2 (Or.inr rfl))
  have hwL_lt : wL < 26 + j := hback j hlt.2 wL ((hwj_inp wL).2 (Or.inl rfl))
  have hwR_po : pureOr gs wR :=
    pureOr_wR gs hmon hback i j wR hiA hjA hij hAP ((hwj_inp wR).2 (Or.inr rfl)) hwR_no_i
  let A := orSetAvoid gs gs.length uA
  let B := orSetAvoid gs gs.length uB
  let R := orSetAvoid gs gs.length wR
  let X := A ∩ B
  let Y := A ∩ R
  let Z := B ∩ R
  have hnok_AB : ¬ okQuad A B := by
    intro hok
    rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hQ0_i
    obtain ⟨a, ha, hqa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp Q0 (TQ Q0)) (inp_len _ _)).1 (hQ0_i uA (by rw [hui_eq]; simp))
    obtain ⟨b, hb, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q0 (TQ Q0)) (inp_len _ _)).1 (hQ0_i uB (by rw [hui_eq]; simp))
    rw [qHit_eq_inp_getD] at hqa hqb
    exact absurd ⟨hqa, hqb⟩ (inc_false_on_quad a b (hok a ha b hb) Q0)
  have h3 : okQuad3 A B R := by
    rintro Q hQ ⟨⟨a, ha, hqa⟩, ⟨b, hb, hqb⟩, ⟨r, hr, hqr⟩⟩
    rw [← qHit_eq_inp_getD] at hqa hqb hqr
    have hVA := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp Q (TQ Q)) (inp_len _ _)).2 ⟨a, ha, hqa⟩
    have hVB := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).2 ⟨b, hb, hqb⟩
    have hVwR := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp Q (TQ Q)) (inp_len _ _)).2 ⟨r, hr, hqr⟩
    have hVi : V gs (inp Q (TQ Q)) (26 + i) = true := by
      rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi]
      intro z hz; rw [hui_eq] at hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl; exact hVA; exact hVB
    have hVwL := reachesOr_V gs gs.length (26 + i) hback (inp Q (TQ Q)) (inp_len _ _) wL hwL_reach hVi
    have hVj : V gs (inp Q (TQ Q)) (26 + j) = true := by
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj]
      intro z hz; rw [← hga0j, hwj_inp] at hz
      rcases hz with rfl | rfl; exact hVwL; exact hVwR
    rw [hjQ Q hQ] at hVj; cases hVj
  have hkeep_i : ∀ m g, m ∉ ({i} : Finset ℕ) → (if m = i then (⟨GateOp.or, [uA]⟩ : Gate) else g) = g := fun m g hm => by
    simp only [Finset.mem_singleton] at hm; exact ite_eq_right hm
  have hkeep_iB : ∀ m g, m ∉ ({i} : Finset ℕ) → (if m = i then (⟨GateOp.or, [uB]⟩ : Gate) else g) = g := fun m g hm => by
    simp only [Finset.mem_singleton] at hm; exact ite_eq_right hm
  by_cases hok_AR : okQuad A R
  · refine case2_replace_i_or gs outG hout hsz hmon hback hacc hrej i j wL wR hiA hjA hij hAP hjQ hi_no_bypass
      hwR_lt hwR_no_i hwj_inp hwL_lt ⟨GateOp.or, [uA]⟩ rfl (by simp) (fun z hz => by simp at hz; omega)
      (fun z hz => by simp at hz; subst hz; exact huA_po) ?_ ?_
    · intro p l hp hVj
      let pI : ℕ → Gate → Gate := fun m g => if m = i then ⟨GateOp.or, [uA]⟩ else g
      let gs' := gs.mapIdx pI
      have hgs'_len : gs'.length = gs.length := List.length_mapIdx
      have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
        apply mapIdx_readsBack; intro m g hg u hu; dsimp only [pI] at hu; split_ifs at hu with hm
        · simp at hu; omega
        · have hml := (List.getElem?_eq_some_iff.1 hg).1
          have hgam : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
          exact hback m hml u (by rw [hgam]; exact hu)
      rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
      have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
      have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
      cases hVi0 : V gs (inp {p} {l}) (26 + i)
      · have hbad_wL : reachesBadOnlyVia gs {i} i wL := fun b hb hbi _ => by simp at hb; exact absurd hb hbi
        exact mapIdx_eval_up gs pI {i} i hback hback' hgs_eq hkeep_i (inp {p} {l}) (inp_len _ _)
          (fun h => by rw [hVi0] at h; cases h) wL (by omega) hbad_wL hVwL
      · rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hVi0
        have hVA := hVi0 uA (by rw [hui_eq]; simp)
        have hgi' : gs'[i]? = some ⟨GateOp.or, [uA]⟩ := by simp [gs', List.getElem?_mapIdx, hg0i, pI]
        have hbi' : ∀ z ∈ ([uA] : List ℕ), z < 26 + i := fun z hz => by simp at hz; omega
        have huA_ev : V gs' (inp {p} {l}) uA = V gs (inp {p} {l}) uA :=
          mapIdx_eval_avoid gs pI {i} hback hkeep_i _ (inp_len _ _) uA (by omega) (fun b hb => by
            simp only [Finset.mem_singleton] at hb; rw [hb]; exact ⟨by omega, fun _ hc => by have := (inCone_lt ⟨gs, 0⟩ i (uA - 26) hc).1; omega⟩)
        have hVi' : V gs' (inp {p} {l}) (26 + i) = true := by
          rw [orN gs' _ (inp_len _ _) i _ hgi' hbi' rfl]; exact ⟨uA, by simp, by rw [huA_ev]; exact hVA⟩
        exact reachesOr_V gs' gs.length (26 + i) hback' _ (inp_len _ _) wL
          (reachesOr_map_above gs gs' gs.length i wL (fun c hci hcl => by
            have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hcl
            simp [gs', List.getElem?_mapIdx, hg0c, pI, show c ≠ i by omega]) hwL_reach) hVi'
    · intro Q hQ hVwR ⟨v, hv, hVv⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rw [hv] at hVv
      obtain ⟨a, ha, hqa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp Q (TQ Q)) (inp_len _ _)).1 hVv
      obtain ⟨r, hr, hqr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp Q (TQ Q)) (inp_len _ _)).1 hVwR
      rw [qHit_eq_inp_getD] at hqa hqr
      exact absurd ⟨hqa, hqr⟩ (inc_false_on_quad a r (hok_AR a ha r hr) Q)
  · by_cases hok_BR : okQuad B R
    · refine case2_replace_i_or gs outG hout hsz hmon hback hacc hrej i j wL wR hiA hjA hij hAP hjQ hi_no_bypass
        hwR_lt hwR_no_i hwj_inp hwL_lt ⟨GateOp.or, [uB]⟩ rfl (by simp) (fun z hz => by simp at hz; omega)
        (fun z hz => by simp at hz; subst hz; exact huB_po) ?_ ?_
      · intro p l hp hVj
        let pI : ℕ → Gate → Gate := fun m g => if m = i then ⟨GateOp.or, [uB]⟩ else g
        let gs' := gs.mapIdx pI
        have hgs'_len : gs'.length = gs.length := List.length_mapIdx
        have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
          apply mapIdx_readsBack; intro m g hg u hu; dsimp only [pI] at hu; split_ifs at hu with hm
          · simp at hu; omega
          · have hml := (List.getElem?_eq_some_iff.1 hg).1
            have hgam : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
            exact hback m hml u (by rw [hgam]; exact hu)
        rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
        have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
        cases hVi0 : V gs (inp {p} {l}) (26 + i)
        · have hbad_wL : reachesBadOnlyVia gs {i} i wL := fun b hb hbi _ => by simp at hb; exact absurd hb hbi
          exact mapIdx_eval_up gs pI {i} i hback hback' hgs_eq hkeep_iB (inp {p} {l}) (inp_len _ _)
            (fun h => by rw [hVi0] at h; cases h) wL (by omega) hbad_wL hVwL
        · rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hVi0
          have hVB := hVi0 uB (by rw [hui_eq]; simp)
          have hgi' : gs'[i]? = some ⟨GateOp.or, [uB]⟩ := by simp [gs', List.getElem?_mapIdx, hg0i, pI]
          have hbi' : ∀ z ∈ ([uB] : List ℕ), z < 26 + i := fun z hz => by simp at hz; omega
          have huB_ev : V gs' (inp {p} {l}) uB = V gs (inp {p} {l}) uB :=
            mapIdx_eval_avoid gs pI {i} hback hkeep_iB _ (inp_len _ _) uB (by omega) (fun b hb => by
              simp only [Finset.mem_singleton] at hb; rw [hb]; exact ⟨by omega, fun _ hc => by have := (inCone_lt ⟨gs, 0⟩ i (uB - 26) hc).1; omega⟩)
          have hVi' : V gs' (inp {p} {l}) (26 + i) = true := by
            rw [orN gs' _ (inp_len _ _) i _ hgi' hbi' rfl]; exact ⟨uB, by simp, by rw [huB_ev]; exact hVB⟩
          exact reachesOr_V gs' gs.length (26 + i) hback' _ (inp_len _ _) wL
            (reachesOr_map_above gs gs' gs.length i wL (fun c hci hcl => by
              have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hcl
              simp [gs', List.getElem?_mapIdx, hg0c, pI, show c ≠ i by omega]) hwL_reach) hVi'
      · intro Q hQ hVwR ⟨v, hv, hVv⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rw [hv] at hVv
        obtain ⟨b, hb, hqb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp Q (TQ Q)) (inp_len _ _)).1 hVv
        obtain ⟨r, hr, hqr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp Q (TQ Q)) (inp_len _ _)).1 hVwR
        rw [qHit_eq_inp_getD] at hqb hqr
        exact absurd ⟨hqb, hqr⟩ (inc_false_on_quad b r (hok_BR b hb r hr) Q)
    · by_cases hXne : X.Nonempty <;> by_cases hYne : Y.Nonempty <;> by_cases hZne : Z.Nonempty
      · obtain ⟨x0, hx0⟩ := hXne; obtain ⟨y0, hy0⟩ := hYne; obtain ⟨z0, hz0⟩ := hZne
        have hxy := okQuad_of_okQuad3_inter A B R h3 x0 hx0 y0 (Finset.mem_inter.1 hy0).2
        have hxz := okQuad_of_okQuad3_inter A B R h3 x0 hx0 z0 (Finset.mem_inter.1 hz0).2
        have hyz := okQuad_of_okQuad3_interL A B R h3 y0 hy0 z0 (Finset.mem_inter.1 hz0).1
        rw [isInc26_symm] at hxy
        have hfl := isInc26_bipartite y0 x0 z0 hxy hxz
        rw [hyz] at hfl; cases hfl
      · have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        obtain ⟨x0, hx0⟩ := hXne; obtain ⟨y0, hy0⟩ := hYne
        exact case2_sub7 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uA uB wL wR
          hiA hjA hij hAP hjQ hi_no_bypass hu_inp hwL_reach hwR_lt hwR_no_i hwj_inp x0 y0 hx0 hy0 hZe hok_AR hok_BR h3
      · have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.1 hYne
        obtain ⟨x0, hx0⟩ := hXne; obtain ⟨z0, hz0⟩ := hZne
        exact case2_sub7 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uB uA wL wR
          hiA hjA hij hAP hjQ hi_no_bypass (fun w => by rw [hu_inp w, or_comm]) hwL_reach hwR_lt hwR_no_i hwj_inp
          x0 z0 (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hx0).2, (Finset.mem_inter.1 hx0).1⟩) hz0 hYe
          hok_BR hok_AR (fun Q hQ ⟨⟨b, hb⟩, ⟨a, ha⟩, ⟨r, hr⟩⟩ => h3 Q hQ ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨r, hr⟩⟩)
      · have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.1 hYne
        have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        by_cases hX2 : 2 ≤ X.card
        · exact case2_sub3 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uA uB wL wR
            hiA hjA hij hAP hjQ hi_no_bypass hu_ne hu_inp hwL_reach hwR_lt hwR_no_i hwj_inp
            hX2 hYe hZe hok_AR hok_BR h3
        · obtain ⟨x0, hx0⟩ := hXne
          have hX1 : ∀ x ∈ X, x = x0 := fun x hx => Finset.card_le_one.1 (by omega : X.card ≤ 1) x hx x0 hx0
          refine case2_replace_i_or gs outG hout hsz hmon hback hacc hrej i j wL wR hiA hjA hij hAP hjQ hi_no_bypass
            hwR_lt hwR_no_i hwj_inp hwL_lt ⟨GateOp.or, [x0.1]⟩ rfl (by simp) (fun z hz => by simp at hz; have := x0.2; omega)
            (fun z hz hz26 => by simp at hz; subst hz; exact absurd x0.2 (by omega)) ?_ ?_
          · intro p l hp hVj
            let pI : ℕ → Gate → Gate := fun m g => if m = i then ⟨GateOp.or, [x0.1]⟩ else g
            let gs' := gs.mapIdx pI
            have hgs'_len : gs'.length = gs.length := List.length_mapIdx
            have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
              apply mapIdx_readsBack; intro m g hg u hu; dsimp only [pI] at hu; split_ifs at hu with hm
              · simp at hu; have := x0.2; omega
              · have hml := (List.getElem?_eq_some_iff.1 hg).1
                have hgam : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
                exact hback m hml u (by rw [hgam]; exact hu)
            have hkeep_x0 : ∀ m g, m ∉ ({i} : Finset ℕ) → pI m g = g := fun m g hm => by
              simp only [Finset.mem_singleton] at hm; exact ite_eq_right hm
            rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
            have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
            have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
            cases hVi0 : V gs (inp {p} {l}) (26 + i)
            · have hbad_wL : reachesBadOnlyVia gs {i} i wL := fun b hb hbi _ => by simp at hb; exact absurd hb hbi
              exact mapIdx_eval_up gs pI {i} i hback hback' hgs_eq hkeep_x0 (inp {p} {l}) (inp_len _ _)
                (fun h => by rw [hVi0] at h; cases h) wL (by omega) hbad_wL hVwL
            · rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hVi0
              obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 (hVi0 uA (by rw [hui_eq]; simp))
              obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 (hVi0 uB (by rw [hui_eq]; simp))
              obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
              obtain ⟨c, hc, hpc⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
              have hcX : c ∈ X := by
                simp only [Finset.mem_union] at hc
                rcases hc with (hc | hc) | hc
                · exact hc
                · change c ∈ Y at hc; rw [hYe] at hc; cases hc
                · change c ∈ Z at hc; rw [hZe] at hc; cases hc
              rw [hX1 c hcX] at hpc
              have hgi' : gs'[i]? = some ⟨GateOp.or, [x0.1]⟩ := by simp [gs', List.getElem?_mapIdx, hg0i, pI]
              have hbi' : ∀ z ∈ ([x0.1] : List ℕ), z < 26 + i := fun z hz => by simp at hz; have := x0.2; omega
              have hVi' : V gs' (inp {p} {l}) (26 + i) = true := by
                rw [orN gs' _ (inp_len _ _) i _ hgi' hbi' rfl]
                exact ⟨x0.1, by simp, by unfold V; rw [getD_wiresFrom _ _ _ (by rw [inp_len]; exact x0.2)]; exact hpc⟩
              exact reachesOr_V gs' gs.length (26 + i) hback' _ (inp_len _ _) wL
                (reachesOr_map_above gs gs' gs.length i wL (fun c hci hcl => by
                  have hg0c : gs[c]? = some gs[c] := List.getElem?_eq_getElem hcl
                  simp [gs', List.getElem?_mapIdx, hg0c, pI, show c ≠ i by omega]) hwL_reach) hVi'
          · intro Q hQ hVwR ⟨v, hv, hVv⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst hv
            have hqx0 : qHit Q x0 = true := by
              have hv0 : V gs (inp Q (TQ Q)) x0.1 = (inp Q (TQ Q)).getD x0.1 false := by
                unfold V; exact getD_wiresFrom gs _ _ (by rw [inp_len]; exact x0.2)
              rw [← qHit_eq_inp_getD, ← hv0, hVv]
            obtain ⟨r, hr, hqr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp Q (TQ Q)) (inp_len _ _)).1 hVwR
            rw [qHit_eq_inp_getD] at hqr
            exact absurd ⟨hqx0, hqr⟩ (inc_false_on_quad x0 r (okQuad_of_okQuad3_inter A B R h3 x0 hx0 r hr) Q)
      · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.1 hXne
        obtain ⟨y0, hy0⟩ := hYne; obtain ⟨z0, hz0⟩ := hZne
        exact case2_sub6 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uA uB wL wR
          hiA hjA hij hAP hjQ hi_no_bypass hu_inp hwL_reach hwR_lt hwR_no_i hwj_inp y0 z0 hy0 hz0 hXe h3
      · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.1 hXne
        have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        by_cases hY2 : 2 ≤ Y.card
        · exact case2_sub5 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uA uB wL wR
            hiA hjA hij hAP hjQ hi_no_bypass hu_inp hwL_reach hwR_lt hwR_no_i hwj_inp
            hY2 ⟨hXe, hZe⟩ hnok_AB hok_AR hok_BR h3
        · obtain ⟨y0, hy0⟩ := hYne
          have hY1 : ∀ y ∈ Y, y = y0 := fun y hy => Finset.card_le_one.1 (by omega : Y.card ≤ 1) y hy y0 hy0
          exact case2_sub4 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uA uB wL wR
            hiA hjA hij hAP hjQ hi_no_bypass hu_inp hwL_reach hwR_lt hwR_no_i hwj_inp
            y0 hY1 hy0 ⟨hXe, hZe⟩ h3
      · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.1 hXne
        have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.1 hYne
        by_cases hZ2 : 2 ≤ Z.card
        · exact case2_sub5 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uB uA wL wR
            hiA hjA hij hAP hjQ hi_no_bypass (fun w => by rw [hu_inp w, or_comm]) hwL_reach hwR_lt hwR_no_i hwj_inp
            hZ2 ⟨by simpa [Finset.inter_comm] using hXe, hYe⟩ (fun h => hnok_AB (fun a ha b hb => by rw [isInc26_symm]; exact h b hb a ha)) hok_BR hok_AR
            (fun Q hQ ⟨⟨b, hb⟩, ⟨a, ha⟩, ⟨r, hr⟩⟩ => h3 Q hQ ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨r, hr⟩⟩)
        · obtain ⟨z0, hz0⟩ := hZne
          have hZ1 : ∀ z ∈ Z, z = z0 := fun z hz => Finset.card_le_one.1 (by omega : Z.card ≤ 1) z hz z0 hz0
          exact case2_sub4 gs outG hout hsz hmon hback htwo hreach hacc hrej i j uB uA wL wR
            hiA hjA hij hAP hjQ hi_no_bypass (fun w => by rw [hu_inp w, or_comm]) hwL_reach hwR_lt hwR_no_i hwj_inp
            z0 hZ1 hz0 ⟨by simpa [Finset.inter_comm] using hXe, hYe⟩
            (fun Q hQ ⟨⟨b, hb⟩, ⟨a, ha⟩, ⟨r, hr⟩⟩ => h3 Q hQ ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨r, hr⟩⟩)
      · have hXe : X = ∅ := Finset.not_nonempty_iff_eq_empty.1 hXne
        have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.1 hYne
        have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        refine case2_replace_i_or gs outG hout hsz hmon hback hacc hrej i j wL wR hiA hjA hij hAP hjQ hi_no_bypass
          hwR_lt hwR_no_i hwj_inp hwL_lt ⟨GateOp.or, []⟩ rfl (by simp) (by simp) (by simp) ?_ (by simp)
        intro p l hp hVj
        let pI : ℕ → Gate → Gate := fun m g => if m = i then ⟨GateOp.or, []⟩ else g
        let gs' := gs.mapIdx pI
        have hgs'_len : gs'.length = gs.length := List.length_mapIdx
        have hback' : ReadsBack 26 ⟨gs', 0⟩ := by
          apply mapIdx_readsBack; intro m g hg u hu; dsimp only [pI] at hu; split_ifs at hu with hm
          · simp at hu
          · have hml := (List.getElem?_eq_some_iff.1 hg).1
            have hgam : gateAt ⟨gs, 0⟩ m = g := by simp [gateAt, List.getD_eq_getElem?_getD, hg]
            exact hback m hml u (by rw [hgam]; exact hu)
        have hkeep0 : ∀ m g, m ∉ ({i} : Finset ℕ) → pI m g = g := fun m g hm => by
          simp only [Finset.mem_singleton] at hm; exact ite_eq_right hm
        rw [andN_iff gs _ (inp_len _ _) j gs[j] hg0j hbj hopj] at hVj
        have hVwL := hVj wL (by rw [← hga0j, hwj_inp]; left; rfl)
        have hVwR := hVj wR (by rw [← hga0j, hwj_inp]; right; rfl)
        cases hVi0 : V gs (inp {p} {l}) (26 + i)
        · have hbad_wL : reachesBadOnlyVia gs {i} i wL := fun b hb hbi _ => by simp at hb; exact absurd hb hbi
          exact mapIdx_eval_up gs pI {i} i hback hback' hgs_eq hkeep0 (inp {p} {l}) (inp_len _ _)
            (fun h => by rw [hVi0] at h; cases h) wL (by omega) hbad_wL hVwL
        · rw [andN_iff gs _ (inp_len _ _) i gs[i] hg0i hbi hopi] at hVi0
          obtain ⟨a, ha, hpa⟩ := (pureOr_V_orSet gs hback uA (by omega) huA_po (inp {p} {l}) (inp_len _ _)).1 (hVi0 uA (by rw [hui_eq]; simp))
          obtain ⟨b, hb, hpb⟩ := (pureOr_V_orSet gs hback uB (by omega) huB_po (inp {p} {l}) (inp_len _ _)).1 (hVi0 uB (by rw [hui_eq]; simp))
          obtain ⟨r, hr, hpr⟩ := (pureOr_V_orSet gs hback wR (by omega) hwR_po (inp {p} {l}) (inp_len _ _)).1 hVwR
          obtain ⟨c, hc, _⟩ := pigeonhole_hit A B R p l ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩ ⟨r, hr, hpr⟩
          simp only [Finset.mem_union] at hc
          rcases hc with (hc | hc) | hc
          · change c ∈ X at hc; rw [hXe] at hc; cases hc
          · change c ∈ Y at hc; rw [hYe] at hc; cases hc
          · change c ∈ Z at hc; rw [hZe] at hc; cases hc

theorem main_thm (gs : List Gate) (out : ℕ)
    (hsz : gs.length < 64)
    (hmon0 : PEqualNP.MetaComplexity.Monotone2 ⟨gs, out⟩)
    (hback : ReadsBack 26 ⟨gs, out⟩)
    (htwo : ∀ g ∈ gs, g.inputs.length = 2 ∧ g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)
    (i j : ℕ) (hiA : (gateAt ⟨gs, out⟩ i).op = GateOp.and)
    (hjA : (gateAt ⟨gs, out⟩ j).op = GateOp.and)
    (hij : InCone 26 ⟨gs, out⟩ i j)
    (hAP : PEqualNP.TopForm.andPairs 26 ⟨gs, out⟩ ≤ 1)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) out = false) :
    ∃ C' : Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧
      (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → V C'.gates (inp {p} {l}) C'.output = true) ∧
      (∀ Q : Finset (Fin 13), isQuad Q → V C'.gates (inp Q (TQ Q)) C'.output = false) ∧
      C'.size < gs.length := by
  have hmon : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := fun g hg => by
    have hm := hmon0 g hg
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hm
  rcases reach_reduction gs out hmon hback hacc hrej with hRed | ⟨outG, hout_eq, hout, hreach⟩
  · exact hRed
  · subst hout_eq
    have hgs_eq : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hmon g hg).1
    have hiA0 : (gateAt ⟨gs, 0⟩ i).op = GateOp.and := hiA
    have hjA0 : (gateAt ⟨gs, 0⟩ j).op = GateOp.and := hjA
    have hij0 : InCone 26 ⟨gs, 0⟩ i j := hij
    have hAP0 : PEqualNP.TopForm.andPairs 26 ⟨gs, 0⟩ ≤ 1 := hAP
    have hback0 : ReadsBack 26 ⟨gs, 0⟩ := hback
    have hreach0 : ∀ k < gs.length, k = outG ∨ InCone 26 ⟨gs, 0⟩ k outG := hreach
    have hlt := inCone_lt ⟨gs, 0⟩ i j hij0
    dsimp only at hlt
    have hjQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + j) = false := by
      intro Q hQ
      by_cases hjo : j = outG
      · subst hjo; exact hrej Q hQ
      · have hinc_jo := (hreach0 j hlt.2).resolve_left hjo
        rcases reachesAvoiding_split gs gs.length (26 + j) hgs_eq (26 + outG) (inCone_reachesAvoiding gs j outG hinc_jo) with hOr | hAnd
        · rw [Bool.eq_false_iff]; intro htr
          have := reachesOr_V gs gs.length (26 + j) hback0 (inp Q (TQ Q)) (inp_len _ _) (26 + outG) hOr htr
          rw [hrej Q hQ] at this; cases this
        · obtain ⟨a, ga, hga, haop, _, _, u, hu, hult, hOr⟩ := hAnd
          have halen : a < gs.length := (List.getElem?_eq_some_iff.1 hga).1
          have hga_eq : gateAt ⟨gs, 0⟩ a = ga := by simp [gateAt, List.getD_eq_getElem?_getD, hga]
          have hja : InCone 26 ⟨gs, 0⟩ j a := by
            rcases reachesOr_inCone gs gs.length (26 + j) u (by omega) hOr with heq | ⟨hu26, hic⟩
            · rw [heq] at hu
              exact inCone_direct ⟨gs, 0⟩ j a halen (by rw [hga_eq]; exact hu)
                (by have := hback0 a halen (26 + j) (by rw [hga_eq]; exact hu); omega)
            · exact (inCone_iff 26 ⟨gs, 0⟩ j a halen).2 ⟨u, by rw [hga_eq]; exact hu, hu26, hult, Or.inr (by simpa [Nat.add_sub_cancel_left] using hic)⟩
          have := (andPairs_unique ⟨gs, 0⟩ hAP0 hiA0 hjA0 hij0 hjA0 (by rw [hga_eq]; exact haop) hja).1
          omega
    by_cases hiQ : ∀ Q : Finset (Fin 13), isQuad Q → V gs (inp Q (TQ Q)) (26 + i) = false
    · exact False.elim (case1_contradiction gs outG hout hsz hmon hback0 htwo hreach0 hacc hrej i j hiA0 hjA0 hij0 hAP0 hiQ)
    · push Not at hiQ
      obtain ⟨Q0, hQ0, hQ0_tr⟩ := hiQ
      have hQ0_t : V gs (inp Q0 (TQ Q0)) (26 + i) = true := by
        cases h : V gs (inp Q0 (TQ Q0)) (26 + i)
        · exact absurd h hQ0_tr
        · rfl
      exact False.elim (case2_contradiction gs outG hout hsz hmon hback0 htwo hreach0 hacc hrej i j hiA0 hjA0 hij0 hAP0 hjQ ⟨Q0, hQ0, hQ0_t⟩)

end L1961


end PEqualNP.Outside.L_meta_1961_aux


theorem PEqualNP.Outside.L_meta_1961 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro x1 x2 x3 C hmon hback hsound hsz hnested htwo hAP
  obtain ⟨gs, out⟩ := C
  have hacc := hsound.1
  have hrej := hsound.2
  obtain ⟨i, j, hiA, hjA, hij⟩ := hnested
  have hres := PEqualNP.Outside.L_meta_1961_aux.L1961.main_thm gs out hsz hmon hback htwo i j hiA hjA hij hAP
    (fun p l hpl => by
      have he : PEqualNP.Outside.L_meta_1961_aux.inp {p} {l}
          = List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l)) := by
        unfold PEqualNP.Outside.L_meta_1961_aux.inp
        simp only [Finset.mem_singleton]
      rw [← PEqualNP.Outside.L_meta_1961_aux.eval_eq, he]
      exact hacc p l hpl)
    (fun Q hQ => by
      have he : PEqualNP.Outside.L_meta_1961_aux.inp Q (PEqualNP.Outside.L_meta_1961_aux.TQ Q)
          = List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 =>
              decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) := by
        unfold PEqualNP.Outside.L_meta_1961_aux.inp PEqualNP.Outside.L_meta_1961_aux.TQ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← PEqualNP.Outside.L_meta_1961_aux.eval_eq, he]
      exact hrej Q hQ.1 hQ.2)
  obtain ⟨⟨gs', out'⟩, hmon', hback', hacc', hrej', hsz'⟩ := hres
  refine ⟨⟨gs', out'⟩, hmon', hback', ⟨?_, ?_⟩, hsz'⟩
  · intro p l hpl
    have he : PEqualNP.Outside.L_meta_1961_aux.inp {p} {l}
        = List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l)) := by
      unfold PEqualNP.Outside.L_meta_1961_aux.inp
      simp only [Finset.mem_singleton]
    rw [PEqualNP.Outside.L_meta_1961_aux.eval_eq, ← he]
    exact hacc' p l hpl
  · intro Q hc hk
    have he : PEqualNP.Outside.L_meta_1961_aux.inp Q (PEqualNP.Outside.L_meta_1961_aux.TQ Q)
        = List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 =>
            decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) := by
      unfold PEqualNP.Outside.L_meta_1961_aux.inp PEqualNP.Outside.L_meta_1961_aux.TQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [PEqualNP.Outside.L_meta_1961_aux.eval_eq, ← he]
    exact hrej' Q ⟨hc, hk⟩

