import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1836

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem ifp {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem ifn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem difp {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬ c → α} :
    dite c a b = a h := by simp [h]

theorem difn {α : Type} {c : Prop} [Decidable c] (h : ¬ c) {a : c → α} {b : ¬ c → α} :
    dite c a b = b h := by simp [h]

def fd {α : Type} (F : Gate → List α → α) (X : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [F g w]) X

theorem fd_len {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α), (fd F X gs).length = X.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro X; simp [fd]
  | cons g gs ih =>
    intro X
    have := ih (X ++ [F g X])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp
    omega

theorem fd_pre {α : Type} (F : Gate → List α → α) :
    ∀ (gs : List Gate) (X : List α) (i : ℕ), i < X.length → (fd F X gs)[i]? = X[i]? := by
  intro gs
  induction gs with
  | nil => intro X i _; simp [fd]
  | cons g gs ih =>
    intro X i hi
    have := ih (X ++ [F g X]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this, List.getElem?_append_left hi]

theorem fd_app {α : Type} (F : Gate → List α → α) (X : List α) (gs hs : List Gate) :
    fd F X (gs ++ hs) = fd F (fd F X gs) hs := by
  simp [fd, List.foldl_append]

theorem fd_gate' {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (as : List Gate) (g : Gate) (bs : List Gate) (X : List α)
    (hrb : ∀ i ∈ g.inputs, i < X.length + as.length) :
    (fd F X (as ++ g :: bs)).getD (X.length + as.length) dflt = F g (fd F X (as ++ g :: bs)) := by
  have e1 : fd F X (as ++ g :: bs) = fd F (fd F X as ++ [F g (fd F X as)]) bs := by
    simp [fd, List.foldl_append]
  have hWl : (fd F X as).length = X.length + as.length := fd_len F as X
  have key : ∀ i, i < (fd F X as).length + 1 →
      (fd F X (as ++ g :: bs))[i]? = (fd F X as ++ [F g (fd F X as)])[i]? := by
    intro i hi
    rw [e1]
    exact fd_pre F bs _ i (by simp; omega)
  rw [List.getD_eq_getElem?_getD, key _ (by omega), ← hWl,
    List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply hF
  intro i hi
  have hi' := hrb i hi
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, key i (by omega),
    List.getElem?_append_left (by omega)]

theorem fd_gate {α : Type} (F : Gate → List α → α) (dflt : α)
    (hF : ∀ (g : Gate) (w w' : List α),
      (∀ i ∈ g.inputs, w.getD i dflt = w'.getD i dflt) → F g w = F g w')
    (gs : List Gate) (X : List α) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < X.length + j) :
    (fd F X gs).getD (X.length + j) dflt = F (gs.getD j ⟨GateOp.or, []⟩) (fd F X gs) := by
  have h1 : gs.take j ++ gs[j] :: gs.drop (j + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hj]
    exact List.take_append_drop j gs
  have h2 : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := by
    simp [List.getD_eq_getElem?_getD, hj]
  have h3 := fd_gate' F dflt hF (gs.take j) gs[j] (gs.drop (j + 1)) X (by
    rw [List.length_take, min_eq_left hj.le, ← h2]
    exact hrb)
  rw [h1, List.length_take, min_eq_left hj.le] at h3
  rw [h2]
  exact h3

def stpF : Gate → List Bool → Bool :=
  fun g w => g.op.eval (g.inputs.map fun i => w.getD i false)

theorem stpF_congr (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = w'.getD i false) : stpF g w = stpF g w' := by
  unfold stpF
  rw [List.map_congr_left h]

theorem ld_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : g.lineDegree w = g.lineDegree w' := by
  unfold Gate.lineDegree
  rw [List.map_congr_left h]

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ifn (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ifn (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (fd stpF W1 gs).getD i false = true → (fd stpF W2 gs).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa [fd] using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    have := ih (W1 ++ [stpF g W1]) (W2 ++ [stpF g W2]) (by simp [hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) (by
        intro i
        simp only [getD_snoc, hl]
        split_ifs
        · unfold stpF
          rcases hop g List.mem_cons_self with ha | ho
          · rw [ev_and g _ ha, ev_and g _ ha]
            intro h k hk
            exact H k (h k hk)
          · rw [ev_or g _ ho, ev_or g _ ho]
            rintro ⟨k, hk, h⟩
            exact ⟨k, hk, H k h⟩
        · exact H i)
    simpa only [fd, List.foldl_cons] using this

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem app_getD {n m : ℕ} (x : Fin n → Bool) (y : Fin m → Bool) (i : ℕ) :
    (List.ofFn (Fin.append x y)).getD i false =
      if h : i < n then x ⟨i, h⟩ else if h2 : i - n < m then y ⟨i - n, h2⟩ else false := by
  rw [ofFn_getD]
  by_cases h : i < n
  · rw [difp (by omega), difp h]
    exact Fin.append_left x y ⟨i, h⟩
  · rw [difn h]
    by_cases h2 : i - n < m
    · rw [difp (by omega), difp h2]
      have hh : (⟨i, by omega⟩ : Fin (n + m)) = Fin.natAdd n ⟨i - n, h2⟩ := by
        apply Fin.ext
        show i = n + (i - n)
        omega
      rw [hh, Fin.append_right]
    · rw [difn (by omega), difn h2]

abbrev VV (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

abbrev DD (n : ℕ) (mk : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees n mk).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem VV_in (C : Circuit) (X : List Bool) (w : ℕ) (hw : w < X.length) :
    VV C X w = X.getD w false := by
  show (C.wires X).getD w false = X.getD w false
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hw]

theorem VV_out (C : Circuit) (X : List Bool) (w : ℕ) (hw : X.length + C.gates.length ≤ w) :
    VV C X w = false := by
  show (C.wires X).getD w false = false
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; exact hw)]
  rfl

theorem VV_gate (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (X : List Bool) (hX : X.length = n)
    (j : ℕ) (hj : j < C.gates.length) :
    VV C X (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (VV C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem DD_len (n : ℕ) (mk : Finset ℕ) (C : Circuit) :
    (C.lineDegrees n mk).length = n + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates ((List.range n).map fun i => if i ∈ mk then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem DD_in (n : ℕ) (mk : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    DD n mk C w = if w ∈ mk then 1 else 0 := by
  show (C.lineDegrees n mk).getD w 0 = _
  unfold Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range n).map fun i => if i ∈ mk then 1 else 0) w (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem DD_out (n : ℕ) (mk : Finset ℕ) (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    DD n mk C w = 0 := by
  show (C.lineDegrees n mk).getD w 0 = 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [DD_len]; exact hw)]
  rfl

theorem DD_gate (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hrb : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) :
    DD n mk C (n + j) = (gateAt C j).lineDegree (C.lineDegrees n mk) := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range n).map fun i => if i ∈ mk then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  exact h

theorem gate_shape (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, gateAt C j = ⟨GateOp.and, [a, b]⟩ ∨ gateAt C j = ⟨GateOp.or, [a, b]⟩ := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hg _ hmem
  obtain ⟨a, b, hins⟩ := List.length_eq_two.mp hlen
  refine ⟨a, b, ?_⟩
  have e : gateAt C j = ⟨(gateAt C j).op, (gateAt C j).inputs⟩ := rfl
  rcases hop with h | h
  · left
    rw [e, h, hins]
  · right
    rw [e, h, hins]

theorem V_and (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (X : List Bool) (hX : X.length = n)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.and, [a, b]⟩) :
    VV C X (n + j) = (VV C X a && VV C X b) := by
  rw [VV_gate n C hrb X hX j hj, h]
  simp [GateOp.eval]

theorem V_or (n : ℕ) (C : Circuit) (hrb : ReadsBack n C) (X : List Bool) (hX : X.length = n)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.or, [a, b]⟩) :
    VV C X (n + j) = (VV C X a || VV C X b) := by
  rw [VV_gate n C hrb X hX j hj, h]
  simp [GateOp.eval]

theorem D_and (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.and, [a, b]⟩) :
    DD n mk C (n + j) = DD n mk C a + DD n mk C b := by
  rw [DD_gate n mk C hrb j hj, h]
  unfold Gate.lineDegree
  split_ifs with hc
  · simp
  · exact absurd rfl hc

theorem D_or (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (a b : ℕ) (h : gateAt C j = ⟨GateOp.or, [a, b]⟩) :
    DD n mk C (n + j) = max (DD n mk C a) (DD n mk C b) := by
  rw [DD_gate n mk C hrb j hj, h]
  simp [Gate.lineDegree]

theorem indep (n : ℕ) (mk : Finset ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack n C) (X X' : List Bool) (hX : X.length = n) (hX' : X'.length = n)
    (hag : ∀ i, i < n → i ∉ mk → X.getD i false = X'.getD i false) :
    ∀ w, DD n mk C w = 0 → VV C X w = VV C X' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases h1 : w < n
    · rw [DD_in n mk C w h1] at hd
      have hwm : w ∉ mk := by
        intro hc
        rw [ifp hc] at hd
        omega
      rw [VV_in C X w (by omega), VV_in C X' w (by omega)]
      exact hag w h1 hwm
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨a, b, hab | hab⟩ := gate_shape C hg j hj
        · have ha : a < n + j := hrb j hj a (by simp [hab])
          have hb : b < n + j := hrb j hj b (by simp [hab])
          rw [D_and n mk C hrb j hj a b hab] at hd
          rw [V_and n C hrb X hX j hj a b hab, V_and n C hrb X' hX' j hj a b hab,
            ih a ha (by omega), ih b hb (by omega)]
        · have ha : a < n + j := hrb j hj a (by simp [hab])
          have hb : b < n + j := hrb j hj b (by simp [hab])
          rw [D_or n mk C hrb j hj a b hab] at hd
          have l1 := le_max_left (DD n mk C a) (DD n mk C b)
          have l2 := le_max_right (DD n mk C a) (DD n mk C b)
          rw [V_or n C hrb X hX j hj a b hab, V_or n C hrb X' hX' j hj a b hab,
            ih a ha (by omega), ih b hb (by omega)]
      · rw [VV_out C X w (by omega), VV_out C X' w (by omega)]

abbrev E (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

abbrev dL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

abbrev dP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

theorem E_mono (N : ℕ) (C : Circuit) (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin N → Bool) (y : Fin N → Bool) (w : ℕ)
    (h : E N C x (fun _ => false) w = true) : E N C x y w = true := by
  unfold E at h ⊢
  rw [wires_fd] at h ⊢
  refine mono C.gates _ _ (by simp) hm ?_ w h
  intro i
  rw [app_getD, app_getD]
  split_ifs <;> simp

theorem E_indep_y (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) (x : Fin N → Bool) (w : ℕ) (hd : dL N C w = 0)
    (y y' : Fin N → Bool) : E N C x y w = E N C x y' w :=
  indep (N + N) (Finset.Ico N (N + N)) C hg hrb _ _ (by simp) (by simp) (fun i hi hni => by
    have hiN : i < N := by
      by_contra hc
      exact hni (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
    rw [app_getD, app_getD, difp hiN, difp hiN]) w hd

theorem E_indep_x (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) (y : Fin N → Bool) (w : ℕ) (hd : dP N C w = 0)
    (x x' : Fin N → Bool) : E N C x y w = E N C x' y w :=
  indep (N + N) (Finset.range N) C hg hrb _ _ (by simp) (by simp) (fun i _ hni => by
    have hiN : ¬ i < N := fun hc => hni (Finset.mem_range.mpr hc)
    rw [app_getD, app_getD, difn hiN, difn hiN]) w hd

theorem E_pt (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) (hw : w < N) :
    E N C x y w = x ⟨w, hw⟩ := by
  show VV C (List.ofFn (Fin.append x y)) w = _
  rw [VV_in C (List.ofFn (Fin.append x y)) w (by rw [List.length_ofFn]; omega), app_getD, difp hw]

theorem dL_in (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N + N) :
    dL N C w = if N ≤ w then 1 else 0 := by
  have := DD_in (N + N) (Finset.Ico N (N + N)) C w hw
  show DD (N + N) (Finset.Ico N (N + N)) C w = _
  rw [this]
  simp [hw]

theorem dP_in (N : ℕ) (C : Circuit) (w : ℕ) (hw : w < N + N) :
    dP N C w = if w < N then 1 else 0 := by
  have := DD_in (N + N) (Finset.range N) C w hw
  show DD (N + N) (Finset.range N) C w = _
  rw [this]
  simp

def F {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun d g => d ++ [f g d]) init

def ev (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = F ev C.gates x := rfl

theorem getD_app_lt {α : Type} (A B : List α) (d : α) (i : ℕ) (h : i < A.length) :
    (A ++ B).getD i d = A.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge {α : Type} (A B : List α) (d : α) (i : ℕ) (h : A.length ≤ i) :
    (A ++ B).getD i d = B.getD (i - A.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_big {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_true_lt (l : List Bool) (i : ℕ) (h : l.getD i false = true) : i < l.length := by
  by_contra hc
  rw [getD_big l false i (by omega)] at h
  exact absurd h (by decide)

theorem pre_getD {α : Type} {P Q : List α} (h : P <+: Q) (i : ℕ) (d : α) (hi : i < P.length) :
    Q.getD i d = P.getD i d := by
  obtain ⟨r, rfl⟩ := h
  exact getD_app_lt _ _ _ _ hi

theorem pre_zero {P Q : List ℕ} (h : P <+: Q) (u : ℕ) (hu : Q.getD u 0 = 0) : P.getD u 0 = 0 := by
  by_cases hlt : u < P.length
  · rw [← pre_getD h u 0 hlt]
    exact hu
  · exact getD_big _ _ _ (by omega)

theorem F_snoc {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α) :
    F f (gs ++ [g]) init = F f gs init ++ [f g (F f gs init)] := by
  simp [F, List.foldl_append]

theorem F_cons {α : Type} (f : Gate → List α → α) (gs : List Gate) (g : Gate) (init : List α) :
    F f (g :: gs) init = F f gs (init ++ [f g init]) := rfl

theorem F_app {α : Type} (f : Gate → List α → α) (A B : List Gate) (init : List α) :
    F f (A ++ B) init = F f B (F f A init) := by
  simp [F, List.foldl_append]

theorem F_len {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) :
    (F f gs init).length = init.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [F]
  | append_singleton gs g ih =>
    rw [F_snoc]
    simp [ih]
    omega

theorem F_pre {α : Type} (f : Gate → List α → α) (gs : List Gate) (init : List α) :
    init <+: F f gs init := by
  induction gs using List.reverseRecOn with
  | nil => exact List.prefix_refl _
  | append_singleton gs g ih =>
    rw [F_snoc]
    exact ih.trans (List.prefix_append _ _)

theorem F_at {α : Type} (f : Gate → List α → α) (g0 : Gate) (d : α) (gs : List Gate) (init : List α)
    (j : ℕ) (hj : j < gs.length) :
    ∃ pre : List α, pre <+: F f gs init ∧ pre.length = init.length + j ∧
      (F f gs init).getD (init.length + j) d = f (gs.getD j g0) pre := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    rw [F_snoc]
    by_cases h : j < gs.length
    · obtain ⟨pre, h1, h2, h3⟩ := ih h
      refine ⟨pre, h1.trans (List.prefix_append _ _), h2, ?_⟩
      rw [getD_app_lt _ _ _ _ (by rw [F_len]; omega), h3, getD_app_lt _ _ _ _ h]
    · have hj' : j = gs.length := by
        simp at hj
        omega
      subst hj'
      refine ⟨F f gs init, List.prefix_append _ _, F_len _ _ _, ?_⟩
      rw [getD_app_ge _ _ _ _ (by rw [F_len]), getD_app_ge _ _ _ _ (le_refl _)]
      simp [F_len]

def lastIdx {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) : ℕ → Option ℕ
  | 0 => none
  | k + 1 => if cls k = c then some k else lastIdx cls c k

theorem lastIdx_none {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) :
    ∀ k, lastIdx cls c k = none → ∀ i, i < k → cls i ≠ c := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    omega
  | succ k ih =>
    intro h i hi
    unfold lastIdx at h
    split at h
    · cases h
    · rename_i hne
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
      · exact ih h i h1
      · rw [h1]
        exact hne

theorem lastIdx_some {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) :
    ∀ k i, lastIdx cls c k = some i → i < k ∧ cls i = c ∧ ∀ i', i' < k → cls i' = c → i' ≤ i := by
  intro k
  induction k with
  | zero =>
    intro i h
    simp [lastIdx] at h
  | succ k ih =>
    intro i h
    unfold lastIdx at h
    split at h
    · rename_i he
      have hik : k = i := by
        injection h
      rw [← hik]
      exact ⟨Nat.lt_succ_self _, he, fun i' hi' _ => Nat.lt_succ_iff.1 hi'⟩
    · rename_i hne
      obtain ⟨h1, h2, h3⟩ := ih i h
      refine ⟨Nat.lt_succ_of_lt h1, h2, fun i' hi' hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h4 | h4
      · exact h3 i' h4 hc
      · rw [h4] at hc
        exact absurd hc hne

def pick (o : Option ℕ) (dflt B : ℕ) : ℕ :=
  match o with
  | some i => B + i
  | none => dflt

theorem pick_cases {κ : Type} [DecidableEq κ] (cls : ℕ → κ) (c : κ) (k dflt B : ℕ) :
    pick (lastIdx cls c k) dflt B = dflt ∨ ∃ i, i < k ∧ pick (lastIdx cls c k) dflt B = B + i := by
  cases hl : lastIdx cls c k with
  | none =>
    left
    rfl
  | some i =>
    right
    exact ⟨i, (lastIdx_some cls c k i hl).1, rfl⟩

def cg {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (k : ℕ) : Gate :=
  ⟨GateOp.or, [a k, pick (lastIdx cls (cls k) k) (a k) B]⟩

def blk {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ) : List Gate :=
  (List.range m).map (cg B a cls)

def outw {κ : Type} [DecidableEq κ] (B : ℕ) (cls : ℕ → κ) (m : ℕ) (c : κ) : ℕ :=
  pick (lastIdx cls c m) (B + m) B

theorem blk_len {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ) :
    (blk B a cls m).length = m := by
  simp [blk]

theorem blk_getD {κ : Type} [DecidableEq κ] (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m k : ℕ) (hk : k < m) :
    (blk B a cls m).getD k ⟨GateOp.or, []⟩ = cg B a cls k := by
  rw [List.getD_eq_getElem _ _ (by rw [blk_len]; exact hk)]
  simp [blk]

theorem evO (a b : ℕ) (w : List Bool) :
    ev ⟨GateOp.or, [a, b]⟩ w = (w.getD a false || w.getD b false) := by
  simp [ev, GateOp.eval]

theorem blk_val {κ : Type} [DecidableEq κ] (W0 : List Bool) (B : ℕ) (hB : W0.length = B) (a : ℕ → ℕ)
    (cls : ℕ → κ) (m : ℕ) (ha : ∀ i, i < m → a i < B) :
    ∀ k, k < m → ((F ev (blk B a cls m) W0).getD (B + k) false = true ↔
      ∃ i, i ≤ k ∧ cls i = cls k ∧ W0.getD (a i) false = true) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨pre, hp1, hp2, hp3⟩ := F_at ev ⟨GateOp.or, []⟩ false (blk B a cls m) W0 k
      (by rw [blk_len]; exact hk)
    rw [hB] at hp2 hp3
    rw [hp3, blk_getD B a cls m k hk]
    have hW0 : W0 <+: F ev (blk B a cls m) W0 := F_pre _ _ _
    have hak := ha k hk
    have e1 : pre.getD (a k) false = W0.getD (a k) false := by
      rw [← pre_getD hp1 (a k) false (by omega), pre_getD hW0 (a k) false (by omega)]
    cases hl : lastIdx cls (cls k) k with
    | none =>
      have hv : ev (cg B a cls k) pre = W0.getD (a k) false := by
        unfold cg
        rw [evO, hl]
        simp only [pick]
        rw [e1, Bool.or_self]
      rw [hv]
      constructor
      · intro h
        exact ⟨k, le_refl _, rfl, h⟩
      · rintro ⟨i, hi, hc, hv'⟩
        rcases Nat.lt_or_eq_of_le hi with h1 | h1
        · exact absurd hc (lastIdx_none cls (cls k) k hl i h1)
        · rw [h1] at hv'
          exact hv'
    | some i0 =>
      obtain ⟨h1, h2, h3⟩ := lastIdx_some cls (cls k) k i0 hl
      have e2 : pre.getD (B + i0) false = (F ev (blk B a cls m) W0).getD (B + i0) false :=
        (pre_getD hp1 (B + i0) false (by omega)).symm
      have hv : ev (cg B a cls k) pre
          = (W0.getD (a k) false || (F ev (blk B a cls m) W0).getD (B + i0) false) := by
        unfold cg
        rw [evO, hl]
        simp only [pick]
        rw [e1, e2]
      rw [hv, Bool.or_eq_true, ih i0 h1 (by omega)]
      constructor
      · rintro (h | ⟨i, hi, hc, hv'⟩)
        · exact ⟨k, le_refl _, rfl, h⟩
        · exact ⟨i, by omega, hc.trans h2, hv'⟩
      · rintro ⟨i, hi, hc, hv'⟩
        rcases Nat.lt_or_eq_of_le hi with h4 | h4
        · exact Or.inr ⟨i, h3 i h4 hc, hc.trans h2.symm, hv'⟩
        · rw [h4] at hv'
          exact Or.inl hv'

theorem blk_out {κ : Type} [DecidableEq κ] (W0 : List Bool) (B : ℕ) (hB : W0.length = B) (a : ℕ → ℕ)
    (cls : ℕ → κ) (m : ℕ) (ha : ∀ i, i < m → a i < B) (c : κ) :
    ((F ev (blk B a cls m) W0).getD (outw B cls m c) false = true ↔
      ∃ i, i < m ∧ cls i = c ∧ W0.getD (a i) false = true) := by
  unfold outw
  cases hl : lastIdx cls c m with
  | none =>
    have hlen : (F ev (blk B a cls m) W0).length = B + m := by
      rw [F_len, hB, blk_len]
    have hf : (F ev (blk B a cls m) W0).getD (B + m) false = false := getD_big _ _ _ (by omega)
    simp only [pick]
    rw [hf]
    constructor
    · intro h
      exact absurd h (by decide)
    · rintro ⟨i, hi, hc, _⟩
      exact absurd hc (lastIdx_none cls c m hl i hi)
  | some i0 =>
    obtain ⟨h1, h2, h3⟩ := lastIdx_some cls c m i0 hl
    simp only [pick]
    rw [blk_val W0 B hB a cls m ha i0 h1]
    constructor
    · rintro ⟨i, hi, hc, hv⟩
      exact ⟨i, by omega, hc.trans h2, hv⟩
    · rintro ⟨i, hi, hc, hv⟩
      exact ⟨i, h3 i hi hc, hc.trans h2.symm, hv⟩

theorem XX_sem {κ : Type} [DecidableEq κ] (n : ℕ) (G : List Gate) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ)
    (ha : ∀ i, i < m → a i < n + G.length) (x : List Bool) (hx : x.length = n) (c : κ) :
    ((Circuit.wires ⟨G ++ blk (n + G.length) a cls m, 0⟩ x).getD (outw (n + G.length) cls m c) false = true ↔
      ∃ i, i < m ∧ cls i = c ∧ (F ev G x).getD (a i) false = true) := by
  have h := blk_out (F ev G x) (n + G.length) (by rw [F_len, hx]) a cls m ha c
  rw [← F_app] at h
  exact h

theorem XX_ao {κ : Type} [DecidableEq κ] (G : List Gate) (B : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ)
    (h0 : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ g ∈ (Circuit.mk (G ++ blk B a cls m) 0).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hgm
  rcases List.mem_append.1 hgm with h | h
  · exact h0 g h
  · unfold blk at h
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 h
    exact ⟨Or.inr rfl, rfl⟩

theorem XX_rb {κ : Type} [DecidableEq κ] (n : ℕ) (G : List Gate) (o : ℕ) (a : ℕ → ℕ) (cls : ℕ → κ) (m : ℕ)
    (h0 : ReadsBack n ⟨G, o⟩) (ha : ∀ i, i < m → a i < n + G.length) :
    ReadsBack n ⟨G ++ blk (n + G.length) a cls m, 0⟩ := by
  intro j hj i hi
  have hj' : j < G.length + m := by
    have h1 : j < (G ++ blk (n + G.length) a cls m).length := hj
    rw [List.length_append, blk_len] at h1
    exact h1
  by_cases h : j < G.length
  · have e : gateAt ⟨G ++ blk (n + G.length) a cls m, 0⟩ j = gateAt ⟨G, o⟩ j :=
      getD_app_lt _ _ _ _ h
    rw [e] at hi
    exact h0 j h i hi
  · have e : gateAt ⟨G ++ blk (n + G.length) a cls m, 0⟩ j = cg (n + G.length) a cls (j - G.length) := by
      show (G ++ blk (n + G.length) a cls m).getD j ⟨GateOp.or, []⟩ = _
      rw [getD_app_ge _ _ _ _ (by omega)]
      exact blk_getD _ _ _ _ _ (by omega)
    rw [e] at hi
    have hi' : i = a (j - G.length) ∨
        i = pick (lastIdx cls (cls (j - G.length)) (j - G.length)) (a (j - G.length)) (n + G.length) := by
      simpa [cg] using hi
    have hak := ha (j - G.length) (by omega)
    rcases hi' with e1 | e1
    · omega
    · rcases pick_cases cls (cls (j - G.length)) (j - G.length) (a (j - G.length)) (n + G.length) with e2 | ⟨i0, hi0, e2⟩
      · omega
      · omega

theorem getD_mem' (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem mem_getD' (l : List ℕ) (j : ℕ) (hj : j ∈ l) : ∃ i, i < l.length ∧ l.getD i 0 = j := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hj
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩

abbrev AO2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem pos_of (a b : ℕ) (h : a = 0 → b = 0) (hb : 0 < b) : 0 < a := by
  by_contra hc
  have := h (by omega)
  omega

theorem D_zero (n : ℕ) (mk : Finset ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    DD n mk C (n + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, DD n mk C i = 0 := by
  obtain ⟨a, b, hab | hab⟩ := gate_shape C hg j hj
  · rw [D_and n mk C hrb j hj a b hab, hab]
    constructor
    · intro h i hi
      have hi' : i = a ∨ i = b := by simpa using hi
      rcases hi' with e | e <;> rw [e] <;> omega
    · intro h
      have ha := h a (by simp)
      have hb := h b (by simp)
      omega
  · rw [D_or n mk C hrb j hj a b hab, hab]
    have l1 := le_max_left (DD n mk C a) (DD n mk C b)
    have l2 := le_max_right (DD n mk C a) (DD n mk C b)
    constructor
    · intro h i hi
      have hi' : i = a ∨ i = b := by simpa using hi
      rcases hi' with e | e <;> rw [e] <;> omega
    · intro h
      have ha := h a (by simp)
      have hb := h b (by simp)
      rw [ha, hb]
      exact max_self 0

abbrev Sub (C D : Circuit) : Prop :=
  D.gates.length = C.gates.length ∧ ∀ j, j < C.gates.length →
    ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) ∧ (gateAt D j).inputs.length = 2 ∧
      ∀ i ∈ (gateAt D j).inputs, i ∈ (gateAt C j).inputs

theorem sub_ao (C D : Circuit) (h : Sub C D) : AO2 D := by
  intro g hgm
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.1 hgm
  have e' : gateAt D j = g := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact e
  have h2 := h.2 j (lt_of_lt_of_eq hj h.1)
  rw [e'] at h2
  exact ⟨h2.1, h2.2.1⟩

theorem sub_rb (n : ℕ) (C D : Circuit) (hrb : ReadsBack n C) (h : Sub C D) : ReadsBack n D := by
  intro j hj i hi
  have hj' : j < C.gates.length := lt_of_lt_of_eq hj h.1
  exact hrb j hj' i ((h.2 j hj').2.2 i hi)

theorem dz_sub (n : ℕ) (mk : Finset ℕ) (C D : Circuit) (hg : AO2 C) (hrb : ReadsBack n C)
    (h : Sub C D) : ∀ w, DD n mk C w = 0 → DD n mk D w = 0 := by
  have hgD := sub_ao C D h
  have hrD := sub_rb n C D hrb h
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases h1 : w < n
    · rw [DD_in n mk D w h1, ← DD_in n mk C w h1]
      exact hd
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hjD : j < D.gates.length := lt_of_lt_of_eq hj h.1.symm
        have hd' := (D_zero n mk C hg hrb j hj).1 hd
        refine (D_zero n mk D hgD hrD j hjD).2 ?_
        intro i hi
        have hiC := (h.2 j hj).2.2 i hi
        exact ih i (hrb j hj i hiC) (hd' i hiC)
      · exact DD_out n mk D w (by rw [h.1]; omega)

def md (C : Circuit) (f : ℕ → Gate) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => f j.val), C.output⟩

theorem md_len (C : Circuit) (f : ℕ → Gate) : (md C f).gates.length = C.gates.length := by
  simp [md]

theorem md_gate (C : Circuit) (f : ℕ → Gate) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (md C f) j = f j := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ (by rw [md_len]; exact hj)]
  simp [md]

def Cr (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ ((∃ i ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨ (∀ h ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))

noncomputable def orG (N : ℕ) (C : Circuit) (j : ℕ) : Gate :=
  @ite Gate (Cr N C j) (Classical.propDecidable _) ⟨GateOp.or, (gateAt C j).inputs⟩ (gateAt C j)

noncomputable def vwG (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) : Gate :=
  @ite Gate (Cr N C j) (Classical.propDecidable _) ⟨GateOp.or, [(gateAt C j).inputs.getD (sg j).val 0, (gateAt C j).inputs.getD (sg j).val 0]⟩ (gateAt C j)

noncomputable abbrev CO (N : ℕ) (C : Circuit) : Circuit := md C (orG N C)

noncomputable abbrev VW (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) : Circuit := md C (vwG N C sg)

theorem orG_pos (N : ℕ) (C : Circuit) (j : ℕ) (h : Cr N C j) :
    orG N C j = ⟨GateOp.or, (gateAt C j).inputs⟩ := by
  unfold orG
  exact if_pos h

theorem orG_neg (N : ℕ) (C : Circuit) (j : ℕ) (h : ¬ Cr N C j) : orG N C j = gateAt C j := by
  unfold orG
  exact if_neg h

theorem vw_pos (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (h : Cr N C j) :
    vwG N C sg j = ⟨GateOp.or, [(gateAt C j).inputs.getD (sg j).val 0, (gateAt C j).inputs.getD (sg j).val 0]⟩ := by
  unfold vwG
  exact if_pos h

theorem vw_neg (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (h : ¬ Cr N C j) :
    vwG N C sg j = gateAt C j := by
  unfold vwG
  exact if_neg h

theorem co_inputs (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt (CO N C) j).inputs = (gateAt C j).inputs := by
  rw [md_gate _ _ j hj]
  by_cases hc : Cr N C j
  · have hcg := congrArg Gate.inputs (orG_pos N C j hc)
    exact hcg
  · have hcg := congrArg Gate.inputs (orG_neg N C j hc)
    exact hcg

theorem sub_co (N : ℕ) (C : Circuit) (hg : AO2 C) : Sub C (CO N C) := by
  refine ⟨md_len _ _, fun j hj => ?_⟩
  rw [md_gate _ _ j hj]
  have hm := hg _ (gate_mem C j hj)
  by_cases hc : Cr N C j
  · rw [orG_pos N C j hc]
    exact ⟨Or.inr rfl, hm.2, fun i hi => hi⟩
  · rw [orG_neg N C j hc]
    exact ⟨hm.1, hm.2, fun i hi => hi⟩

theorem co_sub (N : ℕ) (C : Circuit) (hg : AO2 C) : Sub (CO N C) C := by
  refine ⟨(md_len _ _).symm, fun j hj => ?_⟩
  have hj' : j < C.gates.length := lt_of_lt_of_eq hj (md_len _ _)
  have hm := hg _ (gate_mem C j hj')
  refine ⟨hm.1, hm.2, fun i hi => ?_⟩
  rw [co_inputs N C j hj']
  exact hi

theorem vw_mem (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hg : AO2 C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs.getD (sg j).val 0 ∈ (gateAt C j).inputs :=
  getD_mem' _ _ (by rw [(hg _ (gate_mem C j hj)).2]; exact (sg j).isLt)

theorem sub_vw (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hg : AO2 C) : Sub C (VW N C sg) := by
  refine ⟨md_len _ _, fun j hj => ?_⟩
  rw [md_gate _ _ j hj]
  have hm := hg _ (gate_mem C j hj)
  by_cases hc : Cr N C j
  · rw [vw_pos N C sg j hc]
    refine ⟨Or.inr rfl, rfl, fun i hi => ?_⟩
    have hi' : i = (gateAt C j).inputs.getD (sg j).val 0 := by
      rcases List.mem_cons.1 hi with e1 | e1
      · exact e1
      · rcases List.mem_cons.1 e1 with e2 | e2
        · exact e2
        · exact absurd e2 (by simp)
    rw [hi']
    exact vw_mem N C sg hg j hj
  · rw [vw_neg N C sg j hc]
    exact ⟨hm.1, hm.2, fun i hi => hi⟩

theorem zc (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C) (mk : Finset ℕ) (w : ℕ) :
    DD (N + N) mk (CO N C) w = 0 ↔ DD (N + N) mk C w = 0 :=
  ⟨dz_sub (N + N) mk (CO N C) C (sub_ao C _ (sub_co N C hg)) (sub_rb _ C _ hrb (sub_co N C hg))
    (co_sub N C hg) w, dz_sub (N + N) mk C (CO N C) hg hrb (sub_co N C hg) w⟩

theorem pz (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C) (mk : Finset ℕ) (w : ℕ) :
    0 < DD (N + N) mk (CO N C) w ↔ 0 < DD (N + N) mk C w :=
  ⟨pos_of _ _ (zc N C hg hrb mk w).2, pos_of _ _ (zc N C hg hrb mk w).1⟩

theorem zv (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hg : AO2 C) (hrb : ReadsBack (N + N) C)
    (mk : Finset ℕ) (w : ℕ) : DD (N + N) mk C w = 0 → DD (N + N) mk (VW N C sg) w = 0 :=
  dz_sub (N + N) mk C (VW N C sg) hg hrb (sub_vw N C sg hg) w

theorem pos_some (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C) :
    ∀ w, w < N + N + C.gates.length → dP N C w = 0 → dL N C w = 0 → False := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h1 h2
    by_cases hlt : w < N + N
    · rw [dP_in N C w hlt] at h1
      rw [dL_in N C w hlt] at h2
      split_ifs at h1 h2 <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hg _ (gate_mem C j hj)).2
      have ha : a ∈ (gateAt C j).inputs := by
        rw [hab]
        simp
      have hal := hrb j hj a ha
      exact ih a hal (by omega)
        ((D_zero (N + N) (Finset.range N) C hg hrb j hj).1 h1 a ha)
        ((D_zero (N + N) (Finset.Ico N (N + N)) C hg hrb j hj).1 h2 a ha)

abbrev Le (g g' : Gate) : Prop :=
  ∀ f f' : ℕ → Bool, (∀ i ∈ g.inputs, f i = true → f' i = true) →
    g.op.eval (g.inputs.map f) = true → g'.op.eval (g'.inputs.map f') = true

theorem le_same (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) : Le g g := by
  intro f f' H
  rcases h with ha | ho
  · rw [ev_and g _ ha, ev_and g _ ha]
    intro h k hk
    exact H k hk (h k hk)
  · rw [ev_or g _ ho, ev_or g _ ho]
    rintro ⟨k, hk, h⟩
    exact ⟨k, hk, H k hk h⟩

theorem val_le (n : ℕ) (C D : Circuit) (hrb : ReadsBack n C) (hrD : ReadsBack n D)
    (hlen : D.gates.length = C.gates.length)
    (hle : ∀ j, j < C.gates.length → Le (gateAt C j) (gateAt D j))
    (X : List Bool) (hX : X.length = n) :
    ∀ w, VV C X w = true → VV D X w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases h1 : w < n
    · rw [VV_in D X w (by omega)]
      rw [VV_in C X w (by omega)] at hv
      exact hv
    · by_cases h2 : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [VV_gate n D hrD X hX j (by omega)]
        rw [VV_gate n C hrb X hX j hj] at hv
        exact hle j hj _ _ (fun i hi => ih i (hrb j hj i hi)) hv
      · rw [VV_out C X w (by omega)] at hv
        exact absurd hv (by decide)

theorem le_co (N : ℕ) (C : Circuit) (hg : AO2 C) (j : ℕ) (hj : j < C.gates.length) :
    Le (gateAt C j) (gateAt (CO N C) j) := by
  rw [md_gate _ _ j hj]
  have hm := hg _ (gate_mem C j hj)
  by_cases hc : Cr N C j
  · rw [orG_pos N C j hc]
    intro f f' H hv
    rw [ev_and _ _ hc.1] at hv
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hm.2
    have ha : a ∈ (gateAt C j).inputs := by
      rw [hab]
      simp
    exact (ev_or ⟨GateOp.or, (gateAt C j).inputs⟩ f' rfl).2 ⟨a, ha, H a ha (hv a ha)⟩
  · rw [orG_neg N C j hc]
    exact le_same _ hm.1

theorem le_vw_co (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hg : AO2 C) (j : ℕ)
    (hj : j < C.gates.length) : Le (gateAt (VW N C sg) j) (gateAt (CO N C) j) := by
  rw [md_gate _ _ j hj, md_gate _ _ j hj]
  have hm := hg _ (gate_mem C j hj)
  by_cases hc : Cr N C j
  · rw [orG_pos N C j hc, vw_pos N C sg j hc]
    intro f f' H hv
    obtain ⟨i, hi, hfi⟩ := (ev_or ⟨GateOp.or, [(gateAt C j).inputs.getD (sg j).val 0, (gateAt C j).inputs.getD (sg j).val 0]⟩ f rfl).1 hv
    exact (ev_or ⟨GateOp.or, (gateAt C j).inputs⟩ f' rfl).2
      ⟨i, (sub_vw N C sg hg).2 j hj |>.2.2 i (by rw [md_gate _ _ j hj, vw_pos N C sg j hc]; exact hi), H i hi hfi⟩
  · rw [orG_neg N C j hc, vw_neg N C sg j hc]
    exact le_same _ hm.1

theorem canon (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C) (X : List Bool)
    (hX : X.length = N + N) :
    ∃ sg : ℕ → Fin 2, ∀ w, VV (VW N C sg) X w = VV (CO N C) X w := by
  obtain ⟨sg, hsg⟩ : ∃ sg : ℕ → Fin 2, ∀ j, sg j =
      if VV (CO N C) X ((gateAt C j).inputs.getD 0 0) = true then (⟨0, by omega⟩ : Fin 2)
      else ⟨1, by omega⟩ := ⟨_, fun _ => rfl⟩
  refine ⟨sg, ?_⟩
  have hrO := sub_rb (N + N) C _ hrb (sub_co N C hg)
  have hrV := sub_rb (N + N) C _ hrb (sub_vw N C sg hg)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N + N
    · rw [VV_in _ X w (by omega), VV_in _ X w (by omega)]
    · by_cases h2 : w < N + N + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < C.gates.length := by omega
        have hjO : j < (CO N C).gates.length := lt_of_lt_of_eq hj (md_len _ _).symm
        have hjV : j < (VW N C sg).gates.length := lt_of_lt_of_eq hj (md_len _ _).symm
        have hm := hg _ (gate_mem C j hj)
        by_cases hc : Cr N C j
        · obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hm.2
          have eO : gateAt (CO N C) j = ⟨GateOp.or, [a, b]⟩ := by
            rw [md_gate _ _ j hj, orG_pos N C j hc, hab]
          have ha : a < N + N + j := hrb j hj a (by rw [hab]; simp)
          have hb : b < N + N + j := hrb j hj b (by rw [hab]; simp)
          have e0 : (gateAt C j).inputs.getD 0 0 = a := by simp [hab]
          rw [V_or (N + N) (CO N C) hrO X hX j hjO a b eO]
          by_cases hva : VV (CO N C) X a = true
          · have es : (sg j).val = 0 := by
              rw [hsg j, e0, if_pos hva]
            have e1 : (gateAt C j).inputs.getD (sg j).val 0 = a := by simp [es, hab]
            have eV : gateAt (VW N C sg) j = ⟨GateOp.or, [a, a]⟩ := by
              rw [md_gate _ _ j hj, vw_pos N C sg j hc, e1]
            rw [V_or (N + N) (VW N C sg) hrV X hX j hjV a a eV, ih a ha, hva]
            rfl
          · have es : (sg j).val = 1 := by
              rw [hsg j, e0, if_neg hva]
            have e1 : (gateAt C j).inputs.getD (sg j).val 0 = b := by simp [es, hab]
            have eV : gateAt (VW N C sg) j = ⟨GateOp.or, [b, b]⟩ := by
              rw [md_gate _ _ j hj, vw_pos N C sg j hc, e1]
            have hva' : VV (CO N C) X a = false := Bool.eq_false_iff.2 hva
            rw [V_or (N + N) (VW N C sg) hrV X hX j hjV b b eV, ih b hb, hva', Bool.or_self,
              Bool.false_or]
        · have eO : gateAt (CO N C) j = gateAt C j := by
            rw [md_gate _ _ j hj, orG_neg N C j hc]
          have eV : gateAt (VW N C sg) j = gateAt C j := by
            rw [md_gate _ _ j hj, vw_neg N C sg j hc]
          rw [VV_gate (N + N) (VW N C sg) hrV X hX j hjV, VV_gate (N + N) (CO N C) hrO X hX j hjO,
            eO, eV]
          congr 1
          exact List.map_congr_left (fun i hi => ih i (hrb j hj i hi))
      · rw [VV_out _ X w (by rw [md_len]; omega), VV_out _ X w (by rw [md_len]; omega)]

theorem cor_rej (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C)
    (z : Fin (N + N) → Bool)
    (hv : ∀ sg : ℕ → Fin 2, circuitFun (N + N) (VW N C sg) z = false) :
    VV (CO N C) (List.ofFn z) C.output = false := by
  obtain ⟨sg, hsg⟩ := canon N C hg hrb (List.ofFn z) (by simp)
  rw [← hsg C.output]
  exact hv sg

abbrev St (N : ℕ) (C : Circuit) (x : Fin N → Bool) (a b : ℕ) : Prop :=
  ∃ j < C.gates.length, b = N + N + j ∧ (0 < dP N C b ∧ 0 < dL N C b) ∧ a ∈ (gateAt C j).inputs ∧ ((gateAt C j).op = GateOp.or ∨ ∀ i ∈ (gateAt C j).inputs, i ≠ a → (C.wires (List.ofFn (Fin.append x (fun _ : Fin N => false)))).getD i false = true)

abbrev Fr (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  dP N C h = 0 ∧ 0 < dL N C h ∧ ∃ j < C.gates.length, h ∈ (gateAt C j).inputs ∧ (0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j))

abbrev LS (N : ℕ) (C : Circuit) (W : Finset (Fin N)) (h : ℕ) (w : Fin N) : Prop :=
  W.filter (fun l : Fin N => (C.wires (List.ofFn (Fin.append (fun _ : Fin N => false) (fun a : Fin N => decide (a = l))))).getD h false = true) = ({w} : Finset (Fin N))

theorem path_true (N : ℕ) (D : Circuit) (hg : AO2 D) (hrb : ReadsBack (N + N) D)
    (x y : Fin N → Bool) (h o : ℕ)
    (hp : Relation.ReflTransGen (St N D x) h o) (hh : E N D x y h = true) :
    E N D x y o = true := by
  induction hp with
  | refl => exact hh
  | @tail b c _ hs ih =>
    obtain ⟨j, hj, rfl, _, hin, halt⟩ := hs
    have hm := hg _ (gate_mem D j hj)
    show VV D (List.ofFn (Fin.append x y)) (N + N + j) = true
    rw [VV_gate (N + N) D hrb (List.ofFn (Fin.append x y)) (by simp) j hj]
    rcases hm.1 with ha | ho
    · rw [ev_and _ _ ha]
      intro i hi
      by_cases e : i = b
      · rw [e]
        exact ih
      · rcases halt with h1 | h1
        · rw [ha] at h1
          cases h1
        · exact E_mono N D (fun g hg' => (hg g hg').1) x y i (h1 i hi e)
    · rw [ev_or _ _ ho]
      exact ⟨b, hin, ih⟩

theorem st_vw_co (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (hg : AO2 C) (hrb : ReadsBack (N + N) C)
    (x : Fin N → Bool) (a b : ℕ) (h : St N (VW N C sg) x a b) : St N (CO N C) x a b := by
  obtain ⟨j, hj, hb, hmx, hin, halt⟩ := h
  have hj' : j < C.gates.length := lt_of_lt_of_eq hj (md_len _ _)
  have hjO : j < (CO N C).gates.length := lt_of_lt_of_eq hj' (md_len _ _).symm
  have hinC : a ∈ (gateAt C j).inputs := (sub_vw N C sg hg).2 j hj' |>.2.2 a hin
  have hinO : a ∈ (gateAt (CO N C) j).inputs := by
    rw [co_inputs N C j hj']
    exact hinC
  refine ⟨j, hjO, hb, ⟨?_, ?_⟩, hinO, ?_⟩
  · exact pos_of _ _ (fun h0 => zv N C sg hg hrb _ b ((zc N C hg hrb _ b).1 h0)) hmx.1
  · exact pos_of _ _ (fun h0 => zv N C sg hg hrb _ b ((zc N C hg hrb _ b).1 h0)) hmx.2
  · by_cases hc : Cr N C j
    · left
      rw [md_gate _ _ j hj']
      have hcg := congrArg Gate.op (orG_pos N C j hc)
      exact hcg
    · have e : gateAt (VW N C sg) j = gateAt (CO N C) j := by
        rw [md_gate _ _ j hj', md_gate _ _ j hj', vw_neg N C sg j hc, orG_neg N C j hc]
      rcases halt with h1 | h1
      · left
        rw [← e]
        exact h1
      · right
        intro i hi hne
        rw [← e] at hi
        exact val_le (N + N) (VW N C sg) (CO N C)
          (sub_rb (N + N) C _ hrb (sub_vw N C sg hg)) (sub_rb (N + N) C _ hrb (sub_co N C hg))
          ((md_len _ _).trans (md_len _ _).symm)
          (fun k hk => le_vw_co N C sg hg k (lt_of_lt_of_eq hk (md_len _ _)))
          (List.ofFn (Fin.append x (fun _ : Fin N => false))) (by simp) i (h1 i hi hne)

theorem co_km (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C) :
    ∀ j < (CO N C).gates.length, (gateAt (CO N C) j).op = GateOp.and →
      (∃ i ∈ (gateAt (CO N C) j).inputs, dL N (CO N C) i = 0) ∨
        (∀ h ∈ (gateAt (CO N C) j).inputs, dP N (CO N C) h = 0) := by
  intro j hjO hop
  have hj : j < C.gates.length := lt_of_lt_of_eq hjO (md_len _ _)
  rw [co_inputs N C j hj]
  rw [md_gate _ _ j hj] at hop
  by_cases hc : Cr N C j
  · rw [orG_pos N C j hc] at hop
    exact absurd hop (by simp)
  · rw [orG_neg N C j hc] at hop
    have hK : (∃ i ∈ (gateAt C j).inputs, dL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, dP N C h = 0) := by
      by_contra hn
      exact hc (And.intro hop hn)
    rcases hK with ⟨i, hi, h0⟩ | h0
    · exact Or.inl ⟨i, hi, (zc N C hg hrb _ i).2 h0⟩
    · exact Or.inr (fun h hh => (zc N C hg hrb _ h).2 (h0 h hh))

theorem partA (N R : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (S W : Finset (Fin N))
    (hg : AO2 C) (hrb : ReadsBack (N + N) C)
    (hv : ∀ sg : ℕ → Fin 2, ∀ w ∈ W, ∀ X : Finset (Fin N), X ⊆ S → (∀ p ∈ X, ¬ I p w) → X.card ≤ R →
      circuitFun (N + N) (VW N C sg) (Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ ({w} : Finset (Fin N))))) = false) :
    ∀ w ∈ W, ∀ X : Finset (Fin N), X ⊆ S → (∀ p ∈ X, ¬ I p w) → X.card ≤ R →
      ¬ ∃ h : ℕ, Fr N (CO N C) h ∧ LS N C W h w ∧
        Relation.ReflTransGen (St N (CO N C) (fun a : Fin N => decide (a ∈ X))) h (CO N C).output := by
  intro w hw X hXS hXI hXR
  rintro ⟨h, hfr, hls, hp⟩
  have hgO := sub_ao C _ (sub_co N C hg)
  have hrO := sub_rb (N + N) C _ hrb (sub_co N C hg)
  have ey : (fun l : Fin N => decide (l ∈ ({w} : Finset (Fin N)))) = (fun a : Fin N => decide (a = w)) := by
    funext l
    simp
  have hrej := cor_rej N C hg hrb _ (fun sg => hv sg w hw X hXS hXI hXR)
  rw [ey] at hrej
  have hmem := Finset.mem_singleton_self w
  rw [← hls] at hmem
  have hval : E N C (fun _ : Fin N => false) (fun a : Fin N => decide (a = w)) h = true :=
    (Finset.mem_filter.1 hmem).2
  have h1 : E N (CO N C) (fun _ : Fin N => false) (fun a : Fin N => decide (a = w)) h = true :=
    val_le (N + N) C (CO N C) hrb hrO (md_len _ _) (fun j hj => le_co N C hg j hj) _ (by simp) h hval
  have h2 : E N (CO N C) (fun a : Fin N => decide (a ∈ X)) (fun a : Fin N => decide (a = w)) h = true :=
    (E_indep_x N (CO N C) hgO hrO _ h hfr.1 _ _).trans h1
  have h3 : E N (CO N C) (fun a : Fin N => decide (a ∈ X)) (fun a : Fin N => decide (a = w)) C.output = true :=
    path_true N (CO N C) hgO hrO _ _ h _ hp h2
  have h4 : E N (CO N C) (fun a : Fin N => decide (a ∈ X)) (fun a : Fin N => decide (a = w)) C.output = false :=
    hrej
  exact absurd (h3.symm.trans h4) (by decide)

theorem partB (N : ℕ) (C : Circuit) (hg : AO2 C) (hrb : ReadsBack (N + N) C) :
    ∀ (sg : ℕ → Fin 2) (g h : ℕ) (x : Fin N → Bool), Fr N (VW N C sg) g → dP N C h = 0 →
      Relation.ReflTransGen (fun a b : ℕ => ∃ j < (VW N C sg).gates.length, b = N + N + j ∧ a ∈ (gateAt (VW N C sg) j).inputs ∧ (gateAt (VW N C sg) j).op = GateOp.or ∧ 0 < dP N C b ∧ 0 < dL N C b) h g →
      Fr N (CO N C) h ∧ (Relation.ReflTransGen (St N (VW N C sg) x) g (VW N C sg).output →
        Relation.ReflTransGen (St N (CO N C) x) h (CO N C).output) := by
  intro sg g h x hfr hd hch
  have hinO : ∀ j, j < C.gates.length → ∀ a, a ∈ (gateAt (VW N C sg) j).inputs →
      a ∈ (gateAt (CO N C) j).inputs := by
    intro j hj a ha
    rw [co_inputs N C j hj]
    exact (sub_vw N C sg hg).2 j hj |>.2.2 a ha
  have hopO : ∀ j, j < C.gates.length → (gateAt (VW N C sg) j).op = GateOp.or →
      (gateAt (CO N C) j).op = GateOp.or := by
    intro j hj hop
    rw [md_gate _ _ j hj] at hop
    rw [md_gate _ _ j hj]
    by_cases hc : Cr N C j
    · have hcg := congrArg Gate.op (orG_pos N C j hc)
      exact hcg
    · rw [vw_neg N C sg j hc] at hop
      rw [orG_neg N C j hc]
      exact hop
  have hch' : Relation.ReflTransGen (St N (CO N C) x) h g := by
    refine Relation.ReflTransGen.mono ?_ _ _ hch
    rintro a b ⟨j, hj, hb, hin, hop, hm1, hm2⟩
    have hj' : j < C.gates.length := lt_of_lt_of_eq hj (md_len _ _)
    exact ⟨j, lt_of_lt_of_eq hj' (md_len _ _).symm, hb,
      ⟨(pz N C hg hrb _ b).2 hm1, (pz N C hg hrb _ b).2 hm2⟩, hinO j hj' a hin,
      Or.inl (hopO j hj' hop)⟩
  refine ⟨⟨(zc N C hg hrb _ h).2 hd, ?_⟩, fun hp => hch'.trans ?_⟩
  · rcases Relation.ReflTransGen.cases_head hch with e | ⟨c, hs, _⟩
    · rw [e]
      obtain ⟨_, hl, j, hj, hin, hm1, hm2⟩ := hfr
      have hj' : j < C.gates.length := lt_of_lt_of_eq hj (md_len _ _)
      exact ⟨(pz N C hg hrb _ g).2 (pos_of _ _ (zv N C sg hg hrb _ g) hl), j,
        lt_of_lt_of_eq hj' (md_len _ _).symm, hinO j hj' g hin,
        (pz N C hg hrb _ _).2 (pos_of _ _ (zv N C sg hg hrb _ _) hm1),
        (pz N C hg hrb _ _).2 (pos_of _ _ (zv N C sg hg hrb _ _) hm2)⟩
    · obtain ⟨j, hj, hb, hin, hop, hm1, hm2⟩ := hs
      subst hb
      have hj' : j < C.gates.length := lt_of_lt_of_eq hj (md_len _ _)
      have hinC : h ∈ (gateAt C j).inputs := (sub_vw N C sg hg).2 j hj' |>.2.2 h hin
      have hlt := hrb j hj' h hinC
      have hl : 0 < dL N C h := by
        by_contra hc
        exact pos_some N C hg hrb h (by omega) hd (Nat.eq_zero_of_not_pos hc)
      exact ⟨(pz N C hg hrb _ h).2 hl, j, lt_of_lt_of_eq hj' (md_len _ _).symm, hinO j hj' h hin,
        (pz N C hg hrb _ _).2 hm1, (pz N C hg hrb _ _).2 hm2⟩
  · exact Relation.ReflTransGen.mono (fun a b hs => st_vw_co N C sg hg hrb x a b hs) _ _ hp

def IsX (N : ℕ) (C X : Circuit) (W : Finset (Fin N)) (ph hb : ℕ → ℕ) (H : Set ℕ) (j : ℕ) : Prop :=
  Fr N (CO N C) (hb j) ∧ hb j ∉ H ∧ ph (hb j) < N + X.gates.length ∧ ∃ w : Fin N, LS N C W (hb j) w

theorem partC (N R : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (S W : Finset (Fin N))
    (hg : AO2 C) (hrb : ReadsBack (N + N) C)
    (hro : ∀ j < C.gates.length, ∀ i ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.image (fun p : Fin N => (p : ℕ)) Sᶜ ∪ Finset.image (fun l : Fin N => N + (l : ℕ)) Wᶜ)).getD i 0 = 0)
    (hv : ∀ sg : ℕ → Fin 2, ∀ w ∈ W, ∀ X : Finset (Fin N), X ⊆ S → (∀ p ∈ X, ¬ I p w) → X.card ≤ R →
      circuitFun (N + N) (VW N C sg) (Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ ({w} : Finset (Fin N))))) = false)
    (X : Circuit) (ph : ℕ → ℕ) (H : Set ℕ) (hXg : AO2 X) (hXr : ReadsBack N X)
    (hXs0 : X.size ≤ Set.ncard {j : ℕ | j < (CO N C).gates.length ∧ dL N (CO N C) (N + N + j) = 0} + 2 * Set.ncard {j : ℕ | j < (CO N C).gates.length ∧ 0 < dP N (CO N C) (N + N + j) ∧ 0 < dL N (CO N C) (N + N + j)})
    (hHp : ∀ h ∈ H, ∀ x : Fin N → Bool, Relation.ReflTransGen (St N (CO N C) x) h (CO N C).output)
    (hXp : ∀ h : ℕ, Fr N (CO N C) h → h ∉ H → ∀ x : Fin N → Bool, ((X.wires (List.ofFn x)).getD (ph h) false = true ↔ Relation.ReflTransGen (St N (CO N C) x) h (CO N C).output)) :
    ∃ (Xc : Circuit) (ps : Fin N → ℕ), (AO2 Xc ∧ ReadsBack N Xc) ∧
      Xc.size ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} + 3 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} ∧
      (∀ (w : Fin N) (x1 x2 : Fin N → Bool), (∀ p ∈ S, x1 p = x2 p) → (Xc.wires (List.ofFn x1)).getD (ps w) false = (Xc.wires (List.ofFn x2)).getD (ps w) false) ∧
      ∀ w ∈ W, ∀ x : Fin N → Bool, ((Xc.wires (List.ofFn x)).getD (ps w) false = true ↔
        ∃ h : ℕ, Fr N (CO N C) h ∧ LS N C W h w ∧ Relation.ReflTransGen (St N (CO N C) x) h (CO N C).output) := by
  classical
  have hgO := sub_ao C _ (sub_co N C hg)
  have hrO := sub_rb (N + N) C _ hrb (sub_co N C hg)
  have e1 : {j : ℕ | j < (CO N C).gates.length ∧ dL N (CO N C) (N + N + j) = 0} = {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} := by
    ext j
    simp only [Set.mem_setOf_eq]
    exact and_congr (iff_of_eq (congrArg (fun n => j < n) (md_len C (orG N C)))) (zc N C hg hrb _ _)
  have e2 : {j : ℕ | j < (CO N C).gates.length ∧ 0 < dP N (CO N C) (N + N + j) ∧ 0 < dL N (CO N C) (N + N + j)} = {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} := by
    ext j
    simp only [Set.mem_setOf_eq]
    exact and_congr (iff_of_eq (congrArg (fun n => j < n) (md_len C (orG N C))))
      (and_congr (pz N C hg hrb _ _) (pz N C hg hrb _ _))
  have hXs : X.gates.length ≤ Set.ncard {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} + 2 * Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} :=
    le_of_le_of_eq hXs0 (congrArg₂ (fun a b : Set ℕ => Set.ncard a + 2 * Set.ncard b) e1 e2)
  have hnotH : ∀ (h : ℕ) (w : Fin N), w ∈ W → Fr N (CO N C) h → LS N C W h w → h ∉ H := by
    intro h w hw hf hls hH
    exact partA N R I C S W hg hrb hv w hw ∅ (Finset.empty_subset _) (fun p hp => by simp at hp)
      (by simp) ⟨h, hf, hls, hHp h hH _⟩
  have hLSu : ∀ (h : ℕ) (w w' : Fin N), LS N C W h w → LS N C W h w' → w = w' := by
    intro h w w' h1 h2
    exact Finset.singleton_injective (h1.symm.trans h2)
  have hSt : ∀ (x1 x2 : Fin N → Bool), (∀ p ∈ S, x1 p = x2 p) → ∀ a b, St N (CO N C) x1 a b →
      St N (CO N C) x2 a b := by
    intro x1 x2 hag a b hs
    obtain ⟨j, hj, hb, hmx, hin, halt⟩ := hs
    refine ⟨j, hj, hb, hmx, hin, ?_⟩
    rcases halt with h1 | h1
    · exact Or.inl h1
    · right
      intro i hi hne
      have hj' : j < C.gates.length := lt_of_lt_of_eq hj (md_len _ _)
      have hiC : i ∈ (gateAt C j).inputs := by
        rw [← co_inputs N C j hj']
        exact hi
      have hd0 := (zc N C hg hrb _ i).2 (hro j hj' i hiC)
      have key : VV (CO N C) (List.ofFn (Fin.append x1 (fun _ : Fin N => false))) i
          = VV (CO N C) (List.ofFn (Fin.append x2 (fun _ : Fin N => false))) i := by
        refine indep (N + N) _ (CO N C) hgO hrO _ _ (by simp) (by simp) ?_ i hd0
        intro k hk hnk
        rw [app_getD, app_getD]
        by_cases hkN : k < N
        · rw [difp hkN, difp hkN]
          apply hag
          by_contra hS
          apply hnk
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨⟨k, hkN⟩, Finset.mem_compl.2 hS, rfl⟩)
        · rw [difn hkN, difn hkN]
      exact key.symm.trans (h1 i hi hne)
  have hPc : ∀ (x1 x2 : Fin N → Bool), (∀ p ∈ S, x1 p = x2 p) → ∀ h : ℕ,
      (Relation.ReflTransGen (St N (CO N C) x1) h (CO N C).output ↔
        Relation.ReflTransGen (St N (CO N C) x2) h (CO N C).output) := by
    intro x1 x2 hag h
    exact ⟨fun hp => Relation.ReflTransGen.mono (hSt x1 x2 hag) _ _ hp,
      fun hp => Relation.ReflTransGen.mono (hSt x2 x1 (fun p hp => (hag p hp).symm)) _ _ hp⟩
  have huniqB : ∀ j h h', j < C.gates.length → 0 < dP N (CO N C) (N + N + j) → dP N (CO N C) h = 0 →
      dP N (CO N C) h' = 0 → h ∈ (gateAt (CO N C) j).inputs → h' ∈ (gateAt (CO N C) j).inputs → h = h' := by
    intro j h h' hj hm h0 h0' hi hi'
    by_contra hne
    have hjO : j < (CO N C).gates.length := lt_of_lt_of_eq hj (md_len _ _).symm
    obtain ⟨u, v, huv⟩ := List.length_eq_two.1 (hgO _ (gate_mem _ j hjO)).2
    rw [huv] at hi hi'
    have hi2 : h = u ∨ h = v := by simpa using hi
    have hi2' : h' = u ∨ h' = v := by simpa using hi'
    have huv0 : dP N (CO N C) u = 0 ∧ dP N (CO N C) v = 0 := by
      rcases hi2 with e1 | e1 <;> rcases hi2' with e2 | e2
      · exact absurd (e1.trans e2.symm) hne
      · rw [← e1, ← e2]
        exact ⟨h0, h0'⟩
      · rw [← e1, ← e2]
        exact ⟨h0', h0⟩
      · exact absurd (e1.trans e2.symm) hne
    have h1 : dP N (CO N C) (N + N + j) = 0 := by
      refine (D_zero (N + N) (Finset.range N) (CO N C) hgO hrO j hjO).2 ?_
      intro i hi3
      rw [huv] at hi3
      have hi4 : i = u ∨ i = v := by simpa using hi3
      rcases hi4 with e | e
      · rw [e]
        exact huv0.1
      · rw [e]
        exact huv0.2
    exact absurd h1 (Nat.ne_of_gt hm)
  have hex : ∀ j, ∃ hbj : ℕ, ∀ h, (dP N (CO N C) h = 0 ∧ h ∈ (gateAt (CO N C) j).inputs) →
      (dP N (CO N C) hbj = 0 ∧ hbj ∈ (gateAt (CO N C) j).inputs) := by
    intro j
    by_cases hh : ∃ h, dP N (CO N C) h = 0 ∧ h ∈ (gateAt (CO N C) j).inputs
    · obtain ⟨h0, hh0⟩ := hh
      exact ⟨h0, fun _ _ => hh0⟩
    · exact ⟨0, fun h hh' => absurd ⟨h, hh'⟩ hh⟩
  choose hb hb1 using hex
  have hbeq : ∀ j h, j < C.gates.length → 0 < dP N (CO N C) (N + N + j) → dP N (CO N C) h = 0 →
      h ∈ (gateAt (CO N C) j).inputs → hb j = h := by
    intro j h hj hm h0 hin
    have h' := hb1 j h ⟨h0, hin⟩
    exact huniqB j _ _ hj hm h'.1 h0 h'.2 hin
  have hexw : ∀ j, ∃ o : Option (Fin N), (∀ w, LS N C W (hb j) w → o = some w) ∧
      (∀ w, o = some w → LS N C W (hb j) w) := by
    intro j
    by_cases hh : ∃ w, LS N C W (hb j) w
    · obtain ⟨w0, hw0⟩ := hh
      refine ⟨some w0, fun w hw => congrArg some (hLSu _ _ _ hw0 hw), fun w e => ?_⟩
      cases e
      exact hw0
    · exact ⟨none, fun w hw => absurd ⟨w, hw⟩ hh, fun w e => by cases e⟩
  choose wx wx1 wx2 using hexw
  obtain ⟨ML, hML, hMLlen⟩ : ∃ ML : List ℕ, (∀ j, j ∈ ML ↔ (j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j))) ∧ ML.length = (Finset.filter (fun j => 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)) (Finset.range C.gates.length)).card :=
    ⟨(Finset.filter (fun j => 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)) (Finset.range C.gates.length)).toList, by intro j; simp, Finset.length_toList _⟩
  obtain ⟨MLX, hMLX, hMLXlen⟩ : ∃ MLX : List ℕ, (∀ j, j ∈ MLX ↔ (j ∈ ML ∧ IsX N C X W ph hb H j)) ∧ MLX.length ≤ ML.length :=
    ⟨ML.filter (fun j => decide (IsX N C X W ph hb H j)), by intro j; simp, List.length_filter_le _ _⟩
  obtain ⟨aX, haXd⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = ph (hb (MLX.getD i 0)) := ⟨_, fun _ => rfl⟩
  obtain ⟨cX, hcXd⟩ : ∃ f : ℕ → Option (Fin N), ∀ i, f i = wx (MLX.getD i 0) := ⟨_, fun _ => rfl⟩
  have haX : ∀ i, i < MLX.length → aX i < N + X.gates.length := by
    intro i hi
    rw [haXd]
    exact ((hMLX _).1 (getD_mem' MLX i hi)).2.2.2.1
  have semX : ∀ (w : Fin N) (x : Fin N → Bool),
      ((Circuit.wires ⟨X.gates ++ blk (N + X.gates.length) aX cX MLX.length, 0⟩ (List.ofFn x)).getD
        (outw (N + X.gates.length) cX MLX.length (some w)) false = true ↔
      ∃ i, i < MLX.length ∧ cX i = some w ∧ (F ev X.gates (List.ofFn x)).getD (aX i) false = true) :=
    fun w x => XX_sem N X.gates aX cX MLX.length haX (List.ofFn x) (List.length_ofFn) (some w)
  refine ⟨⟨X.gates ++ blk (N + X.gates.length) aX cX MLX.length, 0⟩,
    fun w => outw (N + X.gates.length) cX MLX.length (some w),
    ⟨XX_ao _ _ _ _ _ hXg, XX_rb N X.gates X.output aX cX MLX.length hXr haX⟩, ?_, ?_, ?_⟩
  · show (X.gates ++ blk (N + X.gates.length) aX cX MLX.length).length ≤ _
    rw [List.length_append, blk_len]
    have e3 : {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} = ↑(Finset.filter (fun j => 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)) (Finset.range C.gates.length)) := by
      ext j
      simp
    rw [e3, Set.ncard_coe_finset] at hXs ⊢
    omega
  · intro w x1 x2 hag
    have hx : ∀ i, i < MLX.length → (F ev X.gates (List.ofFn x1)).getD (aX i) false
        = (F ev X.gates (List.ofFn x2)).getD (aX i) false := by
      intro i hi
      have hI := ((hMLX _).1 (getD_mem' MLX i hi)).2
      rw [haXd]
      have k1 := hXp _ hI.1 hI.2.1 x1
      have k2 := hXp _ hI.1 hI.2.1 x2
      have k3 := hPc x1 x2 hag (hb (MLX.getD i 0))
      exact Bool.eq_iff_iff.2 (k1.trans (k3.trans k2.symm))
    apply Bool.eq_iff_iff.2
    rw [semX w x1, semX w x2]
    constructor
    · rintro ⟨i, hi, hc, hv'⟩
      exact ⟨i, hi, hc, (hx i hi).symm.trans hv'⟩
    · rintro ⟨i, hi, hc, hv'⟩
      exact ⟨i, hi, hc, (hx i hi).trans hv'⟩
  · intro w hw x
    rw [semX w x]
    constructor
    · rintro ⟨i, hi, hc, hv'⟩
      have hI := ((hMLX _).1 (getD_mem' MLX i hi)).2
      rw [hcXd] at hc
      rw [haXd] at hv'
      exact ⟨hb (MLX.getD i 0), hI.1, wx2 _ w hc, (hXp _ hI.1 hI.2.1 x).1 hv'⟩
    · rintro ⟨h, hf, hls, hp⟩
      have hnH := hnotH h w hw hf hls
      have hx : (X.wires (List.ofFn x)).getD (ph h) false = true := (hXp h hf hnH x).2 hp
      obtain ⟨hf0, hf1, j, hjO, hin, hm1, hm2⟩ := id hf
      have hj : j < C.gates.length := lt_of_lt_of_eq hjO (md_len _ _)
      have hbj : hb j = h := hbeq j h hj hm1 hf0 hin
      have hjML : j ∈ ML := (hML j).2 ⟨hj, (pz N C hg hrb _ _).1 hm1, (pz N C hg hrb _ _).1 hm2⟩
      have hlt : ph h < N + X.gates.length := by
        have h1 : (F ev X.gates (List.ofFn x)).getD (ph h) false = true := hx
        have h2 := getD_true_lt _ _ h1
        rw [F_len, List.length_ofFn] at h2
        exact h2
      have hX : IsX N C X W ph hb H j := by
        show Fr N (CO N C) (hb j) ∧ hb j ∉ H ∧ ph (hb j) < N + X.gates.length ∧ ∃ w : Fin N, LS N C W (hb j) w
        rw [hbj]
        exact ⟨hf, hnH, hlt, w, hls⟩
      obtain ⟨i, hi, e⟩ := mem_getD' MLX j ((hMLX j).2 ⟨hjML, hX⟩)
      refine ⟨i, hi, ?_, ?_⟩
      · rw [hcXd, e]
        refine wx1 j w ?_
        rw [hbj]
        exact hls
      · rw [haXd, e, hbj]
        exact hx

end PEqualNP.Outside.L_meta_1836

theorem PEqualNP.Outside.L_meta_1836 : (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 2 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ (∀ hv22 ∈ H22, ∀ xv22 : Fin N22 → Bool, (Relation.ReflTransGen (fun av22 bv22 : ℕ => ∃ jv22 < C22.gates.length, bv22 = N22 + N22 + jv22 ∧ (0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD bv22 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD bv22 0) ∧ av22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ iv22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22).inputs, iv22 ≠ av22 → (C22.wires (List.ofFn (Fin.append xv22 (fun uv22 : Fin N22 => false)))).getD iv22 false = true)) hv22 C22.output)) ∧ (∀ hv22x1 : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD hv22x1 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD hv22x1 0 ∧ ∃ jv22x1 < C22.gates.length, hv22x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x1).inputs ∧ (0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + jv22x1) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + jv22x1) 0)) → hv22x1 ∉ H22 → ∀ xv22x1 : Fin N22 → Bool, ((X22.wires (List.ofFn xv22x1)).getD (ph22 hv22x1) false = true ↔ (Relation.ReflTransGen (fun av22x1 bv22x1 : ℕ => ∃ jv22x2 < C22.gates.length, bv22x1 = N22 + N22 + jv22x2 ∧ (0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD bv22x1 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD bv22x1 0) ∧ av22x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x2).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ iv22x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x2).inputs, iv22x1 ≠ av22x1 → (C22.wires (List.ofFn (Fin.append xv22x1 (fun uv22x1 : Fin N22 => false)))).getD iv22x1 false = true)) hv22x1 C22.output))) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (Nlv17a Rlv17a : ℕ) (Ilv17a : Fin Nlv17a → Fin Nlv17a → Prop) [DecidableRel Ilv17a] (Clv17a Corlv17a : PEqualNP.CircuitLowerBounds.Circuit) (Vlv17a : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit) (Slv17a Wlv17a : Finset (Fin Nlv17a)), ((∀ glv17ax2 ∈ Clv17a.gates, (glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17a + Nlv17a) Clv17a) → (0 < Clv17a.gates.length ∧ (∀ jlv17ax11 < Clv17a.gates.length, ∀ ilv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax11).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax6 : Fin Nlv17a => (plv17ax6 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax4 : Fin Nlv17a => Nlv17a + (llv17ax4 : ℕ)) (Wlv17a)ᶜ)).getD ilv17ax4 0 = 0) ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax7 : Fin Nlv17a => (plv17ax7 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax5 : Fin Nlv17a => Nlv17a + (llv17ax5 : ℕ)) (Wlv17a)ᶜ)).getD Clv17a.output 0 = 0) → Corlv17a = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax12 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax5 0 = 0) ∨ (∀ hlv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val))) Clv17a.output) → Vlv17a = (fun sglv17ax3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax13 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax6 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax6 0 = 0) ∨ (∀ hlv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax4 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val))) Clv17a.output)) → ((∀ sglv17a : ℕ → Fin 2, ∀ wlv17ax1 ∈ Wlv17a, ∀ Xlv17ax1 : Finset (Fin Nlv17a), Xlv17ax1 ⊆ Slv17a → (∀ plv17ax1 ∈ Xlv17ax1, ¬ Ilv17a plv17ax1 wlv17ax1) → Xlv17ax1.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17a) (Fin.append (fun plv17ax2 : Fin Nlv17a => decide (plv17ax2 ∈ Xlv17ax1)) (fun llv17a : Fin Nlv17a => decide (llv17a ∈ ({wlv17ax1} : Finset (Fin Nlv17a))))) = false) → ∀ wlv17a ∈ Wlv17a, ∀ Xlv17a : Finset (Fin Nlv17a), Xlv17a ⊆ Slv17a → (∀ plv17a ∈ Xlv17a, ¬ Ilv17a plv17a wlv17a) → Xlv17a.card ≤ Rlv17a → ¬ (∃ hlv17a : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17a 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17a 0 ∧ ∃ jlv17a < Corlv17a.gates.length, hlv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17a).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17a) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17a) 0)) ∧ (Wlv17a.filter (fun llv17ax1 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17a : Fin Nlv17a => false) (fun alv17ax1 : Fin Nlv17a => decide (alv17ax1 = llv17ax1))))).getD hlv17a false = true)) = ({wlv17a} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax2 blv17a : ℕ => ∃ jlv17ax1 < Corlv17a.gates.length, blv17a = Nlv17a + Nlv17a + jlv17ax1 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17a 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17a 0) ∧ alv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs, ilv17a ≠ alv17ax2 → (Corlv17a.wires (List.ofFn (Fin.append (fun alv17a : Fin Nlv17a => decide (alv17a ∈ Xlv17a)) (fun ulv17ax1 : Fin Nlv17a => false)))).getD ilv17a false = true)) hlv17a Corlv17a.output))) ∧ (∀ (sglv17ax1 : ℕ → Fin 2) (glv17a hlv17ax1 : ℕ) (xlv17a : Fin Nlv17a → Bool), (((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD glv17a 0 = 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD glv17a 0 ∧ ∃ jlv17ax2 < (Vlv17a sglv17ax1).gates.length, glv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax2).inputs ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax2) 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax2) 0)) → (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 → (Relation.ReflTransGen (fun alv17ax3 blv17ax1 : ℕ => ∃ jlv17ax3 < (Vlv17a sglv17ax1).gates.length, blv17ax1 = Nlv17a + Nlv17a + jlv17ax3 ∧ alv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax1 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax1 0) hlv17ax1 glv17a) → ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax1 0 ∧ ∃ jlv17ax4 < Corlv17a.gates.length, hlv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax4).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax4) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax4) 0)) ∧ ((Relation.ReflTransGen (fun alv17ax4 blv17ax2 : ℕ => ∃ jlv17ax5 < (Vlv17a sglv17ax1).gates.length, blv17ax2 = Nlv17a + Nlv17a + jlv17ax5 ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax2 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax2 0) ∧ alv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs, ilv17ax1 ≠ alv17ax4 → ((Vlv17a sglv17ax1).wires (List.ofFn (Fin.append xlv17a (fun ulv17ax2 : Fin Nlv17a => false)))).getD ilv17ax1 false = true)) glv17a (Vlv17a sglv17ax1).output) → (Relation.ReflTransGen (fun alv17ax5 blv17ax3 : ℕ => ∃ jlv17ax6 < Corlv17a.gates.length, blv17ax3 = Nlv17a + Nlv17a + jlv17ax6 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax3 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax3 0) ∧ alv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs, ilv17ax2 ≠ alv17ax5 → (Corlv17a.wires (List.ofFn (Fin.append xlv17a (fun ulv17ax3 : Fin Nlv17a => false)))).getD ilv17ax2 false = true)) hlv17ax1 Corlv17a.output))) ∧ ((∀ sglv17ax2 : ℕ → Fin 2, ∀ wlv17ax4 ∈ Wlv17a, ∀ Xlv17ax2 : Finset (Fin Nlv17a), Xlv17ax2 ⊆ Slv17a → (∀ plv17ax4 ∈ Xlv17ax2, ¬ Ilv17a plv17ax4 wlv17ax4) → Xlv17ax2.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17ax2) (Fin.append (fun plv17ax5 : Fin Nlv17a => decide (plv17ax5 ∈ Xlv17ax2)) (fun llv17ax2 : Fin Nlv17a => decide (llv17ax2 ∈ ({wlv17ax4} : Finset (Fin Nlv17a))))) = false) → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD Clv17a.output 0 → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD Clv17a.output 0 → ∃ (Xclv17a : PEqualNP.CircuitLowerBounds.Circuit) (pslv17a : Fin Nlv17a → ℕ), ((∀ glv17ax1 ∈ Xclv17a.gates, (glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17a Xclv17a) ∧ Xclv17a.size ≤ Set.ncard {jlv17ax7 : ℕ | jlv17ax7 < Clv17a.gates.length ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax7) 0 = 0} + 3 * Set.ncard {jlv17ax8 : ℕ | jlv17ax8 < Clv17a.gates.length ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax8) 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax8) 0} ∧ (∀ (wlv17ax2 : Fin Nlv17a) (xlv17ax1 xlv17ax2 : Fin Nlv17a → Bool), (∀ plv17ax3 ∈ Slv17a, xlv17ax1 plv17ax3 = xlv17ax2 plv17ax3) → (Xclv17a.wires (List.ofFn xlv17ax1)).getD (pslv17a wlv17ax2) false = (Xclv17a.wires (List.ofFn xlv17ax2)).getD (pslv17a wlv17ax2) false) ∧ ∀ wlv17ax3 ∈ Wlv17a, ∀ xlv17ax3 : Fin Nlv17a → Bool, ((Xclv17a.wires (List.ofFn xlv17ax3)).getD (pslv17a wlv17ax3) false = true ↔ (∃ hlv17ax2 : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax2 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax2 0 ∧ ∃ jlv17ax9 < Corlv17a.gates.length, hlv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax9).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax9) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax9) 0)) ∧ (Wlv17a.filter (fun llv17ax3 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17ax4 : Fin Nlv17a => false) (fun alv17ax6 : Fin Nlv17a => decide (alv17ax6 = llv17ax3))))).getD hlv17ax2 false = true)) = ({wlv17ax3} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax7 blv17ax4 : ℕ => ∃ jlv17ax10 < Corlv17a.gates.length, blv17ax4 = Nlv17a + Nlv17a + jlv17ax10 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax4 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax4 0) ∧ alv17ax7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs, ilv17ax3 ≠ alv17ax7 → (Corlv17a.wires (List.ofFn (Fin.append xlv17ax3 (fun ulv17ax5 : Fin Nlv17a => false)))).getD ilv17ax3 false = true)) hlv17ax2 Corlv17a.output)))) := by
  intro hyp N R I _ C Cor V S W hC hro hCor hV
  have hCor' : Cor = PEqualNP.Outside.L_meta_1836.CO N C := hCor
  have hV' : V = fun sg => PEqualNP.Outside.L_meta_1836.VW N C sg := hV
  subst hCor'
  subst hV'
  refine ⟨PEqualNP.Outside.L_meta_1836.partA N R I C S W hC.1 hC.2,
    PEqualNP.Outside.L_meta_1836.partB N C hC.1 hC.2, ?_⟩
  intro hv hoP hoL
  obtain ⟨X, ph, H, hX, hXs, _, hHp, hXp, _⟩ := hyp N (PEqualNP.Outside.L_meta_1836.CO N C)
    (PEqualNP.Outside.L_meta_1836.sub_ao C _ (PEqualNP.Outside.L_meta_1836.sub_co N C hC.1))
    (PEqualNP.Outside.L_meta_1836.sub_rb (N + N) C _ hC.2 (PEqualNP.Outside.L_meta_1836.sub_co N C hC.1))
    (PEqualNP.Outside.L_meta_1836.co_km N C hC.1 hC.2)
    ((PEqualNP.Outside.L_meta_1836.pz N C hC.1 hC.2 _ _).2 hoP)
    ((PEqualNP.Outside.L_meta_1836.pz N C hC.1 hC.2 _ _).2 hoL)
  exact PEqualNP.Outside.L_meta_1836.partC N R I C S W hC.1 hC.2 hro.2.1 hv X ph H hX.1 hX.2 hXs hHp hXp
