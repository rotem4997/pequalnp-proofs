import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1952

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

abbrev XV (N : ℕ) (G : List Gate) (x : Fin N → Bool) (i : ℕ) : Bool :=
  ((⟨G, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

abbrev WFX (N : ℕ) (G : List Gate) : Prop :=
  (∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    ReadsBack N ⟨G, 0⟩

abbrev Has (N : ℕ) (G : List Gate) (f : (Fin N → Bool) → Bool) : Prop :=
  ∃ i, i < N + G.length ∧ ∀ x, XV N G x i = f x

abbrev Good (N : ℕ) (G : List Gate) (f : (Fin N → Bool) → Bool) : Prop :=
  f = (fun _ => false) ∨ f = (fun _ => true) ∨ Has N G f

theorem XV_in (N : ℕ) (G : List Gate) (x : Fin N → Bool) (w : ℕ) (hw : w < N) :
    XV N G x w = x ⟨w, hw⟩ := by
  show VV ⟨G, 0⟩ (List.ofFn x) w = _
  rw [VV_in ⟨G, 0⟩ (List.ofFn x) w (by rw [List.length_ofFn]; exact hw), ofFn_getD, difp hw]

theorem XV_snoc (N : ℕ) (G : List Gate) (g : Gate) (x : Fin N → Bool) (k : ℕ) :
    XV N (G ++ [g]) x k =
      if k = N + G.length then stpF g (fd stpF (List.ofFn x) G) else XV N G x k := by
  show (fd stpF (List.ofFn x) (G ++ [g])).getD k false =
    if k = N + G.length then stpF g (fd stpF (List.ofFn x) G)
    else (fd stpF (List.ofFn x) G).getD k false
  rw [fd_app]
  show ((fd stpF (List.ofFn x) G) ++ [stpF g (fd stpF (List.ofFn x) G)]).getD k false = _
  rw [getD_snoc, fd_len, List.length_ofFn]

theorem has_in (N : ℕ) (C : Circuit) (G : List Gate) (w : ℕ) (y0 : Fin N → Bool)
    (hw : w < N + N) (hd : dL N C w = 0) : Has N G (fun x => E N C x y0 w) := by
  have hwN : w < N := by
    rw [dL_in N C w hw] at hd
    by_contra hc
    rw [ifp (by omega)] at hd
    omega
  refine ⟨w, by omega, fun x => ?_⟩
  show XV N G x w = E N C x y0 w
  rw [XV_in N G x w hwN, E_pt N C x y0 w hwN]

theorem has_op (N : ℕ) (G : List Gate) (hW : WFX N G) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (f g : (Fin N → Bool) → Bool)
    (hf : Has N G f) (hg : Has N G g) :
    ∃ G', WFX N G' ∧ G'.length = G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Has N G' (fun x => op.eval [f x, g x]) := by
  obtain ⟨i, hi, hfi⟩ := hf
  obtain ⟨j, hj, hgj⟩ := hg
  refine ⟨G ++ [⟨op, [i, j]⟩], ⟨?_, ?_⟩, by simp, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hW.1 g' h
    · rw [List.mem_singleton] at h
      rw [h]
      exact ⟨hop, rfl⟩
  · intro j' hj' a ha
    by_cases hlt : j' < G.length
    · have e : gateAt ⟨G ++ [⟨op, [i, j]⟩], 0⟩ j' = gateAt ⟨G, 0⟩ j' := by
        show (G ++ [(⟨op, [i, j]⟩ : Gate)]).getD j' _ = G.getD j' _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left hlt]
      rw [e] at ha
      exact hW.2 j' hlt a ha
    · have hj'' : j' = G.length := by
        have : j' < G.length + 1 := by simpa using hj'
        omega
      rw [hj''] at ha ⊢
      have e : gateAt ⟨G ++ [⟨op, [i, j]⟩], 0⟩ G.length = ⟨op, [i, j]⟩ := by
        show (G ++ [(⟨op, [i, j]⟩ : Gate)]).getD G.length _ = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
        simp
      rw [e] at ha
      simp at ha
      rcases ha with h | h
      · rw [h]; omega
      · rw [h]; omega
  · rintro h ⟨k, hk, hkk⟩
    refine ⟨k, by simp; omega, fun x => ?_⟩
    rw [XV_snoc, ifn (by omega)]
    exact hkk x
  · refine ⟨N + G.length, by simp, fun x => ?_⟩
    rw [XV_snoc, ifp rfl]
    have e1 := hfi x
    have e2 := hgj x
    show op.eval [XV N G x i, XV N G x j] = op.eval [f x, g x]
    rw [e1, e2]

theorem has_and (N : ℕ) (G : List Gate) (hW : WFX N G) (f g : (Fin N → Bool) → Bool)
    (hf : Has N G f) (hg : Has N G g) :
    ∃ G', WFX N G' ∧ G'.length = G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Has N G' (fun x => f x && g x) := by
  obtain ⟨G', h1, h2, h3, h4⟩ := has_op N G hW GateOp.and (Or.inl rfl) f g hf hg
  refine ⟨G', h1, h2, h3, ?_⟩
  have e : (fun x => GateOp.and.eval [f x, g x]) = (fun x => f x && g x) := by
    funext x
    simp [GateOp.eval]
  rw [← e]
  exact h4

theorem has_or (N : ℕ) (G : List Gate) (hW : WFX N G) (f g : (Fin N → Bool) → Bool)
    (hf : Has N G f) (hg : Has N G g) :
    ∃ G', WFX N G' ∧ G'.length = G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Has N G' (fun x => f x || g x) := by
  obtain ⟨G', h1, h2, h3, h4⟩ := has_op N G hW GateOp.or (Or.inr rfl) f g hf hg
  refine ⟨G', h1, h2, h3, ?_⟩
  have e : (fun x => GateOp.or.eval [f x, g x]) = (fun x => f x || g x) := by
    funext x
    simp [GateOp.eval]
  rw [← e]
  exact h4

theorem good_lift (N : ℕ) (G G' : List Gate) (f : (Fin N → Bool) → Bool)
    (h : ∀ h, Has N G h → Has N G' h) (hf : Good N G f) : Good N G' f := by
  rcases hf with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (h f h1))

theorem good_or (N : ℕ) (G : List Gate) (hW : WFX N G) (f g : (Fin N → Bool) → Bool)
    (hf : Good N G f) (hg : Good N G g) :
    ∃ G', WFX N G' ∧ G'.length ≤ G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Good N G' (fun x => f x || g x) := by
  rcases hf with hf | hf | hf
  · have e : (fun x => f x || g x) = g := by
      funext x
      rw [hf]
      simp
    refine ⟨G, hW, by omega, fun h hh => hh, ?_⟩
    rw [e]
    exact hg
  · have e : (fun x => f x || g x) = (fun _ => true) := by
      funext x
      rw [hf]
      simp
    exact ⟨G, hW, by omega, fun h hh => hh, Or.inr (Or.inl e)⟩
  · rcases hg with hg | hg | hg
    · have e : (fun x => f x || g x) = f := by
        funext x
        rw [hg]
        simp
      refine ⟨G, hW, by omega, fun h hh => hh, ?_⟩
      rw [e]
      exact Or.inr (Or.inr hf)
    · have e : (fun x => f x || g x) = (fun _ => true) := by
        funext x
        rw [hg]
        simp
      exact ⟨G, hW, by omega, fun h hh => hh, Or.inr (Or.inl e)⟩
    · obtain ⟨G', h1, h2, h3, h4⟩ := has_or N G hW f g hf hg
      exact ⟨G', h1, by omega, h3, Or.inr (Or.inr h4)⟩

theorem good_and (N : ℕ) (G : List Gate) (hW : WFX N G) (f s : (Fin N → Bool) → Bool)
    (hf : Good N G f) (hs : Has N G s) :
    ∃ G', WFX N G' ∧ G'.length ≤ G.length + 1 ∧ (∀ h, Has N G h → Has N G' h) ∧
      Good N G' (fun x => f x && s x) := by
  rcases hf with hf | hf | hf
  · have e : (fun x => f x && s x) = (fun _ => false) := by
      funext x
      rw [hf]
      simp
    exact ⟨G, hW, by omega, fun h hh => hh, Or.inl e⟩
  · have e : (fun x => f x && s x) = s := by
      funext x
      rw [hf]
      simp
    refine ⟨G, hW, by omega, fun h hh => hh, ?_⟩
    rw [e]
    exact Or.inr (Or.inr hs)
  · obtain ⟨G', h1, h2, h3, h4⟩ := has_and N G hW f s hf hs
    exact ⟨G', h1, by omega, h3, Or.inr (Or.inr h4)⟩

def cx (N : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if dL N C (N + N + i) = 0 then 1 else 0

def cm (N : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if 0 < dP N C (N + N + i) ∧ 0 < dL N C (N + N + i) then 1 else 0

theorem cx_succ (N : ℕ) (C : Circuit) (k : ℕ) :
    cx N C (k + 1) = cx N C k + if dL N C (N + N + k) = 0 then 1 else 0 := by
  unfold cx
  rw [Finset.sum_range_succ]

theorem cm_succ (N : ℕ) (C : Circuit) (k : ℕ) :
    cm N C (k + 1) =
      cm N C k + if 0 < dP N C (N + N + k) ∧ 0 < dL N C (N + N + k) then 1 else 0 := by
  unfold cm
  rw [Finset.sum_range_succ]

theorem ncx (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} = cx N C C.gates.length := by
  have e : {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} =
      ↑((Finset.range C.gates.length).filter (fun j => dL N C (N + N + j) = 0)) := by
    ext j
    simp
  rw [e, Set.ncard_coe_finset]
  exact Finset.card_filter _ _

theorem ncm (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} =
      cm N C C.gates.length := by
  have e : {j : ℕ | j < C.gates.length ∧ 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)} =
      ↑((Finset.range C.gates.length).filter
        (fun j => 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j))) := by
    ext j
    simp
  rw [e, Set.ncard_coe_finset]
  exact Finset.card_filter _ _

theorem base (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) :
    ∀ k, k ≤ C.gates.length → ∃ G, WFX N G ∧ G.length ≤ cx N C k ∧
      ∀ w, w < N + N + k → dL N C w = 0 → Has N G (fun x => E N C x (fun _ => false) w) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], ⟨by simp, ?_⟩, by simp, ?_⟩
    · intro j hj
      simp at hj
    · intro w hw hd
      exact has_in N C [] w _ (by omega) hd
  | succ k ih =>
    intro hk
    obtain ⟨G, hW, hlen, hhas⟩ := ih (by omega)
    have hj : k < C.gates.length := by omega
    by_cases hd0 : dL N C (N + N + k) = 0
    · obtain ⟨a, b, hab | hab⟩ := gate_shape C hg k hj
      · have ha : a < N + N + k := hrb k hj a (by simp [hab])
        have hb : b < N + N + k := hrb k hj b (by simp [hab])
        have hdd : dL N C (N + N + k) = dL N C a + dL N C b :=
          D_and (N + N) (Finset.Ico N (N + N)) C hrb k hj a b hab
        obtain ⟨G', h1, h2, h3, h4⟩ := has_and N G hW _ _ (hhas a ha (by omega))
          (hhas b hb (by omega))
        refine ⟨G', h1, ?_, ?_⟩
        · rw [cx_succ, ifp hd0]
          omega
        · intro w hw hd
          by_cases hwk : w = N + N + k
          · have e : (fun x => E N C x (fun _ => false) w) =
                (fun x => E N C x (fun _ => false) a && E N C x (fun _ => false) b) := by
              funext x
              rw [hwk]
              exact V_and (N + N) C hrb _ (by simp) k hj a b hab
            rw [e]
            exact h4
          · exact h3 _ (hhas w (by omega) hd)
      · have ha : a < N + N + k := hrb k hj a (by simp [hab])
        have hb : b < N + N + k := hrb k hj b (by simp [hab])
        have hdd : dL N C (N + N + k) = max (dL N C a) (dL N C b) :=
          D_or (N + N) (Finset.Ico N (N + N)) C hrb k hj a b hab
        have l1 := le_max_left (dL N C a) (dL N C b)
        have l2 := le_max_right (dL N C a) (dL N C b)
        obtain ⟨G', h1, h2, h3, h4⟩ := has_or N G hW _ _ (hhas a ha (by omega))
          (hhas b hb (by omega))
        refine ⟨G', h1, ?_, ?_⟩
        · rw [cx_succ, ifp hd0]
          omega
        · intro w hw hd
          by_cases hwk : w = N + N + k
          · have e : (fun x => E N C x (fun _ => false) w) =
                (fun x => E N C x (fun _ => false) a || E N C x (fun _ => false) b) := by
              funext x
              rw [hwk]
              exact V_or (N + N) C hrb _ (by simp) k hj a b hab
            rw [e]
            exact h4
          · exact h3 _ (hhas w (by omega) hd)
    · refine ⟨G, hW, ?_, ?_⟩
      · rw [cx_succ, ifn hd0]
        omega
      · intro w hw hd
        have hwk : w ≠ N + N + k := by
          intro hc
          rw [hc] at hd
          exact hd0 hd
        exact hhas w (by omega) hd

def RSB : Prop :=
  ∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size

abbrev F2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem rsb_fin (H1 : RSB) {ι : Type} (T : Finset ι) (n k : ℕ) (U S : ι → Finset (Fin n))
    (C : Circuit) (o c : ι → ℕ)
    (hU : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hS : ∀ i ∈ T, S i ⊆ U i) (h2 : ∀ i ∈ T, 2 ≤ (S i).card) (hF : F2 C) (hrb : ReadsBack n C)
    (hsing : ∀ i ∈ T, ∀ p : Fin n,
      (VV C (List.ofFn (fun a : Fin n => decide (a = p))) (o i) = true ↔ p ∈ S i))
    (hzero : ∀ i ∈ T, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) → VV C (List.ofFn x) (o i) = false)
    (hck : ∀ i ∈ T, c i ≤ k) (hcS : ∀ i ∈ T, c i + 1 ≤ (S i).card) :
    ∑ i ∈ T, c i ≤ C.gates.length := by
  have e := T.equivFin
  have h := H1 n T.card k (fun i => U (e.symm i).1) (fun i => S (e.symm i).1) C
    (fun i => o (e.symm i).1) (fun i => c (e.symm i).1)
    (fun i j hij => hU _ (e.symm i).2 _ (e.symm j).2
      (fun hc => hij (e.symm.injective (Subtype.ext hc))))
    (fun i => hS _ (e.symm i).2) (fun i => h2 _ (e.symm i).2) hF hrb
    (fun i p => hsing _ (e.symm i).2 p) (fun i x hx hxU => hzero _ (e.symm i).2 x hx hxU)
    (fun i => hck _ (e.symm i).2) (fun i => hcS _ (e.symm i).2)
  have e1 : ∑ i : Fin T.card, c (e.symm i).1 = ∑ t : T, c t.1 :=
    Equiv.sum_comp e.symm (fun t : T => c t.1)
  have e2 : ∑ t : T, c t.1 = ∑ i ∈ T, c i := Finset.sum_coe_sort T c
  rw [← e2, ← e1]
  exact h

theorem wmono (N : ℕ) (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : Fin N → Bool) (hx : ∀ a, x a = true → x' a = true) (y : Fin N → Bool) (i : ℕ)
    (h : (C.wires (List.ofFn (Fin.append x y))).getD i false = true) :
    (C.wires (List.ofFn (Fin.append x' y))).getD i false = true := by
  rw [wires_fd] at h ⊢
  refine mono C.gates _ _ (by simp) hg ?_ i h
  intro k
  rw [app_getD, app_getD]
  split_ifs
  · exact hx _
  · exact id
  · exact id

theorem rmono {α : Type} {r q : α → α → Prop} (hq : ∀ a b, r a b → q a b) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen q a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hq _ _ hbc)

def ep {N : ℕ} (p : Fin N) : Fin N → Bool := fun a => decide (a = p)

def xb {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (w : Fin N) : Fin N → Bool :=
  fun a => decide (¬ I a w)

theorem ep_le {N : ℕ} (p : Fin N) (x : Fin N → Bool) (hx : x p = true) :
    ∀ a, ep p a = true → x a = true := by
  intro a ha
  have e : a = p := by simpa [ep] using ha
  rw [e]
  exact hx

theorem xb_at {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (w p : Fin N) (h : ¬ I p w) :
    xb I w p = true := by
  simpa [xb] using h

def Mx (N : ℕ) (C : Circuit) (i : ℕ) : Prop := 0 < dP N C i ∧ 0 < dL N C i

def Cone (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ Mx N C (N + N + j) ∧
    Relation.ReflTransGen (fun a b : ℕ => a < b ∧ ∃ f : Fin C.gates.length,
      b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs) (N + N + j) C.output

def Gok (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.or ∨ ∃ i ∈ (gateAt C j).inputs,
    dL N C i = 0 ∧ E N C x (fun _ => false) i = true

def Stp (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j k : ℕ) : Prop :=
  Cone N C k ∧ N + N + j ∈ (gateAt C k).inputs ∧ Gok N C x k

def Lv (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  Cone N C j ∧ Gok N C x j ∧
    ∃ jo : ℕ, N + N + jo = C.output ∧ Relation.ReflTransGen (Stp N C x) j jo

def Slot (N : ℕ) (C : Circuit) (h j : ℕ) : Prop :=
  Cone N C j ∧ h ∈ (gateAt C j).inputs ∧ dP N C h = 0

def Ap (N : ℕ) (C : Circuit) (h : ℕ) (p : Fin N) : Prop :=
  ∃ j : ℕ, Slot N C h j ∧ Lv N C (ep p) j

def Lh (N : ℕ) (C : Circuit) (h : ℕ) (w : Fin N) : Prop :=
  E N C (fun _ => false) (fun a => decide (a = w)) h = true

def Lpw (N : ℕ) (C : Circuit) (h : ℕ) (w : Fin N) : Prop :=
  ∀ w' : Fin N, Lh N C h w' ↔ w' = w

def Lps (N : ℕ) (C : Circuit) (p w : Fin N) : Prop :=
  ∃ h : ℕ, Lpw N C h w ∧ Ap N C h p

def TW (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∃ p p' : Fin N, p ≠ p' ∧ Lv N C (ep p) j ∧ Lv N C (ep p') j

def UQ (N : ℕ) (C : Circuit) (j : ℕ) (p : Fin N) : Prop :=
  Lv N C (ep p) j ∧ ∀ p' : Fin N, Lv N C (ep p') j → p' = p

def KN (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (j : ℕ) : Prop :=
  Cone N C j ∧ (gateAt C j).op = GateOp.and ∧ TW N C j ∧ ∀ w0 : Fin N, Gok N C (xb I w0) j

def KF (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (j : ℕ) : Prop :=
  Cone N C j ∧ (gateAt C j).op = GateOp.and ∧ TW N C j ∧ ∃ w0 : Fin N, ¬ Gok N C (xb I w0) j

def QL (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (x : Fin N → Bool)
    (j : ℕ) : Prop :=
  Gok N C x j ∧ ∃ j', Relation.ReflTransGen (Stp N C x) j j' ∧
    (N + N + j' = C.output ∨ (TW N C j' ∧ ∃ w0 : Fin N, ¬ Gok N C (xb I w0) j') ∨
      ∃ p0 : Fin N, x p0 = true ∧ Lv N C (ep p0) j')

def AL (N : ℕ) (C : Circuit) (j : ℕ) : Prop := ∀ x : Fin N → Bool, Lv N C x j

def NW (N : ℕ) (C : Circuit) (j : ℕ) : Prop := (∃ p : Fin N, Lv N C (ep p) j) ∧ ¬ AL N C j

abbrev Inv (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (G : List Gate)
    (om : ℕ → (Fin N → Bool) → Bool) (t : ℕ) : Prop :=
  ∀ j, t ≤ j → NW N C j →
    Has N G (om j) ∧ (∀ p : Fin N, Lv N C (ep p) j → om j (ep p) = true) ∧
      ∀ x, om j x = true → QL N I C x j

theorem get_eq (C : Circuit) (f : Fin C.gates.length) : C.gates.get f = gateAt C f.val :=
  (List.getD_eq_getElem _ _ f.isLt).symm

theorem inlen (C : Circuit) (hg : F2 C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs.length = 2 := by
  obtain ⟨a, b, h | h⟩ := gate_shape C hg j hj <;> simp [h]

theorem getD_mem (C : Circuit) (hg : F2 C) (j : ℕ) (hj : j < C.gates.length) (s : ℕ)
    (hs : s < 2) : (gateAt C j).inputs.getD s 0 ∈ (gateAt C j).inputs := by
  have hl := inlen C hg j hj
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem mem_getD (C : Circuit) (hg : F2 C) (j : ℕ) (hj : j < C.gates.length) (h : ℕ)
    (hh : h ∈ (gateAt C j).inputs) : ∃ s, s < 2 ∧ (gateAt C j).inputs.getD s 0 = h := by
  obtain ⟨a, b, hab | hab⟩ := gate_shape C hg j hj
  · rw [hab] at hh ⊢
    have e : h = a ∨ h = b := by simpa using hh
    rcases e with e | e
    · exact ⟨0, by norm_num, by simp [e]⟩
    · exact ⟨1, by norm_num, by simp [e]⟩
  · rw [hab] at hh ⊢
    have e : h = a ∨ h = b := by simpa using hh
    rcases e with e | e
    · exact ⟨0, by norm_num, by simp [e]⟩
    · exact ⟨1, by norm_num, by simp [e]⟩

theorem mx_up (N : ℕ) (C : Circuit) (hg : F2 C) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hj : j < C.gates.length) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (hm : Mx N C a) :
    Mx N C (N + N + j) := by
  obtain ⟨h1, h2⟩ := hm
  obtain ⟨u, v, huv | huv⟩ := gate_shape C hg j hj
  · have e1 : dP N C (N + N + j) = dP N C u + dP N C v :=
      D_and (N + N) (Finset.range N) C hrb j hj u v huv
    have e2 : dL N C (N + N + j) = dL N C u + dL N C v :=
      D_and (N + N) (Finset.Ico N (N + N)) C hrb j hj u v huv
    rw [huv] at ha
    have e : a = u ∨ a = v := by simpa using ha
    show 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)
    rcases e with e | e
    · rw [e] at h1 h2
      constructor <;> omega
    · rw [e] at h1 h2
      constructor <;> omega
  · have e1 : dP N C (N + N + j) = max (dP N C u) (dP N C v) :=
      D_or (N + N) (Finset.range N) C hrb j hj u v huv
    have e2 : dL N C (N + N + j) = max (dL N C u) (dL N C v) :=
      D_or (N + N) (Finset.Ico N (N + N)) C hrb j hj u v huv
    have l1 := le_max_left (dP N C u) (dP N C v)
    have l2 := le_max_right (dP N C u) (dP N C v)
    have l3 := le_max_left (dL N C u) (dL N C v)
    have l4 := le_max_right (dL N C u) (dL N C v)
    rw [huv] at ha
    have e : a = u ∨ a = v := by simpa using ha
    show 0 < dP N C (N + N + j) ∧ 0 < dL N C (N + N + j)
    rcases e with e | e
    · rw [e] at h1 h2
      constructor <;> omega
    · rw [e] at h1 h2
      constructor <;> omega

theorem cone_parent (N : ℕ) (C : Circuit) (hg : F2 C) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hc : Cone N C j) (hne : N + N + j ≠ C.output) :
    ∃ j', Cone N C j' ∧ N + N + j ∈ (gateAt C j').inputs := by
  obtain ⟨hj, hm, hr⟩ := hc
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨b, ⟨_, f, hb, hin⟩, hrest⟩
  · exact absurd h hne
  · rw [get_eq] at hin
    refine ⟨f.val, ⟨f.isLt, mx_up N C hg hrb f.val f.isLt _ hin hm, ?_⟩, hin⟩
    rw [← hb]
    exact hrest

theorem gok_mono (N : ℕ) (C : Circuit) (hg : F2 C) (x x' : Fin N → Bool)
    (hx : ∀ a, x a = true → x' a = true) (j : ℕ) (h : Gok N C x j) : Gok N C x' j := by
  rcases h with h | ⟨i, hi, hd, hv⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi, hd, wmono N C (fun g hg' => (hg g hg').1) x x' hx _ i hv⟩

theorem stp_mono (N : ℕ) (C : Circuit) (hg : F2 C) (x x' : Fin N → Bool)
    (hx : ∀ a, x a = true → x' a = true) (a b : ℕ) (h : Stp N C x a b) : Stp N C x' a b :=
  ⟨h.1, h.2.1, gok_mono N C hg x x' hx b h.2.2⟩

theorem lv_parent (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) (h : Lv N C x j)
    (hne : N + N + j ≠ C.output) : ∃ j', Stp N C x j j' ∧ Lv N C x j' := by
  obtain ⟨_, _, jo, hjo, hr⟩ := h
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hs, hrest⟩
  · exfalso
    apply hne
    rw [h]
    exact hjo
  · exact ⟨c, hs, hs.1, hs.2.2, jo, hjo, hrest⟩

theorem lv_child (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j j' : ℕ) (hc : Cone N C j)
    (hgk : Gok N C x j) (hs : Stp N C x j j') (hl : Lv N C x j') : Lv N C x j := by
  obtain ⟨_, _, jo, hjo, hr⟩ := hl
  exact ⟨hc, hgk, jo, hjo, Relation.ReflTransGen.head hs hr⟩

theorem rtg_lift (N : ℕ) (C : Circuit) (x x' : Fin N → Bool) (jo : ℕ)
    (hjo : N + N + jo = C.output) (hall : ∀ j, Lv N C x j → Gok N C x' j) :
    ∀ j, Relation.ReflTransGen (Stp N C x) j jo → Relation.ReflTransGen (Stp N C x') j jo := by
  intro j hr
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hac hcr ih =>
    exact Relation.ReflTransGen.head
      ⟨hac.1, hac.2.1, hall _ ⟨hac.1, hac.2.2, jo, hjo, hcr⟩⟩ ih

theorem gok_and (N : ℕ) (C : Circuit) (hg : F2 C) (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, dL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, dP N C h = 0))
    (j : ℕ) (hc : Cone N C j) (a b : ℕ) (hab : gateAt C j = ⟨GateOp.and, [a, b]⟩) :
    ∃ i, i < N + N + j ∧ dL N C i = 0 ∧
      ∀ x, (Gok N C x j ↔ E N C x (fun _ => false) i = true) := by
  obtain ⟨hj, ⟨hp, hl⟩, _⟩ := hc
  have e1 : dP N C (N + N + j) = dP N C a + dP N C b :=
    D_and (N + N) (Finset.range N) C hrb j hj a b hab
  have e2 : dL N C (N + N + j) = dL N C a + dL N C b :=
    D_and (N + N) (Finset.Ico N (N + N)) C hrb j hj a b hab
  have ha : a < N + N + j := hrb j hj a (by simp [hab])
  have hb : b < N + N + j := hrb j hj b (by simp [hab])
  have hk := hkm j hj (by rw [hab])
  rw [hab] at hk
  have hor : dL N C a = 0 ∨ dL N C b = 0 := by
    rcases hk with ⟨i, hi, hd⟩ | hall
    · have e : i = a ∨ i = b := by simpa using hi
      rcases e with e | e
      · left
        rw [← e]
        exact hd
      · right
        rw [← e]
        exact hd
    · exfalso
      have h1 := hall a (by simp)
      have h2 := hall b (by simp)
      omega
  rcases hor with h0 | h0
  · refine ⟨a, ha, h0, fun x => ?_⟩
    have hbpos : 0 < dL N C b := by omega
    unfold Gok
    rw [hab]
    constructor
    · rintro (h | ⟨i, hi, hd, hv⟩)
      · exact absurd h (by simp)
      · have e : i = a ∨ i = b := by simpa using hi
        rcases e with e | e
        · rw [← e]
          exact hv
        · rw [e] at hd
          omega
    · intro hv
      exact Or.inr ⟨a, by simp, h0, hv⟩
  · refine ⟨b, hb, h0, fun x => ?_⟩
    have hapos : 0 < dL N C a := by omega
    unfold Gok
    rw [hab]
    constructor
    · rintro (h | ⟨i, hi, hd, hv⟩)
      · exact absurd h (by simp)
      · have e : i = a ∨ i = b := by simpa using hi
        rcases e with e | e
        · rw [e] at hd
          omega
        · rw [← e]
          exact hv
    · intro hv
      exact Or.inr ⟨b, by simp, h0, hv⟩

theorem sound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hg : F2 C)
    (no4 : ∀ p p' w w' : Fin N, p ≠ p' → w ≠ w' → I p w → I p' w → I p w' → I p' w' → False)
    (h24 : ∀ (h j : ℕ) (w : Fin N), Slot N C h j → Lh N C h w → ¬ Lv N C (xb I w) j)
    (h3 : ∀ (h j6 j7 : ℕ) (w p : Fin N), Slot N C h j6 → Lh N C h w → Gok N C (xb I w) j6 →
      Relation.ReflTransGen (Stp N C (xb I w)) j6 j7 → ¬ I p w → ∀ j8 : ℕ,
      N + N + j8 = C.output → ¬ Relation.ReflTransGen (Stp N C (ep p)) j7 j8)
    (h j0 : ℕ) (w : Fin N) (hs : Slot N C h j0) (hl : Lh N C h w) (x : Fin N → Bool)
    (hx : ∀ p, x p = true → ¬ I p w) (hq : QL N I C x j0) : False := by
  obtain ⟨hgk, j', hr, ht⟩ := hq
  have hxb : ∀ a, x a = true → xb I w a = true := fun a ha => xb_at I w a (hx a ha)
  have hgk' := gok_mono N C hg x _ hxb j0 hgk
  have hr' := rmono (fun a b hab => stp_mono N C hg x _ hxb a b hab) hr
  rcases ht with ht | ht | ⟨p0, hp0, hlv⟩
  · exact h24 h j0 w hs hl ⟨hs.1, hgk', j', ht, hr'⟩
  · obtain ⟨⟨p1, p2, hne, hl1, hl2⟩, w0, hw0⟩ := ht
    have hgj' : Gok N C (xb I w) j' := by
      rcases Relation.ReflTransGen.cases_tail hr' with h' | ⟨c, _, hc⟩
      · rw [h']
        exact hgk'
      · exact hc.2.2
    have key : ∀ p : Fin N, Lv N C (ep p) j' → I p w ∧ I p w0 := by
      intro p hp
      obtain ⟨_, hgp, jo, hjo, hrp⟩ := hp
      constructor
      · by_contra hI
        exact h3 h j0 j' w p hs hl hgk' hr' hI jo hjo hrp
      · by_contra hI
        exact hw0 (gok_mono N C hg (ep p) _ (ep_le p _ (xb_at I w0 p hI)) j' hgp)
    have k1 := key p1 hl1
    have k2 := key p2 hl2
    by_cases hww : w = w0
    · rw [← hww] at hw0
      exact hw0 hgj'
    · exact no4 p1 p2 w w0 hne hww k1.1 k2.1 k1.2 k2.2
  · obtain ⟨_, _, jo, hjo, hrp⟩ := hlv
    exact h3 h j0 j' w p0 hs hl hgk' hr' (hx p0 hp0) jo hjo hrp

theorem has_ors {α : Type} (N : ℕ) (fam : α → (Fin N → Bool) → Bool) (S : Finset α)
    (hS : S.Nonempty) :
    ∀ (G : List Gate), WFX N G → (∀ a ∈ S, Has N G (fam a)) →
    ∃ G', WFX N G' ∧ G'.length + 1 = G.length + S.card ∧ (∀ h, Has N G h → Has N G' h) ∧
      ∃ F, Has N G' F ∧ ∀ x, (F x = true ↔ ∃ a ∈ S, fam a x = true) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro G hW hh
    refine ⟨G, hW, by simp, fun h hh' => hh', fam a, hh a (Finset.mem_singleton_self a), ?_⟩
    intro x
    constructor
    · intro h
      exact ⟨a, Finset.mem_singleton_self a, h⟩
    · rintro ⟨b, hb, hbx⟩
      rw [Finset.mem_singleton.mp hb] at hbx
      exact hbx
  | cons a s ha hs ih =>
    intro G hW hh
    obtain ⟨G1, hW1, hl1, hlift1, F1, hF1, hFs1⟩ :=
      ih G hW (fun b hb => hh b (Finset.mem_cons.mpr (Or.inr hb)))
    obtain ⟨G2, hW2, hl2, hlift2, hF2⟩ := has_or N G1 hW1 _ _
      (hlift1 _ (hh a (Finset.mem_cons.mpr (Or.inl rfl)))) hF1
    refine ⟨G2, hW2, ?_, fun h hh' => hlift2 h (hlift1 h hh'), _, hF2, ?_⟩
    · rw [Finset.card_cons]
      omega
    · intro x
      show (fam a x || F1 x) = true ↔ _
      rw [Bool.or_eq_true, hFs1 x]
      constructor
      · rintro (h | ⟨b, hb, hbx⟩)
        · exact ⟨a, Finset.mem_cons.mpr (Or.inl rfl), h⟩
        · exact ⟨b, Finset.mem_cons.mpr (Or.inr hb), hbx⟩
      · rintro ⟨b, hb, hbx⟩
        rcases Finset.mem_cons.mp hb with h | h
        · left
          rw [← h]
          exact hbx
        · right
          exact ⟨b, h, hbx⟩

theorem has_fam {α ι : Type} [DecidableEq ι] (N : ℕ) (fam : α → (Fin N → Bool) → Bool)
    (S : ι → Finset α) :
    ∀ (T : Finset ι) (G : List Gate), WFX N G →
    (∀ i ∈ T, (S i).Nonempty ∧ ∀ a ∈ S i, Has N G (fam a)) →
    ∃ G', WFX N G' ∧ G'.length + T.card = G.length + ∑ i ∈ T, (S i).card ∧
      (∀ h, Has N G h → Has N G' h) ∧
      ∀ i ∈ T, ∃ F, Has N G' F ∧ ∀ x, (F x = true ↔ ∃ a ∈ S i, fam a x = true) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro G hW _
    exact ⟨G, hW, by simp, fun h hh => hh, by simp⟩
  | insert a T ha ih =>
    intro G hW hT
    obtain ⟨G1, hW1, hl1, hlift1, hF1⟩ :=
      ih G hW (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨hne, hha⟩ := hT a (Finset.mem_insert_self a T)
    obtain ⟨G2, hW2, hl2, hlift2, F, hF, hFs⟩ :=
      has_ors N fam (S a) hne G1 hW1 (fun b hb => hlift1 _ (hha b hb))
    refine ⟨G2, hW2, ?_, fun h hh => hlift2 h (hlift1 h hh), ?_⟩
    · rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      omega
    · intro i hi
      by_cases hia : i = a
      · rw [hia]
        exact ⟨F, hF, hFs⟩
      · obtain ⟨F', hF', hFs'⟩ := hF1 i ((Finset.mem_insert.mp hi).resolve_left hia)
        exact ⟨F', hlift2 _ hF', hFs'⟩

def Spc (N : ℕ) (C : Circuit) (t : ℕ) (js : ℕ × ℕ) : Prop :=
  Cone N C js.1 ∧ js.2 < 2 ∧ (gateAt C js.1).inputs.getD js.2 0 = N + N + t ∧ Mx N C (N + N + t)

open Classical in
noncomputable def SpF (N : ℕ) (C : Circuit) (t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range C.gates.length ×ˢ Finset.range 2).filter (Spc N C t)

theorem mem_SpF (N : ℕ) (C : Circuit) (t : ℕ) (js : ℕ × ℕ) : js ∈ SpF N C t ↔ Spc N C t js := by
  classical
  unfold SpF
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.1, h.2.1⟩, h⟩

theorem spot_of (N : ℕ) (C : Circuit) (hg : F2 C) (t j' : ℕ) (hm : Mx N C (N + N + t))
    (hc : Cone N C j') (hin : N + N + t ∈ (gateAt C j').inputs) : ∃ s, (j', s) ∈ SpF N C t := by
  obtain ⟨s, hs, he⟩ := mem_getD C hg j' hc.1 _ hin
  exact ⟨s, (mem_SpF N C t _).2 ⟨hc, hs, he, hm⟩⟩

theorem spot_mem (N : ℕ) (C : Circuit) (hg : F2 C) (hrb : ReadsBack (N + N) C) (t : ℕ)
    (js : ℕ × ℕ) (h : js ∈ SpF N C t) :
    Cone N C js.1 ∧ N + N + t ∈ (gateAt C js.1).inputs ∧ t < js.1 := by
  obtain ⟨hc, hs, he, _⟩ := (mem_SpF N C t js).1 h
  have hin : N + N + t ∈ (gateAt C js.1).inputs := by
    rw [← he]
    exact getD_mem C hg js.1 hc.1 js.2 hs
  have := hrb js.1 hc.1 _ hin
  exact ⟨hc, hin, by omega⟩

open Classical in
noncomputable def aud (N : ℕ) (C : Circuit) (t : ℕ) : ℕ := if Cone N C t then 1 else 0

open Classical in
noncomputable def bud (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (t : ℕ) : ℕ :=
  (SpF N C t).card + (if KN N I C t then 1 else 0) + (if N + N + t = C.output then 1 else 0)

theorem aud_le (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hg : F2 C)
    (hrb : ReadsBack (N + N) C) (t : ℕ) : aud N C t ≤ bud N I C t := by
  unfold aud bud
  by_cases hc : Cone N C t
  · rw [if_pos hc]
    by_cases ho : N + N + t = C.output
    · rw [if_pos ho]
      omega
    · obtain ⟨j', hc', hin⟩ := cone_parent N C hg hrb t hc ho
      obtain ⟨s, hs⟩ := spot_of N C hg t j' hc.2.1 hc' hin
      have := Finset.card_pos.mpr ⟨_, hs⟩
      omega
  · rw [if_neg hc]
    exact Nat.zero_le _

theorem par_or (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hg : F2 C)
    (hrb : ReadsBack (N + N) C) (t : ℕ) (G : List Gate) (om : ℕ → (Fin N → Bool) → Bool)
    (hW : WFX N G) (hinv : Inv N I C G om (t + 1)) (hne : N + N + t ≠ C.output)
    (hnoAL : ∀ j', Cone N C j' → N + N + t ∈ (gateAt C j').inputs → ¬ AL N C j')
    (pl : Fin N) (hpl : Lv N C (ep pl) t) :
    ∃ G1 F1, WFX N G1 ∧ (∀ h, Has N G h → Has N G1 h) ∧
      G1.length + 1 ≤ G.length + (SpF N C t).card ∧ Has N G1 F1 ∧
      (∀ p : Fin N, Lv N C (ep p) t → F1 (ep p) = true) ∧
      (∀ x, F1 x = true → ∃ j', Stp N C x t j' ∧ QL N I C x j') := by
  classical
  have key : ∀ p : Fin N, Lv N C (ep p) t →
      ∃ js ∈ (SpF N C t).filter (fun js => NW N C js.1), om js.1 (ep p) = true := by
    intro p hp
    obtain ⟨j', hs, hl⟩ := lv_parent N C (ep p) t hp hne
    obtain ⟨s, hsm⟩ := spot_of N C hg t j' hp.1.2.1 hs.1 hs.2.1
    have hnw : NW N C j' := ⟨⟨p, hl⟩, hnoAL j' hs.1 hs.2.1⟩
    have hlt : t < j' := (spot_mem N C hg hrb t _ hsm).2.2
    exact ⟨(j', s), Finset.mem_filter.mpr ⟨hsm, hnw⟩, (hinv j' (by omega) hnw).2.1 p hl⟩
  obtain ⟨js0, hjs0, _⟩ := key pl hpl
  obtain ⟨G1, hW1, hl1, hlift1, F1, hF1, hFs⟩ :=
    has_ors N (fun js : ℕ × ℕ => om js.1) _ ⟨js0, hjs0⟩ G hW (fun js hjs => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hjs
      have hlt := (spot_mem N C hg hrb t js h1).2.2
      exact (hinv js.1 (by omega) h2).1)
  refine ⟨G1, F1, hW1, hlift1, ?_, hF1, ?_, ?_⟩
  · have := Finset.card_filter_le (SpF N C t) (fun js => NW N C js.1)
    omega
  · intro p hp
    exact (hFs _).2 (key p hp)
  · intro x hx
    obtain ⟨js, hjs, hv⟩ := (hFs x).1 hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hjs
    obtain ⟨hcj, hin, hlt⟩ := spot_mem N C hg hrb t js h1
    have hq := (hinv js.1 (by omega) h2).2.2 x hv
    exact ⟨js.1, ⟨hcj, hin, hq.1⟩, hq⟩

theorem wire_step (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hg : F2 C) (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, dL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, dP N C h = 0))
    (G0 : List Gate)
    (hG0 : ∀ w, w < N + N + C.gates.length → dL N C w = 0 →
      Has N G0 (fun x => E N C x (fun _ => false) w))
    (t : ℕ) (ht : t < C.gates.length) (G : List Gate) (om : ℕ → (Fin N → Bool) → Bool)
    (hW : WFX N G) (hlift : ∀ h, Has N G0 h → Has N G h) (hinv : Inv N I C G om (t + 1)) :
    ∃ G' om', WFX N G' ∧ (∀ h, Has N G h → Has N G' h) ∧ Inv N I C G' om' t ∧
      G'.length + aud N C t ≤ G.length + bud N I C t := by
  classical
  by_cases hnw : NW N C t
  swap
  · refine ⟨G, om, hW, fun h hh => hh, ?_, ?_⟩
    · intro j hj hjn
      have hjt : j ≠ t := by
        intro h
        rw [h] at hjn
        exact hnw hjn
      exact hinv j (by omega) hjn
    · have := aud_le N I C hg hrb t
      omega
  · obtain ⟨⟨pl, hpl⟩, hnal⟩ := hnw
    have hc : Cone N C t := hpl.1
    have hkeep : ∀ (G' : List Gate) (f : (Fin N → Bool) → Bool),
        (∀ h, Has N G h → Has N G' h) → Has N G' f →
        (∀ p : Fin N, Lv N C (ep p) t → f (ep p) = true) →
        (∀ x, f x = true → QL N I C x t) → Inv N I C G' (Function.update om t f) t := by
      intro G' f hl' hf hd hsn j hj hjn
      by_cases hjt : j = t
      · rw [hjt, Function.update_self]
        exact ⟨hf, hd, hsn⟩
      · rw [Function.update_of_ne hjt]
        obtain ⟨h1, h2, h3⟩ := hinv j (by omega) hjn
        exact ⟨hl' _ h1, h2, h3⟩
    obtain ⟨a, b, hab | hab⟩ := gate_shape C hg t ht
    · obtain ⟨i, hi, hdi, hgi⟩ := gok_and N C hg hrb hkm t hc a b hab
      have hHi : Has N G (fun x => E N C x (fun _ => false) i) :=
        hlift _ (hG0 i (by omega) hdi)
      by_cases huniq : ∃ p0 : Fin N, ∀ p : Fin N, Lv N C (ep p) t → p = p0
      · obtain ⟨p0, hp0⟩ := huniq
        have hpl' : Lv N C (ep p0) t := by
          rw [← hp0 pl hpl]
          exact hpl
        refine ⟨G, Function.update om t (fun x => x p0), hW, fun h hh => hh, ?_, ?_⟩
        · refine hkeep G _ (fun h hh => hh)
            ⟨p0.val, by have := p0.isLt; omega, fun x => XV_in N G x p0.val p0.isLt⟩ ?_ ?_
          · intro p hp
            rw [hp0 p hp]
            simp [ep]
          · intro x hx
            exact ⟨gok_mono N C hg (ep p0) x (ep_le p0 x hx) t hpl'.2.1, t,
              Relation.ReflTransGen.refl, Or.inr (Or.inr ⟨p0, hx, hpl'⟩)⟩
        · have := aud_le N I C hg hrb t
          omega
      · have htwo : TW N C t := by
          by_contra hcon
          apply huniq
          refine ⟨pl, fun p hp => ?_⟩
          by_contra hpp
          exact hcon ⟨p, pl, hpp, hp, hpl⟩
        by_cases hfree : N + N + t = C.output ∨
            (∃ j', Cone N C j' ∧ N + N + t ∈ (gateAt C j').inputs ∧ AL N C j') ∨
            ∃ w0 : Fin N, ¬ Gok N C (xb I w0) t
        · refine ⟨G, Function.update om t (fun x => E N C x (fun _ => false) i), hW,
            fun h hh => hh, ?_, ?_⟩
          · refine hkeep G _ (fun h hh => hh) hHi (fun p hp => (hgi (ep p)).1 hp.2.1) ?_
            intro x hx
            have hgx : Gok N C x t := (hgi x).2 hx
            rcases hfree with ho | ⟨j', hcj, hin, hal⟩ | hw0
            · exact ⟨hgx, t, Relation.ReflTransGen.refl, Or.inl ho⟩
            · obtain ⟨_, hgj, jo, hjo, hr⟩ := hal x
              exact ⟨hgx, jo, Relation.ReflTransGen.head ⟨hcj, hin, hgj⟩ hr, Or.inl hjo⟩
            · exact ⟨hgx, t, Relation.ReflTransGen.refl, Or.inr (Or.inl ⟨htwo, hw0⟩)⟩
          · have := aud_le N I C hg hrb t
            omega
        · obtain ⟨hno, hrest⟩ := not_or.mp hfree
          obtain ⟨hnoal, hallw⟩ := not_or.mp hrest
          have hnoAL : ∀ j', Cone N C j' → N + N + t ∈ (gateAt C j').inputs → ¬ AL N C j' :=
            fun j' h1 h2 h3 => hnoal ⟨j', h1, h2, h3⟩
          have hallw' : ∀ w0 : Fin N, Gok N C (xb I w0) t := by
            intro w0
            by_contra h
            exact hallw ⟨w0, h⟩
          have hkn : KN N I C t := ⟨hc, by rw [hab], htwo, hallw'⟩
          obtain ⟨G1, F1, hW1, hlift1, hl1, hF1, hD1, hS1⟩ :=
            par_or N I C hg hrb t G om hW hinv hno hnoAL pl hpl
          obtain ⟨G2, hW2, hl2, hlift2, hF2⟩ := has_and N G1 hW1 _ _ (hlift1 _ hHi) hF1
          refine ⟨G2, Function.update om t (fun x => E N C x (fun _ => false) i && F1 x), hW2,
            fun h hh => hlift2 h (hlift1 h hh), ?_, ?_⟩
          · refine hkeep G2 _ (fun h hh => hlift2 h (hlift1 h hh)) hF2 ?_ ?_
            · intro p hp
              show (E N C (ep p) (fun _ => false) i && F1 (ep p)) = true
              rw [(hgi (ep p)).1 hp.2.1, hD1 p hp]
              rfl
            · intro x hx
              have hx' : E N C x (fun _ => false) i = true ∧ F1 x = true := by
                simpa using hx
              obtain ⟨j', hs, hq⟩ := hS1 x hx'.2
              obtain ⟨_, j'', hr, htm⟩ := hq
              exact ⟨(hgi x).2 hx'.1, j'', Relation.ReflTransGen.head hs hr, htm⟩
          · unfold aud bud
            rw [if_pos hc, if_pos hkn]
            split_ifs <;> omega
    · have hgor : ∀ x, Gok N C x t := fun x => Or.inl (by rw [hab])
      have hno : N + N + t ≠ C.output := by
        intro ho
        apply hnal
        intro x
        exact ⟨hc, hgor x, t, ho, Relation.ReflTransGen.refl⟩
      have hnoAL : ∀ j', Cone N C j' → N + N + t ∈ (gateAt C j').inputs → ¬ AL N C j' := by
        intro j' h1 h2 h3
        apply hnal
        intro x
        exact lv_child N C x t j' hc (hgor x) ⟨h1, h2, (h3 x).2.1⟩ (h3 x)
      obtain ⟨G1, F1, hW1, hlift1, hl1, hF1, hD1, hS1⟩ :=
        par_or N I C hg hrb t G om hW hinv hno hnoAL pl hpl
      refine ⟨G1, Function.update om t F1, hW1, hlift1, ?_, ?_⟩
      · refine hkeep G1 _ hlift1 hF1 hD1 ?_
        intro x hx
        obtain ⟨j', hs, hq⟩ := hS1 x hx
        obtain ⟨_, j'', hr, htm⟩ := hq
        exact ⟨hgor x, j'', Relation.ReflTransGen.head hs hr, htm⟩
      · unfold aud bud
        rw [if_pos hc]
        split_ifs <;> omega

theorem live (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hg : F2 C) (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, dL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, dP N C h = 0))
    (G0 : List Gate) (hW0 : WFX N G0)
    (hG0 : ∀ w, w < N + N + C.gates.length → dL N C w = 0 →
      Has N G0 (fun x => E N C x (fun _ => false) w)) :
    ∀ k, k ≤ C.gates.length → ∃ G om, WFX N G ∧ Inv N I C G om (C.gates.length - k) ∧
      G.length + ∑ j ∈ Finset.Ico (C.gates.length - k) C.gates.length, aud N C j ≤
        G0.length + ∑ j ∈ Finset.Ico (C.gates.length - k) C.gates.length, bud N I C j ∧
      (∀ h, Has N G0 h → Has N G h) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨G0, fun _ _ => false, hW0, ?_, by simp, fun h hh => hh⟩
    intro j hj hjn
    exfalso
    obtain ⟨⟨p, hp⟩, _⟩ := hjn
    have := hp.1.1
    omega
  | succ k ih =>
    intro hk
    obtain ⟨G, om, hW, hinv, hcnt, hlift⟩ := ih (by omega)
    have ht : C.gates.length - (k + 1) < C.gates.length := by omega
    have e : C.gates.length - k = C.gates.length - (k + 1) + 1 := by omega
    rw [e] at hinv hcnt
    obtain ⟨G', om', hW', hlift', hinv', hc'⟩ :=
      wire_step N I C hg hrb hkm G0 hG0 _ ht G om hW hlift hinv
    refine ⟨G', om', hW', hinv', ?_, fun h hh => hlift' h (hlift h hh)⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot ht, Finset.sum_eq_sum_Ico_succ_bot ht]
    omega

theorem sum_card_le {ι α : Type} [DecidableEq α] (s : Finset ι) (f : ι → Finset α)
    (B : Finset α) (hsub : ∀ i ∈ s, f i ⊆ B)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, ∀ a, a ∈ f i → a ∈ f j → i = j) :
    ∑ i ∈ s, (f i).card ≤ B.card := by
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro a ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    exact hsub i hi hai
  · intro i hi j hj hij
    show Disjoint (f i) (f j)
    rw [Finset.disjoint_left]
    intro a hai haj
    exact hij (hdis i hi j hj a hai haj)

theorem fin_pairs (n : ℕ) (P : ℕ × ℕ → Prop) (hP : ∀ js, P js → js.1 < n ∧ js.2 < 2) :
    ∃ B : Finset (ℕ × ℕ), ∀ js, js ∈ B ↔ P js := by
  classical
  refine ⟨(Finset.range n ×ˢ Finset.range 2).filter P, fun js => ?_⟩
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hP js h, h⟩⟩

theorem fin_of (n : ℕ) (P : ℕ → Prop) (hP : ∀ j, P j → j < n) :
    ∃ B : Finset ℕ, ∀ j, j ∈ B ↔ P j := by
  classical
  refine ⟨(Finset.range n).filter P, fun j => ?_⟩
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨hP j h, h⟩⟩

theorem fin_ty {α : Type} [Fintype α] (P : α → Prop) : ∃ B : Finset α, ∀ a, a ∈ B ↔ P a := by
  classical
  refine ⟨Finset.univ.filter P, fun a => ?_⟩
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem ncard_set {α : Type} (P : α → Prop) (B : Finset α) (hB : ∀ a, a ∈ B ↔ P a) :
    Set.ncard {a : α | P a} = B.card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext a
  exact (hB a).symm

theorem sum_ite_card (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (hP : ∀ j, P j → j < n)
    (B : Finset ℕ) (hB : ∀ j, j ∈ B ↔ P j) :
    ∑ j ∈ Finset.range n, (if P j then 1 else 0) = B.card := by
  rw [← Finset.card_filter]
  congr 1
  ext j
  rw [Finset.mem_filter, Finset.mem_range, hB]
  exact ⟨fun h => h.2, fun h => ⟨hP j h, h⟩⟩

theorem sum_out (n K o : ℕ) : ∑ j ∈ Finset.range n, (if K + j = o then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter, Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  omega

theorem main (H1 : RSB) (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hg : F2 C) (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, dL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, dP N C h = 0))
    (no4 : ∀ p p' w w' : Fin N, p ≠ p' → w ≠ w' → I p w → I p' w → I p w' → I p' w' → False)
    (hedge : ∃ p w : Fin N, I p w)
    (h24 : ∀ (h j : ℕ) (w : Fin N), Slot N C h j → Lh N C h w → ¬ Lv N C (xb I w) j)
    (h3 : ∀ (h j6 j7 : ℕ) (w p : Fin N), Slot N C h j6 → Lh N C h w → Gok N C (xb I w) j6 →
      Relation.ReflTransGen (Stp N C (xb I w)) j6 j7 → ¬ I p w → ∀ j8 : ℕ,
      N + N + j8 = C.output → ¬ Relation.ReflTransGen (Stp N C (ep p)) j7 j8) :
    ∃ (TL TP : Finset (Fin N)) (KB KP : Finset ℕ) (own : ℕ → Fin N),
      (∀ j ∈ KB ∪ KP, Cone N C j ∧ (gateAt C j).op = GateOp.and) ∧ Disjoint KB KP ∧
      (∀ j ∈ KB, ∃ p p' : Fin N, p ≠ p' ∧ Lv N C (ep p) j ∧ Lv N C (ep p') j) ∧
      (∀ j ∈ KP, own j ∈ TP ∧ ∀ p : Fin N, Lv N C (ep p) j → p = own j) ∧
      (∀ p ∈ TP, ∃ j ∈ KP, own j = p) ∧
      (∀ p w : Fin N, Lps N C p w → w ∈ TL ∨ p ∈ TP) ∧
      ∑ w : Fin N, Set.ncard {p : Fin N | Lps N C p w} + TL.card +
          Set.ncard {j : ℕ | Cone N C j} ≤
        Set.ncard {j : ℕ | j < C.gates.length ∧ dL N C (N + N + j) = 0} + KB.card +
        Set.ncard {js : ℕ × ℕ | Cone N C js.1 ∧ js.2 < 2 ∧
          dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0 ∧
          ∃ w : Fin N, Lpw N C ((gateAt C js.1).inputs.getD js.2 0) w} +
        Set.ncard {js : ℕ × ℕ | Cone N C js.1 ∧ js.2 < 2 ∧
          Mx N C ((gateAt C js.1).inputs.getD js.2 0)} + 1 := by
  classical
  obtain ⟨pd, _, _⟩ := hedge
  obtain ⟨KNf, hKN⟩ := fin_of C.gates.length (KN N I C) (fun j h => h.1.1)
  obtain ⟨KFf, hKF⟩ := fin_of C.gates.length (KF N I C) (fun j h => h.1.1)
  obtain ⟨KPf, hKP⟩ := fin_of C.gates.length
    (fun j => Cone N C j ∧ (gateAt C j).op = GateOp.and ∧ ∃ p : Fin N, UQ N C j p)
    (fun j h => h.1.1)
  obtain ⟨CNf, hCN⟩ := fin_of C.gates.length (Cone N C) (fun j h => h.1)
  obtain ⟨TL, hTL⟩ := fin_ty (fun w : Fin N => ∃ j : ℕ, Cone N C j ∧
    (gateAt C j).op = GateOp.and ∧ TW N C j ∧ ¬ Gok N C (xb I w) j)
  obtain ⟨TP, hTP⟩ := fin_ty (fun p : Fin N => ∃ j : ℕ, Cone N C j ∧
    (gateAt C j).op = GateOp.and ∧ UQ N C j p)
  obtain ⟨own, hown⟩ : ∃ own : ℕ → Fin N, ∀ j p, UQ N C j p → own j = p := by
    refine ⟨fun j => if h : ∃ p, UQ N C j p then Classical.choose h else pd, fun j p hp => ?_⟩
    have h : ∃ p, UQ N C j p := ⟨p, hp⟩
    show (if h : ∃ p, UQ N C j p then Classical.choose h else pd) = p
    rw [dif_pos h]
    exact ((Classical.choose_spec h).2 p hp.1).symm
  have hKBtw : ∀ j ∈ KNf ∪ KFf, Cone N C j ∧ (gateAt C j).op = GateOp.and ∧ TW N C j := by
    intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · obtain ⟨h1, h2, h3, _⟩ := (hKN j).1 h
      exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, _⟩ := (hKF j).1 h
      exact ⟨h1, h2, h3⟩
  have hgokI : ∀ (j : ℕ) (p w0 : Fin N), Lv N C (ep p) j → ¬ Gok N C (xb I w0) j → I p w0 := by
    intro j p w0 hp hng
    by_contra hI
    exact hng (gok_mono N C hg (ep p) _ (ep_le p _ (xb_at I w0 p hI)) j hp.2.1)
  have hTLc : TL.card ≤ KFf.card := by
    have hch : ∀ w : Fin N, ∃ j : ℕ, w ∈ TL → (Cone N C j ∧
        (gateAt C j).op = GateOp.and ∧ TW N C j ∧ ¬ Gok N C (xb I w) j) := by
      intro w
      by_cases hw : w ∈ TL
      · obtain ⟨j, hj⟩ := (hTL w).1 hw
        exact ⟨j, fun _ => hj⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose f hf using hch
    apply Finset.card_le_card_of_injOn f
    · intro w hw
      obtain ⟨h1, h2, h3, h4⟩ := hf w hw
      exact (hKF _).2 ⟨h1, h2, h3, w, h4⟩
    · intro w hw w' hw' he
      obtain ⟨_, _, ⟨p1, p2, hne, hl1, hl2⟩, h4⟩ := hf w hw
      obtain ⟨_, _, _, h4'⟩ := hf w' hw'
      rw [← he] at h4'
      by_contra hww
      exact no4 p1 p2 w w' hne hww (hgokI _ p1 w hl1 h4) (hgokI _ p2 w hl2 h4)
        (hgokI _ p1 w' hl1 h4') (hgokI _ p2 w' hl2 h4')
  have hdisj : Disjoint KNf KFf := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    obtain ⟨_, _, _, hall⟩ := (hKN j).1 h1
    obtain ⟨_, _, _, w0, hw0⟩ := (hKF j).1 h2
    exact hw0 (hall w0)
  have hKBc : (KNf ∪ KFf).card = KNf.card + KFf.card := Finset.card_union_of_disjoint hdisj
  refine ⟨TL, TP, KNf ∪ KFf, KPf, own, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact ⟨(hKBtw j h).1, (hKBtw j h).2.1⟩
    · exact ⟨((hKP j).1 h).1, ((hKP j).1 h).2.1⟩
  · rw [Finset.disjoint_left]
    intro j h1 h2
    obtain ⟨_, _, p, p', hne, hl1, hl2⟩ := hKBtw j h1
    obtain ⟨_, _, p0, hu⟩ := (hKP j).1 h2
    exact hne ((hu.2 p hl1).trans (hu.2 p' hl2).symm)
  · intro j hj
    exact (hKBtw j hj).2.2
  · intro j hj
    obtain ⟨hc, ho, p0, hu⟩ := (hKP j).1 hj
    rw [hown j p0 hu]
    exact ⟨(hTP p0).2 ⟨j, hc, ho, hu⟩, fun p hp => hu.2 p hp⟩
  · intro p hp
    obtain ⟨j, hc, ho, hu⟩ := (hTP p).1 hp
    exact ⟨j, (hKP j).2 ⟨hc, ho, p, hu⟩, hown j p hu⟩
  · intro p w hl
    by_contra hcon
    obtain ⟨hnTL, hnTP⟩ := not_or.mp hcon
    obtain ⟨h, hlpw, j0, hslot, hlv⟩ := hl
    have hlh : Lh N C h w := (hlpw w).2 rfl
    have hall : ∀ j, Lv N C (ep p) j → Gok N C (xb I w) j := by
      intro j hj
      by_contra hng
      obtain ⟨a, b, hab | hab⟩ := gate_shape C hg j hj.1.1
      · have hop : (gateAt C j).op = GateOp.and := by rw [hab]
        by_cases htw : TW N C j
        · exact hnTL ((hTL w).2 ⟨j, hj.1, hop, htw, hng⟩)
        · apply hnTP
          refine (hTP p).2 ⟨j, hj.1, hop, hj, fun p' hp' => ?_⟩
          by_contra hne
          exact htw ⟨p', p, hne, hp', hj⟩
      · exact hng (Or.inl (by rw [hab]))
    obtain ⟨hc0, hg0, jo, hjo, hr⟩ := hlv
    exact h24 h j0 w hslot hlh ⟨hc0, hall j0 ⟨hc0, hg0, jo, hjo, hr⟩, jo, hjo,
      rtg_lift N C (ep p) (xb I w) jo hjo hall j0 hr⟩
  · obtain ⟨G0, hW0, hlen0, hhas0⟩ := base N C hg hrb C.gates.length le_rfl
    obtain ⟨G, om, hW, hinv, hcnt, hlift⟩ :=
      live N I C hg hrb hkm G0 hW0 hhas0 C.gates.length le_rfl
    rw [Nat.sub_self] at hinv hcnt
    rw [← Finset.range_eq_Ico] at hcnt
    have hA1 : Set.ncard {j : ℕ | Cone N C j} = CNf.card := ncard_set _ CNf hCN
    have hA2 : ∑ j ∈ Finset.range C.gates.length, aud N C j = CNf.card := by
      unfold aud
      exact sum_ite_card C.gates.length (Cone N C) (fun j h => h.1) CNf hCN
    obtain ⟨B4, hB4⟩ := fin_pairs C.gates.length (fun js : ℕ × ℕ => Cone N C js.1 ∧ js.2 < 2 ∧
      Mx N C ((gateAt C js.1).inputs.getD js.2 0)) (fun js h => ⟨h.1.1, h.2.1⟩)
    have hB4c : Set.ncard {js : ℕ × ℕ | Cone N C js.1 ∧ js.2 < 2 ∧
        Mx N C ((gateAt C js.1).inputs.getD js.2 0)} = B4.card := ncard_set _ B4 hB4
    have hBs : ∑ j ∈ Finset.range C.gates.length, bud N I C j ≤ B4.card + KNf.card + 1 := by
      unfold bud
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h1 : ∑ j ∈ Finset.range C.gates.length, (SpF N C j).card ≤ B4.card := by
        refine sum_card_le _ _ B4 ?_ ?_
        · intro j _ js hjs
          obtain ⟨k1, k2, k3, k4⟩ := (mem_SpF N C j js).1 hjs
          exact (hB4 js).2 ⟨k1, k2, by rw [k3]; exact k4⟩
        · intro i _ j _ js hi hj
          have k3 := ((mem_SpF N C i js).1 hi).2.2.1
          have k3' := ((mem_SpF N C j js).1 hj).2.2.1
          omega
      have h2 : ∑ j ∈ Finset.range C.gates.length, (if KN N I C j then 1 else 0) = KNf.card :=
        sum_ite_card C.gates.length (KN N I C) (fun j h => h.1.1) KNf hKN
      have h3 := sum_out C.gates.length (N + N) C.output
      omega
    have hSwE : ∀ w : Fin N, ∃ B : Finset (ℕ × ℕ), ∀ js, js ∈ B ↔ (Cone N C js.1 ∧ js.2 < 2 ∧
        dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0 ∧
        Lpw N C ((gateAt C js.1).inputs.getD js.2 0) w) :=
      fun w => fin_pairs C.gates.length _ (fun js h => ⟨h.1.1, h.2.1⟩)
    choose Sw hSw using hSwE
    obtain ⟨B3, hB3⟩ := fin_pairs C.gates.length (fun js : ℕ × ℕ => Cone N C js.1 ∧ js.2 < 2 ∧
      dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0 ∧
      ∃ w : Fin N, Lpw N C ((gateAt C js.1).inputs.getD js.2 0) w) (fun js h => ⟨h.1.1, h.2.1⟩)
    have hB3c : Set.ncard {js : ℕ × ℕ | Cone N C js.1 ∧ js.2 < 2 ∧
        dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0 ∧
        ∃ w : Fin N, Lpw N C ((gateAt C js.1).inputs.getD js.2 0) w} = B3.card :=
      ncard_set _ B3 hB3
    have hSwsum : ∑ w : Fin N, (Sw w).card ≤ B3.card := by
      refine sum_card_le Finset.univ Sw B3 ?_ ?_
      · intro w _ js hjs
        obtain ⟨k1, k2, k3, k4⟩ := (hSw w js).1 hjs
        exact (hB3 js).2 ⟨k1, k2, k3, w, k4⟩
      · intro w _ w' _ js h1 h2
        have l1 := ((hSw w js).1 h1).2.2.2
        have l2 := ((hSw w' js).1 h2).2.2.2
        exact (l2 w).1 ((l1 w).2 rfl)
    have hslot : ∀ (w : Fin N) (js : ℕ × ℕ), js ∈ Sw w →
        Slot N C ((gateAt C js.1).inputs.getD js.2 0) js.1 ∧
        Lh N C ((gateAt C js.1).inputs.getD js.2 0) w := by
      intro w js hjs
      obtain ⟨hc, hs, hd, hl⟩ := (hSw w js).1 hjs
      exact ⟨⟨hc, getD_mem C hg js.1 hc.1 js.2 hs, hd⟩, (hl w).2 rfl⟩
    have hnw : ∀ (w : Fin N) (js : ℕ × ℕ), js ∈ Sw w → (∃ p : Fin N, Lv N C (ep p) js.1) →
        NW N C js.1 := by
      intro w js hjs hp
      exact ⟨hp, fun hal => h24 _ js.1 w (hslot w js hjs).1 (hslot w js hjs).2 (hal _)⟩
    have hsound : ∀ (w : Fin N) (js : ℕ × ℕ), js ∈ Sw w → NW N C js.1 →
        ∀ x : Fin N → Bool, (∀ p, x p = true → ¬ I p w) → om js.1 x = true → False := by
      intro w js hjs hn x hx hv
      exact sound N I C hg no4 h24 h3 _ js.1 w (hslot w js hjs).1 (hslot w js hjs).2 x hx
        ((hinv js.1 (Nat.zero_le _) hn).2.2 x hv)
    have hSvE : ∀ w : Fin N, ∃ B : Finset (ℕ × ℕ), ∀ js, js ∈ B ↔
        (js ∈ Sw w ∧ ∃ p : Fin N, Lv N C (ep p) js.1) :=
      fun w => ⟨(Sw w).filter (fun js => ∃ p : Fin N, Lv N C (ep p) js.1),
        fun js => Finset.mem_filter⟩
    choose Sv hSv using hSvE
    have hS1E : ∀ w : Fin N, ∃ B : Finset (Fin N), ∀ p, p ∈ B ↔
        ∃ js ∈ Sv w, om js.1 (ep p) = true := fun w => fin_ty _
    choose S1 hS1 using hS1E
    obtain ⟨U, hU⟩ : ∃ U : Fin N → Finset (Fin N), ∀ w p, p ∈ U w ↔ I p w :=
      ⟨fun w => Finset.univ.filter (fun p => I p w), fun w p => by simp⟩
    obtain ⟨T, hT⟩ := fin_ty (fun w : Fin N => 2 ≤ (S1 w).card)
    have hspot : ∀ p w : Fin N, Lps N C p w → ∃ js, js ∈ Sw w ∧ Lv N C (ep p) js.1 := by
      intro p w hl
      obtain ⟨h, hlpw, j0, hsl, hlv⟩ := hl
      obtain ⟨s, hs, hse⟩ := mem_getD C hg j0 hsl.1.1 h hsl.2.1
      refine ⟨(j0, s), (hSw w (j0, s)).2 ⟨hsl.1, hs, ?_, ?_⟩, hlv⟩
      · show dP N C ((gateAt C j0).inputs.getD s 0) = 0
        rw [hse]
        exact hsl.2.2
      · show Lpw N C ((gateAt C j0).inputs.getD s 0) w
        rw [hse]
        exact hlpw
    have hDom : ∀ p w : Fin N, Lps N C p w → p ∈ S1 w := by
      intro p w hl
      obtain ⟨js, hjs, hlv⟩ := hspot p w hl
      exact (hS1 w p).2 ⟨js, (hSv w js).2 ⟨hjs, p, hlv⟩,
        (hinv js.1 (Nat.zero_le _) (hnw w js hjs ⟨p, hlv⟩)).2.1 p hlv⟩
    obtain ⟨G2, hW2, hl2, hlift2, hF2⟩ :=
      has_fam N (fun js : ℕ × ℕ => om js.1) Sv T G hW (by
        intro w hw
        have h2 : 2 ≤ (S1 w).card := (hT w).1 hw
        obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (S1 w).card)
        obtain ⟨js, hjs, _⟩ := (hS1 w p).1 hp
        refine ⟨⟨js, hjs⟩, fun js' hjs' => ?_⟩
        obtain ⟨h1, hp'⟩ := (hSv w js').1 hjs'
        exact (hinv js'.1 (Nat.zero_le _) (hnw w js' h1 hp')).1)
    have hoE : ∀ w : Fin N, ∃ i : ℕ, w ∈ T → ∀ x : Fin N → Bool,
        (XV N G2 x i = true ↔ ∃ js ∈ Sv w, om js.1 x = true) := by
      intro w
      by_cases hw : w ∈ T
      · obtain ⟨F, ⟨i, _, hi⟩, hFs⟩ := hF2 w hw
        exact ⟨i, fun _ x => by rw [hi x]; exact hFs x⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose o ho using hoE
    have hP := rsb_fin H1 T N N U S1 ⟨G2, 0⟩ o (fun w => (S1 w).card - 1)
      (fun i _ j _ hij => by
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        rw [Finset.mem_inter, hU, hU] at ha hb
        exact no4 a b i j hab hij ha.1 hb.1 ha.2 hb.2)
      (fun w hw p hp => by
        rw [hU]
        by_contra hI
        obtain ⟨js, hjs, hv⟩ := (hS1 w p).1 hp
        obtain ⟨h1, hp'⟩ := (hSv w js).1 hjs
        refine hsound w js h1 (hnw w js h1 hp') (ep p) ?_ hv
        intro p' hp''
        have e : p' = p := by simpa [ep] using hp''
        rw [e]
        exact hI)
      (fun w hw => (hT w).1 hw) hW2.1 hW2.2
      (fun w hw p => by
        rw [hS1]
        exact ho w hw (ep p))
      (fun w hw x _ hz => by
        by_contra hne
        have hV : XV N G2 x (o w) = true := by simpa using hne
        obtain ⟨js, hjs, hv⟩ := (ho w hw x).1 hV
        obtain ⟨h1, hp'⟩ := (hSv w js).1 hjs
        refine hsound w js h1 (hnw w js h1 hp') x ?_ hv
        intro p hp hI
        rw [hz p ((hU w p).2 hI)] at hp
        exact Bool.false_ne_true hp)
      (fun w _ => by
        have := Finset.card_le_univ (S1 w)
        rw [Fintype.card_fin] at this
        omega)
      (fun w hw => by
        have := (hT w).1 hw
        omega)
    have hP' : ∑ w ∈ T, (S1 w).card ≤ G2.length + T.card := by
      have e : ∑ w ∈ T, (S1 w).card = ∑ w ∈ T, (((S1 w).card - 1) + 1) :=
        Finset.sum_congr rfl (fun w hw => by
          have := (hT w).1 hw
          omega)
      rw [e, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      exact Nat.add_le_add_right hP _
    have hline : ∀ w : Fin N, Set.ncard {p : Fin N | Lps N C p w} +
        (if w ∈ T then (Sv w).card else 0) ≤
        (if w ∈ T then (S1 w).card else 0) + (Sw w).card := by
      intro w
      have h1 : Set.ncard {p : Fin N | Lps N C p w} ≤ (S1 w).card := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard (fun p hp => hDom p w hp) (Finset.finite_toSet _)
      have h2 : (Sv w).card ≤ (Sw w).card :=
        Finset.card_le_card (fun js h => ((hSv w js).1 h).1)
      by_cases hw : w ∈ T
      · rw [if_pos hw, if_pos hw]
        omega
      · rw [if_neg hw, if_neg hw]
        have h3 : ¬ 2 ≤ (S1 w).card := fun h => hw ((hT w).2 h)
        by_cases hex : ∃ p, Lps N C p w
        · obtain ⟨p, hp⟩ := hex
          obtain ⟨js, hjs, _⟩ := hspot p w hp
          have := Finset.card_pos.mpr ⟨_, hjs⟩
          omega
        · have h0 : Set.ncard {p : Fin N | Lps N C p w} ≤ Set.ncard (∅ : Set (Fin N)) :=
            Set.ncard_le_ncard (fun p hp => (hex ⟨p, hp⟩).elim) Set.finite_empty
          rw [Set.ncard_empty] at h0
          omega
    have eT : ∀ f : Fin N → ℕ, ∑ w : Fin N, (if w ∈ T then f w else 0) = ∑ w ∈ T, f w := by
      intro f
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hsum := Finset.sum_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset (Fin N))) => hline w)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, eT, eT] at hsum
    have hlf := ncx N C
    have hG2 : (⟨G2, 0⟩ : Circuit).gates.length = G2.length := rfl
    omega

end PEqualNP.Outside.L_meta_1952

theorem PEqualNP.Outside.L_meta_1952 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → (∀ (N240 : ℕ) (I240 : Fin N240 → Fin N240 → Prop) [DecidableRel I240] (C240 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g240 ∈ C240.gates, (g240.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g240.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g240.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N240 + N240) C240) → (∀ j240 < C240.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240 0 = 0) ∨ (∀ h240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240 0 = 0)) → (∀ p240 p240x1 w240 w240x1 : Fin N240, p240 ≠ p240x1 → w240 ≠ w240x1 → I240 p240 w240 → I240 p240x1 w240 → I240 p240 w240x1 → I240 p240x1 w240x1 → False) → (∃ p240x2 w240x2 : Fin N240, I240 p240x2 w240x2) → (∀ p240x3 w240x3 : Fin N240, I240 p240x3 w240x3 → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append (fun a240 : Fin N240 => decide (a240 = p240x3)) (fun a240x1 : Fin N240 => decide (a240x1 = w240x3))) = true) → (∀ x240 y240 : Fin N240 → Bool, (Finset.univ.filter (fun l240 : Fin N240 => y240 l240 = true)).card ≤ 1 → (¬ ∃ p240x4 w240x4 : Fin N240, I240 p240x4 w240x4 ∧ x240 p240x4 = true ∧ y240 w240x4 = true) → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append x240 y240) = false) → ∀ mixed240 : ℕ → Prop, mixed240 = (fun i240x1 : ℕ => 0 < (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD i240x1 0 ∧ 0 < (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x1 0) → ∀ cone240 : ℕ → Prop, cone240 = (fun j240x1 : ℕ => j240x1 < C240.gates.length ∧ mixed240 (N240 + N240 + j240x1) ∧ Relation.ReflTransGen (fun a240x2 b240 : ℕ => a240x2 < b240 ∧ ∃ f240 : Fin C240.gates.length, b240 = N240 + N240 + f240.val ∧ a240x2 ∈ (C240.gates.get f240).inputs) (N240 + N240 + j240x1) C240.output) → ∀ gok240 : (Fin N240 → Bool) → ℕ → Prop, gok240 = (fun (x240x1 : Fin N240 → Bool) (j240x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i240x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x2 0 = 0 ∧ (C240.wires (List.ofFn (Fin.append x240x1 (fun u240 : Fin N240 => false)))).getD i240x2 false = true) → ∀ step240 : (Fin N240 → Bool) → ℕ → ℕ → Prop, step240 = (fun (x240x2 : Fin N240 → Bool) (j240x3 j240x4 : ℕ) => cone240 j240x4 ∧ N240 + N240 + j240x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x4).inputs ∧ gok240 x240x2 j240x4) → ∀ slot240 : ℕ → ℕ → Prop, slot240 = (fun h240x1 j240x5 : ℕ => cone240 j240x5 ∧ h240x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x5).inputs ∧ (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240x1 0 = 0) → ∀ lh240 : ℕ → Fin N240 → Prop, lh240 = (fun (h240x2 : ℕ) (w240x5 : Fin N240) => (C240.wires (List.ofFn (Fin.append (fun u240x1 : Fin N240 => false) (fun a240x3 : Fin N240 => decide (a240x3 = w240x5))))).getD h240x2 false = true) → ∀ (h240x3 j240x6 j240x7 : ℕ) (w240x6 p240x5 : Fin N240), slot240 h240x3 j240x6 → lh240 h240x3 w240x6 → gok240 (fun a240x4 : Fin N240 => decide (¬ I240 a240x4 w240x6)) j240x6 → Relation.ReflTransGen (step240 (fun a240x5 : Fin N240 => decide (¬ I240 a240x5 w240x6))) j240x6 j240x7 → ¬ I240 p240x5 w240x6 → ∀ j240x8 : ℕ, N240 + N240 + j240x8 = C240.output → ¬ Relation.ReflTransGen (step240 (fun a240x6 : Fin N240 => decide (a240x6 = p240x5))) j240x7 j240x8) → ∀ (N241 : ℕ) (I241 : Fin N241 → Fin N241 → Prop) [DecidableRel I241] (C241 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g241 ∈ C241.gates, (g241.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g241.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g241.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N241 + N241) C241) → (∀ j241 < C241.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241 0 = 0) ∨ (∀ h241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241 0 = 0)) → (∀ p241 p241x1 w241 w241x1 : Fin N241, p241 ≠ p241x1 → w241 ≠ w241x1 → I241 p241 w241 → I241 p241x1 w241 → I241 p241 w241x1 → I241 p241x1 w241x1 → False) → (∃ p241x2 w241x2 : Fin N241, I241 p241x2 w241x2) → (∀ p241x3 w241x3 : Fin N241, I241 p241x3 w241x3 → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append (fun a241 : Fin N241 => decide (a241 = p241x3)) (fun a241x1 : Fin N241 => decide (a241x1 = w241x3))) = true) → (∀ x241 y241 : Fin N241 → Bool, (Finset.univ.filter (fun l241 : Fin N241 => y241 l241 = true)).card ≤ 1 → (¬ ∃ p241x4 w241x4 : Fin N241, I241 p241x4 w241x4 ∧ x241 p241x4 = true ∧ y241 w241x4 = true) → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append x241 y241) = false) → ∀ mixed241 : ℕ → Prop, mixed241 = (fun i241x1 : ℕ => 0 < (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD i241x1 0 ∧ 0 < (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241x1 0) → ∀ cone241 : ℕ → Prop, cone241 = (fun j241x1 : ℕ => j241x1 < C241.gates.length ∧ mixed241 (N241 + N241 + j241x1) ∧ Relation.ReflTransGen (fun a241x2 b241 : ℕ => a241x2 < b241 ∧ ∃ f241 : Fin C241.gates.length, b241 = N241 + N241 + f241.val ∧ a241x2 ∈ (C241.gates.get f241).inputs) (N241 + N241 + j241x1) C241.output) → ∀ gok241 : (Fin N241 → Bool) → ℕ → Prop, gok241 = (fun (x241x1 : Fin N241 → Bool) (j241x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i241x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241x2 0 = 0 ∧ (C241.wires (List.ofFn (Fin.append x241x1 (fun u241 : Fin N241 => false)))).getD i241x2 false = true) → ∀ step241 : (Fin N241 → Bool) → ℕ → ℕ → Prop, step241 = (fun (x241x2 : Fin N241 → Bool) (j241x3 j241x4 : ℕ) => cone241 j241x4 ∧ N241 + N241 + j241x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x4).inputs ∧ gok241 x241x2 j241x4) → ∀ lvx241 : (Fin N241 → Bool) → ℕ → Prop, lvx241 = (fun (x241x3 : Fin N241 → Bool) (j241x5 : ℕ) => cone241 j241x5 ∧ gok241 x241x3 j241x5 ∧ ∃ j241x6 : ℕ, N241 + N241 + j241x6 = C241.output ∧ Relation.ReflTransGen (step241 x241x3) j241x5 j241x6) → ∀ slot241 : ℕ → ℕ → Prop, slot241 = (fun h241x1 j241x7 : ℕ => cone241 j241x7 ∧ h241x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x7).inputs ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241x1 0 = 0) → ∀ ap241 : ℕ → Fin N241 → Prop, ap241 = (fun (h241x2 : ℕ) (p241x5 : Fin N241) => ∃ j241x8 : ℕ, slot241 h241x2 j241x8 ∧ lvx241 (fun a241x3 : Fin N241 => decide (a241x3 = p241x5)) j241x8) → ∀ lh241 : ℕ → Fin N241 → Prop, lh241 = (fun (h241x3 : ℕ) (w241x5 : Fin N241) => (C241.wires (List.ofFn (Fin.append (fun u241x1 : Fin N241 => false) (fun a241x4 : Fin N241 => decide (a241x4 = w241x5))))).getD h241x3 false = true) → ∀ lpw241 : ℕ → Fin N241 → Prop, lpw241 = (fun (h241x4 : ℕ) (w241x6 : Fin N241) => ∀ w241x7 : Fin N241, lh241 h241x4 w241x7 ↔ w241x7 = w241x6) → ∀ lps241 : Fin N241 → Fin N241 → Prop, lps241 = (fun p241x6 w241x8 : Fin N241 => ∃ h241x5 : ℕ, lpw241 h241x5 w241x8 ∧ ap241 h241x5 p241x6) → ∃ (TL241 TP241 : Finset (Fin N241)) (KB241 KP241 : Finset ℕ) (own241 : ℕ → Fin N241), (∀ j241x9 ∈ KB241 ∪ KP241, cone241 j241x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Disjoint KB241 KP241 ∧ (∀ j241x10 ∈ KB241, ∃ p241x7 p241x8 : Fin N241, p241x7 ≠ p241x8 ∧ lvx241 (fun a241x5 : Fin N241 => decide (a241x5 = p241x7)) j241x10 ∧ lvx241 (fun a241x6 : Fin N241 => decide (a241x6 = p241x8)) j241x10) ∧ (∀ j241x11 ∈ KP241, own241 j241x11 ∈ TP241 ∧ ∀ p241x9 : Fin N241, lvx241 (fun a241x7 : Fin N241 => decide (a241x7 = p241x9)) j241x11 → p241x9 = own241 j241x11) ∧ (∀ p241x10 ∈ TP241, ∃ j241x12 ∈ KP241, own241 j241x12 = p241x10) ∧ (∀ p241x11 w241x9 : Fin N241, lps241 p241x11 w241x9 → w241x9 ∈ TL241 ∨ p241x11 ∈ TP241) ∧ ∑ w241x10 : Fin N241, Set.ncard {p241x12 : Fin N241 | lps241 p241x12 w241x10} + TL241.card + Set.ncard {j241x13 : ℕ | cone241 j241x13} ≤ Set.ncard {j241x14 : ℕ | j241x14 < C241.gates.length ∧ (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD (N241 + N241 + j241x14) 0 = 0} + KB241.card + Set.ncard {js241 : ℕ × ℕ | cone241 js241.1 ∧ js241.2 < 2 ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) 0 = 0 ∧ ∃ w241x11 : Fin N241, lpw241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) w241x11} + Set.ncard {js241x1 : ℕ × ℕ | cone241 js241x1.1 ∧ js241x1.2 < 2 ∧ mixed241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241x1.1).inputs.getD js241x1.2 0)} + 1 := by
  intro H1 H2 H3 N I _ C hC hkm no4 hedge hacc hrej mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw lps hlps
  have h2 := (H2 N I C hC hkm no4 hedge hacc hrej mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw _ rfl lps hlps _ rfl).2.2.2.1
  have h3 := H3 N I C hC hkm no4 hedge hacc hrej mixed hmixed cone hcone gok hgok step hstep slot hslot lh hlh
  subst hmixed hcone hgok hstep hlvx hslot hap hlh hlpw hlps
  exact PEqualNP.Outside.L_meta_1952.main H1 N I C hC.1 hC.2 hkm no4 hedge h2 h3
