import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1953

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

def RSB : Prop :=
  ∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size

def F2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (X X' : Circuit) : Prop :=
  F2 X' ∧ ReadsBack n X' ∧ X.gates.length ≤ X'.gates.length ∧
  ∀ (x : List Bool), x.length = n → ∀ w, w < n + X.gates.length → VV X' x w = VV X x w

theorem Ext_refl (n : ℕ) (X : Circuit) (h2 : F2 X) (hrb : ReadsBack n X) : Ext n X X :=
  ⟨h2, hrb, le_refl _, fun _ _ _ _ => rfl⟩

theorem Ext_trans (n : ℕ) (X X1 X2 : Circuit) (h1 : Ext n X X1) (h2 : Ext n X1 X2) :
    Ext n X X2 := by
  obtain ⟨_, _, hl1, hv1⟩ := h1
  obtain ⟨hF, hrb, hl2, hv2⟩ := h2
  refine ⟨hF, hrb, le_trans hl1 hl2, fun x hx w hw => ?_⟩
  rw [hv2 x hx w (by omega), hv1 x hx w hw]

theorem snoc_or (n : ℕ) (X : Circuit) (h2 : F2 X) (hrb : ReadsBack n X) (a b : ℕ)
    (ha : a < n + X.gates.length) (hb : b < n + X.gates.length) :
    ∃ X' : Circuit, Ext n X X' ∧ X'.gates.length = X.gates.length + 1 ∧
      ∀ x : List Bool, x.length = n → VV X' x (n + X.gates.length) = (VV X x a || VV X x b) := by
  have hw : ∀ x : List Bool,
      (⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩ : Circuit).wires x
      = X.wires x ++ [(VV X x a || VV X x b)] := by
    intro x
    show fd stpF x (X.gates ++ [⟨GateOp.or, [a, b]⟩]) = fd stpF x X.gates ++ [_]
    rw [fd_app]
    simp [fd, stpF, GateOp.eval, VV, wires_fd]
  have hlen : ∀ x : List Bool, (X.wires x).length = x.length + X.gates.length :=
    fun x => fd_len stpF X.gates x
  refine ⟨⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact h2 g h
    · rw [List.mem_singleton.mp h]
      exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    have hj' : j < X.gates.length + 1 := by simpa using hj
    by_cases hjl : j < X.gates.length
    · have e : gateAt ⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩ j = gateAt X j := by
        unfold gateAt
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]
      rw [e] at hi
      exact hrb j hjl i hi
    · have hje : j = X.gates.length := by omega
      have e : gateAt ⟨X.gates ++ [⟨GateOp.or, [a, b]⟩], X.output⟩ j = ⟨GateOp.or, [a, b]⟩ := by
        unfold gateAt
        rw [hje]
        simp [List.getD_eq_getElem?_getD]
      rw [e] at hi
      have hi' : i = a ∨ i = b := by simpa using hi
      rcases hi' with h | h <;> omega
  · simp
  · intro x hx w hw'
    unfold VV
    rw [hw x, getD_snoc, ifn (by rw [hlen, hx]; omega)]
  · simp
  · intro x hx
    unfold VV
    rw [hw x, getD_snoc, ifp (by rw [hlen, hx])]

theorem or_set (n : ℕ) (s : Finset ℕ) (hs : s.Nonempty) :
    ∀ (X : Circuit), F2 X → ReadsBack n X → (∀ w ∈ s, w < n + X.gates.length) →
    ∃ (X' : Circuit) (o : ℕ), Ext n X X' ∧ o < n + X'.gates.length ∧
      X'.gates.length + 1 = X.gates.length + s.card ∧
      ∀ x : List Bool, x.length = n → (VV X' x o = true ↔ ∃ w ∈ s, VV X x w = true) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro X h2 hrb hw
    exact ⟨X, a, Ext_refl n X h2 hrb, hw a (Finset.mem_singleton_self a), by simp,
      fun x _ => by simp⟩
  | cons a s ha hs ih =>
    intro X h2 hrb hw
    obtain ⟨X1, o1, hE1, ho1, hl1, hv1⟩ :=
      ih X h2 hrb (fun w hw' => hw w (Finset.mem_cons.mpr (Or.inr hw')))
    have ha' : a < n + X.gates.length := hw a (Finset.mem_cons.mpr (Or.inl rfl))
    have hle := hE1.2.2.1
    obtain ⟨X2, hE2, hl2, hv2⟩ := snoc_or n X1 hE1.1 hE1.2.1 a o1 (by omega) ho1
    refine ⟨X2, n + X1.gates.length, Ext_trans n X X1 X2 hE1 hE2, by omega, ?_, ?_⟩
    · rw [Finset.card_cons]
      omega
    · intro x hx
      rw [hv2 x hx, Bool.or_eq_true, hv1 x hx, hE1.2.2.2 x hx a ha']
      simp only [Finset.mem_cons, exists_eq_or_imp]

theorem or_fam {ι : Type} [DecidableEq ι] (n : ℕ) (f : ι → Finset ℕ) (X : Circuit) (h2 : F2 X)
    (hrb : ReadsBack n X) :
    ∀ (T : Finset ι), (∀ i ∈ T, (f i).Nonempty ∧ ∀ w ∈ f i, w < n + X.gates.length) →
    ∃ (X' : Circuit) (o : ι → ℕ), Ext n X X' ∧
      X'.gates.length + T.card = X.gates.length + ∑ i ∈ T, (f i).card ∧
      (∀ i ∈ T, o i < n + X'.gates.length) ∧
      ∀ i ∈ T, ∀ x : List Bool, x.length = n →
        (VV X' x (o i) = true ↔ ∃ w ∈ f i, VV X x w = true) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨X, fun _ => 0, Ext_refl n X h2 hrb, by simp, by simp, by simp⟩
  | insert a T ha ih =>
    intro hT
    obtain ⟨X1, o1, hE1, hl1, ho1, hv1⟩ := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨hne, hwa⟩ := hT a (Finset.mem_insert_self a T)
    have hle := hE1.2.2.1
    obtain ⟨X2, oa, hE2, hoa, hl2, hv2⟩ := or_set n (f a) hne X1 hE1.1 hE1.2.1
      (fun w hw => by have := hwa w hw; omega)
    have hle2 := hE2.2.2.1
    refine ⟨X2, Function.update o1 a oa, Ext_trans n X X1 X2 hE1 hE2, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      omega
    · intro i hi
      by_cases hia : i = a
      · rw [hia, Function.update_self]
        exact hoa
      · rw [Function.update_of_ne hia]
        have := ho1 i ((Finset.mem_insert.mp hi).resolve_left hia)
        omega
    · intro i hi x hx
      by_cases hia : i = a
      · rw [hia, Function.update_self, hv2 x hx]
        constructor
        · rintro ⟨w, hw, h⟩
          exact ⟨w, hw, by rw [← hE1.2.2.2 x hx w (hwa w hw)]; exact h⟩
        · rintro ⟨w, hw, h⟩
          exact ⟨w, hw, by rw [hE1.2.2.2 x hx w (hwa w hw)]; exact h⟩
      · have hiT := (Finset.mem_insert.mp hi).resolve_left hia
        rw [Function.update_of_ne hia, hE2.2.2.2 x hx (o1 i) (ho1 i hiT)]
        exact hv1 i hiT x hx

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

theorem rsb_or (H1 : RSB) {ι : Type} [DecidableEq ι] (T : Finset ι) (n k : ℕ)
    (U S : ι → Finset (Fin n)) (C : Circuit) (f : ι → Finset ℕ) (c : ι → ℕ) (hF : F2 C)
    (hrb : ReadsBack n C)
    (hf : ∀ i ∈ T, ∀ w ∈ f i, w < n + C.gates.length)
    (hU : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hS : ∀ i ∈ T, S i ⊆ U i) (h2 : ∀ i ∈ T, 2 ≤ (S i).card)
    (hsing : ∀ i ∈ T, ∀ p : Fin n,
      (p ∈ S i ↔ ∃ w ∈ f i, VV C (List.ofFn (fun a : Fin n => decide (a = p))) w = true))
    (hzero : ∀ i ∈ T, ∀ w ∈ f i, ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) → VV C (List.ofFn x) w = false)
    (hck : ∀ i ∈ T, c i ≤ k) (hcS : ∀ i ∈ T, c i + 1 ≤ (S i).card) :
    ∑ i ∈ T, c i + T.card ≤ C.gates.length + ∑ i ∈ T, (f i).card := by
  obtain ⟨X', o, hE, hl, _, hv⟩ := or_fam n f C hF hrb T (fun i hi => by
    refine ⟨?_, hf i hi⟩
    have hpos : 0 < (S i).card := by have := h2 i hi; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    obtain ⟨w, hw, _⟩ := (hsing i hi p).mp hp
    exact ⟨w, hw⟩)
  have h := rsb_fin H1 T n k U S X' o c hU hS h2 hE.1 hE.2.1
    (fun i hi p => (hv i hi _ (by simp)).trans (hsing i hi p).symm)
    (fun i hi x hx hxU => by
      by_contra hne
      have hV : VV X' (List.ofFn x) (o i) = true := by simpa using hne
      obtain ⟨w, hw, h'⟩ := (hv i hi _ (by simp)).mp hV
      rw [hzero i hi w hw x hx hxU] at h'
      cases h')
    hck hcS
  omega

def cy (N : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if dP N C (N + N + i) = 0 then 1 else 0

theorem cy_succ (N : ℕ) (C : Circuit) (k : ℕ) :
    cy N C (k + 1) = cy N C k + if dP N C (N + N + k) = 0 then 1 else 0 := by
  unfold cy
  rw [Finset.sum_range_succ]

theorem ncy (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ dP N C (N + N + j) = 0} = cy N C C.gates.length := by
  have e : {j : ℕ | j < C.gates.length ∧ dP N C (N + N + j) = 0} =
      ↑((Finset.range C.gates.length).filter (fun j => dP N C (N + N + j) = 0)) := by
    ext j
    simp
  rw [e, Set.ncard_coe_finset]
  exact Finset.card_filter _ _

theorem E_ln (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    E N C x y w = y ⟨w - N, by omega⟩ := by
  show VV C (List.ofFn (Fin.append x y)) w = _
  rw [VV_in C (List.ofFn (Fin.append x y)) w (by rw [List.length_ofFn]; exact h2), app_getD,
    difn (by omega), difp (by omega)]

theorem has_inY (N : ℕ) (C : Circuit) (G : List Gate) (w : ℕ) (x0 : Fin N → Bool)
    (hw : w < N + N) (hd : dP N C w = 0) : Has N G (fun y => E N C x0 y w) := by
  have hwN : N ≤ w := by
    rw [dP_in N C w hw] at hd
    by_contra hc
    rw [ifp (by omega)] at hd
    omega
  refine ⟨w - N, by omega, fun y => ?_⟩
  show XV N G y (w - N) = E N C x0 y w
  rw [XV_in N G y (w - N) (by omega), E_ln N C x0 y w hwN hw]

theorem baseY (N : ℕ) (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C) :
    ∀ k, k ≤ C.gates.length → ∃ G, WFX N G ∧ G.length ≤ cy N C k ∧
      ∀ w, w < N + N + k → dP N C w = 0 → Has N G (fun y => E N C (fun _ => false) y w) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], ⟨by simp, ?_⟩, by simp, ?_⟩
    · intro j hj
      simp at hj
    · intro w hw hd
      exact has_inY N C [] w _ (by omega) hd
  | succ k ih =>
    intro hk
    obtain ⟨G, hW, hlen, hhas⟩ := ih (by omega)
    have hj : k < C.gates.length := by omega
    by_cases hd0 : dP N C (N + N + k) = 0
    · obtain ⟨a, b, hab | hab⟩ := gate_shape C hg k hj
      · have ha : a < N + N + k := hrb k hj a (by simp [hab])
        have hb : b < N + N + k := hrb k hj b (by simp [hab])
        have hdd : dP N C (N + N + k) = dP N C a + dP N C b :=
          D_and (N + N) (Finset.range N) C hrb k hj a b hab
        obtain ⟨G', h1, h2, h3, h4⟩ := has_and N G hW _ _ (hhas a ha (by omega))
          (hhas b hb (by omega))
        refine ⟨G', h1, ?_, ?_⟩
        · rw [cy_succ, ifp hd0]
          omega
        · intro w hw hd
          by_cases hwk : w = N + N + k
          · have e : (fun y => E N C (fun _ => false) y w) =
                (fun y => E N C (fun _ => false) y a && E N C (fun _ => false) y b) := by
              funext y
              rw [hwk]
              exact V_and (N + N) C hrb _ (by simp) k hj a b hab
            rw [e]
            exact h4
          · exact h3 _ (hhas w (by omega) hd)
      · have ha : a < N + N + k := hrb k hj a (by simp [hab])
        have hb : b < N + N + k := hrb k hj b (by simp [hab])
        have hdd : dP N C (N + N + k) = max (dP N C a) (dP N C b) :=
          D_or (N + N) (Finset.range N) C hrb k hj a b hab
        have l1 := le_max_left (dP N C a) (dP N C b)
        have l2 := le_max_right (dP N C a) (dP N C b)
        obtain ⟨G', h1, h2, h3, h4⟩ := has_or N G hW _ _ (hhas a ha (by omega))
          (hhas b hb (by omega))
        refine ⟨G', h1, ?_, ?_⟩
        · rw [cy_succ, ifp hd0]
          omega
        · intro w hw hd
          by_cases hwk : w = N + N + k
          · have e : (fun y => E N C (fun _ => false) y w) =
                (fun y => E N C (fun _ => false) y a || E N C (fun _ => false) y b) := by
              funext y
              rw [hwk]
              exact V_or (N + N) C hrb _ (by simp) k hj a b hab
            rw [e]
            exact h4
          · exact h3 _ (hhas w (by omega) hd)
    · refine ⟨G, hW, ?_, ?_⟩
      · rw [cy_succ, ifn hd0]
        omega
      · intro w hw hd
        have hwk : w ≠ N + N + k := by
          intro hc
          rw [hc] at hd
          exact hd0 hd
        exact hhas w (by omega) hd

abbrev mixed (N : ℕ) (C : Circuit) (i : ℕ) : Prop := 0 < dP N C i ∧ 0 < dL N C i

abbrev cone (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ mixed N C (N + N + j) ∧
    Relation.ReflTransGen (fun a b : ℕ => a < b ∧ ∃ f : Fin C.gates.length,
      b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs) (N + N + j) C.output

abbrev gok (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.or ∨ ∃ i ∈ (gateAt C j).inputs,
    dL N C i = 0 ∧ E N C x (fun _ => false) i = true

abbrev stp (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j3 j4 : ℕ) : Prop :=
  cone N C j4 ∧ N + N + j3 ∈ (gateAt C j4).inputs ∧ gok N C x j4

abbrev lvx (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  cone N C j ∧ gok N C x j ∧ ∃ j6 : ℕ, N + N + j6 = C.output ∧
    Relation.ReflTransGen (stp N C x) j j6

abbrev slot (N : ℕ) (C : Circuit) (h j : ℕ) : Prop :=
  cone N C j ∧ h ∈ (gateAt C j).inputs ∧ dP N C h = 0

abbrev ap (N : ℕ) (C : Circuit) (h : ℕ) (p : Fin N) : Prop :=
  ∃ j : ℕ, slot N C h j ∧ lvx N C (fun a : Fin N => decide (a = p)) j

abbrev lh (N : ℕ) (C : Circuit) (h : ℕ) (w : Fin N) : Prop :=
  E N C (fun _ => false) (fun a : Fin N => decide (a = w)) h = true

abbrev lpw (N : ℕ) (C : Circuit) (h : ℕ) (w : Fin N) : Prop :=
  ∀ w7 : Fin N, lh N C h w7 ↔ w7 = w

abbrev ppw (N : ℕ) (C : Circuit) (h : ℕ) (p : Fin N) : Prop :=
  (∃ w8 w9 : Fin N, w8 ≠ w9 ∧ lh N C h w8 ∧ lh N C h w9) ∧ ∀ p7 : Fin N, ap N C h p7 ↔ p7 = p

abbrev pps (N : ℕ) (C : Circuit) (p w : Fin N) : Prop :=
  ∃ h : ℕ, ppw N C h p ∧ lh N C h w

theorem climb (N : ℕ) (C : Circuit) (hF : F2 C) (x : Fin N → Bool) (j6 j : ℕ)
    (h : Relation.ReflTransGen (stp N C x) j j6) :
    cone N C j → gok N C x j →
    ((∀ x', gok N C x' j ∧ Relation.ReflTransGen (stp N C x') j j6) ∨
    ∃ j', cone N C j' ∧ (gateAt C j').op = GateOp.and ∧
      (gok N C x j' ∧ Relation.ReflTransGen (stp N C x) j' j6) ∧
      ∀ x', (gok N C x' j' ∧ Relation.ReflTransGen (stp N C x') j' j6) →
        (gok N C x' j ∧ Relation.ReflTransGen (stp N C x') j j6)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hc hg
    obtain ⟨a, b, hab | hab⟩ := gate_shape C hF j6 hc.1
    · right
      exact ⟨j6, hc, by rw [hab], ⟨hg, Relation.ReflTransGen.refl⟩, fun x' hx' => hx'⟩
    · left
      exact fun x' => ⟨Or.inl (by rw [hab]), Relation.ReflTransGen.refl⟩
  | @head a c h' hr ih =>
    intro hc hg
    obtain ⟨hcc, hmem, hgc⟩ := h'
    obtain ⟨u, v, hab | hab⟩ := gate_shape C hF a hc.1
    · right
      exact ⟨a, hc, by rw [hab],
        ⟨hg, Relation.ReflTransGen.head ⟨hcc, hmem, hgc⟩ hr⟩, fun x' hx' => hx'⟩
    · have hor : ∀ x', gok N C x' a := fun x' => Or.inl (by rw [hab])
      rcases ih hcc hgc with hl | ⟨j', hj'c, hj'a, hj'l, hj'i⟩
      · left
        exact fun x' => ⟨hor x', Relation.ReflTransGen.head ⟨hcc, hmem, (hl x').1⟩ (hl x').2⟩
      · right
        exact ⟨j', hj'c, hj'a, hj'l, fun x' hx' =>
          ⟨hor x', Relation.ReflTransGen.head ⟨hcc, hmem, (hj'i x' hx').1⟩ (hj'i x' hx').2⟩⟩

theorem partA (N : ℕ) (C : Circuit) (hF : F2 C) (p : Fin N) (h : ℕ) (hp : ppw N C h p) :
    ∃ j : ℕ, cone N C j ∧ (gateAt C j).op = GateOp.and ∧
      lvx N C (fun a : Fin N => decide (a = p)) j ∧
      ∀ p' : Fin N, lvx N C (fun a : Fin N => decide (a = p')) j → p' = p := by
  obtain ⟨⟨w8, w9, hne, _, _⟩, hap⟩ := hp
  obtain ⟨j, hsl, hc, hg, j6, hout, hpath⟩ := (hap p).2 rfl
  rcases climb N C hF _ j6 j hpath hc hg with hl | ⟨j', hj'c, hj'a, hj'l, hj'i⟩
  · exfalso
    have h1 : ∀ p' : Fin N, p' = p := fun p' =>
      (hap p').1 ⟨j, hsl, hc, (hl _).1, j6, hout, (hl _).2⟩
    exact hne ((h1 w8).trans (h1 w9).symm)
  · refine ⟨j', hj'c, hj'a, ⟨hj'c, hj'l.1, j6, hout, hj'l.2⟩, fun p' hp' => ?_⟩
    obtain ⟨_, hg', j6', hout', hpath'⟩ := hp'
    have e : j6' = j6 := by omega
    rw [e] at hpath'
    have h2 := hj'i _ ⟨hg', hpath'⟩
    exact (hap p').1 ⟨j, hsl, hc, h2.1, j6, hout, h2.2⟩

theorem cnt {α β : Type} (B : Set α) (hfin : B.Finite) (P : α → Prop) (g : α → β) (A2 : Set β)
    (hA2 : ∀ h ∈ A2, ∃ a ∈ B, g a = h ∧ ¬ P a) :
    Set.ncard {a | a ∈ B ∧ P a} + Set.ncard A2 ≤ Set.ncard B := by
  have hB1 : ({a | a ∈ B ∧ P a} : Set α).Finite := hfin.subset (fun a ha => ha.1)
  have hB2 : ({a | a ∈ B ∧ ¬ P a} : Set α).Finite := hfin.subset (fun a ha => ha.1)
  have h1 : Set.ncard A2 ≤ Set.ncard {a | a ∈ B ∧ ¬ P a} := by
    refine le_trans (Set.ncard_le_ncard (t := g '' {a | a ∈ B ∧ ¬ P a}) ?_ (hB2.image g))
      (Set.ncard_image_le hB2)
    intro h hh
    obtain ⟨a, ha, hga, hna⟩ := hA2 h hh
    exact ⟨a, ⟨ha, hna⟩, hga⟩
  have h2 : Set.ncard ({a | a ∈ B ∧ P a} ∪ {a | a ∈ B ∧ ¬ P a}) =
      Set.ncard {a | a ∈ B ∧ P a} + Set.ncard {a | a ∈ B ∧ ¬ P a} := by
    refine Set.ncard_union_eq ?_ hB1 hB2
    rw [Set.disjoint_left]
    intro a ha hb
    exact hb.2 ha.2
  have h3 : Set.ncard ({a | a ∈ B ∧ P a} ∪ {a | a ∈ B ∧ ¬ P a}) ≤ Set.ncard B :=
    Set.ncard_le_ncard (fun a ha => by
      rcases ha with h | h
      · exact h.1
      · exact h.1) hfin
  omega

theorem partC (N : ℕ) (C : Circuit) (hF : F2 C) :
    Set.ncard {js : ℕ × ℕ | cone N C js.1 ∧ js.2 < 2 ∧
        dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0 ∧
        ∃ w : Fin N, lpw N C ((gateAt C js.1).inputs.getD js.2 0) w} +
      Set.ncard {h : ℕ | ∃ p : Fin N, ppw N C h p} ≤
    Set.ncard {js : ℕ × ℕ | cone N C js.1 ∧ js.2 < 2 ∧
        dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0} := by
  have hfin : ({js : ℕ × ℕ | cone N C js.1 ∧ js.2 < 2 ∧
      dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0} : Set (ℕ × ℕ)).Finite := by
    refine (Finset.finite_toSet ((Finset.range C.gates.length) ×ˢ (Finset.range 2))).subset ?_
    intro js hjs
    obtain ⟨hc, h2, _⟩ := hjs
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨hc.1, h2⟩
  have e : {js : ℕ × ℕ | cone N C js.1 ∧ js.2 < 2 ∧
        dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0 ∧
        ∃ w : Fin N, lpw N C ((gateAt C js.1).inputs.getD js.2 0) w} =
      {a | a ∈ {js : ℕ × ℕ | cone N C js.1 ∧ js.2 < 2 ∧
        dP N C ((gateAt C js.1).inputs.getD js.2 0) = 0} ∧
        ∃ w : Fin N, lpw N C ((gateAt C a.1).inputs.getD a.2 0) w} := by
    ext js
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩, fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [e]
  refine cnt _ hfin (fun a => ∃ w : Fin N, lpw N C ((gateAt C a.1).inputs.getD a.2 0) w)
    (fun a => (gateAt C a.1).inputs.getD a.2 0) _ ?_
  intro h hh
  obtain ⟨p, hp⟩ := hh
  obtain ⟨⟨w8, w9, hne, h8, h9⟩, hap⟩ := hp
  obtain ⟨j, ⟨hc, hmem, hd⟩, _⟩ := (hap p).2 rfl
  have hs : ∃ s, s < 2 ∧ (gateAt C j).inputs.getD s 0 = h := by
    obtain ⟨a, b, hab | hab⟩ := gate_shape C hF j hc.1
    · rw [hab] at hmem ⊢
      have hm : h = a ∨ h = b := by simpa using hmem
      rcases hm with e1 | e1
      · exact ⟨0, by omega, e1.symm⟩
      · exact ⟨1, by omega, e1.symm⟩
    · rw [hab] at hmem ⊢
      have hm : h = a ∨ h = b := by simpa using hmem
      rcases hm with e1 | e1
      · exact ⟨0, by omega, e1.symm⟩
      · exact ⟨1, by omega, e1.symm⟩
  obtain ⟨s, hs1, hs2⟩ := hs
  refine ⟨(j, s), ⟨hc, hs1, ?_⟩, hs2, ?_⟩
  · show dP N C ((gateAt C j).inputs.getD s 0) = 0
    rw [hs2]
    exact hd
  · rintro ⟨w, hw⟩
    have hw' : lpw N C ((gateAt C j).inputs.getD s 0) w := hw
    rw [hs2] at hw'
    exact hne (((hw' w8).1 h8).trans ((hw' w9).1 h9).symm)

theorem partB (H1 : RSB) (N k : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hF : F2 C) (hrb : ReadsBack (N + N) C)
    (h4 : ∀ p p' w w' : Fin N, p ≠ p' → w ≠ w' → I p w → I p' w → I p w' → I p' w' → False)
    (hrej : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ k →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) →
      circuitFun (N + N) C (Fin.append x y) = false)
    (L2 : ∀ (x y : Fin N → Bool) (h j : ℕ), slot N C h j → lvx N C x j →
      E N C (fun _ => false) y h = true → circuitFun (N + N) C (Fin.append x y) = true)
    (L5 : ∀ (h : ℕ) (p w : Fin N), ap N C h p → lh N C h w → I p w) :
    ∑ p : Fin N, min (k + 1) (Set.ncard {w : Fin N | pps N C p w}) ≤
      Set.ncard {j : ℕ | j < C.gates.length ∧ dP N C (N + N + j) = 0} +
        Set.ncard {h : ℕ | ∃ p : Fin N, ppw N C h p} := by
  classical
  obtain ⟨G, hW, hlen, hhas⟩ := baseY N C hF hrb C.gates.length le_rfl
  have hhas' : ∀ w, w < N + N + C.gates.length → dP N C w = 0 →
      ∃ i, i < N + G.length ∧ ∀ y : Fin N → Bool, XV N G y i = E N C (fun _ => false) y w := hhas
  choose! φ hφ1 hφ2 using hhas'
  have hlt : ∀ h p, ppw N C h p → h < N + N + C.gates.length := by
    intro h p hp
    obtain ⟨⟨w8, _, _, h8, _⟩, _⟩ := hp
    by_contra hc
    have hv : E N C (fun _ => false) (fun a : Fin N => decide (a = w8)) h = false :=
      VV_out C _ h (by rw [List.length_ofFn]; omega)
    exact Bool.false_ne_true (hv.symm.trans h8)
  have happ : ∀ h p, ppw N C h p → ap N C h p := fun h p hp => (hp.2 p).2 rfl
  have hdp : ∀ h p, ppw N C h p → dP N C h = 0 := by
    intro h p hp
    obtain ⟨j, ⟨_, _, hd⟩, _⟩ := happ h p hp
    exact hd
  have huniq : ∀ h p p', ppw N C h p → ppw N C h p' → p = p' :=
    fun h p p' hp hp' => (hp'.2 p).1 (happ h p hp)
  have hval : ∀ h p, ppw N C h p → ∀ y : Fin N → Bool,
      VV ⟨G, 0⟩ (List.ofFn y) (φ h) = E N C (fun _ => false) y h :=
    fun h p hp y => hφ2 h (hlt h p hp) (hdp h p hp) y
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin N), ∀ p, p ∈ T ↔ ∃ h, ppw N C h p :=
    ⟨Finset.univ.filter (fun p => ∃ h, ppw N C h p), fun p =>
      Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin N → Finset (Fin N), ∀ p w, w ∈ U p ↔ I p w :=
    ⟨fun p => Finset.univ.filter (fun w => I p w), fun p w =>
      Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩⟩
  obtain ⟨S, hS⟩ : ∃ S : Fin N → Finset (Fin N), ∀ p w, w ∈ S p ↔ pps N C p w :=
    ⟨fun p => Finset.univ.filter (fun w => pps N C p w), fun p w =>
      Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩⟩
  obtain ⟨Hp, hHp⟩ : ∃ Hp : Fin N → Finset ℕ, ∀ p h, h ∈ Hp p ↔ ppw N C h p :=
    ⟨fun p => (Finset.range (N + N + C.gates.length)).filter (fun h => ppw N C h p), fun p h =>
      Finset.mem_filter.trans ⟨fun hh => hh.2, fun hh =>
        ⟨Finset.mem_range.mpr (hlt h p hh), hh⟩⟩⟩
  have hf' : ∀ p ∈ T, ∀ i ∈ (Hp p).image φ, i < N + (⟨G, 0⟩ : Circuit).gates.length := by
    intro p _ i hi
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    have hp := (hHp p h).1 hh
    exact hφ1 h (hlt h p hp) (hdp h p hp)
  have hU' : ∀ p ∈ T, ∀ p' ∈ T, p ≠ p' → (U p ∩ U p').card ≤ 1 := by
    intro p _ p' _ hne
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rw [Finset.mem_inter, hU, hU] at ha hb
    exact h4 p p' a b hne hab ha.1 ha.2 hb.1 hb.2
  have hS' : ∀ p ∈ T, S p ⊆ U p := by
    intro p _ w hw
    rw [hS] at hw
    rw [hU]
    obtain ⟨h, hp, hl⟩ := hw
    exact L5 h p w (happ h p hp) hl
  have h2' : ∀ p ∈ T, 2 ≤ (S p).card := by
    intro p hp
    obtain ⟨h, hh⟩ := (hT p).1 hp
    obtain ⟨w8, w9, hne, h8, h9⟩ := hh.1
    exact Finset.one_lt_card.2 ⟨w8, (hS p w8).2 ⟨h, hh, h8⟩, w9, (hS p w9).2 ⟨h, hh, h9⟩, hne⟩
  have hsing' : ∀ p ∈ T, ∀ w : Fin N, (w ∈ S p ↔ ∃ i ∈ (Hp p).image φ,
      VV ⟨G, 0⟩ (List.ofFn (fun a : Fin N => decide (a = w))) i = true) := by
    intro p _ w
    rw [hS]
    constructor
    · rintro ⟨h, hp, hl⟩
      exact ⟨φ h, Finset.mem_image.mpr ⟨h, (hHp p h).2 hp, rfl⟩, (hval h p hp _).trans hl⟩
    · rintro ⟨i, hi, hv⟩
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
      have hp := (hHp p h).1 hh
      exact ⟨h, hp, (hval h p hp _).symm.trans hv⟩
  have hzero' : ∀ p ∈ T, ∀ i ∈ (Hp p).image φ, ∀ y : Fin N → Bool,
      (Finset.univ.filter (fun b : Fin N => y b = true)).card ≤ k →
      (∀ b ∈ U p, y b = false) → VV ⟨G, 0⟩ (List.ofFn y) i = false := by
    intro p _ i hi y hy hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    have hp := (hHp p h).1 hh
    refine (hval h p hp y).trans ?_
    by_contra hne
    have ht : E N C (fun _ => false) y h = true := (Bool.not_eq_false _).mp hne
    obtain ⟨j, hsl, hlv⟩ := happ h p hp
    have hacc := L2 (fun a : Fin N => decide (a = p)) y h j hsl hlv ht
    have hr := hrej (fun a : Fin N => decide (a = p)) y hy (by
      rintro ⟨p', w, hI, hx, hyw⟩
      have e : p' = p := by simpa using hx
      rw [e] at hI
      rw [hz w ((hU p w).2 hI)] at hyw
      exact Bool.false_ne_true hyw)
    exact Bool.false_ne_true (hr.symm.trans hacc)
  have hck' : ∀ p ∈ T, min k ((S p).card - 1) ≤ k := fun p _ => min_le_left _ _
  have hcS' : ∀ p ∈ T, min k ((S p).card - 1) + 1 ≤ (S p).card := by
    intro p hp
    have a1 := h2' p hp
    have a2 := min_le_right k ((S p).card - 1)
    omega
  have key : ∑ p ∈ T, min k ((S p).card - 1) + T.card ≤
      G.length + ∑ p ∈ T, ((Hp p).image φ).card :=
    rsb_or H1 T N k U S ⟨G, 0⟩ (fun p => (Hp p).image φ) (fun p => min k ((S p).card - 1))
      hW.1 hW.2 hf' hU' hS' h2' hsing' hzero' hck' hcS'
  have e1 : ∀ p, Set.ncard {w : Fin N | pps N C p w} = (S p).card := by
    intro p
    rw [← Set.ncard_coe_finset]
    congr 1
    ext w
    rw [Set.mem_ofPred_eq, Finset.mem_coe, hS]
  have hS0 : ∀ p, p ∉ T → (S p).card = 0 := by
    intro p hp
    by_contra hne
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    obtain ⟨h, hh, _⟩ := (hS p w).1 hw
    exact hp ((hT p).2 ⟨h, hh⟩)
  have a1 : ∑ p ∈ T, min (k + 1) ((S p).card) = ∑ p : Fin N, min (k + 1) ((S p).card) :=
    Finset.sum_subset (Finset.subset_univ T) (fun p _ hp => by
      rw [hS0 p hp]
      exact Nat.min_zero _)
  have a2 : ∑ p : Fin N, min (k + 1) (Set.ncard {w : Fin N | pps N C p w}) =
      ∑ p : Fin N, min (k + 1) ((S p).card) :=
    Finset.sum_congr rfl (fun p _ => by rw [e1 p])
  have a3 : ∑ p ∈ T, min (k + 1) ((S p).card) = ∑ p ∈ T, (min k ((S p).card - 1) + 1) :=
    Finset.sum_congr rfl (fun p hp => by
      have a0 := h2' p hp
      rcases le_total k ((S p).card - 1) with hle | hle
      · rw [min_eq_left hle, min_eq_left (show k + 1 ≤ (S p).card by omega)]
      · rw [min_eq_right hle, min_eq_right (show (S p).card ≤ k + 1 by omega)]
        omega)
  have a4 : ∑ p ∈ T, (min k ((S p).card - 1) + 1) =
      ∑ p ∈ T, min k ((S p).card - 1) + T.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have b1 : ∑ p ∈ T, ((Hp p).image φ).card ≤ ∑ p ∈ T, (Hp p).card :=
    Finset.sum_le_sum (fun p _ => Finset.card_image_le)
  have b2 : (T.biUnion Hp).card = ∑ p ∈ T, (Hp p).card := by
    refine Finset.card_biUnion ?_
    intro p _ p' _ hne
    show Disjoint (Hp p) (Hp p')
    rw [Finset.disjoint_left]
    intro h hh hh'
    exact hne (huniq h p p' ((hHp p h).1 hh) ((hHp p' h).1 hh'))
  have hfin : ({h : ℕ | ∃ p : Fin N, ppw N C h p} : Set ℕ).Finite := by
    refine (Finset.finite_toSet (Finset.range (N + N + C.gates.length))).subset ?_
    intro h hh
    obtain ⟨p, hp⟩ := hh
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hlt h p hp))
  have b3 : (T.biUnion Hp).card ≤ Set.ncard {h : ℕ | ∃ p : Fin N, ppw N C h p} := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard (fun h hh => ?_) hfin
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hh)
    exact ⟨p, (hHp p h).1 hp⟩
  have b4 := ncy N C
  rw [a2, ← a1, a3, a4, b4]
  exact le_trans key (Nat.add_le_add hlen (le_trans b1 (le_trans (le_of_eq b2.symm) b3)))

end PEqualNP.Outside.L_meta_1953

theorem PEqualNP.Outside.L_meta_1953 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → ∀ (N250 k250 : ℕ) (I250 : Fin N250 → Fin N250 → Prop) [DecidableRel I250] (C250 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g250 ∈ C250.gates, (g250.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g250.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g250.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N250 + N250) C250) → (∀ j250 < C250.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250 0 = 0) ∨ (∀ h250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250 0 = 0)) → (∀ p250 p250x1 w250 w250x1 : Fin N250, p250 ≠ p250x1 → w250 ≠ w250x1 → I250 p250 w250 → I250 p250x1 w250 → I250 p250 w250x1 → I250 p250x1 w250x1 → False) → (∃ p250x2 w250x2 : Fin N250, I250 p250x2 w250x2) → 1 ≤ k250 → (∀ p250x3 w250x3 : Fin N250, I250 p250x3 w250x3 → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append (fun a250 : Fin N250 => decide (a250 = p250x3)) (fun a250x1 : Fin N250 => decide (a250x1 = w250x3))) = true) → (∀ x250 y250 : Fin N250 → Bool, (Finset.univ.filter (fun l250 : Fin N250 => y250 l250 = true)).card ≤ k250 → (¬ ∃ p250x4 w250x4 : Fin N250, I250 p250x4 w250x4 ∧ x250 p250x4 = true ∧ y250 w250x4 = true) → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append x250 y250) = false) → ∀ mixed250 : ℕ → Prop, mixed250 = (fun i250x1 : ℕ => 0 < (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD i250x1 0 ∧ 0 < (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250x1 0) → ∀ cone250 : ℕ → Prop, cone250 = (fun j250x1 : ℕ => j250x1 < C250.gates.length ∧ mixed250 (N250 + N250 + j250x1) ∧ Relation.ReflTransGen (fun a250x2 b250 : ℕ => a250x2 < b250 ∧ ∃ f250 : Fin C250.gates.length, b250 = N250 + N250 + f250.val ∧ a250x2 ∈ (C250.gates.get f250).inputs) (N250 + N250 + j250x1) C250.output) → ∀ gok250 : (Fin N250 → Bool) → ℕ → Prop, gok250 = (fun (x250x1 : Fin N250 → Bool) (j250x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i250x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250x2 0 = 0 ∧ (C250.wires (List.ofFn (Fin.append x250x1 (fun u250 : Fin N250 => false)))).getD i250x2 false = true) → ∀ step250 : (Fin N250 → Bool) → ℕ → ℕ → Prop, step250 = (fun (x250x2 : Fin N250 → Bool) (j250x3 j250x4 : ℕ) => cone250 j250x4 ∧ N250 + N250 + j250x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x4).inputs ∧ gok250 x250x2 j250x4) → ∀ lvx250 : (Fin N250 → Bool) → ℕ → Prop, lvx250 = (fun (x250x3 : Fin N250 → Bool) (j250x5 : ℕ) => cone250 j250x5 ∧ gok250 x250x3 j250x5 ∧ ∃ j250x6 : ℕ, N250 + N250 + j250x6 = C250.output ∧ Relation.ReflTransGen (step250 x250x3) j250x5 j250x6) → ∀ slot250 : ℕ → ℕ → Prop, slot250 = (fun h250x1 j250x7 : ℕ => cone250 j250x7 ∧ h250x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x7).inputs ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250x1 0 = 0) → ∀ ap250 : ℕ → Fin N250 → Prop, ap250 = (fun (h250x2 : ℕ) (p250x5 : Fin N250) => ∃ j250x8 : ℕ, slot250 h250x2 j250x8 ∧ lvx250 (fun a250x3 : Fin N250 => decide (a250x3 = p250x5)) j250x8) → ∀ lh250 : ℕ → Fin N250 → Prop, lh250 = (fun (h250x3 : ℕ) (w250x5 : Fin N250) => (C250.wires (List.ofFn (Fin.append (fun u250x1 : Fin N250 => false) (fun a250x4 : Fin N250 => decide (a250x4 = w250x5))))).getD h250x3 false = true) → ∀ lpw250 : ℕ → Fin N250 → Prop, lpw250 = (fun (h250x4 : ℕ) (w250x6 : Fin N250) => ∀ w250x7 : Fin N250, lh250 h250x4 w250x7 ↔ w250x7 = w250x6) → ∀ ppw250 : ℕ → Fin N250 → Prop, ppw250 = (fun (h250x5 : ℕ) (p250x6 : Fin N250) => (∃ w250x8 w250x9 : Fin N250, w250x8 ≠ w250x9 ∧ lh250 h250x5 w250x8 ∧ lh250 h250x5 w250x9) ∧ ∀ p250x7 : Fin N250, ap250 h250x5 p250x7 ↔ p250x7 = p250x6) → ∀ pps250 : Fin N250 → Fin N250 → Prop, pps250 = (fun p250x8 w250x10 : Fin N250 => ∃ h250x6 : ℕ, ppw250 h250x6 p250x8 ∧ lh250 h250x6 w250x10) → (∀ (p250x9 : Fin N250) (h250x7 : ℕ), ppw250 h250x7 p250x9 → ∃ j250x9 : ℕ, cone250 j250x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ lvx250 (fun a250x5 : Fin N250 => decide (a250x5 = p250x9)) j250x9 ∧ ∀ p250x10 : Fin N250, lvx250 (fun a250x6 : Fin N250 => decide (a250x6 = p250x10)) j250x9 → p250x10 = p250x9) ∧ ∑ p250x11 : Fin N250, min (k250 + 1) (Set.ncard {w250x11 : Fin N250 | pps250 p250x11 w250x11}) ≤ Set.ncard {j250x10 : ℕ | j250x10 < C250.gates.length ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD (N250 + N250 + j250x10) 0 = 0} + Set.ncard {h250x8 : ℕ | ∃ p250x12 : Fin N250, ppw250 h250x8 p250x12} ∧ Set.ncard {js250 : ℕ × ℕ | cone250 js250.1 ∧ js250.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) 0 = 0 ∧ ∃ w250x12 : Fin N250, lpw250 ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) w250x12} + Set.ncard {h250x9 : ℕ | ∃ p250x13 : Fin N250, ppw250 h250x9 p250x13} ≤ Set.ncard {js250x1 : ℕ × ℕ | cone250 js250x1.1 ∧ js250x1.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250x1.1).inputs.getD js250x1.2 0) 0 = 0} := by
  intro H1 HL N k I _ C hC hkm h4 hedge hk hacc hrej mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw pps hpps
  subst hmixed hcone hgok hstep hlvx hslot hap hlh hlpw hppw hpps
  obtain ⟨-, L2, -, -, L5, -⟩ := HL N I C hC hkm h4 hedge hacc
    (fun x y hy hne => hrej x y (le_trans hy hk) hne)
    _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  exact ⟨fun p h hp => PEqualNP.Outside.L_meta_1953.partA N C hC.1 p h hp,
    PEqualNP.Outside.L_meta_1953.partB H1 N k I C hC.1 hC.2 h4 hrej L2 L5,
    PEqualNP.Outside.L_meta_1953.partC N C hC.1⟩
