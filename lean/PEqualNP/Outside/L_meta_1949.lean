import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1949

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


theorem ble (a b : Bool) (h : a ≤ b) (ha : a = true) : b = true := by
  subst ha
  revert h
  cases b <;> decide

theorem mono_of {α : Type} [Preorder α] (f : α → Bool)
    (h : ∀ a b, a ≤ b → f a = true → f b = true) : Monotone f := by
  intro a b hab
  cases ha : f a
  · exact Bool.false_le _
  · rw [h a b hab ha]

theorem of_mono {α : Type} [Preorder α] (f : α → Bool) (h : Monotone f) (a b : α) (hab : a ≤ b)
    (ha : f a = true) : f b = true := ble _ _ (h hab) ha

def V (C : Circuit) (X : List Bool) (w : ℕ) : Bool := (C.wires X).getD w false

def D (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) : ℕ := (C.lineDegrees K M).getD w 0

theorem wires_fd (C : Circuit) (X : List Bool) : C.wires X = fd stpF X C.gates := rfl

theorem V_in (C : Circuit) (X : List Bool) (w : ℕ) (hw : w < X.length) :
    V C X w = X.getD w false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, fd_pre _ _ _ _ hw]

theorem V_out (C : Circuit) (X : List Bool) (w : ℕ) (hw : X.length + C.gates.length ≤ w) :
    V C X w = false := by
  unfold V
  rw [wires_fd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    rw [fd_len]; exact hw)]
  rfl

theorem V_gate (K : ℕ) (C : Circuit) (hrb : ReadsBack K C) (X : List Bool) (hX : X.length = K)
    (j : ℕ) (hj : j < C.gates.length) :
    V C X (K + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (V C X)) := by
  have h := fd_gate stpF false stpF_congr C.gates X j hj (by
    intro i hi
    have := hrb j hj i hi
    rw [hX]
    exact this)
  rw [hX] at h
  exact h

theorem D_len (K : ℕ) (M : Finset ℕ) (C : Circuit) :
    (C.lineDegrees K M).length = K + C.gates.length := by
  have := fd_len Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0)
  simpa [fd, Circuit.lineDegrees] using this

theorem D_in (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : w < K) :
    D K M C w = if w ∈ M then 1 else 0 := by
  unfold D Circuit.lineDegrees
  have := fd_pre Gate.lineDegree C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) w
    (by simpa using hw)
  unfold fd at this
  rw [List.getD_eq_getElem?_getD, this]
  simp [hw]

theorem D_out (K : ℕ) (M : Finset ℕ) (C : Circuit) (w : ℕ) (hw : K + C.gates.length ≤ w) :
    D K M C w = 0 := by
  unfold D
  have hl := D_len K M C
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem foldr_max_zero : ∀ (l : List ℕ), l.foldr max 0 = 0 ↔ ∀ a ∈ l, a = 0 := by
  intro l
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    omega

theorem D_zero_iff (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (j : ℕ)
    (hj : j < C.gates.length) :
    D K M C (K + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, D K M C i = 0 := by
  have h := fd_gate Gate.lineDegree 0 ld_congr C.gates
    ((List.range K).map fun i => if i ∈ M then 1 else 0) j hj (by
    intro i hi
    have := hrb j hj i hi
    simpa using this)
  simp only [List.length_map, List.length_range] at h
  have h' : D K M C (K + j) = (gateAt C j).lineDegree (C.lineDegrees K M) := h
  rw [h']
  unfold Gate.lineDegree
  split_ifs
  · rw [List.sum_eq_zero_iff]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl
  · rw [foldr_max_zero]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    rfl

theorem indep (K : ℕ) (M : Finset ℕ) (C : Circuit) (hrb : ReadsBack K C) (X X' : List Bool)
    (hX : X.length = K) (hX' : X'.length = K)
    (h : ∀ i, i < K → i ∉ M → X.getD i false = X'.getD i false) :
    ∀ w, D K M C w = 0 → V C X w = V C X' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    by_cases h1 : w < K
    · rw [D_in K M C w h1] at hd
      have hwn : w ∉ M := by
        intro hc
        rw [ifp hc] at hd
        omega
      rw [V_in _ _ _ (by omega), V_in _ _ _ (by omega)]
      exact h w h1 hwn
    · by_cases h2 : w < K + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = K + j := ⟨w - K, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [V_gate K C hrb X hX j hj, V_gate K C hrb X' hX' j hj]
        congr 1
        apply List.map_congr_left
        intro i hi
        have := hrb j hj i hi
        exact ih i (by omega) ((D_zero_iff K M C hrb j hj).mp hd i hi)
      · rw [V_out _ _ _ (by omega), V_out _ _ _ (by omega)]

theorem V_mono (C : Circuit) (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (X X' : List Bool) (hl : X.length = X'.length)
    (h : ∀ i, X.getD i false = true → X'.getD i false = true) (w : ℕ)
    (hw : V C X w = true) : V C X' w = true := by
  unfold V at hw ⊢
  rw [wires_fd] at hw ⊢
  exact mono C.gates _ _ hl hm h w hw

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

theorem V_false (K : ℕ) (C : Circuit) (hrb : ReadsBack K C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (X : List Bool) (hX : X.length = K) (h0 : ∀ i, X.getD i false = false) :
    ∀ w, V C X w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < K
    · rw [V_in _ _ _ (by omega)]
      exact h0 w
    · by_cases hlt : w < K + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = K + j := ⟨w - K, by omega⟩
        have hj : j < C.gates.length := by omega
        have hg := h2 _ (gateAt_mem C j hj)
        have hne : ∃ a, a ∈ (gateAt C j).inputs := by
          rcases hin : (gateAt C j).inputs with _ | ⟨a, t⟩
          · rw [hin] at hg
            simp at hg
          · exact ⟨a, by simp⟩
        obtain ⟨a, ha⟩ := hne
        by_contra hc
        have hc' : V C X (K + j) = true := by simpa using hc
        rw [V_gate K C hrb X hX j hj] at hc'
        rcases hg.1 with hop | hop
        · rw [ev_and _ _ hop] at hc'
          have h3 := hc' a ha
          rw [ih a (by have := hrb j hj a ha; omega)] at h3
          cases h3
        · rw [ev_or _ _ hop] at hc'
          obtain ⟨i, hi, h3⟩ := hc'
          rw [ih i (by have := hrb j hj i hi; omega)] at h3
          cases h3
      · exact V_out _ _ _ (by omega)

def W (N : ℕ) (C : Circuit) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn (Fin.append x y))).getD w false

def DL (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

def DP (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

theorem W_indL (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x y y' : Fin N → Bool) (w : ℕ)
    (h : DL N C w = 0) : W N C x y w = W N C x y' w := by
  refine indep (N + N) (Finset.Ico N (N + N)) C hrb _ _ (by simp) (by simp) ?_ w h
  intro i hi hni
  have hlt : i < N := by
    by_contra hc
    exact hni (Finset.mem_Ico.mpr ⟨by omega, hi⟩)
  rw [app_getD, app_getD, difp hlt, difp hlt]

theorem W_indP (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x x' y : Fin N → Bool) (w : ℕ)
    (h : DP N C w = 0) : W N C x y w = W N C x' y w := by
  refine indep (N + N) (Finset.range N) C hrb _ _ (by simp) (by simp) ?_ w h
  intro i hi hni
  have hlt : ¬ i < N := by
    intro hc
    exact hni (Finset.mem_range.mpr hc)
  rw [app_getD, app_getD, difn hlt, difn hlt]

theorem W_zero (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) (w : ℕ) :
    W N C (fun _ => false) (fun _ => false) w = false := by
  refine V_false (N + N) C hrb h2 _ (by simp) ?_ w
  intro i
  rw [app_getD]
  split_ifs <;> rfl

theorem W_monoX (N : ℕ) (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x x' y : Fin N → Bool) (hx : x ≤ x') (w : ℕ) (h : W N C x y w = true) :
    W N C x' y w = true := by
  refine V_mono C (fun g hg => (h2 g hg).1) _ _ (by simp) ?_ w h
  intro i
  rw [app_getD, app_getD]
  split_ifs with ha hb
  · exact ble _ _ (hx ⟨i, ha⟩)
  · exact id
  · exact id

theorem W_gate (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (x y : Fin N → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    W N C x y (N + N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W N C x y)) :=
  V_gate (N + N) C hrb _ (by simp) j hj


theorem V_true (K : ℕ) (C : Circuit) (hrb : ReadsBack K C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (X : List Bool) (hX : X.length = K) (h1 : ∀ i, i < K → X.getD i false = true) :
    ∀ w, w < K + C.gates.length → V C X w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hK : w < K
    · rw [V_in _ _ _ (by omega)]
      exact h1 w hK
    · obtain ⟨j, rfl⟩ : ∃ j, w = K + j := ⟨w - K, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := h2 _ (gateAt_mem C j hj)
      rw [V_gate K C hrb X hX j hj]
      rcases hg.1 with hop | hop
      · rw [ev_and _ _ hop]
        intro i hi
        have := hrb j hj i hi
        exact ih i (by omega) (by omega)
      · rw [ev_or _ _ hop]
        rcases hin : (gateAt C j).inputs with _ | ⟨a, t⟩
        · rw [hin] at hg
          simp at hg
        · have ha : a ∈ (gateAt C j).inputs := by rw [hin]; simp
          have := hrb j hj a ha
          exact ⟨a, by simp, ih a (by omega) (by omega)⟩

theorem W_one (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (hw : w < N + N + C.gates.length) (hl : DL N C w = 0) :
    W N C (fun _ => true) (fun _ => false) w = true := by
  rw [W_indL N C hrb (fun _ => true) (fun _ => false) (fun _ => true) w hl]
  refine V_true (N + N) C hrb h2 _ (by simp) ?_ w hw
  intro i hi
  rw [app_getD]
  split_ifs <;> first | rfl | omega

theorem DP_eq (N : ℕ) (C : Circuit) (w : ℕ) : DP N C w = D (N + N) (Finset.range N) C w := rfl
theorem DL_eq (N : ℕ) (C : Circuit) (w : ℕ) :
    DL N C w = D (N + N) (Finset.Ico N (N + N)) C w := rfl

theorem DP_zero (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hj : j < C.gates.length) :
    DP N C (N + N + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, DP N C i = 0 :=
  D_zero_iff (N + N) (Finset.range N) C hrb j hj

theorem DL_zero (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hj : j < C.gates.length) :
    DL N C (N + N + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, DL N C i = 0 :=
  D_zero_iff (N + N) (Finset.Ico N (N + N)) C hrb j hj

theorem NZ (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, w < N + N + C.gates.length → 0 < DP N C w ∨ 0 < DL N C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · left
      rw [DP_eq, D_in _ _ _ _ (by omega), if_pos (Finset.mem_range.mpr h1)]
      omega
    · by_cases h3 : w < N + N
      · right
        rw [DL_eq, D_in _ _ _ _ h3, if_pos (Finset.mem_Ico.mpr ⟨by omega, h3⟩)]
        omega
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < C.gates.length := by omega
        have hg := h2 _ (gateAt_mem C j hj)
        rcases hin : (gateAt C j).inputs with _ | ⟨a, t⟩
        · rw [hin] at hg
          simp at hg
        · have ha : a ∈ (gateAt C j).inputs := by rw [hin]; simp
          have := hrb j hj a ha
          by_contra hc
          have hP : DP N C (N + N + j) = 0 := by omega
          have hL : DL N C (N + N + j) = 0 := by omega
          rw [DP_zero N C hrb j hj] at hP
          rw [DL_zero N C hrb j hj] at hL
          rcases ih a (by omega) (by omega) with h | h
          · rw [hP a ha] at h; omega
          · rw [hL a ha] at h; omega

theorem two_ne (l : List ℕ) (hl : l.length = 2) (a b c : ℕ) (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  match l, hl with
  | [p, q], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb hc
    omega

theorem two_eq (l : List ℕ) (hl : l.length = 2) : ∃ p q, l = [p, q] := by
  match l, hl with
  | [p, q], _ => exact ⟨p, q, rfl⟩

def Mx (N : ℕ) (C : Circuit) (i : ℕ) : Prop := 0 < DP N C i ∧ 0 < DL N C i

def Rl (N : ℕ) (C : Circuit) : ℕ → ℕ → Prop := fun a b =>
  a < b ∧ ∃ f : Fin C.gates.length, b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs

def Cn (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ Mx N C (N + N + j) ∧ Relation.ReflTransGen (Rl N C) (N + N + j) C.output

theorem get_eq (C : Circuit) (f : Fin C.gates.length) : C.gates.get f = gateAt C f.val := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ f.isLt]
  rfl

theorem mx_up (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (j : ℕ)
    (hj : j < C.gates.length) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (hm : Mx N C a) :
    Mx N C (N + N + j) := by
  constructor
  · by_contra hc
    have h0 : DP N C (N + N + j) = 0 := by omega
    rw [DP_zero N C hrb j hj] at h0
    have := hm.1
    rw [h0 a ha] at this
    omega
  · by_contra hc
    have h0 : DL N C (N + N + j) = 0 := by omega
    rw [DL_zero N C hrb j hj] at h0
    have := hm.2
    rw [h0 a ha] at this
    omega

theorem up (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (a b : ℕ) (hab : Relation.ReflTransGen (Rl N C) a b) (hm : Mx N C a)
    (ht : W N C (fun _ => true) (fun _ => false) a = true) :
    Mx N C b ∧ W N C (fun _ => true) (fun _ => false) b = true := by
  induction hab with
  | refl => exact ⟨hm, ht⟩
  | @tail b c _ hbc ih =>
    obtain ⟨hmb, htb⟩ := ih
    obtain ⟨_, f, rfl, hbin⟩ := hbc
    rw [get_eq] at hbin
    have hf := f.isLt
    have hmc := mx_up N C hrb f.val hf b hbin hmb
    refine ⟨hmc, ?_⟩
    rw [W_gate N C hrb _ _ f.val hf]
    have hg := h2 _ (gateAt_mem C f.val hf)
    rcases hg.1 with hop | hop
    · rw [ev_and _ _ hop]
      intro u hu
      have hur := hrb f.val hf u hu
      by_cases hlu : DL N C u = 0
      · exact W_one N C hrb h2 u (by omega) hlu
      · rcases hkm f.val hf hop with ⟨i, hi, hli⟩ | hall
        · by_cases hub : u = b
          · rw [hub]; exact htb
          · exfalso
            exact two_ne _ hg.2 u b i hu hbin hi hub (by intro h; rw [h] at hlu; exact hlu hli)
              (by intro h; rw [h] at hmb; have := hmb.2; omega)
        · have := hmb.1
          rw [hall b hbin] at this
          omega
    · rw [ev_or _ _ hop]
      exact ⟨b, hbin, htb⟩

theorem or_lf (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (hf : circuitFun (N + N) C (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false)) = false)
    (j : ℕ) (hc : Cn N C j) (hop : (gateAt C j).op = GateOp.or) (i : ℕ)
    (hi : i ∈ (gateAt C j).inputs) : 0 < DL N C i := by
  by_contra hcon
  have hl : DL N C i = 0 := by omega
  obtain ⟨hj, hm, hr⟩ := hc
  have hir := hrb j hj i hi
  have hti := W_one N C hrb h2 i (by omega) hl
  have htj : W N C (fun _ => true) (fun _ => false) (N + N + j) = true := by
    rw [W_gate N C hrb _ _ j hj, ev_or _ _ hop]
    exact ⟨i, hi, hti⟩
  have := (up N C hrb h2 hkm _ _ hr hm htj).2
  have e : W N C (fun _ => true) (fun _ => false) C.output =
      circuitFun (N + N) C (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false)) := rfl
  rw [e, hf] at this
  cases this

theorem ncard_one (L : ℕ) (P : ℕ → Prop) (hP : ∀ j, P j → j < L) :
    Set.ncard {j : ℕ | P j} = (by classical exact ((Finset.range L).filter P).card) := by
  classical
  have : {j : ℕ | P j} = ↑((Finset.range L).filter P) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    exact ⟨fun h => ⟨hP j h, h⟩, fun h => h.2⟩
  rw [this, Set.ncard_coe_finset]

theorem ncard_pairs (L : ℕ) (P : ℕ → Prop) (Q : ℕ → ℕ → Prop) (hP : ∀ j, P j → j < L) :
    Set.ncard {js : ℕ × ℕ | P js.1 ∧ js.2 < 2 ∧ Q js.1 js.2} =
      (by classical exact
        ((((Finset.range L).filter P) ×ˢ Finset.range 2).filter (fun js => Q js.1 js.2)).card) := by
  classical
  have : {js : ℕ × ℕ | P js.1 ∧ js.2 < 2 ∧ Q js.1 js.2} =
      ↑((((Finset.range L).filter P) ×ˢ Finset.range 2).filter (fun js => Q js.1 js.2)) := by
    ext js
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨⟨hP _ h1, h1⟩, h2⟩, h3⟩
    · rintro ⟨⟨⟨_, h1⟩, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  rw [this, Set.ncard_coe_finset]

theorem card_pairs (s : Finset ℕ) (Q : ℕ → ℕ → Prop) :
    (by classical exact ((s ×ˢ Finset.range 2).filter (fun js => Q js.1 js.2)).card) =
      (by classical exact ∑ j ∈ s, ((if Q j 0 then 1 else 0) + (if Q j 1 then 1 else 0))) := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_range_succ, Finset.sum_range_one]

theorem pointwise (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (hf : circuitFun (N + N) C (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false)) = false)
    (j : ℕ) (hc : Cn N C j) [Decidable ((gateAt C j).op = GateOp.or)]
    [∀ s, Decidable (DP N C ((gateAt C j).inputs.getD s 0) = 0)]
    [∀ s, Decidable (Mx N C ((gateAt C j).inputs.getD s 0))] :
    (if (gateAt C j).op = GateOp.or then 1 else 0) + 1 =
      ((if DP N C ((gateAt C j).inputs.getD 0 0) = 0 then 1 else 0) +
        (if DP N C ((gateAt C j).inputs.getD 1 0) = 0 then 1 else 0)) +
      ((if Mx N C ((gateAt C j).inputs.getD 0 0) then 1 else 0) +
        (if Mx N C ((gateAt C j).inputs.getD 1 0) then 1 else 0)) := by
  have hj := hc.1
  have hm := hc.2.1
  have hg := h2 _ (gateAt_mem C j hj)
  have hor := or_lf N C hrb h2 hkm hf j hc
  have hkj := hkm j hj
  have hPz := DP_zero N C hrb j hj
  have hLz := DL_zero N C hrb j hj
  obtain ⟨p, q, hpq⟩ := two_eq _ hg.2
  have hpr := hrb j hj p (by rw [hpq]; simp)
  have hqr := hrb j hj q (by rw [hpq]; simp)
  have np := NZ N C hrb h2 p (by omega)
  have nq := NZ N C hrb h2 q (by omega)
  have hop := hg.1
  rw [hpq] at hor hkj hPz hLz
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq, exists_eq_left] at hor hkj hPz hLz
  have hP2 : ¬ (DP N C p = 0 ∧ DP N C q = 0) := fun hh => by rw [← hPz] at hh; have := hm.1; omega
  have hL2 : ¬ (DL N C p = 0 ∧ DL N C q = 0) := fun hh => by rw [← hLz] at hh; have := hm.2; omega
  have e0 : (gateAt C j).inputs.getD 0 0 = p := by rw [hpq]; rfl
  have e1 : (gateAt C j).inputs.getD 1 0 = q := by rw [hpq]; rfl
  have c0 : (if DP N C ((gateAt C j).inputs.getD 0 0) = 0 then 1 else 0) =
      (if DP N C p = 0 then 1 else 0) := by
    by_cases hc : DP N C p = 0
    · rw [if_pos hc, if_pos (by rw [e0]; exact hc)]
    · rw [if_neg hc, if_neg (by rw [e0]; exact hc)]
  have c1 : (if DP N C ((gateAt C j).inputs.getD 1 0) = 0 then 1 else 0) =
      (if DP N C q = 0 then 1 else 0) := by
    by_cases hc : DP N C q = 0
    · rw [if_pos hc, if_pos (by rw [e1]; exact hc)]
    · rw [if_neg hc, if_neg (by rw [e1]; exact hc)]
  have m0 : (if Mx N C ((gateAt C j).inputs.getD 0 0) then 1 else 0) =
      (if 0 < DP N C p ∧ 0 < DL N C p then 1 else 0) := by
    by_cases hc : 0 < DP N C p ∧ 0 < DL N C p
    · rw [if_pos hc, if_pos (by rw [e0]; exact hc)]
    · rw [if_neg hc, if_neg (by rw [e0]; exact hc)]
  have m1 : (if Mx N C ((gateAt C j).inputs.getD 1 0) then 1 else 0) =
      (if 0 < DP N C q ∧ 0 < DL N C q then 1 else 0) := by
    by_cases hc : 0 < DP N C q ∧ 0 < DL N C q
    · rw [if_pos hc, if_pos (by rw [e1]; exact hc)]
    · rw [if_neg hc, if_neg (by rw [e1]; exact hc)]
  rw [c0, c1, m0, m1]
  rcases hop with h | h
  · have hne : ¬ (gateAt C j).op = GateOp.or := by intro h'; rw [h] at h'; cases h'
    have hk := hkj h
    rw [if_neg hne]
    clear hor hkj hPz hLz c0 c1 m0 m1 e0 e1 hc hpq hpr hqr
    rcases hk with hk | hk
    · rcases hk with hk | hk
      · rcases np with np | np <;> rcases nq with nq | nq <;> split_ifs <;> omega
      · rcases np with np | np <;> rcases nq with nq | nq <;> split_ifs <;> omega
    · exact absurd hk hP2
  · have h1 := hor h
    rw [if_pos h]
    split_ifs <;> omega

theorem main (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (hf : circuitFun (N + N) C (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false)) = false) :
    (∀ j, Cn N C j → (gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs, 0 < DL N C i) ∧
    Set.ncard {j : ℕ | Cn N C j ∧ (gateAt C j).op = GateOp.or} + Set.ncard {j : ℕ | Cn N C j} =
      Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
        DP N C ((gateAt C js.1).inputs.getD js.2 0) = 0} +
      Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
        Mx N C ((gateAt C js.1).inputs.getD js.2 0)} ∧
    Set.ncard {j : ℕ | Cn N C j} ≤ Set.ncard {js : ℕ × ℕ | Cn N C js.1 ∧ js.2 < 2 ∧
        Mx N C ((gateAt C js.1).inputs.getD js.2 0)} + 1 := by
  classical
  have hP : ∀ j, Cn N C j → j < C.gates.length := fun j h => h.1
  refine ⟨fun j hc hop i hi => or_lf N C hrb h2 hkm hf j hc hop i hi, ?_, ?_⟩
  · rw [ncard_one C.gates.length _ (fun j h => h.1.1), ncard_one C.gates.length _ hP,
      ncard_pairs C.gates.length _ (fun j s => DP N C ((gateAt C j).inputs.getD s 0) = 0) hP,
      ncard_pairs C.gates.length _ (fun j s => Mx N C ((gateAt C j).inputs.getD s 0)) hP]
    have e1 := card_pairs ((Finset.range C.gates.length).filter (Cn N C))
      (fun j s => DP N C ((gateAt C j).inputs.getD s 0) = 0)
    have e2 := card_pairs ((Finset.range C.gates.length).filter (Cn N C))
      (fun j s => Mx N C ((gateAt C j).inputs.getD s 0))
    beta_reduce at e1 e2
    rw [e1, e2, Finset.card_filter, Finset.card_filter, Finset.sum_filter,
      Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hc : Cn N C j
    · have := pointwise N C hrb h2 hkm hf j hc
      simp only [hc, true_and, ↓reduceIte]
      split_ifs at this ⊢ <;> omega
    · simp only [hc, false_and, ↓reduceIte]
  · rw [ncard_one C.gates.length _ hP,
      ncard_pairs C.gates.length _ (fun j s => Mx N C ((gateAt C j).inputs.getD s 0)) hP]
    let S := (Finset.range C.gates.length).filter (Cn N C)
    let T := (S ×ˢ Finset.range 2).filter (fun js => Mx N C ((gateAt C js.1).inputs.getD js.2 0))
    let φ : ℕ × ℕ → ℕ := fun js => (gateAt C js.1).inputs.getD js.2 0 - (N + N)
    have hsub : S ⊆ insert (C.output - (N + N)) (T.image φ) := by
      intro j hjS
      have hc : Cn N C j := (Finset.mem_filter.mp hjS).2
      obtain ⟨hj, hm, hr⟩ := hc
      rw [Finset.mem_insert]
      rcases Relation.ReflTransGen.cases_head hr with he | ⟨c, hrc, hcr⟩
      · left; omega
      · right
        obtain ⟨_, f, rfl, hin⟩ := hrc
        rw [get_eq] at hin
        have hf2 := f.isLt
        have hmf := mx_up N C hrb f.val hf2 _ hin hm
        have hg := h2 _ (gateAt_mem C f.val hf2)
        obtain ⟨p, q, hpq⟩ := two_eq _ hg.2
        rw [Finset.mem_image]
        have hfS : f.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hf2, hf2, hmf, hcr⟩
        rw [hpq] at hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with h | h
        · refine ⟨(f.val, 0), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hfS, by simp⟩, ?_⟩
            simp only [hpq, List.getD_cons_zero]
            rw [← h]; exact hm
          · simp only [φ, hpq, List.getD_cons_zero]
            omega
        · refine ⟨(f.val, 1), ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hfS, by simp⟩, ?_⟩
            simp only [hpq, List.getD_cons_zero, List.getD_cons_succ]
            rw [← h]; exact hm
          · simp only [φ, hpq, List.getD_cons_zero, List.getD_cons_succ]
            omega
    calc S.card ≤ (insert (C.output - (N + N)) (T.image φ)).card := Finset.card_le_card hsub
      _ ≤ (T.image φ).card + 1 := Finset.card_insert_le _ _
      _ ≤ T.card + 1 := by have := Finset.card_image_le (s := T) (f := φ); omega

end PEqualNP.Outside.L_meta_1949

theorem PEqualNP.Outside.L_meta_1949 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → ∀ (N230 : ℕ) (C230 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g230 ∈ C230.gates, (g230.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g230.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g230.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N230 + N230) C230) → (∀ j230x2 < C230.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i230x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x2 0 = 0) ∨ (∀ h230 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD h230 0 = 0)) → PEqualNP.MetaComplexity.circuitFun (N230 + N230) C230 (Fin.append (fun u230 : Fin N230 => true) (fun u230x1 : Fin N230 => false)) = false → ∀ mixed230 : ℕ → Prop, mixed230 = (fun i230 : ℕ => 0 < (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD i230 0 ∧ 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230 0) → ∀ cone230 : ℕ → Prop, cone230 = (fun j230 : ℕ => j230 < C230.gates.length ∧ mixed230 (N230 + N230 + j230) ∧ Relation.ReflTransGen (fun a230 b230 : ℕ => a230 < b230 ∧ ∃ f230 : Fin C230.gates.length, b230 = N230 + N230 + f230.val ∧ a230 ∈ (C230.gates.get f230).inputs) (N230 + N230 + j230) C230.output) → (∀ j230x1 : ℕ, cone230 j230x1 → (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i230x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).inputs, 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x1 0) ∧ Set.ncard {j230x3 : ℕ | cone230 j230x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x3).op = PEqualNP.CircuitLowerBounds.GateOp.or} + Set.ncard {j230x4 : ℕ | cone230 j230x4} = Set.ncard {js230 : ℕ × ℕ | cone230 js230.1 ∧ js230.2 < 2 ∧ (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230.1).inputs.getD js230.2 0) 0 = 0} + Set.ncard {js230x1 : ℕ × ℕ | cone230 js230x1.1 ∧ js230x1.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x1.1).inputs.getD js230x1.2 0)} ∧ Set.ncard {j230x5 : ℕ | cone230 j230x5} ≤ Set.ncard {js230x2 : ℕ × ℕ | cone230 js230x2.1 ∧ js230x2.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x2.1).inputs.getD js230x2.2 0)} + 1 := by
  intro _ N C hC hkm hf mixed hmixed cone hcone
  obtain ⟨h2, hrb⟩ := hC
  subst hmixed hcone
  exact PEqualNP.Outside.L_meta_1949.main N C hrb h2 hkm hf
