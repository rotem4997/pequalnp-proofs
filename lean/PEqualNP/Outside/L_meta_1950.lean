import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1950

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

def Mx (N : ℕ) (C : Circuit) (i : ℕ) : Prop := 0 < DP N C i ∧ 0 < DL N C i

def Cone (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  j < C.gates.length ∧ Mx N C (N + N + j) ∧
    Relation.ReflTransGen (fun a b : ℕ => a < b ∧ ∃ f : Fin C.gates.length,
      b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs) (N + N + j) C.output

def Gok (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.or ∨ ∃ i ∈ (gateAt C j).inputs,
    DL N C i = 0 ∧ W N C x (fun _ => false) i = true

def Stp (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j k : ℕ) : Prop :=
  Cone N C k ∧ N + N + j ∈ (gateAt C k).inputs ∧ Gok N C x k

def Lv (N : ℕ) (C : Circuit) (x : Fin N → Bool) (j : ℕ) : Prop :=
  Cone N C j ∧ Gok N C x j ∧
    ∃ jo : ℕ, N + N + jo = C.output ∧ Relation.ReflTransGen (Stp N C x) j jo

def Slot (N : ℕ) (C : Circuit) (h j : ℕ) : Prop :=
  Cone N C j ∧ h ∈ (gateAt C j).inputs ∧ DP N C h = 0

def Ap (N : ℕ) (C : Circuit) (h : ℕ) (p : Fin N) : Prop :=
  ∃ j : ℕ, Slot N C h j ∧ Lv N C (fun a => decide (a = p)) j

def Lh (N : ℕ) (C : Circuit) (h : ℕ) (w : Fin N) : Prop :=
  W N C (fun _ => false) (fun a => decide (a = w)) h = true

theorem tr {P : ℕ → Prop} {a b : ℕ} (e : a = b) (h : P a) : P b := by
  subst e
  exact h

theorem two (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (j : ℕ) (hj : j < C.gates.length) : ∃ a b, (gateAt C j).inputs = [a, b] := by
  have hg := (h2 _ (gateAt_mem C j hj)).2
  rcases hin : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rw [hin] at hg
    simp at hg
  · rw [hin] at hg
    simp at hg
  · exact ⟨a, b, rfl⟩
  · rw [hin] at hg
    simp at hg

theorem mx_gate (N : ℕ) (C : Circuit) (w : ℕ) (h : Mx N C w) :
    ∃ j, j < C.gates.length ∧ w = N + N + j := by
  obtain ⟨hp, hl⟩ := h
  by_cases h1 : w < N + N
  · exfalso
    have e1 : DP N C w = if w ∈ Finset.range N then 1 else 0 := D_in (N + N) _ C w h1
    have e2 : DL N C w = if w ∈ Finset.Ico N (N + N) then 1 else 0 := D_in (N + N) _ C w h1
    by_cases h3 : w < N
    · rw [e2, ifn (by rw [Finset.mem_Ico]; omega)] at hl
      omega
    · rw [e1, ifn (by rw [Finset.mem_range]; omega)] at hp
      omega
  · by_cases h2 : w < N + N + C.gates.length
    · exact ⟨w - (N + N), by omega, by omega⟩
    · exfalso
      have e1 : DP N C w = 0 := D_out (N + N) _ C w (by omega)
      omega

theorem step_up (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin N → Bool) (j u : ℕ) (hj : j < C.gates.length) (hg : Gok N C x j)
    (hu : u ∈ (gateAt C j).inputs) (hW : W N C x y u = true) (hd : 0 < DL N C u) :
    W N C x y (N + N + j) = true := by
  rw [W_gate N C hrb x y j hj]
  rcases hg with hop | ⟨i, hi, hdi, hwi⟩
  · exact (ev_or _ _ hop).mpr ⟨u, hu, hW⟩
  · have hwi2 : W N C x y i = true := by
      rw [W_indL N C hrb x y (fun _ => false) i hdi]
      exact hwi
    rcases (h2 _ (gateAt_mem C j hj)).1 with hop | hop
    · rw [ev_and _ _ hop]
      obtain ⟨a, b, hab⟩ := two C h2 j hj
      have hne : i ≠ u := by
        intro e
        rw [e] at hdi
        omega
      rw [hab] at hu hi
      rw [hab]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hi hc
      rcases hc with rfl | rfl <;> rcases hu with rfl | rfl <;> rcases hi with rfl | rfl <;>
        first | assumption | exact absurd rfl hne
    · exact (ev_or _ _ hop).mpr ⟨u, hu, hW⟩

theorem chain_up (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin N → Bool) (j jo : ℕ) (hch : Relation.ReflTransGen (Stp N C x) j jo)
    (hW : W N C x y (N + N + j) = true) (hd : 0 < DL N C (N + N + j)) :
    W N C x y (N + N + jo) = true ∧ 0 < DL N C (N + N + jo) := by
  induction hch with
  | refl => exact ⟨hW, hd⟩
  | tail _ hst ih =>
    obtain ⟨hc, hm, hg⟩ := hst
    exact ⟨step_up N C hrb h2 x y _ _ hc.1 hg hm ih.1 ih.2, hc.2.1.2⟩

theorem snd (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin N → Bool) (h j : ℕ) (hs : Slot N C h j) (hl : Lv N C x j)
    (hh : W N C (fun _ => false) y h = true) : W N C x y C.output = true := by
  obtain ⟨hc, hm, hdp⟩ := hs
  obtain ⟨_, hg, jo, hjo, hch⟩ := hl
  have hxy : W N C x y h = true := by
    rw [W_indP N C hrb x (fun _ => false) y h hdp]
    exact hh
  have hdl : 0 < DL N C h := by
    by_contra hc0
    have h0 : DL N C h = 0 := by omega
    rw [W_indL N C hrb (fun _ => false) y (fun _ => false) h h0, W_zero N C hrb h2 h] at hh
    cases hh
  have h1 := step_up N C hrb h2 x y j h hc.1 hg hm hxy hdl
  have h3 := chain_up N C hrb h2 x y j jo hch h1 hc.2.1.2
  exact tr (P := fun o => W N C x y o = true) hjo h3.1

theorem descent (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (x y : Fin N → Bool) (jo : ℕ) (hjo : N + N + jo = C.output) :
    ∀ j, Cone N C j → Relation.ReflTransGen (Stp N C x) j jo →
      W N C x y (N + N + j) = true → W N C x (fun _ => false) (N + N + j) = false →
      ∃ h k, Slot N C h k ∧ Lv N C x k ∧ W N C (fun _ => false) y h = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hc hch hT hF
    have hj := hc.1
    have child : ∀ u, Gok N C x j → u ∈ (gateAt C j).inputs → W N C x y u = true →
        W N C x (fun _ => false) u = false →
        ∃ h k, Slot N C h k ∧ Lv N C x k ∧ W N C (fun _ => false) y h = true := by
      intro u hg hu huT huF
      have hdl : 0 < DL N C u := by
        by_contra hc0
        have h0 : DL N C u = 0 := by omega
        rw [W_indL N C hrb x y (fun _ => false) u h0, huF] at huT
        cases huT
      by_cases hdp : DP N C u = 0
      · refine ⟨u, j, ⟨hc, hu, hdp⟩, ⟨hc, hg, jo, hjo, hch⟩, ?_⟩
        rw [← W_indP N C hrb x (fun _ => false) y u hdp]
        exact huT
      · have hmx : Mx N C u := ⟨by omega, hdl⟩
        obtain ⟨k, hk, rfl⟩ := mx_gate N C u hmx
        have hlt := hrb j hj _ hu
        have e : C.gates.get ⟨j, hj⟩ = gateAt C j := (List.getD_eq_getElem C.gates _ hj).symm
        have hmem : N + N + k ∈ (C.gates.get ⟨j, hj⟩).inputs := by
          rw [e]
          exact hu
        have hck : Cone N C k := ⟨hk, hmx,
          Relation.ReflTransGen.head ⟨by omega, ⟨⟨j, hj⟩, rfl, hmem⟩⟩ hc.2.2⟩
        exact ih k (by omega) hck (Relation.ReflTransGen.head ⟨hc, hu, hg⟩ hch) huT huF
    rw [W_gate N C hrb x y j hj] at hT
    rw [W_gate N C hrb x (fun _ => false) j hj] at hF
    rcases (h2 _ (gateAt_mem C j hj)).1 with hop | hop
    · rw [ev_and _ _ hop] at hT
      have hex : ∃ u ∈ (gateAt C j).inputs, W N C x (fun _ => false) u = false := by
        by_contra hne
        push_neg at hne
        have hall : (gateAt C j).op.eval
            ((gateAt C j).inputs.map (W N C x (fun _ => false))) = true :=
          (ev_and _ _ hop).mpr (fun i hi => by simpa using hne i hi)
        rw [hall] at hF
        cases hF
      obtain ⟨u, hu, huF⟩ := hex
      rcases hkm j hj hop with ⟨i, hi, hdi⟩ | hall
      · have hiT := hT i hi
        rw [W_indL N C hrb x y (fun _ => false) i hdi] at hiT
        exact child u (Or.inr ⟨i, hi, hdi, hiT⟩) hu (hT u hu) huF
      · exfalso
        have h0 : D (N + N) (Finset.range N) C (N + N + j) = 0 :=
          (D_zero_iff (N + N) (Finset.range N) C hrb j hj).mpr hall
        have h3 : 0 < D (N + N) (Finset.range N) C (N + N + j) := hc.2.1.1
        omega
    · have hg : Gok N C x j := Or.inl hop
      obtain ⟨u, hu, huT⟩ := (ev_or _ _ hop).mp hT
      have huF : W N C x (fun _ => false) u = false := by
        by_contra hne
        have hne2 : W N C x (fun _ => false) u = true := by simpa using hne
        rw [(ev_or _ _ hop).mpr ⟨u, hu, hne2⟩] at hF
        cases hF
      exact child u hg hu huT huF

theorem main (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack (N + N) C)
    (hkm : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨ (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))
    (no4 : ∀ p q w v : Fin N, p ≠ q → w ≠ v → I p w → I q w → I p v → I q v → False)
    (hedge : ∃ p w : Fin N, I p w)
    (hacc : ∀ p w : Fin N, I p w →
      W N C (fun a => decide (a = p)) (fun a => decide (a = w)) C.output = true)
    (hrej : ∀ x y : Fin N → Bool, (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) → W N C x y C.output = false) :
    (∃ j, N + N + j = C.output ∧ Cone N C j) ∧
    (∀ (x y : Fin N → Bool) (h j : ℕ), Slot N C h j → Lv N C x j →
      W N C (fun _ => false) y h = true → W N C x y C.output = true) ∧
    (∀ x y : Fin N → Bool, W N C x y C.output = true →
      W N C x (fun _ => false) C.output = false →
      ∃ h j, Slot N C h j ∧ Lv N C x j ∧ W N C (fun _ => false) y h = true) ∧
    (∀ (h j : ℕ) (w : Fin N), Slot N C h j → Lh N C h w →
      ¬ Lv N C (fun a => decide (¬ I a w)) j) ∧
    (∀ (h : ℕ) (p w : Fin N), Ap N C h p → Lh N C h w → I p w) ∧
    (∀ p w : Fin N, I p w →
      (∃ h, (∀ v, Lh N C h v ↔ v = w) ∧ Ap N C h p) ∨
      (∃ h, ((∃ w8 w9 : Fin N, w8 ≠ w9 ∧ Lh N C h w8 ∧ Lh N C h w9) ∧
        ∀ q, Ap N C h q ↔ q = p) ∧ Lh N C h w)) := by
  have card1 : ∀ w : Fin N,
      (Finset.univ.filter (fun l : Fin N => (fun a : Fin N => decide (a = w)) l = true)).card
        ≤ 1 := by
    intro w
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
    rw [ha, hb]
  have rej0 : ∀ p : Fin N,
      W N C (fun a => decide (a = p)) (fun _ => false) C.output = false := by
    intro p
    refine hrej (fun a => decide (a = p)) (fun _ => false) (by simp) ?_
    rintro ⟨_, _, _, _, h⟩
    exact Bool.false_ne_true h
  have p1 : ∃ j, N + N + j = C.output ∧ Cone N C j := by
    obtain ⟨p, w, hI⟩ := hedge
    have a1 := hacc p w hI
    have a2 := rej0 p
    have a3 : W N C (fun _ => false) (fun a => decide (a = w)) C.output = false := by
      refine hrej (fun _ => false) (fun a => decide (a = w)) (card1 w) ?_
      rintro ⟨_, _, _, h, _⟩
      exact Bool.false_ne_true h
    have hl : 0 < DL N C C.output := by
      by_contra hc0
      have h0 : DL N C C.output = 0 := by omega
      rw [W_indL N C hrb _ _ (fun _ => false) _ h0, a2] at a1
      cases a1
    have hp : 0 < DP N C C.output := by
      by_contra hc0
      have h0 : DP N C C.output = 0 := by omega
      rw [W_indP N C hrb _ (fun _ => false) _ _ h0, a3] at a1
      cases a1
    obtain ⟨j, hj, e⟩ := mx_gate N C C.output ⟨hp, hl⟩
    refine ⟨j, e.symm, hj, ?_, ?_⟩
    · exact tr (P := fun o => Mx N C o) e ⟨hp, hl⟩
    · exact tr (P := fun o => Relation.ReflTransGen (fun a b : ℕ => a < b ∧
        ∃ f : Fin C.gates.length, b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs) o C.output) e
        Relation.ReflTransGen.refl
  have p2 : ∀ (x y : Fin N → Bool) (h j : ℕ), Slot N C h j → Lv N C x j →
      W N C (fun _ => false) y h = true → W N C x y C.output = true :=
    fun x y h j => snd N C hrb h2 x y h j
  have p3 : ∀ x y : Fin N → Bool, W N C x y C.output = true →
      W N C x (fun _ => false) C.output = false →
      ∃ h j, Slot N C h j ∧ Lv N C x j ∧ W N C (fun _ => false) y h = true := by
    intro x y hT hF
    obtain ⟨jo, hjo, hc⟩ := p1
    exact descent N C hrb h2 hkm x y jo hjo jo hc Relation.ReflTransGen.refl
      (tr (P := fun o => W N C x y o = true) hjo.symm hT)
      (tr (P := fun o => W N C x (fun _ => false) o = false) hjo.symm hF)
  have p5 : ∀ (h : ℕ) (p w : Fin N), Ap N C h p → Lh N C h w → I p w := by
    intro h p w ⟨j, hs, hl⟩ hw
    by_contra hn
    have a := p2 _ _ h j hs hl hw
    have r : W N C (fun a => decide (a = p)) (fun a => decide (a = w)) C.output = false := by
      refine hrej (fun a => decide (a = p)) (fun a => decide (a = w)) (card1 w) ?_
      rintro ⟨q, v, hI, hx, hy⟩
      have e1 : q = p := by simpa using hx
      have e2 : v = w := by simpa using hy
      rw [e1, e2] at hI
      exact hn hI
    exact Bool.false_ne_true (r.symm.trans a)
  refine ⟨p1, p2, p3, ?_, p5, ?_⟩
  · intro h j w hs hw hl
    have a := p2 _ _ h j hs hl hw
    have r : W N C (fun a => decide (¬ I a w)) (fun a => decide (a = w)) C.output = false := by
      refine hrej (fun a => decide (¬ I a w)) (fun a => decide (a = w)) (card1 w) ?_
      rintro ⟨q, v, hI, hx, hy⟩
      have e2 : v = w := by simpa using hy
      have e1 : ¬ I q w := by simpa using hx
      rw [e2] at hI
      exact e1 hI
    exact Bool.false_ne_true (r.symm.trans a)
  · intro p w hI
    have a1 := hacc p w hI
    have a2 := rej0 p
    obtain ⟨h, j, hs, hl, hw⟩ := p3 _ _ a1 a2
    have hap : Ap N C h p := ⟨j, hs, hl⟩
    by_cases hex : ∃ v, v ≠ w ∧ Lh N C h v
    · obtain ⟨v, hne, hv⟩ := hex
      refine Or.inr ⟨h, ⟨⟨v, w, hne, hv, hw⟩, fun q => ⟨fun hq => ?_, fun e => ?_⟩⟩, hw⟩
      · by_contra hne2
        exact no4 q p v w hne2 hne (p5 h q v hq hv) (p5 h p v hap hv)
          (p5 h q w hq hw) (p5 h p w hap hw)
      · rw [e]
        exact hap
    · refine Or.inl ⟨h, fun v => ⟨fun hl2 => ?_, fun e => ?_⟩, hap⟩
      · by_contra hne
        exact hex ⟨v, hne, hl2⟩
      · rw [e]
        exact hw


end PEqualNP.Outside.L_meta_1950

theorem PEqualNP.Outside.L_meta_1950 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → ∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14) := by
  intro _ N I _ C hC hkm no4 hedge hacc hrej mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  subst hmixed hcone hgok hstep hlvx hslot hap hlh hlpw hppw hlps hpps
  exact PEqualNP.Outside.L_meta_1950.main N I C hC.1 hC.2 hkm no4 hedge hacc hrej
