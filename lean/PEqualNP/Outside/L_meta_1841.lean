import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1841

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

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

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

theorem bt (b : Bool) (h : ¬ b = false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem pos (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C)
    (h2 : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w, w < N + N + C.gates.length → ¬ (DP N C w = 0 ∧ DL N C w = 0) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hc
    by_cases h1 : w < N + N
    · have ha : D (N + N) (Finset.range N) C w = 0 := hc.1
      have hb : D (N + N) (Finset.Ico N (N + N)) C w = 0 := hc.2
      rw [D_in _ _ _ _ h1] at ha
      rw [D_in _ _ _ _ h1] at hb
      by_cases h3 : w < N
      · rw [ifp (Finset.mem_range.mpr h3)] at ha
        omega
      · rw [ifp (Finset.mem_Ico.mpr ⟨by omega, h1⟩)] at hb
        omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      have hg := h2 _ (gateAt_mem C j hj)
      obtain ⟨a, ha⟩ : ∃ a, a ∈ (gateAt C j).inputs := by
        rcases hin : (gateAt C j).inputs with _ | ⟨a, t⟩
        · rw [hin] at hg
          simp at hg
        · exact ⟨a, by simp⟩
      have hlt := hrb j hj a ha
      exact ih a (by omega) (by omega)
        ⟨(D_zero_iff (N + N) (Finset.range N) C hrb j hj).mp hc.1 a ha,
         (D_zero_iff (N + N) (Finset.Ico N (N + N)) C hrb j hj).mp hc.2 a ha⟩

theorem cnt (n : ℕ) (a b : ℕ → ℕ) (h : ∀ j < n, ¬ (a j = 0 ∧ b j = 0)) :
    Set.ncard {j : ℕ | j < n ∧ a j = 0} + Set.ncard {j : ℕ | j < n ∧ b j = 0}
      + Set.ncard {j : ℕ | j < n ∧ 0 < a j ∧ 0 < b j} ≤ n := by
  have e1 : {j : ℕ | j < n ∧ a j = 0} = ↑((Finset.range n).filter (fun j => a j = 0)) := by
    ext j
    simp
  have e2 : {j : ℕ | j < n ∧ b j = 0} = ↑((Finset.range n).filter (fun j => b j = 0)) := by
    ext j
    simp
  have e3 : {j : ℕ | j < n ∧ 0 < a j ∧ 0 < b j}
      = ↑((Finset.range n).filter (fun j => 0 < a j ∧ 0 < b j)) := by
    ext j
    simp
  rw [e1, e2, e3, Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset,
    Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  calc _ ≤ ∑ j ∈ Finset.range n, 1 := by
        apply Finset.sum_le_sum
        intro j hj
        have := h j (Finset.mem_range.mp hj)
        split_ifs <;> omega
    _ = n := by simp

theorem fin {N R D q M1 INC tpf tx tm sz xs : ℕ} {S W : Finset (Fin N)}
    {Q : (Fin N → Bool) → Fin N → Prop} {g : (Fin N → Bool) → Fin N → Bool}
    (hiff : ∀ w ∈ W, ∀ x : Fin N → Bool, (g x w = true ↔ Q x w))
    (h2 : D * INC ≤ M1 * tpf
      + D * ∑ w ∈ W, Set.ncard {u : Fin N | u ∈ S ∧ Q (fun a => decide (a = u)) w})
    (h3 : R * ∑ w ∈ W, (S.filter (fun u : Fin N => g (fun a => decide (a = u)) w = true)).card
      ≤ R * W.card + q * xs)
    (hxs : xs ≤ tx + 3 * tm) (hsz : tpf + tx + tm ≤ sz) :
    R * D * INC ≤ R * D * W.card + max (R * M1) (3 * q * D) * sz := by
  have hs : ∑ w ∈ W, Set.ncard {u : Fin N | u ∈ S ∧ Q (fun a => decide (a = u)) w}
      = ∑ w ∈ W, (S.filter (fun u : Fin N => g (fun a => decide (a = u)) w = true)).card := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [← Set.ncard_coe_finset]
    congr 1
    ext u
    constructor
    · rintro ⟨h1, h4⟩
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨h1, (hiff w hw _).mpr h4⟩)
    · intro h
      have h5 := Finset.mem_filter.mp (Finset.mem_coe.mp h)
      exact ⟨h5.1, (hiff w hw _).mp h5.2⟩
  rw [hs] at h2
  have e4 : R * M1 ≤ max (R * M1) (3 * q * D) := le_max_left _ _
  have e5 : 3 * q * D ≤ max (R * M1) (3 * q * D) := le_max_right _ _
  have e1 := Nat.mul_le_mul_left R h2
  have e2 := Nat.mul_le_mul_left D h3
  have e3 : D * (q * xs) ≤ D * (q * (tx + 3 * tm)) :=
    Nat.mul_le_mul_left D (Nat.mul_le_mul_left q hxs)
  have e6 := Nat.mul_le_mul_right tpf e4
  have e7 := Nat.mul_le_mul_right tx e5
  have e8 := Nat.mul_le_mul_right tm e5
  have e9 := Nat.mul_le_mul_left (max (R * M1) (3 * q * D)) hsz
  have e10 : 0 ≤ q * D * tx := Nat.zero_le _
  generalize max (R * M1) (3 * q * D) = Mx at *
  generalize ∑ w ∈ W, (S.filter (fun u : Fin N => g (fun a => decide (a = u)) w = true)).card
    = T at *
  nlinarith [e1, e2, e3, e6, e7, e8, e9, e10]

end PEqualNP.Outside.L_meta_1841

theorem PEqualNP.Outside.L_meta_1841 : (∀ (Nlv17a Rlv17a : ℕ) (Ilv17a : Fin Nlv17a → Fin Nlv17a → Prop) [DecidableRel Ilv17a] (Clv17a Corlv17a : PEqualNP.CircuitLowerBounds.Circuit) (Vlv17a : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit) (Slv17a Wlv17a : Finset (Fin Nlv17a)), ((∀ glv17ax2 ∈ Clv17a.gates, (glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17a + Nlv17a) Clv17a) → (0 < Clv17a.gates.length ∧ (∀ jlv17ax11 < Clv17a.gates.length, ∀ ilv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax11).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax6 : Fin Nlv17a => (plv17ax6 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax4 : Fin Nlv17a => Nlv17a + (llv17ax4 : ℕ)) (Wlv17a)ᶜ)).getD ilv17ax4 0 = 0) ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax7 : Fin Nlv17a => (plv17ax7 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax5 : Fin Nlv17a => Nlv17a + (llv17ax5 : ℕ)) (Wlv17a)ᶜ)).getD Clv17a.output 0 = 0) → Corlv17a = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax12 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax5 0 = 0) ∨ (∀ hlv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val))) Clv17a.output) → Vlv17a = (fun sglv17ax3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax13 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax6 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax6 0 = 0) ∨ (∀ hlv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax4 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val))) Clv17a.output)) → ((∀ sglv17a : ℕ → Fin 2, ∀ wlv17ax1 ∈ Wlv17a, ∀ Xlv17ax1 : Finset (Fin Nlv17a), Xlv17ax1 ⊆ Slv17a → (∀ plv17ax1 ∈ Xlv17ax1, ¬ Ilv17a plv17ax1 wlv17ax1) → Xlv17ax1.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17a) (Fin.append (fun plv17ax2 : Fin Nlv17a => decide (plv17ax2 ∈ Xlv17ax1)) (fun llv17a : Fin Nlv17a => decide (llv17a ∈ ({wlv17ax1} : Finset (Fin Nlv17a))))) = false) → ∀ wlv17a ∈ Wlv17a, ∀ Xlv17a : Finset (Fin Nlv17a), Xlv17a ⊆ Slv17a → (∀ plv17a ∈ Xlv17a, ¬ Ilv17a plv17a wlv17a) → Xlv17a.card ≤ Rlv17a → ¬ (∃ hlv17a : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17a 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17a 0 ∧ ∃ jlv17a < Corlv17a.gates.length, hlv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17a).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17a) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17a) 0)) ∧ (Wlv17a.filter (fun llv17ax1 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17a : Fin Nlv17a => false) (fun alv17ax1 : Fin Nlv17a => decide (alv17ax1 = llv17ax1))))).getD hlv17a false = true)) = ({wlv17a} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax2 blv17a : ℕ => ∃ jlv17ax1 < Corlv17a.gates.length, blv17a = Nlv17a + Nlv17a + jlv17ax1 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17a 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17a 0) ∧ alv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs, ilv17a ≠ alv17ax2 → (Corlv17a.wires (List.ofFn (Fin.append (fun alv17a : Fin Nlv17a => decide (alv17a ∈ Xlv17a)) (fun ulv17ax1 : Fin Nlv17a => false)))).getD ilv17a false = true)) hlv17a Corlv17a.output))) ∧ (∀ (sglv17ax1 : ℕ → Fin 2) (glv17a hlv17ax1 : ℕ) (xlv17a : Fin Nlv17a → Bool), (((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD glv17a 0 = 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD glv17a 0 ∧ ∃ jlv17ax2 < (Vlv17a sglv17ax1).gates.length, glv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax2).inputs ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax2) 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax2) 0)) → (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 → (Relation.ReflTransGen (fun alv17ax3 blv17ax1 : ℕ => ∃ jlv17ax3 < (Vlv17a sglv17ax1).gates.length, blv17ax1 = Nlv17a + Nlv17a + jlv17ax3 ∧ alv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax1 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax1 0) hlv17ax1 glv17a) → ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax1 0 ∧ ∃ jlv17ax4 < Corlv17a.gates.length, hlv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax4).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax4) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax4) 0)) ∧ ((Relation.ReflTransGen (fun alv17ax4 blv17ax2 : ℕ => ∃ jlv17ax5 < (Vlv17a sglv17ax1).gates.length, blv17ax2 = Nlv17a + Nlv17a + jlv17ax5 ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax2 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax2 0) ∧ alv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs, ilv17ax1 ≠ alv17ax4 → ((Vlv17a sglv17ax1).wires (List.ofFn (Fin.append xlv17a (fun ulv17ax2 : Fin Nlv17a => false)))).getD ilv17ax1 false = true)) glv17a (Vlv17a sglv17ax1).output) → (Relation.ReflTransGen (fun alv17ax5 blv17ax3 : ℕ => ∃ jlv17ax6 < Corlv17a.gates.length, blv17ax3 = Nlv17a + Nlv17a + jlv17ax6 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax3 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax3 0) ∧ alv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs, ilv17ax2 ≠ alv17ax5 → (Corlv17a.wires (List.ofFn (Fin.append xlv17a (fun ulv17ax3 : Fin Nlv17a => false)))).getD ilv17ax2 false = true)) hlv17ax1 Corlv17a.output))) ∧ ((∀ sglv17ax2 : ℕ → Fin 2, ∀ wlv17ax4 ∈ Wlv17a, ∀ Xlv17ax2 : Finset (Fin Nlv17a), Xlv17ax2 ⊆ Slv17a → (∀ plv17ax4 ∈ Xlv17ax2, ¬ Ilv17a plv17ax4 wlv17ax4) → Xlv17ax2.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17ax2) (Fin.append (fun plv17ax5 : Fin Nlv17a => decide (plv17ax5 ∈ Xlv17ax2)) (fun llv17ax2 : Fin Nlv17a => decide (llv17ax2 ∈ ({wlv17ax4} : Finset (Fin Nlv17a))))) = false) → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD Clv17a.output 0 → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD Clv17a.output 0 → ∃ (Xclv17a : PEqualNP.CircuitLowerBounds.Circuit) (pslv17a : Fin Nlv17a → ℕ), ((∀ glv17ax1 ∈ Xclv17a.gates, (glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17a Xclv17a) ∧ Xclv17a.size ≤ Set.ncard {jlv17ax7 : ℕ | jlv17ax7 < Clv17a.gates.length ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax7) 0 = 0} + 3 * Set.ncard {jlv17ax8 : ℕ | jlv17ax8 < Clv17a.gates.length ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax8) 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax8) 0} ∧ (∀ (wlv17ax2 : Fin Nlv17a) (xlv17ax1 xlv17ax2 : Fin Nlv17a → Bool), (∀ plv17ax3 ∈ Slv17a, xlv17ax1 plv17ax3 = xlv17ax2 plv17ax3) → (Xclv17a.wires (List.ofFn xlv17ax1)).getD (pslv17a wlv17ax2) false = (Xclv17a.wires (List.ofFn xlv17ax2)).getD (pslv17a wlv17ax2) false) ∧ ∀ wlv17ax3 ∈ Wlv17a, ∀ xlv17ax3 : Fin Nlv17a → Bool, ((Xclv17a.wires (List.ofFn xlv17ax3)).getD (pslv17a wlv17ax3) false = true ↔ (∃ hlv17ax2 : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax2 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax2 0 ∧ ∃ jlv17ax9 < Corlv17a.gates.length, hlv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax9).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax9) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax9) 0)) ∧ (Wlv17a.filter (fun llv17ax3 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17ax4 : Fin Nlv17a => false) (fun alv17ax6 : Fin Nlv17a => decide (alv17ax6 = llv17ax3))))).getD hlv17ax2 false = true)) = ({wlv17ax3} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax7 blv17ax4 : ℕ => ∃ jlv17ax10 < Corlv17a.gates.length, blv17ax4 = Nlv17a + Nlv17a + jlv17ax10 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax4 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax4 0) ∧ alv17ax7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs, ilv17ax3 ≠ alv17ax7 → (Corlv17a.wires (List.ofFn (Fin.append xlv17ax3 (fun ulv17ax5 : Fin Nlv17a => false)))).getD ilv17ax3 false = true)) hlv17ax2 Corlv17a.output))))) → (∀ (qlv17b Nlv17b Klv17b mlv17b Dlv17b : ℕ) (Ilv17b : Fin Nlv17b → Fin Nlv17b → Prop) [DecidableRel Ilv17b] (Clv17b Corlv17b : PEqualNP.CircuitLowerBounds.Circuit) (Slv17b Wlv17b : Finset (Fin Nlv17b)), 2 ≤ qlv17b → Nlv17b = qlv17b ^ 2 + qlv17b + 1 → (∀ llv17b : Fin Nlv17b, (Finset.univ.filter (fun plv17b => Ilv17b plv17b llv17b)).card = qlv17b + 1) → (∀ palv17b pblv17b : Fin Nlv17b, palv17b ≠ pblv17b → ∃! lblv17b : Fin Nlv17b, Ilv17b palv17b lblv17b ∧ Ilv17b pblv17b lblv17b) → ((∀ glv17b ∈ Clv17b.gates, (glv17b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17b + Nlv17b) Clv17b) → Corlv17b = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17b : Fin Clv17b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD ilv17b 0 = 0) ∨ (∀ hlv17b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17b 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val))) Clv17b.output) → Set.ncard {jlv17bx1 : ℕ | jlv17bx1 < Clv17b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD ilv17bx1 0 = 0) ∨ (∀ hlv17bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17bx1 0 = 0))} ≤ mlv17b → ((0 < Clv17b.gates.length ∧ (∀ jlv17bx2 < Clv17b.gates.length, ∀ ilv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx2).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.image (fun plv17bx3 : Fin Nlv17b => (plv17bx3 : ℕ)) (Slv17b)ᶜ ∪ Finset.image (fun llv17bx3 : Fin Nlv17b => Nlv17b + (llv17bx3 : ℕ)) (Wlv17b)ᶜ)).getD ilv17bx2 0 = 0) ∧ (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.image (fun plv17bx4 : Fin Nlv17b => (plv17bx4 : ℕ)) (Slv17b)ᶜ ∪ Finset.image (fun llv17bx4 : Fin Nlv17b => Nlv17b + (llv17bx4 : ℕ)) (Wlv17b)ᶜ)).getD Clv17b.output 0 = 0) ∧ (∀ plv17bx1 ∈ Slv17b, ∀ llv17bx1 ∈ Wlv17b, Ilv17b plv17bx1 llv17bx1 → PEqualNP.MetaComplexity.circuitFun (Nlv17b + Nlv17b) Clv17b (Fin.append (fun plv17bx5 : Fin Nlv17b => decide (plv17bx5 ∈ ({plv17bx1} : Finset (Fin Nlv17b)))) (fun llv17bx5 : Fin Nlv17b => decide (llv17bx5 ∈ ({llv17bx1} : Finset (Fin Nlv17b))))) = true) ∧ (∀ Xlv17b Ylv17b : Finset (Fin Nlv17b), Xlv17b ⊆ Slv17b → Ylv17b ⊆ Wlv17b → Ylv17b.card ≤ Klv17b → (∀ plv17bx2 ∈ Xlv17b, ∀ llv17bx2 ∈ Ylv17b, ¬ Ilv17b plv17bx2 llv17bx2) → PEqualNP.MetaComplexity.circuitFun (Nlv17b + Nlv17b) Clv17b (Fin.append (fun plv17bx6 : Fin Nlv17b => decide (plv17bx6 ∈ Xlv17b)) (fun llv17bx6 : Fin Nlv17b => decide (llv17bx6 ∈ Ylv17b))) = false)) → 2 ^ mlv17b + Dlv17b = Klv17b + 1 → 1 ≤ Dlv17b → Dlv17b * ((Slv17b ×ˢ Wlv17b).filter (fun pllv17b => Ilv17b pllv17b.1 pllv17b.2)).card ≤ max (2 * Dlv17b) (qlv17b + 1) * Set.ncard {jlv17bx3 : ℕ | jlv17bx3 < Clv17b.gates.length ∧ (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD (Nlv17b + Nlv17b + jlv17bx3) 0 = 0} + Dlv17b * ∑ wlv17b ∈ Wlv17b, Set.ncard {ulv17b : Fin Nlv17b | ulv17b ∈ Slv17b ∧ (∃ hlv17bx2 : ℕ, ((Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17bx2 0 = 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD hlv17bx2 0 ∧ ∃ jlv17bx4 < Corlv17b.gates.length, hlv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx4).inputs ∧ (0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD (Nlv17b + Nlv17b + jlv17bx4) 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD (Nlv17b + Nlv17b + jlv17bx4) 0)) ∧ (Wlv17b.filter (fun llv17bx7 : Fin Nlv17b => (Clv17b.wires (List.ofFn (Fin.append (fun ulv17bx1 : Fin Nlv17b => false) (fun alv17bx1 : Fin Nlv17b => decide (alv17bx1 = llv17bx7))))).getD hlv17bx2 false = true)) = ({wlv17b} : Finset (Fin Nlv17b)) ∧ (Relation.ReflTransGen (fun alv17bx2 blv17b : ℕ => ∃ jlv17bx5 < Corlv17b.gates.length, blv17b = Nlv17b + Nlv17b + jlv17bx5 ∧ (0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD blv17b 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD blv17b 0) ∧ alv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).inputs, ilv17bx3 ≠ alv17bx2 → (Corlv17b.wires (List.ofFn (Fin.append (fun alv17b : Fin Nlv17b => decide (alv17b = ulv17b)) (fun ulv17bx2 : Fin Nlv17b => false)))).getD ilv17bx3 false = true)) hlv17bx2 Corlv17b.output))}) → (∀ (qlv17c Nlv17c Rlv17c : ℕ) (Ilv17c : Fin Nlv17c → Fin Nlv17c → Prop) [DecidableRel Ilv17c] (Xlv17c : PEqualNP.CircuitLowerBounds.Circuit) (pslv17c : Fin Nlv17c → ℕ) (Slv17c Wlv17c : Finset (Fin Nlv17c)), 2 ≤ qlv17c → Nlv17c = qlv17c ^ 2 + qlv17c + 1 → (∀ llv17c : Fin Nlv17c, (Finset.univ.filter (fun plv17cx2 => Ilv17c plv17cx2 llv17c)).card = qlv17c + 1) → (∀ palv17c pblv17c : Fin Nlv17c, palv17c ≠ pblv17c → ∃! lblv17c : Fin Nlv17c, Ilv17c palv17c lblv17c ∧ Ilv17c pblv17c lblv17c) → 1 ≤ Rlv17c → Rlv17c ≤ qlv17c → ((∀ glv17c ∈ Xlv17c.gates, (glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17c.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17c Xlv17c) → (∀ (wlv17c : Fin Nlv17c) (xlv17c xlv17cx1 : Fin Nlv17c → Bool), (∀ plv17c ∈ Slv17c, xlv17c plv17c = xlv17cx1 plv17c) → (Xlv17c.wires (List.ofFn xlv17c)).getD (pslv17c wlv17c) false = (Xlv17c.wires (List.ofFn xlv17cx1)).getD (pslv17c wlv17c) false) → (∀ wlv17cx1 ∈ Wlv17c, ∀ Xslv17c : Finset (Fin Nlv17c), Xslv17c ⊆ Slv17c → (∀ plv17cx1 ∈ Xslv17c, ¬ Ilv17c plv17cx1 wlv17cx1) → Xslv17c.card ≤ Rlv17c → (Xlv17c.wires (List.ofFn (fun alv17c : Fin Nlv17c => decide (alv17c ∈ Xslv17c)))).getD (pslv17c wlv17cx1) false = false) → Rlv17c * ∑ wlv17cx2 ∈ Wlv17c, (Slv17c.filter (fun ulv17c : Fin Nlv17c => (Xlv17c.wires (List.ofFn (fun alv17cx1 : Fin Nlv17c => decide (alv17cx1 = ulv17c)))).getD (pslv17c wlv17cx2) false = true)).card ≤ Rlv17c * Wlv17c.card + qlv17c * Xlv17c.size) → ∀ (qlv17 Nlv17 Klv17 mlv17 Rlv17 Dlv17 : ℕ) (Ilv17 : Fin Nlv17 → Fin Nlv17 → Prop) [DecidableRel Ilv17] (Clv17 : PEqualNP.CircuitLowerBounds.Circuit) (Slv17 Wlv17 : Finset (Fin Nlv17)), 2 ≤ qlv17 → Nlv17 = qlv17 ^ 2 + qlv17 + 1 → (∀ llv17 : Fin Nlv17, (Finset.univ.filter (fun plv17 => Ilv17 plv17 llv17)).card = qlv17 + 1) → (∀ palv17 pblv17 : Fin Nlv17, palv17 ≠ pblv17 → ∃! lblv17 : Fin Nlv17, Ilv17 palv17 lblv17 ∧ Ilv17 pblv17 lblv17) → ((∀ glv17 ∈ Clv17.gates, (glv17.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17 + Nlv17) Clv17) → Set.ncard {jlv17 : ℕ | jlv17 < Clv17.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17 0 = 0) ∨ (∀ hlv17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17 0 = 0))} ≤ mlv17 → ((0 < Clv17.gates.length ∧ (∀ jlv17x1 < Clv17.gates.length, ∀ ilv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x1).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x3 : Fin Nlv17 => (plv17x3 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x3 : Fin Nlv17 => Nlv17 + (llv17x3 : ℕ)) (Wlv17)ᶜ)).getD ilv17x1 0 = 0) ∧ (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.image (fun plv17x4 : Fin Nlv17 => (plv17x4 : ℕ)) (Slv17)ᶜ ∪ Finset.image (fun llv17x4 : Fin Nlv17 => Nlv17 + (llv17x4 : ℕ)) (Wlv17)ᶜ)).getD Clv17.output 0 = 0) ∧ (∀ plv17x1 ∈ Slv17, ∀ llv17x1 ∈ Wlv17, Ilv17 plv17x1 llv17x1 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x5 : Fin Nlv17 => decide (plv17x5 ∈ ({plv17x1} : Finset (Fin Nlv17)))) (fun llv17x5 : Fin Nlv17 => decide (llv17x5 ∈ ({llv17x1} : Finset (Fin Nlv17))))) = true) ∧ (∀ Xlv17 Ylv17 : Finset (Fin Nlv17), Xlv17 ⊆ Slv17 → Ylv17 ⊆ Wlv17 → Ylv17.card ≤ Klv17 → (∀ plv17x2 ∈ Xlv17, ∀ llv17x2 ∈ Ylv17, ¬ Ilv17 plv17x2 llv17x2) → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) Clv17 (Fin.append (fun plv17x6 : Fin Nlv17 => decide (plv17x6 ∈ Xlv17)) (fun llv17x6 : Fin Nlv17 => decide (llv17x6 ∈ Ylv17))) = false)) → 2 ^ mlv17 + Dlv17 = Klv17 + 1 → 1 ≤ Dlv17 → 1 ≤ Rlv17 → Rlv17 ≤ qlv17 → (∀ sglv17 : ℕ → Fin 2, ∀ wlv17 ∈ Wlv17, ∀ Xlv17x1 : Finset (Fin Nlv17), Xlv17x1 ⊆ Slv17 → (∀ plv17x7 ∈ Xlv17x1, ¬ Ilv17 plv17x7 wlv17) → Xlv17x1.card ≤ Rlv17 → PEqualNP.MetaComplexity.circuitFun (Nlv17 + Nlv17) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17x2 : Fin Clv17.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.Ico Nlv17 (Nlv17 + Nlv17))).getD ilv17x2 0 = 0) ∨ (∀ hlv17x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs, (Clv17.lineDegrees (Nlv17 + Nlv17) (Finset.range Nlv17)).getD hlv17x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val).inputs.getD (sglv17 jlv17x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17 jlv17x2.val))) Clv17.output) (Fin.append (fun plv17x8 : Fin Nlv17 => decide (plv17x8 ∈ Xlv17x1)) (fun llv17x7 : Fin Nlv17 => decide (llv17x7 ∈ ({wlv17} : Finset (Fin Nlv17))))) = false) → Rlv17 * Dlv17 * ((Slv17 ×ˢ Wlv17).filter (fun pllv17 => Ilv17 pllv17.1 pllv17.2)).card ≤ Rlv17 * Dlv17 * Wlv17.card + max (Rlv17 * max (2 * Dlv17) (qlv17 + 1)) (3 * qlv17 * Dlv17) * Clv17.size := by
  intro H1 H2 H3 q N K m R Dd I instI C S Wl hq hN hl hu hAO hm hC hK hD hR1 hRq hV
  by_cases hinc : ((S ×ˢ Wl).filter (fun pl => I pl.1 pl.2)).card = 0
  · rw [hinc]
    simp
  obtain ⟨⟨p, l⟩, hpl⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hinc)
  have hpl2 := Finset.mem_filter.mp hpl
  have hp : p ∈ S := (Finset.mem_product.mp hpl2.1).1
  have hlW : l ∈ Wl := (Finset.mem_product.mp hpl2.1).2
  have hI : I p l := hpl2.2
  have hK1 : 1 ≤ K := by
    have := Nat.two_pow_pos m
    omega
  have ht : PEqualNP.Outside.L_meta_1841.W N C (fun a => decide (a ∈ ({p} : Finset (Fin N))))
      (fun b => decide (b ∈ ({l} : Finset (Fin N)))) C.output = true := hC.2.1 p hp l hlW hI
  have hf1 : PEqualNP.Outside.L_meta_1841.W N C (fun a => decide (a ∈ (∅ : Finset (Fin N))))
      (fun b => decide (b ∈ ({l} : Finset (Fin N)))) C.output = false :=
    hC.2.2 ∅ {l} (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr hlW)
      (by simpa using hK1) (by simp)
  have hf2 : PEqualNP.Outside.L_meta_1841.W N C (fun a => decide (a ∈ ({p} : Finset (Fin N))))
      (fun b => decide (b ∈ (∅ : Finset (Fin N)))) C.output = false :=
    hC.2.2 {p} ∅ (Finset.singleton_subset_iff.mpr hp) (Finset.empty_subset _)
      (by simp) (by simp)
  have hDP : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD C.output 0 := by
    by_contra h0
    have h0z : PEqualNP.Outside.L_meta_1841.DP N C C.output = 0 := Nat.eq_zero_of_not_pos h0
    have h5 := PEqualNP.Outside.L_meta_1841.W_indP N C hAO.2
      (fun a => decide (a ∈ ({p} : Finset (Fin N)))) (fun a => decide (a ∈ (∅ : Finset (Fin N))))
      (fun b => decide (b ∈ ({l} : Finset (Fin N)))) C.output h0z
    exact absurd (ht.symm.trans (h5.trans hf1)) (by decide)
  have hDL : 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD C.output 0 := by
    by_contra h0
    have h0z : PEqualNP.Outside.L_meta_1841.DL N C C.output = 0 := Nat.eq_zero_of_not_pos h0
    have h5 := PEqualNP.Outside.L_meta_1841.W_indL N C hAO.2
      (fun a => decide (a ∈ ({p} : Finset (Fin N)))) (fun b => decide (b ∈ ({l} : Finset (Fin N))))
      (fun b => decide (b ∈ (∅ : Finset (Fin N)))) C.output h0z
    exact absurd (ht.symm.trans (h5.trans hf2)) (by decide)
  obtain ⟨ha, -, hc⟩ := H1 N R I C _ _ S Wl hAO hC.1 rfl rfl
  have ha2 := ha hV
  obtain ⟨Xc, ps, hXao, hXsize, hXdep, hXiff⟩ := hc hV hDP hDL
  have h2 := H2 q N K m Dd I C _ S Wl hq hN hl hu hAO rfl hm hC hK hD
  have h3 := H3 q N R I Xc ps S Wl hq hN hl hu hR1 hRq hXao hXdep (by
    intro w hw Xs hXs hoff hcard
    apply Classical.byContradiction
    intro hne
    exact ha2 w hw Xs hXs hoff hcard
      ((hXiff w hw (fun a => decide (a ∈ Xs))).mp (PEqualNP.Outside.L_meta_1841.bt _ hne)))
  have hcount := PEqualNP.Outside.L_meta_1841.cnt C.gates.length
    (fun j => (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0)
    (fun j => (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0)
    (fun j hj => PEqualNP.Outside.L_meta_1841.pos N C hAO.2 hAO.1 (N + N + j) (by omega))
  exact PEqualNP.Outside.L_meta_1841.fin hXiff h2 h3 hXsize hcount
