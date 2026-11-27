import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1838

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

theorem lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

theorem two_lines (N : ℕ) (I : Fin N → Fin N → Prop)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (p p' l l' : Fin N) (h1 : I p l) (h2 : I p' l) (h3 : I p l') (h4 : I p' l') :
    p = p' ∨ l = l' := by
  by_cases h : p = p'
  · exact Or.inl h
  · exact Or.inr ((hu p p' h).unique ⟨h1, h2⟩ ⟨h3, h4⟩)

theorem ncard_eq (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Set.ncard {j : ℕ | j < n ∧ P j} = ((Finset.range n).filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp

def AO2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Fr (N : ℕ) (C : Circuit) (h : ℕ) : Prop :=
  DP N C h = 0 ∧ 0 < DL N C h ∧ ∃ j < C.gates.length, h ∈ (gateAt C j).inputs ∧
    (0 < DP N C (N + N + j) ∧ 0 < DL N C (N + N + j))

def PR (N : ℕ) (C : Circuit) (x : Fin N → Bool) : ℕ → ℕ → Prop := fun a b =>
  ∃ j < C.gates.length, b = N + N + j ∧ (0 < DP N C b ∧ 0 < DL N C b) ∧
    a ∈ (gateAt C j).inputs ∧ ((gateAt C j).op = GateOp.or ∨
      ∀ i ∈ (gateAt C j).inputs, i ≠ a → W N C x (fun _ => false) i = true)

def OV (N : ℕ) (C V : Circuit) : ℕ → ℕ → Prop := fun a b =>
  ∃ j < V.gates.length, b = N + N + j ∧ a ∈ (gateAt V j).inputs ∧
    (gateAt V j).op = GateOp.or ∧ 0 < DP N C b ∧ 0 < DL N C b

def Cross (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ ((∃ i ∈ (gateAt C j).inputs, DL N C i = 0) ∨
    (∀ h ∈ (gateAt C j).inputs, DP N C h = 0))

noncomputable def Vw (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) : Circuit :=
  Circuit.mk (List.ofFn (fun j : Fin C.gates.length =>
    @ite Gate (Cross N C j.val) (Classical.propDecidable _)
      (Gate.mk GateOp.or [(gateAt C j.val).inputs.getD (sg j.val).val 0,
        (gateAt C j.val).inputs.getD (sg j.val).val 0]) (gateAt C j.val))) C.output

noncomputable def Cor (N : ℕ) (C : Circuit) : Circuit :=
  Circuit.mk (List.ofFn (fun j : Fin C.gates.length =>
    @ite Gate (Cross N C j.val) (Classical.propDecidable _)
      (Gate.mk GateOp.or (gateAt C j.val).inputs) (gateAt C j.val))) C.output

abbrev ep {N : ℕ} (u : Fin N) : Fin N → Bool := fun a => decide (a = u)

abbrev z0 (N : ℕ) : Fin N → Bool := fun _ => false

abbrev ind {N : ℕ} (Y : Finset (Fin N)) : Fin N → Bool := fun l => decide (l ∈ Y)

theorem ind_single {N : ℕ} (u : Fin N) : ind ({u} : Finset (Fin N)) = ep u := by
  funext a
  simp [ind, ep]

theorem ind_empty {N : ℕ} : ind (∅ : Finset (Fin N)) = z0 N := by
  funext a
  simp [ind, z0]

theorem gateAt_ofFn {n : ℕ} (f : Fin n → Gate) (o : ℕ) (j : ℕ) (hj : j < n) :
    gateAt (Circuit.mk (List.ofFn f) o) j = f ⟨j, hj⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

theorem vw_len (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) :
    (Vw N C sg).gates.length = C.gates.length := by
  simp [Vw]

theorem cor_len (N : ℕ) (C : Circuit) : (Cor N C).gates.length = C.gates.length := by
  simp [Cor]

theorem vw_gate (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (Vw N C sg) j = @ite Gate (Cross N C j) (Classical.propDecidable _)
      (Gate.mk GateOp.or [(gateAt C j).inputs.getD (sg j).val 0,
        (gateAt C j).inputs.getD (sg j).val 0]) (gateAt C j) :=
  gateAt_ofFn _ _ j hj

theorem cor_gate (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (Cor N C) j = @ite Gate (Cross N C j) (Classical.propDecidable _)
      (Gate.mk GateOp.or (gateAt C j).inputs) (gateAt C j) :=
  gateAt_ofFn _ _ j hj

theorem cor_inputs (N : ℕ) (C : Circuit) (j : ℕ) :
    (gateAt (Cor N C) j).inputs = (gateAt C j).inputs := by
  by_cases hj : j < C.gates.length
  · rw [cor_gate N C j hj]
    split_ifs <;> rfl
  · have h1 : gateAt (Cor N C) j = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cor_len]; omega)]
      rfl
    have h2 : gateAt C j = ⟨GateOp.or, []⟩ := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [h1, h2]

theorem cor_rb (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) :
    ReadsBack (N + N) (Cor N C) := by
  intro j hj i hi
  rw [cor_len] at hj
  rw [cor_inputs] at hi
  exact hrb j hj i hi

theorem cor_zero (N : ℕ) (C : Circuit) (hrb : ReadsBack (N + N) C) (M : Finset ℕ) :
    ∀ w, D (N + N) M (Cor N C) w = 0 ↔ D (N + N) M C w = 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N + N
    · rw [D_in (N + N) M (Cor N C) w h1, D_in (N + N) M C w h1]
    · by_cases h2 : w < N + N + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < C.gates.length := by omega
        rw [D_zero_iff (N + N) M (Cor N C) (cor_rb N C hrb) j (by rw [cor_len]; exact hj),
          D_zero_iff (N + N) M C hrb j hj, cor_inputs]
        constructor
        · intro h i hi
          exact (ih i (by have := hrb j hj i hi; omega)).mp (h i hi)
        · intro h i hi
          exact (ih i (by have := hrb j hj i hi; omega)).mpr (h i hi)
      · rw [D_out (N + N) M (Cor N C) w (by rw [cor_len]; omega),
          D_out (N + N) M C w (by omega)]

theorem getD_mem2 (l : List ℕ) (s : ℕ) (hl : l.length = 2) (hs : s < 2) : l.getD s 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem ov_step (N : ℕ) (C : Circuit) (hC : AO2 C) (hrb : ReadsBack (N + N) C) (sg : ℕ → Fin 2)
    (x : Fin N → Bool) (a b : ℕ) (h : OV N C (Vw N C sg) a b) : PR N (Cor N C) x a b := by
  obtain ⟨j, hj, rfl, ha, hop, hP, hL⟩ := h
  rw [vw_len] at hj
  have hP' : 0 < DP N (Cor N C) (N + N + j) := Nat.pos_of_ne_zero (fun h0 =>
    (Nat.ne_of_gt hP) ((cor_zero N C hrb (Finset.range N) _).mp h0))
  have hL' : 0 < DL N (Cor N C) (N + N + j) := Nat.pos_of_ne_zero (fun h0 =>
    (Nat.ne_of_gt hL) ((cor_zero N C hrb (Finset.Ico N (N + N)) _).mp h0))
  have hlen := (hC _ (gateAt_mem C j hj)).2
  rw [vw_gate N C sg j hj] at ha hop
  refine ⟨j, by rw [cor_len]; exact hj, rfl, ⟨hP', hL'⟩, ?_, Or.inl ?_⟩
  · rw [cor_inputs]
    split_ifs at ha with hc
    · have ha' : a = (gateAt C j).inputs.getD (sg j).val 0 := by simpa using ha
      rw [ha']
      exact getD_mem2 _ _ hlen (sg j).isLt
    · exact ha
  · rw [cor_gate N C j hj]
    split_ifs at hop ⊢ with hc
    · rfl
    · exact hop

theorem case_c (N : ℕ) (C : Circuit) (hC : AO2 C) (hrb : ReadsBack (N + N) C) (sg : ℕ → Fin 2)
    (x y : Fin N → Bool) (h : ℕ) (hdp : DP N C h = 0)
    (hy : W N C (fun _ => false) y h = true) (hne : h ≠ C.output)
    (hpath : Relation.ReflTransGen (OV N C (Vw N C sg)) h C.output) :
    Fr N (Cor N C) h ∧ Relation.ReflTransGen (PR N (Cor N C) x) h (Cor N C).output := by
  have hp2 : Relation.ReflTransGen (PR N (Cor N C) x) h C.output :=
    Relation.ReflTransGen.mono (fun a b hab => ov_step N C hC hrb sg x a b hab) _ _ hpath
  refine ⟨?_, hp2⟩
  have hdl : 0 < DL N C h := by
    apply Nat.pos_of_ne_zero
    intro h0
    have h1 := W_indL N C hrb (fun _ => false) y (fun _ => false) h h0
    rw [hy, W_zero N C hrb hC h] at h1
    cases h1
  rcases Relation.ReflTransGen.cases_head hp2 with heq | ⟨c, hstep, -⟩
  · exact absurd heq hne
  · obtain ⟨j, hj, rfl, hmix, hin, -⟩ := hstep
    exact ⟨(cor_zero N C hrb _ h).mpr hdp, Nat.pos_of_ne_zero (fun h0 =>
      (Nat.ne_of_gt hdl) ((cor_zero N C hrb _ h).mp h0)), j, hj, hin, hmix⟩

theorem cf_eq (N : ℕ) (V : Circuit) (x y : Fin N → Bool) :
    circuitFun (N + N) V (Fin.append x y) = W N V x y V.output := rfl

theorem cf_mono_y (N : ℕ) (V : Circuit) (hop : AO2 V) (x y y' : Fin N → Bool)
    (h : ∀ l, y l = true → y' l = true) (w : ℕ) (hw : W N V x y w = true) :
    W N V x y' w = true := by
  refine V_mono V (fun g hg => (hop g hg).1) _ _ (by simp) ?_ w hw
  intro i
  rw [app_getD, app_getD]
  split_ifs with ha hb
  · exact id
  · exact h _
  · exact id

def Wit (N : ℕ) (C V : Circuit) (u w : Fin N) (h : ℕ) : Prop :=
  DP N C h = 0 ∧ W N C (z0 N) (ep w) h = true ∧ Fr N (Cor N C) h ∧
    Relation.ReflTransGen (PR N (Cor N C) (ep u)) h (Cor N C).output ∧
    ∀ y, W N C (z0 N) y h = true → circuitFun (N + N) V (Fin.append (ep u) y) = true

theorem view_wit (N : ℕ) (C : Circuit) (hC : AO2 C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (u w : Fin N)
    (hVrb : ReadsBack (N + N) (Vw N C sg))
    (hacc : circuitFun (N + N) (Vw N C sg) (Fin.append (ep u) (ep w)) = true)
    (hrej0 : circuitFun (N + N) C (Fin.append (z0 N) (ep w)) = false)
    (hH1 : 0 < DP N (Vw N C sg) (Vw N C sg).output → 0 < DL N (Vw N C sg) (Vw N C sg).output →
      ∃ (X : Circuit) (ph : ℕ → ℕ) (H : Set ℕ),
        (∀ h ∈ H, ∀ x : Fin N → Bool,
          Relation.ReflTransGen (PR N (Vw N C sg) x) h (Vw N C sg).output) ∧
        (∀ h, Fr N (Vw N C sg) h → h ∉ H → ∀ x : Fin N → Bool,
          ((X.wires (List.ofFn x)).getD (ph h) false = true ↔
            Relation.ReflTransGen (PR N (Vw N C sg) x) h (Vw N C sg).output)) ∧
        ∀ x y : Fin N → Bool, (circuitFun (N + N) (Vw N C sg) (Fin.append x y) = true ↔
          (circuitFun (N + N) (Vw N C sg) (Fin.append x (fun _ => false)) = true ∨
            ∃ h, Fr N (Vw N C sg) h ∧ W N (Vw N C sg) (fun _ => false) y h = true ∧
              (h ∈ H ∨ (X.wires (List.ofFn x)).getD (ph h) false = true))))
    (hV3 : ∀ g, DP N (Vw N C sg) g = 0 → 0 < DL N (Vw N C sg) g → ∃ E : Finset ℕ,
      (∀ h ∈ E, DP N C h = 0 ∧ Relation.ReflTransGen (OV N C (Vw N C sg)) h g) ∧
      ∀ y : Fin N → Bool, (W N (Vw N C sg) (fun _ => false) y g = true ↔
        ∃ h ∈ E, W N C (fun _ => false) y h = true))
    (hH3b : ∀ (g h : ℕ) (x : Fin N → Bool), Fr N (Vw N C sg) g → DP N C h = 0 →
      Relation.ReflTransGen (OV N C (Vw N C sg)) h g →
      Fr N (Cor N C) h ∧ (Relation.ReflTransGen (PR N (Vw N C sg) x) g (Vw N C sg).output →
        Relation.ReflTransGen (PR N (Cor N C) x) h (Cor N C).output)) :
    circuitFun (N + N) (Vw N C sg) (Fin.append (ep u) (z0 N)) = true ∨
      ∃ h, Wit N C (Vw N C sg) u w h := by
  by_cases hfree : circuitFun (N + N) (Vw N C sg) (Fin.append (ep u) (z0 N)) = true
  · exact Or.inl hfree
  right
  by_cases hL : DL N (Vw N C sg) (Vw N C sg).output = 0
  · exfalso
    apply hfree
    rw [cf_eq] at hacc ⊢
    rw [← W_indL N (Vw N C sg) hVrb (ep u) (ep w) (z0 N) _ hL]
    exact hacc
  by_cases hP : DP N (Vw N C sg) (Vw N C sg).output = 0
  · obtain ⟨E, hE1, hE2⟩ := hV3 _ hP (Nat.pos_of_ne_zero hL)
    have h1 : W N (Vw N C sg) (fun _ => false) (ep w) (Vw N C sg).output = true := by
      rw [← W_indP N (Vw N C sg) hVrb (ep u) (fun _ => false) (ep w) _ hP]
      exact hacc
    obtain ⟨h, hhE, hhw⟩ := (hE2 (ep w)).mp h1
    obtain ⟨hdp, hpath⟩ := hE1 h hhE
    have hy : ∀ y, W N C (z0 N) y h = true →
        circuitFun (N + N) (Vw N C sg) (Fin.append (ep u) y) = true := by
      intro y hy
      rw [cf_eq, W_indP N (Vw N C sg) hVrb (ep u) (fun _ => false) y _ hP]
      exact (hE2 y).mpr ⟨h, hhE, hy⟩
    have hne : h ≠ C.output := by
      intro heq
      rw [cf_eq] at hrej0
      rw [heq] at hhw
      have : W N C (z0 N) (ep w) C.output = true := hhw
      rw [this] at hrej0
      cases hrej0
    have hc := case_c N C hC hrb sg (ep u) (ep w) h hdp hhw hne hpath
    exact ⟨h, hdp, hhw, hc.1, hc.2, hy⟩
  · obtain ⟨X, ph, H, h4, h5, h6⟩ := hH1 (Nat.pos_of_ne_zero hP) (Nat.pos_of_ne_zero hL)
    rcases (h6 (ep u) (ep w)).mp hacc with h0 | ⟨g, hgfr, hgw, hgH⟩
    · exact absurd h0 hfree
    have hgpath : Relation.ReflTransGen (PR N (Vw N C sg) (ep u)) g (Vw N C sg).output := by
      by_cases hH : g ∈ H
      · exact h4 g hH (ep u)
      · rcases hgH with hH' | hX
        · exact absurd hH' hH
        · exact (h5 g hgfr hH (ep u)).mp hX
    obtain ⟨E, hE1, hE2⟩ := hV3 g hgfr.1 hgfr.2.1
    obtain ⟨h, hhE, hhw⟩ := (hE2 (ep w)).mp hgw
    obtain ⟨hdp, hpath⟩ := hE1 h hhE
    obtain ⟨hfr, hp⟩ := hH3b g h (ep u) hgfr hdp hpath
    refine ⟨h, hdp, hhw, hfr, hp hgpath, ?_⟩
    intro y hy
    exact (h6 (ep u) y).mpr (Or.inr ⟨g, hgfr, (hE2 y).mpr ⟨h, hhE, hy⟩, hgH⟩)

def Ls {N : ℕ} (Wf : Finset (Fin N)) (val : ℕ → Finset (Fin N) → Bool) (r : ℕ) :
    Finset (Fin N) :=
  Wf.filter (fun l => val r {l} = true)

theorem ne_single {N : ℕ} (F : Finset (Fin N)) (w : Fin N) (hw : w ∈ F) (hne : F ≠ {w}) :
    ∃ w' ∈ F, w' ≠ w := by
  by_contra hc
  push_neg at hc
  exact hne (Finset.eq_singleton_iff_unique_mem.mpr ⟨hw, hc⟩)

theorem q_good {N : ℕ} (Wf : Finset (Fin N)) (val : ℕ → Finset (Fin N) → Bool) (P : ℕ → Prop)
    (w : Fin N) (b : ℕ)
    (hQ : P b ∨ ∃ l : Fin N, ∀ Y, val b Y = decide (l ∈ Y))
    (hw : w ∈ Ls Wf val b) (hw' : ∃ w' ∈ Ls Wf val b, w' ≠ w) : P b := by
  rcases hQ with h | ⟨l, hl⟩
  · exact h
  · exfalso
    obtain ⟨w', hw'1, hw'2⟩ := hw'
    have e1 := (Finset.mem_filter.mp hw).2
    have e2 := (Finset.mem_filter.mp hw'1).2
    rw [hl] at e1 e2
    have a1 : l = w := by simpa using e1
    have a2 : l = w' := by simpa using e2
    exact hw'2 (a2.symm.trans a1)

theorem descent {N : ℕ} (I : Fin N → Fin N → Prop) (Wf : Finset (Fin N)) (u w : Fin N)
    (val : ℕ → Finset (Fin N) → Bool) (P isAnd : ℕ → Prop) (k0 k1 : ℕ → ℕ)
    (hmono : ∀ r (Y Y' : Finset (Fin N)), Y ⊆ Y' → val r Y = true → val r Y' = true)
    (hkid : ∀ r, P r → k0 r < r ∧ k1 r < r ∧
      (P (k0 r) ∨ ∃ l : Fin N, ∀ Y, val (k0 r) Y = decide (l ∈ Y)) ∧
      (P (k1 r) ∨ ∃ l : Fin N, ∀ Y, val (k1 r) Y = decide (l ∈ Y)) ∧
      (isAnd r → ∀ Y, val r Y = (val (k0 r) Y && val (k1 r) Y)) ∧
      (¬ isAnd r → ∀ Y, val r Y = (val (k0 r) Y || val (k1 r) Y)))
    (hno : ∀ r, P r → w ∈ Ls Wf val r → (∃ w' ∈ Ls Wf val r, w' ≠ w) →
      (∀ l ∈ Ls Wf val r, I u l) → ¬ isAnd r →
      Ls Wf val (k0 r) ≠ {w} ∧ Ls Wf val (k1 r) ≠ {w}) :
    ∀ (n : ℕ) (R : Finset ℕ),
      (∀ r ∈ R, P r ∧ w ∈ Ls Wf val r ∧ ∃ w' ∈ Ls Wf val r, w' ≠ w) →
      (∀ r ∈ R, (∀ l ∈ Ls Wf val r, I u l) → r < n) →
      ∃ (A : Finset ℕ) (Y : Finset (Fin N)),
        (∀ a ∈ A, (P a ∧ w ∈ Ls Wf val a ∧ ∃ w' ∈ Ls Wf val a, w' ≠ w) ∧
          (∀ l ∈ Ls Wf val a, I u l) ∧ isAnd a ∧ a < n) ∧
        Y ⊆ Wf ∧ (∀ l ∈ Y, ¬ I u l) ∧ Y.card ≤ A.card + R.card ∧ ∀ r ∈ R, val r Y = true := by
  classical
  intro n
  induction n with
  | zero =>
    intro R hG hC
    have base : ∀ R : Finset ℕ, (∀ r ∈ R, ∃ l ∈ Wf, ¬ I u l ∧ val r {l} = true) →
        ∃ Y : Finset (Fin N), Y ⊆ Wf ∧ (∀ l ∈ Y, ¬ I u l) ∧ Y.card ≤ R.card ∧
          ∀ r ∈ R, val r Y = true := by
      intro R
      induction R using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨∅, by simp, by simp, by simp, by simp⟩
      | insert a s ha ih =>
        intro h
        obtain ⟨Y, h1, h2, h3, h4⟩ := ih (fun r hr => h r (Finset.mem_insert_of_mem hr))
        obtain ⟨l, hl, hIl, hv⟩ := h a (Finset.mem_insert_self _ _)
        refine ⟨insert l Y, Finset.insert_subset hl h1, ?_, ?_, ?_⟩
        · intro l' hl'
          rcases Finset.mem_insert.mp hl' with rfl | h'
          · exact hIl
          · exact h2 _ h'
        · rw [Finset.card_insert_of_notMem ha]
          exact (Finset.card_insert_le _ _).trans (by omega)
        · intro r hr
          rcases Finset.mem_insert.mp hr with rfl | h'
          · exact hmono _ _ _ (by simp) hv
          · exact hmono _ _ _ (Finset.subset_insert _ _) (h4 r h')
    obtain ⟨Y, h1, h2, h3, h4⟩ := base R (by
      intro r hr
      have hnc : ¬ (∀ l ∈ Ls Wf val r, I u l) := fun hc => by
        have := hC r hr hc
        omega
      push_neg at hnc
      obtain ⟨l, hl, hIl⟩ := hnc
      exact ⟨l, (Finset.mem_filter.mp hl).1, hIl, (Finset.mem_filter.mp hl).2⟩)
    exact ⟨∅, Y, by simp, h1, h2, by simpa using h3, h4⟩
  | succ n ih =>
    intro R hG hC
    by_cases hn : n ∈ R ∧ ∀ l ∈ Ls Wf val n, I u l
    · obtain ⟨hnR, hnC⟩ := hn
      have hGn := hG n hnR
      obtain ⟨hk0, hk1, hQ0, hQ1, hand, hor⟩ := hkid n hGn.1
      obtain ⟨w', hw'1, hw'2⟩ := hGn.2.2
      have ew := (Finset.mem_filter.mp hGn.2.1)
      have ew' := (Finset.mem_filter.mp hw'1)
      have hcard : (R.erase n).card + 1 = R.card := by
        rw [Finset.card_erase_of_mem hnR]
        have := Finset.card_pos.mpr ⟨n, hnR⟩
        omega
      by_cases ha : isAnd n
      · have e1 := ew.2
        have e2 := ew'.2
        rw [hand ha, Bool.and_eq_true] at e1 e2
        have g0 : P (k0 n) ∧ w ∈ Ls Wf val (k0 n) ∧ ∃ w' ∈ Ls Wf val (k0 n), w' ≠ w := by
          have a1 : w ∈ Ls Wf val (k0 n) := Finset.mem_filter.mpr ⟨ew.1, e1.1⟩
          have a2 : ∃ w' ∈ Ls Wf val (k0 n), w' ≠ w :=
            ⟨w', Finset.mem_filter.mpr ⟨ew'.1, e2.1⟩, hw'2⟩
          exact ⟨q_good Wf val P w _ hQ0 a1 a2, a1, a2⟩
        have g1 : P (k1 n) ∧ w ∈ Ls Wf val (k1 n) ∧ ∃ w' ∈ Ls Wf val (k1 n), w' ≠ w := by
          have a1 : w ∈ Ls Wf val (k1 n) := Finset.mem_filter.mpr ⟨ew.1, e1.2⟩
          have a2 : ∃ w' ∈ Ls Wf val (k1 n), w' ≠ w :=
            ⟨w', Finset.mem_filter.mpr ⟨ew'.1, e2.2⟩, hw'2⟩
          exact ⟨q_good Wf val P w _ hQ1 a1 a2, a1, a2⟩
        obtain ⟨A, Y, hA, hY1, hY2, hY3, hY4⟩ :=
          ih (insert (k0 n) (insert (k1 n) (R.erase n))) (by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact g0
            · rcases Finset.mem_insert.mp hr with rfl | hr
              · exact g1
              · exact hG r (Finset.mem_of_mem_erase hr)) (by
            intro r hr hc
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact hk0
            · rcases Finset.mem_insert.mp hr with rfl | hr
              · exact hk1
              · have := hC r (Finset.mem_of_mem_erase hr) hc
                have := Finset.ne_of_mem_erase hr
                omega)
        have hnA : n ∉ A := fun hc => by
          have := (hA n hc).2.2.2
          omega
        refine ⟨insert n A, Y, ?_, hY1, hY2, ?_, ?_⟩
        · intro a ha'
          rcases Finset.mem_insert.mp ha' with rfl | ha'
          · exact ⟨hGn, hnC, ha, by omega⟩
          · obtain ⟨b1, b2, b3, b4⟩ := hA a ha'
            exact ⟨b1, b2, b3, by omega⟩
        · rw [Finset.card_insert_of_notMem hnA]
          have c1 := Finset.card_insert_le (k0 n) (insert (k1 n) (R.erase n))
          have c2 := Finset.card_insert_le (k1 n) (R.erase n)
          omega
        · intro r hr
          by_cases hrn : r = n
          · rw [hrn, hand ha, Bool.and_eq_true]
            exact ⟨hY4 _ (Finset.mem_insert_self _ _),
              hY4 _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
          · exact hY4 r (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨hrn, hr⟩)))
      · have e1 := ew.2
        rw [hor ha, Bool.or_eq_true] at e1
        obtain ⟨hn0, hn1⟩ := hno n hGn.1 hGn.2.1 hGn.2.2 hnC ha
        have key : ∃ b, b < n ∧ (P b ∧ w ∈ Ls Wf val b ∧ ∃ w' ∈ Ls Wf val b, w' ≠ w) ∧
            ∀ Y, val b Y = true → val n Y = true := by
          rcases e1 with e | e
          · have a1 : w ∈ Ls Wf val (k0 n) := Finset.mem_filter.mpr ⟨ew.1, e⟩
            have a2 := ne_single _ w a1 hn0
            refine ⟨k0 n, hk0, ⟨q_good Wf val P w _ hQ0 a1 a2, a1, a2⟩, ?_⟩
            intro Y hY
            rw [hor ha, Bool.or_eq_true]
            exact Or.inl hY
          · have a1 : w ∈ Ls Wf val (k1 n) := Finset.mem_filter.mpr ⟨ew.1, e⟩
            have a2 := ne_single _ w a1 hn1
            refine ⟨k1 n, hk1, ⟨q_good Wf val P w _ hQ1 a1 a2, a1, a2⟩, ?_⟩
            intro Y hY
            rw [hor ha, Bool.or_eq_true]
            exact Or.inr hY
        obtain ⟨b, hb, gb, hbv⟩ := key
        obtain ⟨A, Y, hA, hY1, hY2, hY3, hY4⟩ :=
          ih (insert b (R.erase n)) (by
            intro r hr
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact gb
            · exact hG r (Finset.mem_of_mem_erase hr)) (by
            intro r hr hc
            rcases Finset.mem_insert.mp hr with rfl | hr
            · exact hb
            · have := hC r (Finset.mem_of_mem_erase hr) hc
              have := Finset.ne_of_mem_erase hr
              omega)
        refine ⟨A, Y, ?_, hY1, hY2, ?_, ?_⟩
        · intro a ha'
          obtain ⟨b1, b2, b3, b4⟩ := hA a ha'
          exact ⟨b1, b2, b3, by omega⟩
        · have c1 := Finset.card_insert_le b (R.erase n)
          omega
        · intro r hr
          by_cases hrn : r = n
          · rw [hrn]
            exact hbv Y (hY4 _ (Finset.mem_insert_self _ _))
          · exact hY4 r (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hrn, hr⟩))
    · obtain ⟨A, Y, hA, hY1, hY2, hY3, hY4⟩ := ih R hG (by
        intro r hr hc
        have := hC r hr hc
        have hne : r ≠ n := by
          rintro rfl
          exact hn ⟨hr, hc⟩
        omega)
      refine ⟨A, Y, ?_, hY1, hY2, hY3, hY4⟩
      intro a ha'
      obtain ⟨b1, b2, b3, b4⟩ := hA a ha'
      exact ⟨b1, b2, b3, by omega⟩

def val (N : ℕ) (C : Circuit) (r : ℕ) (Y : Finset (Fin N)) : Bool :=
  W N C (fun _ => false) (ind Y) r

def PG (N : ℕ) (C : Circuit) (r : ℕ) : Prop :=
  ∃ j < C.gates.length, r = N + N + j ∧ DP N C r = 0

def isA (N : ℕ) (C : Circuit) (r : ℕ) : Prop :=
  (gateAt C (r - (N + N))).op = GateOp.and

def kd (N : ℕ) (C : Circuit) (i : ℕ) (r : ℕ) : ℕ :=
  (gateAt C (r - (N + N))).inputs.getD i 0

theorem val_mono (N : ℕ) (C : Circuit) (hC : AO2 C) (r : ℕ) (Y Y' : Finset (Fin N))
    (h : Y ⊆ Y') (hv : val N C r Y = true) : val N C r Y' = true := by
  unfold val at hv ⊢
  refine cf_mono_y N C hC _ _ _ ?_ r hv
  intro l hl
  have : l ∈ Y := by simpa [ind] using hl
  simpa [ind] using h this

theorem pf_class (N : ℕ) (C : Circuit) (a : ℕ) (ha : a < N + N + C.gates.length)
    (hda : DP N C a = 0) :
    PG N C a ∨ ∃ l : Fin N, ∀ Y, val N C a Y = decide (l ∈ Y) := by
  by_cases h1 : a < N
  · exfalso
    have h3 := D_in (N + N) (Finset.range N) C a (by omega)
    rw [ifp (Finset.mem_range.mpr h1)] at h3
    have h' : DP N C a = 1 := h3
    omega
  · by_cases h2 : a < N + N
    · right
      refine ⟨⟨a - N, by omega⟩, fun Y => ?_⟩
      have h3 := V_in C (List.ofFn (Fin.append (fun _ : Fin N => false) (ind Y))) a
        (by simp; omega)
      have h4 : val N C a Y = (List.ofFn (Fin.append (fun _ : Fin N => false) (ind Y))).getD a false := h3
      rw [h4, app_getD, difn h1, difp (show a - N < N by omega)]
    · left
      exact ⟨a - (N + N), by omega, by omega, hda⟩

theorem kid_facts (N : ℕ) (C : Circuit) (hC : AO2 C) (hrb : ReadsBack (N + N) C) (r : ℕ)
    (hr : PG N C r) :
    kd N C 0 r < r ∧ kd N C 1 r < r ∧
      (PG N C (kd N C 0 r) ∨ ∃ l : Fin N, ∀ Y, val N C (kd N C 0 r) Y = decide (l ∈ Y)) ∧
      (PG N C (kd N C 1 r) ∨ ∃ l : Fin N, ∀ Y, val N C (kd N C 1 r) Y = decide (l ∈ Y)) ∧
      (isA N C r → ∀ Y, val N C r Y = (val N C (kd N C 0 r) Y && val N C (kd N C 1 r) Y)) ∧
      (¬ isA N C r → ∀ Y, val N C r Y = (val N C (kd N C 0 r) Y || val N C (kd N C 1 r) Y)) := by
  obtain ⟨j, hj, rfl, hd⟩ := hr
  have hsub : N + N + j - (N + N) = j := by omega
  have hg := hC _ (gateAt_mem C j hj)
  obtain ⟨b, c, hbc⟩ : ∃ b c, (gateAt C j).inputs = [b, c] := by
    rcases hin : (gateAt C j).inputs with _ | ⟨b, _ | ⟨c, _ | ⟨d, t⟩⟩⟩
    · rw [hin] at hg
      simp at hg
    · rw [hin] at hg
      simp at hg
    · exact ⟨b, c, rfl⟩
    · rw [hin] at hg
      simp at hg
  have hk0 : kd N C 0 (N + N + j) = b := by simp [kd, hsub, hbc]
  have hk1 : kd N C 1 (N + N + j) = c := by simp [kd, hsub, hbc]
  have hb : b < N + N + j := hrb j hj b (by rw [hbc]; simp)
  have hc : c < N + N + j := hrb j hj c (by rw [hbc]; simp)
  have hz := (D_zero_iff (N + N) (Finset.range N) C hrb j hj).mp hd
  have hdb : DP N C b = 0 := hz b (by rw [hbc]; simp)
  have hdc : DP N C c = 0 := hz c (by rw [hbc]; simp)
  have hev : ∀ Y, val N C (N + N + j) Y =
      (gateAt C j).op.eval [val N C b Y, val N C c Y] := by
    intro Y
    unfold val
    rw [W_gate N C hrb _ _ j hj, hbc, List.map_cons, List.map_cons, List.map_nil]
  rw [hk0, hk1]
  refine ⟨hb, hc, pf_class N C b (by omega) hdb, pf_class N C c (by omega) hdc, ?_, ?_⟩
  · intro ha Y
    unfold isA at ha
    rw [hsub] at ha
    rw [hev, ha]
    simp [GateOp.eval]
  · intro ha Y
    unfold isA at ha
    rw [hsub] at ha
    have ho : (gateAt C j).op = GateOp.or := by
      rcases hg.1 with h | h
      · exact absurd h ha
      · exact h
    rw [hev, ho]
    simp [GateOp.eval]

theorem Ls_conc (N : ℕ) (C : Circuit) (Wf : Finset (Fin N)) (h : ℕ) :
    Wf.filter (fun l => W N C (fun _ => false) (fun a => decide (a = l)) h = true) =
      Ls Wf (val N C) h := by
  unfold Ls
  apply Finset.filter_congr
  intro l _
  unfold val
  rw [ind_single]

def Pool (N : ℕ) (C : Circuit) (Wf : Finset (Fin N)) (u w : Fin N) : Prop :=
  ∃ h, Fr N (Cor N C) h ∧
    Wf.filter (fun l => W N C (fun _ => false) (fun a => decide (a = l)) h = true) = {w} ∧
    Relation.ReflTransGen (PR N (Cor N C) (fun a => decide (a = u))) h (Cor N C).output

theorem wit_good (N : ℕ) (C V : Circuit) (Wf : Finset (Fin N)) (u w : Fin N) (hw : w ∈ Wf)
    (h : ℕ) (hwit : Wit N C V u w h) (hnp : ¬ Pool N C Wf u w) :
    PG N C h ∧ w ∈ Ls Wf (val N C) h ∧ ∃ w' ∈ Ls Wf (val N C) h, w' ≠ w := by
  obtain ⟨hdp, hhw, hfr, hpath, -⟩ := hwit
  have a1 : w ∈ Ls Wf (val N C) h := by
    rw [← Ls_conc]
    exact Finset.mem_filter.mpr ⟨hw, hhw⟩
  have hne : Ls Wf (val N C) h ≠ {w} := by
    intro heq
    apply hnp
    refine ⟨h, hfr, ?_, hpath⟩
    rw [Ls_conc]
    exact heq
  have a2 := ne_single _ w a1 hne
  have hlt : h < N + N + C.gates.length := by
    by_contra hc
    have h3 := V_out C (List.ofFn (Fin.append (z0 N) (ep w))) h (by simp; omega)
    have h4 : W N C (z0 N) (ep w) h = false := h3
    rw [h4] at hhw
    cases hhw
  exact ⟨q_good Wf (val N C) (PG N C) w h (pf_class N C h hlt hdp) a1 a2, a1, a2⟩

noncomputable def sgA (A : Finset ℕ) : ℕ → Fin 2 := fun j =>
  @ite (Fin 2) (j ∈ A) (Classical.propDecidable _) 1 0

theorem vw_congr (N : ℕ) (C : Circuit) (sg sg' : ℕ → Fin 2)
    (h : ∀ j < C.gates.length, Cross N C j → sg j = sg' j) : Vw N C sg = Vw N C sg' := by
  unfold Vw
  refine congrArg (fun l => Circuit.mk l C.output) (congrArg List.ofFn (funext fun j => ?_))
  try dsimp only
  split_ifs with hc
  · rw [h j.val j.isLt hc]
  · rfl

theorem vw_class (N : ℕ) (C : Circuit) (T : Finset ℕ)
    (hT : ∀ j, j ∈ T ↔ j < C.gates.length ∧ Cross N C j) (sg : ℕ → Fin 2) :
    ∃ A ∈ T.powerset, Vw N C sg = Vw N C (sgA A) := by
  classical
  refine ⟨T.filter (fun j => sg j = 1), Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  apply vw_congr
  intro j hj hc
  unfold sgA
  split_ifs with hm
  · exact (Finset.mem_filter.mp hm).2
  · apply Fin.ext
    have h2 : (sg j).val ≠ 1 := fun h =>
      hm (Finset.mem_filter.mpr ⟨(hT j).mpr ⟨hj, hc⟩, Fin.ext h⟩)
    have h3 := (sg j).isLt
    show (sg j).val = 0
    omega

theorem pair_alt (N K m D : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (S Wf : Finset (Fin N)) (hC : AO2 C) (hrb : ReadsBack (N + N) C)
    (hm : Set.ncard {j : ℕ | j < C.gates.length ∧ Cross N C j} ≤ m)
    (hrej : ∀ X Y : Finset (Fin N), X ⊆ S → Y ⊆ Wf → Y.card ≤ K →
      (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
      circuitFun (N + N) C (Fin.append (ind X) (ind Y)) = false)
    (h2m : 2 ^ m + D = K + 1)
    (hV1 : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∀ sg : ℕ → Fin 2, circuitFun (N + N) (Vw N C sg) z = true)
    (hVao : ∀ sg : ℕ → Fin 2, AO2 (Vw N C sg))
    (u w : Fin N) (hu : u ∈ S) (hw : w ∈ Wf)
    (hnp : ¬ Pool N C Wf u w)
    (hwit : ∀ sg : ℕ → Fin 2,
      circuitFun (N + N) (Vw N C sg) (Fin.append (ep u) (z0 N)) = true ∨
        ∃ h, Wit N C (Vw N C sg) u w h) :
    (∃ r, (PG N C r ∧ w ∈ Ls Wf (val N C) r ∧ ∃ w' ∈ Ls Wf (val N C) r, w' ≠ w) ∧
      (∀ l ∈ Ls Wf (val N C) r, I u l) ∧ ¬ isA N C r ∧
      (Ls Wf (val N C) (kd N C 0 r) = {w} ∨ Ls Wf (val N C) (kd N C 1 r) = {w})) ∨
    ∃ A : Finset ℕ, D ≤ A.card ∧ ∀ a ∈ A,
      (PG N C a ∧ w ∈ Ls Wf (val N C) a ∧ ∃ w' ∈ Ls Wf (val N C) a, w' ≠ w) ∧
      (∀ l ∈ Ls Wf (val N C) a, I u l) ∧ isA N C a := by
  classical
  by_cases hor : ∃ r, (PG N C r ∧ w ∈ Ls Wf (val N C) r ∧ ∃ w' ∈ Ls Wf (val N C) r, w' ≠ w) ∧
      (∀ l ∈ Ls Wf (val N C) r, I u l) ∧ ¬ isA N C r ∧
      (Ls Wf (val N C) (kd N C 0 r) = {w} ∨ Ls Wf (val N C) (kd N C 1 r) = {w})
  · exact Or.inl hor
  right
  have hch : ∀ sg : ℕ → Fin 2, ∃ h,
      circuitFun (N + N) (Vw N C sg) (Fin.append (ep u) (z0 N)) = true ∨
        Wit N C (Vw N C sg) u w h := by
    intro sg
    rcases hwit sg with hf | ⟨h, hh⟩
    · exact ⟨0, Or.inl hf⟩
    · exact ⟨h, Or.inr hh⟩
  choose f hf using hch
  let T : Finset ℕ := (Finset.range C.gates.length).filter (fun j => Cross N C j)
  have hT : ∀ j, j ∈ T ↔ j < C.gates.length ∧ Cross N C j := by
    intro j
    simp [T]
  have hTc : T.card ≤ m := by
    rw [ncard_eq] at hm
    exact hm
  let R : Finset ℕ := (T.powerset.filter (fun A =>
    ¬ circuitFun (N + N) (Vw N C (sgA A)) (Fin.append (ep u) (z0 N)) = true)).image
      (fun A => f (sgA A))
  have hRc : R.card ≤ 2 ^ m := by
    refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by omega) hTc
  have hRg : ∀ r ∈ R, PG N C r ∧ w ∈ Ls Wf (val N C) r ∧ ∃ w' ∈ Ls Wf (val N C) r, w' ≠ w := by
    intro r hr
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hr
    have hnf := (Finset.mem_filter.mp hA).2
    rcases hf (sgA A) with h1 | h1
    · exact absurd h1 hnf
    · exact wit_good N C _ Wf u w hw _ h1 hnp
  obtain ⟨A, Y, hA, hY1, hY2, hY3, hY4⟩ := descent I Wf u w (val N C) (PG N C) (isA N C)
    (kd N C 0) (kd N C 1) (fun r Y Y' h hv => val_mono N C hC r Y Y' h hv)
    (fun r hr => kid_facts N C hC hrb r hr)
    (fun r h1 h2 h3 h4 h5 =>
      ⟨fun h0 => hor ⟨r, ⟨h1, h2, h3⟩, h4, h5, Or.inl h0⟩,
       fun h0 => hor ⟨r, ⟨h1, h2, h3⟩, h4, h5, Or.inr h0⟩⟩)
    (N + N + C.gates.length) R hRg (by
      intro r hr _
      obtain ⟨j, hj, rfl, -⟩ := (hRg r hr).1
      omega)
  refine ⟨A, ?_, fun a ha => ⟨(hA a ha).1, (hA a ha).2.1, (hA a ha).2.2.1⟩⟩
  by_contra hlt
  have hYK : Y.card ≤ K := by
    have hRc' : R.card ≤ 2 ^ m := hRc
    generalize 2 ^ m = pp at h2m hRc'
    omega
  have hr := hrej {u} Y (Finset.singleton_subset_iff.mpr hu) hY1 hYK (by
    intro p hp l hl
    rw [Finset.mem_singleton.mp hp]
    exact hY2 l hl)
  rw [ind_single] at hr
  have hacc : circuitFun (N + N) C (Fin.append (ep u) (ind Y)) = true := by
    rw [hV1]
    intro sg
    obtain ⟨A0, hA0, heq⟩ := vw_class N C T hT sg
    rw [heq]
    by_cases hfree : circuitFun (N + N) (Vw N C (sgA A0)) (Fin.append (ep u) (z0 N)) = true
    · rw [cf_eq] at hfree ⊢
      exact cf_mono_y N _ (hVao _) _ _ _ (fun l hl => by simp at hl) _ hfree
    · have hmem : f (sgA A0) ∈ R :=
        Finset.mem_image.mpr ⟨A0, Finset.mem_filter.mpr ⟨hA0, hfree⟩, rfl⟩
      rcases hf (sgA A0) with h1 | h1
      · exact absurd h1 hfree
      · exact h1.2.2.2.2 _ (hY4 _ hmem)
  rw [hacc] at hr
  cases hr

def Gp (N : ℕ) (C : Circuit) (Wf : Finset (Fin N)) (I : Fin N → Fin N → Prop) (u w : Fin N)
    (r : ℕ) : Prop :=
  (PG N C r ∧ w ∈ Ls Wf (val N C) r ∧ ∃ w' ∈ Ls Wf (val N C) r, w' ≠ w) ∧
    (∀ l ∈ Ls Wf (val N C) r, I u l)

theorem gp_point (N : ℕ) (C : Circuit) (Wf : Finset (Fin N)) (I : Fin N → Fin N → Prop)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (u u' w w' : Fin N) (r : ℕ) (h : Gp N C Wf I u w r) (h' : Gp N C Wf I u' w' r) : u = u' := by
  obtain ⟨⟨-, hw, w0, hw0, hne⟩, hc⟩ := h
  obtain ⟨-, hc'⟩ := h'
  rcases two_lines N I hu u u' w w0 (hc w hw) (hc' w hw) (hc w0 hw0) (hc' w0 hw0) with e | e
  · exact e
  · exact absurd e.symm hne

theorem core (q N K m D : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (S Wf : Finset (Fin N)) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb)
    (hC : AO2 C) (hrb : ReadsBack (N + N) C)
    (hm : Set.ncard {j : ℕ | j < C.gates.length ∧ Cross N C j} ≤ m)
    (hacc : ∀ p ∈ S, ∀ l ∈ Wf, I p l →
      circuitFun (N + N) C (Fin.append (ind {p}) (ind {l})) = true)
    (hrej : ∀ X Y : Finset (Fin N), X ⊆ S → Y ⊆ Wf → Y.card ≤ K →
      (∀ p ∈ X, ∀ l ∈ Y, ¬ I p l) →
      circuitFun (N + N) C (Fin.append (ind X) (ind Y)) = false)
    (h2m : 2 ^ m + D = K + 1) (hD : 1 ≤ D)
    (hV1 : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∀ sg : ℕ → Fin 2, circuitFun (N + N) (Vw N C sg) z = true)
    (hVao : ∀ sg : ℕ → Fin 2, AO2 (Vw N C sg) ∧ ReadsBack (N + N) (Vw N C sg))
    (hH1 : ∀ sg : ℕ → Fin 2,
      0 < DP N (Vw N C sg) (Vw N C sg).output → 0 < DL N (Vw N C sg) (Vw N C sg).output →
      ∃ (X : Circuit) (ph : ℕ → ℕ) (H : Set ℕ),
        (∀ h ∈ H, ∀ x : Fin N → Bool,
          Relation.ReflTransGen (PR N (Vw N C sg) x) h (Vw N C sg).output) ∧
        (∀ h, Fr N (Vw N C sg) h → h ∉ H → ∀ x : Fin N → Bool,
          ((X.wires (List.ofFn x)).getD (ph h) false = true ↔
            Relation.ReflTransGen (PR N (Vw N C sg) x) h (Vw N C sg).output)) ∧
        ∀ x y : Fin N → Bool, (circuitFun (N + N) (Vw N C sg) (Fin.append x y) = true ↔
          (circuitFun (N + N) (Vw N C sg) (Fin.append x (fun _ => false)) = true ∨
            ∃ h, Fr N (Vw N C sg) h ∧ W N (Vw N C sg) (fun _ => false) y h = true ∧
              (h ∈ H ∨ (X.wires (List.ofFn x)).getD (ph h) false = true))))
    (hV3 : ∀ (sg : ℕ → Fin 2) (g : ℕ), DP N (Vw N C sg) g = 0 → 0 < DL N (Vw N C sg) g →
      ∃ E : Finset ℕ,
      (∀ h ∈ E, DP N C h = 0 ∧ Relation.ReflTransGen (OV N C (Vw N C sg)) h g) ∧
      ∀ y : Fin N → Bool, (W N (Vw N C sg) (fun _ => false) y g = true ↔
        ∃ h ∈ E, W N C (fun _ => false) y h = true))
    (hH3b : ∀ (sg : ℕ → Fin 2) (g h : ℕ) (x : Fin N → Bool), Fr N (Vw N C sg) g →
      DP N C h = 0 → Relation.ReflTransGen (OV N C (Vw N C sg)) h g →
      Fr N (Cor N C) h ∧ (Relation.ReflTransGen (PR N (Vw N C sg) x) g (Vw N C sg).output →
        Relation.ReflTransGen (PR N (Cor N C) x) h (Cor N C).output)) :
    D * ((S ×ˢ Wf).filter (fun pl => I pl.1 pl.2)).card ≤
      max (2 * D) (q + 1) *
        Set.ncard {j : ℕ | j < C.gates.length ∧ DP N C (N + N + j) = 0} +
      D * ∑ w ∈ Wf, Set.ncard {u : Fin N | u ∈ S ∧ Pool N C Wf u w} := by
  classical
  have hK : 1 ≤ K := by
    have := Nat.one_le_two_pow (n := m)
    omega
  have hpair : ∀ u ∈ S, ∀ w ∈ Wf, I u w → ¬ Pool N C Wf u w →
      (∃ r, Gp N C Wf I u w r ∧ ¬ isA N C r ∧
        (Ls Wf (val N C) (kd N C 0 r) = {w} ∨ Ls Wf (val N C) (kd N C 1 r) = {w})) ∨
      ∃ A : Finset ℕ, D ≤ A.card ∧ ∀ a ∈ A, Gp N C Wf I u w a ∧ isA N C a := by
    intro u hu' w hw hI hnp
    have hCacc : circuitFun (N + N) C (Fin.append (ep u) (ep w)) = true := by
      have h0 := hacc u hu' w hw hI
      rw [ind_single, ind_single] at h0
      exact h0
    have hrej0 : circuitFun (N + N) C (Fin.append (z0 N) (ep w)) = false := by
      have h0 := hrej ∅ {w} (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr hw)
        (by simpa using hK) (by simp)
      rw [ind_empty, ind_single] at h0
      exact h0
    rcases pair_alt N K m D I C S Wf hC hrb hm hrej h2m hV1 (fun sg => (hVao sg).1) u w hu' hw
      hnp (fun sg => view_wit N C hC hrb sg u w (hVao sg).2 ((hV1 _).mp hCacc sg) hrej0
        (hH1 sg) (hV3 sg) (hH3b sg)) with ⟨r, h1, h2, h3, h4⟩ | ⟨A, hA1, hA2⟩
    · exact Or.inl ⟨r, ⟨h1, h2⟩, h3, h4⟩
    · exact Or.inr ⟨A, hA1, fun a ha => ⟨⟨(hA2 a ha).1, (hA2 a ha).2.1⟩, (hA2 a ha).2.2⟩⟩
  obtain ⟨INC, hINC⟩ : ∃ X, X = (S ×ˢ Wf).filter (fun pl => I pl.1 pl.2) := ⟨_, rfl⟩
  obtain ⟨PF, hPF⟩ : ∃ X, X = (Finset.range C.gates.length).filter
    (fun j => DP N C (N + N + j) = 0) := ⟨_, rfl⟩
  obtain ⟨TA, hTA⟩ : ∃ X, X = PF.filter (fun j => isA N C (N + N + j)) := ⟨_, rfl⟩
  obtain ⟨TO, hTO⟩ : ∃ X, X = PF.filter (fun j => ¬ isA N C (N + N + j)) := ⟨_, rfl⟩
  obtain ⟨Cov, hCov⟩ : ∃ X, X = INC.filter (fun pl => Pool N C Wf pl.1 pl.2) := ⟨_, rfl⟩
  obtain ⟨UO, hUO⟩ : ∃ X, X = INC.filter (fun pl => ∃ r, Gp N C Wf I pl.1 pl.2 r ∧
    ¬ isA N C r ∧ (Ls Wf (val N C) (kd N C 0 r) = {pl.2} ∨
      Ls Wf (val N C) (kd N C 1 r) = {pl.2})) := ⟨_, rfl⟩
  obtain ⟨UA, hUA⟩ : ∃ X, X = INC.filter (fun pl => ∃ A : Finset ℕ, D ≤ A.card ∧
    ∀ a ∈ A, Gp N C Wf I pl.1 pl.2 a ∧ isA N C a) := ⟨_, rfl⟩
  have hty : Set.ncard {j : ℕ | j < C.gates.length ∧ DP N C (N + N + j) = 0} = PF.card := by
    rw [hPF]
    exact ncard_eq _ _
  have hsplit : TA.card + TO.card = PF.card := by
    rw [hTA, hTO]
    exact Finset.card_filter_add_card_filter_not _
  have hnc : ∀ w : Fin N, Set.ncard {u : Fin N | u ∈ S ∧ Pool N C Wf u w} =
      (S.filter (fun u => Pool N C Wf u w)).card := by
    intro w
    rw [← Set.ncard_coe_finset]
    congr 1
    ext u
    simp
  have h1 : INC.card ≤ Cov.card + UO.card + UA.card := by
    have hsub : INC ⊆ Cov ∪ (UO ∪ UA) := by
      intro pl hpl
      have hpl' := hpl
      rw [hINC] at hpl'
      obtain ⟨hprod, hI⟩ := Finset.mem_filter.mp hpl'
      obtain ⟨hS, hW⟩ := Finset.mem_product.mp hprod
      by_cases hp : Pool N C Wf pl.1 pl.2
      · exact Finset.mem_union_left _ (by rw [hCov]; exact Finset.mem_filter.mpr ⟨hpl, hp⟩)
      · rcases hpair pl.1 hS pl.2 hW hI hp with h | h
        · exact Finset.mem_union_right _ (Finset.mem_union_left _
            (by rw [hUO]; exact Finset.mem_filter.mpr ⟨hpl, h⟩))
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (by rw [hUA]; exact Finset.mem_filter.mpr ⟨hpl, h⟩))
    have c1 := Finset.card_le_card hsub
    have c2 := Finset.card_union_le Cov (UO ∪ UA)
    have c3 := Finset.card_union_le UO UA
    omega
  have h2 : Cov.card ≤ ∑ w ∈ Wf, (S.filter (fun u => Pool N C Wf u w)).card := by
    have hsub : Cov ⊆ Wf.biUnion (fun w => (S.filter (fun u => Pool N C Wf u w)).image
        (fun u => (u, w))) := by
      intro pl hpl
      rw [hCov] at hpl
      obtain ⟨hpl1, hp⟩ := Finset.mem_filter.mp hpl
      rw [hINC] at hpl1
      obtain ⟨hprod, -⟩ := Finset.mem_filter.mp hpl1
      obtain ⟨hS, hW⟩ := Finset.mem_product.mp hprod
      exact Finset.mem_biUnion.mpr ⟨pl.2, hW, Finset.mem_image.mpr
        ⟨pl.1, Finset.mem_filter.mpr ⟨hS, hp⟩, rfl⟩⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun w _ => Finset.card_image_le)))
  have h3 : UO.card ≤ TO.card * 2 := by
    have key := Finset.card_le_card_of_forall_subsingleton
      (fun (pl : Fin N × Fin N) (jb : ℕ × Bool) => Gp N C Wf I pl.1 pl.2 (N + N + jb.1) ∧
        Ls Wf (val N C) (kd N C jb.2.toNat (N + N + jb.1)) = {pl.2})
      (s := UO) (t := TO ×ˢ (Finset.univ : Finset Bool)) (by
        intro pl hpl
        rw [hUO] at hpl
        obtain ⟨-, r, hG, hnA, hor⟩ := Finset.mem_filter.mp hpl
        obtain ⟨j, hj, rfl, hd⟩ := hG.1.1
        have hjT : j ∈ TO := by
          rw [hTO, hPF]
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hd⟩, hnA⟩
        rcases hor with h0 | h0
        · exact ⟨(j, false), Finset.mem_product.mpr ⟨hjT, Finset.mem_univ _⟩, hG, h0⟩
        · exact ⟨(j, true), Finset.mem_product.mpr ⟨hjT, Finset.mem_univ _⟩, hG, h0⟩) (by
        rintro ⟨j, bb⟩ - pl hpl pl' hpl'
        obtain ⟨-, hG, hL⟩ := hpl
        obtain ⟨-, hG', hL'⟩ := hpl'
        exact Prod.ext (gp_point N C Wf I hu _ _ _ _ _ hG hG')
          (Finset.singleton_injective (hL.symm.trans hL')))
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at key
    exact key
  have h4 : UA.card * D ≤ TA.card * (q + 1) := by
    refine Finset.card_mul_le_card_mul
      (fun (pl : Fin N × Fin N) (j : ℕ) => Gp N C Wf I pl.1 pl.2 (N + N + j)) ?_ ?_
    · intro pl hpl
      rw [hUA] at hpl
      obtain ⟨-, A, hAD, hA⟩ := Finset.mem_filter.mp hpl
      have hinj : Set.InjOn (fun a : ℕ => a - (N + N)) (A : Set ℕ) := by
        intro a ha a' ha' he
        obtain ⟨j, -, rfl, -⟩ := (hA a ha).1.1.1
        obtain ⟨j', -, rfl, -⟩ := (hA a' ha').1.1.1
        simp only at he
        omega
      rw [← Finset.card_image_of_injOn hinj] at hAD
      refine hAD.trans (Finset.card_le_card ?_)
      intro j hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      have hGa := hA a ha
      obtain ⟨j0, hj0, rfl, hd⟩ := hGa.1.1.1
      have e : N + N + j0 - (N + N) = j0 := by omega
      rw [e]
      refine Finset.mem_filter.mpr ⟨?_, hGa.1⟩
      rw [hTA, hPF]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj0, hd⟩, hGa.2⟩
    · intro j _
      by_cases hne : (Finset.bipartiteBelow
          (fun (pl : Fin N × Fin N) (j : ℕ) => Gp N C Wf I pl.1 pl.2 (N + N + j)) UA j).Nonempty
      · obtain ⟨pl0, hpl0⟩ := hne
        have hG0 := (Finset.mem_filter.mp hpl0).2
        have hsub : Finset.bipartiteBelow
            (fun (pl : Fin N × Fin N) (j : ℕ) => Gp N C Wf I pl.1 pl.2 (N + N + j)) UA j ⊆
            (Finset.univ.filter (fun l => I pl0.1 l)).image (fun l => (pl0.1, l)) := by
          intro pl hpl
          have hG := (Finset.mem_filter.mp hpl).2
          have e : pl.1 = pl0.1 := gp_point N C Wf I hu _ _ _ _ _ hG hG0
          have hI : I pl.1 pl.2 := hG.2 pl.2 hG.1.2.1
          rw [e] at hI
          exact Finset.mem_image.mpr ⟨pl.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩,
            Prod.ext e.symm rfl⟩
        refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
        rw [lines_through q N I hq hN hl hu pl0.1]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp
  rw [hty, Finset.sum_congr rfl (fun w _ => hnc w), ← hINC]
  have m1 : 2 * D ≤ max (2 * D) (q + 1) := le_max_left _ _
  have m2 : q + 1 ≤ max (2 * D) (q + 1) := le_max_right _ _
  generalize max (2 * D) (q + 1) = M at m1 m2 ⊢
  generalize (∑ w ∈ Wf, (S.filter (fun u => Pool N C Wf u w)).card) = Sg at h2 ⊢
  calc D * INC.card ≤ D * (Cov.card + UO.card + UA.card) := Nat.mul_le_mul_left _ h1
    _ = D * Cov.card + D * UO.card + UA.card * D := by ring
    _ ≤ D * Sg + D * (TO.card * 2) + TA.card * (q + 1) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h2) (Nat.mul_le_mul_left _ h3)) h4
    _ = D * Sg + (2 * D) * TO.card + (q + 1) * TA.card := by ring
    _ ≤ D * Sg + M * TO.card + M * TA.card :=
      Nat.add_le_add (Nat.add_le_add le_rfl (Nat.mul_le_mul_right _ m1))
        (Nat.mul_le_mul_right _ m2)
    _ = M * PF.card + D * Sg := by rw [← hsplit]; ring

end PEqualNP.Outside.L_meta_1838

theorem PEqualNP.Outside.L_meta_1838 : (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 2 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ (∀ hv22 ∈ H22, ∀ xv22 : Fin N22 → Bool, (Relation.ReflTransGen (fun av22 bv22 : ℕ => ∃ jv22 < C22.gates.length, bv22 = N22 + N22 + jv22 ∧ (0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD bv22 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD bv22 0) ∧ av22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ iv22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22).inputs, iv22 ≠ av22 → (C22.wires (List.ofFn (Fin.append xv22 (fun uv22 : Fin N22 => false)))).getD iv22 false = true)) hv22 C22.output)) ∧ (∀ hv22x1 : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD hv22x1 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD hv22x1 0 ∧ ∃ jv22x1 < C22.gates.length, hv22x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x1).inputs ∧ (0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + jv22x1) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + jv22x1) 0)) → hv22x1 ∉ H22 → ∀ xv22x1 : Fin N22 → Bool, ((X22.wires (List.ofFn xv22x1)).getD (ph22 hv22x1) false = true ↔ (Relation.ReflTransGen (fun av22x1 bv22x1 : ℕ => ∃ jv22x2 < C22.gates.length, bv22x1 = N22 + N22 + jv22x2 ∧ (0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD bv22x1 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD bv22x1 0) ∧ av22x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x2).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ iv22x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 jv22x2).inputs, iv22x1 ≠ av22x1 → (C22.wires (List.ofFn (Fin.append xv22x1 (fun uv22x1 : Fin N22 => false)))).getD iv22x1 false = true)) hv22x1 C22.output))) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → (∀ (Nlv16 : ℕ) (Clv16 : PEqualNP.CircuitLowerBounds.Circuit) (Vlv16 : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit), ((∀ glv16x2 ∈ Clv16.gates, (glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) Clv16) → Vlv16 = (fun sglv16x3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv16x2 : Fin Clv16.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv16x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16x1 0 = 0) ∨ (∀ hlv16x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val))) Clv16.output)) → (∀ zlv16 : Fin (Nlv16 + Nlv16) → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) Clv16 zlv16 = true ↔ ∀ sglv16 : ℕ → Fin 2, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) (Vlv16 sglv16) zlv16 = true) ∧ (∀ sglv16x1 : ℕ → Fin 2, ((∀ glv16x1 ∈ (Vlv16 sglv16x1).gates, (glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) (Vlv16 sglv16x1)) ∧ (∀ jlv16 < (Vlv16 sglv16x1).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∃ ilv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16 0 = 0) ∨ (∀ hlv16x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x2 0 = 0))) ∧ (Vlv16 sglv16x1).size = Clv16.size ∧ ∀ (zlv16x1 : Fin (Nlv16 + Nlv16) → Bool) (wlv16 : ℕ), (Clv16.wires (List.ofFn zlv16x1)).getD wlv16 false = true → ((Vlv16 sglv16x1).wires (List.ofFn zlv16x1)).getD wlv16 false = true) ∧ (∀ (sglv16x2 : ℕ → Fin 2) (glv16 : ℕ), ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD glv16 0 = 0 → 0 < ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD glv16 0 → ∃ Elv16 : Finset ℕ, (∀ hlv16 ∈ Elv16, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16 0 = 0 ∧ (Relation.ReflTransGen (fun alv16 blv16 : ℕ => ∃ jlv16x1 < (Vlv16 sglv16x2).gates.length, blv16 = Nlv16 + Nlv16 + jlv16x1 ∧ alv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD blv16 0 ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD blv16 0) hlv16 glv16)) ∧ ∀ ylv16 : Fin Nlv16 → Bool, ((Vlv16 sglv16x2).wires (List.ofFn (Fin.append (fun ulv16 : Fin Nlv16 => false) ylv16))).getD glv16 false = decide (∃ hlv16x1 ∈ Elv16, (Clv16.wires (List.ofFn (Fin.append (fun ulv16x1 : Fin Nlv16 => false) ylv16))).getD hlv16x1 false = true))) → (∀ (Nlv17a Rlv17a : ℕ) (Ilv17a : Fin Nlv17a → Fin Nlv17a → Prop) [DecidableRel Ilv17a] (Clv17a Corlv17a : PEqualNP.CircuitLowerBounds.Circuit) (Vlv17a : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit) (Slv17a Wlv17a : Finset (Fin Nlv17a)), ((∀ glv17ax2 ∈ Clv17a.gates, (glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17a + Nlv17a) Clv17a) → (0 < Clv17a.gates.length ∧ (∀ jlv17ax11 < Clv17a.gates.length, ∀ ilv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax11).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax6 : Fin Nlv17a => (plv17ax6 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax4 : Fin Nlv17a => Nlv17a + (llv17ax4 : ℕ)) (Wlv17a)ᶜ)).getD ilv17ax4 0 = 0) ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.image (fun plv17ax7 : Fin Nlv17a => (plv17ax7 : ℕ)) (Slv17a)ᶜ ∪ Finset.image (fun llv17ax5 : Fin Nlv17a => Nlv17a + (llv17ax5 : ℕ)) (Wlv17a)ᶜ)).getD Clv17a.output 0 = 0) → Corlv17a = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax12 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax5 0 = 0) ∨ (∀ hlv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax12.val))) Clv17a.output) → Vlv17a = (fun sglv17ax3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17ax13 : Fin Clv17a.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17ax6 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD ilv17ax6 0 = 0) ∨ (∀ hlv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs, (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax4 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val).inputs.getD (sglv17ax3 jlv17ax13.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17a jlv17ax13.val))) Clv17a.output)) → ((∀ sglv17a : ℕ → Fin 2, ∀ wlv17ax1 ∈ Wlv17a, ∀ Xlv17ax1 : Finset (Fin Nlv17a), Xlv17ax1 ⊆ Slv17a → (∀ plv17ax1 ∈ Xlv17ax1, ¬ Ilv17a plv17ax1 wlv17ax1) → Xlv17ax1.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17a) (Fin.append (fun plv17ax2 : Fin Nlv17a => decide (plv17ax2 ∈ Xlv17ax1)) (fun llv17a : Fin Nlv17a => decide (llv17a ∈ ({wlv17ax1} : Finset (Fin Nlv17a))))) = false) → ∀ wlv17a ∈ Wlv17a, ∀ Xlv17a : Finset (Fin Nlv17a), Xlv17a ⊆ Slv17a → (∀ plv17a ∈ Xlv17a, ¬ Ilv17a plv17a wlv17a) → Xlv17a.card ≤ Rlv17a → ¬ (∃ hlv17a : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17a 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17a 0 ∧ ∃ jlv17a < Corlv17a.gates.length, hlv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17a).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17a) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17a) 0)) ∧ (Wlv17a.filter (fun llv17ax1 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17a : Fin Nlv17a => false) (fun alv17ax1 : Fin Nlv17a => decide (alv17ax1 = llv17ax1))))).getD hlv17a false = true)) = ({wlv17a} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax2 blv17a : ℕ => ∃ jlv17ax1 < Corlv17a.gates.length, blv17a = Nlv17a + Nlv17a + jlv17ax1 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17a 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17a 0) ∧ alv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax1).inputs, ilv17a ≠ alv17ax2 → (Corlv17a.wires (List.ofFn (Fin.append (fun alv17a : Fin Nlv17a => decide (alv17a ∈ Xlv17a)) (fun ulv17ax1 : Fin Nlv17a => false)))).getD ilv17a false = true)) hlv17a Corlv17a.output))) ∧ (∀ (sglv17ax1 : ℕ → Fin 2) (glv17a hlv17ax1 : ℕ) (xlv17a : Fin Nlv17a → Bool), (((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD glv17a 0 = 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD glv17a 0 ∧ ∃ jlv17ax2 < (Vlv17a sglv17ax1).gates.length, glv17a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax2).inputs ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax2) 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax2) 0)) → (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 → (Relation.ReflTransGen (fun alv17ax3 blv17ax1 : ℕ => ∃ jlv17ax3 < (Vlv17a sglv17ax1).gates.length, blv17ax1 = Nlv17a + Nlv17a + jlv17ax3 ∧ alv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax3).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax1 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax1 0) hlv17ax1 glv17a) → ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax1 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax1 0 ∧ ∃ jlv17ax4 < Corlv17a.gates.length, hlv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax4).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax4) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax4) 0)) ∧ ((Relation.ReflTransGen (fun alv17ax4 blv17ax2 : ℕ => ∃ jlv17ax5 < (Vlv17a sglv17ax1).gates.length, blv17ax2 = Nlv17a + Nlv17a + jlv17ax5 ∧ (0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax2 0 ∧ 0 < ((Vlv17a sglv17ax1).lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax2 0) ∧ alv17ax4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv17a sglv17ax1) jlv17ax5).inputs, ilv17ax1 ≠ alv17ax4 → ((Vlv17a sglv17ax1).wires (List.ofFn (Fin.append xlv17a (fun ulv17ax2 : Fin Nlv17a => false)))).getD ilv17ax1 false = true)) glv17a (Vlv17a sglv17ax1).output) → (Relation.ReflTransGen (fun alv17ax5 blv17ax3 : ℕ => ∃ jlv17ax6 < Corlv17a.gates.length, blv17ax3 = Nlv17a + Nlv17a + jlv17ax6 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax3 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax3 0) ∧ alv17ax5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax6).inputs, ilv17ax2 ≠ alv17ax5 → (Corlv17a.wires (List.ofFn (Fin.append xlv17a (fun ulv17ax3 : Fin Nlv17a => false)))).getD ilv17ax2 false = true)) hlv17ax1 Corlv17a.output))) ∧ ((∀ sglv17ax2 : ℕ → Fin 2, ∀ wlv17ax4 ∈ Wlv17a, ∀ Xlv17ax2 : Finset (Fin Nlv17a), Xlv17ax2 ⊆ Slv17a → (∀ plv17ax4 ∈ Xlv17ax2, ¬ Ilv17a plv17ax4 wlv17ax4) → Xlv17ax2.card ≤ Rlv17a → PEqualNP.MetaComplexity.circuitFun (Nlv17a + Nlv17a) (Vlv17a sglv17ax2) (Fin.append (fun plv17ax5 : Fin Nlv17a => decide (plv17ax5 ∈ Xlv17ax2)) (fun llv17ax2 : Fin Nlv17a => decide (llv17ax2 ∈ ({wlv17ax4} : Finset (Fin Nlv17a))))) = false) → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD Clv17a.output 0 → 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD Clv17a.output 0 → ∃ (Xclv17a : PEqualNP.CircuitLowerBounds.Circuit) (pslv17a : Fin Nlv17a → ℕ), ((∀ glv17ax1 ∈ Xclv17a.gates, (glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17ax1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17ax1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17a Xclv17a) ∧ Xclv17a.size ≤ Set.ncard {jlv17ax7 : ℕ | jlv17ax7 < Clv17a.gates.length ∧ (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax7) 0 = 0} + 3 * Set.ncard {jlv17ax8 : ℕ | jlv17ax8 < Clv17a.gates.length ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax8) 0 ∧ 0 < (Clv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax8) 0} ∧ (∀ (wlv17ax2 : Fin Nlv17a) (xlv17ax1 xlv17ax2 : Fin Nlv17a → Bool), (∀ plv17ax3 ∈ Slv17a, xlv17ax1 plv17ax3 = xlv17ax2 plv17ax3) → (Xclv17a.wires (List.ofFn xlv17ax1)).getD (pslv17a wlv17ax2) false = (Xclv17a.wires (List.ofFn xlv17ax2)).getD (pslv17a wlv17ax2) false) ∧ ∀ wlv17ax3 ∈ Wlv17a, ∀ xlv17ax3 : Fin Nlv17a → Bool, ((Xclv17a.wires (List.ofFn xlv17ax3)).getD (pslv17a wlv17ax3) false = true ↔ (∃ hlv17ax2 : ℕ, ((Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD hlv17ax2 0 = 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD hlv17ax2 0 ∧ ∃ jlv17ax9 < Corlv17a.gates.length, hlv17ax2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax9).inputs ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD (Nlv17a + Nlv17a + jlv17ax9) 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD (Nlv17a + Nlv17a + jlv17ax9) 0)) ∧ (Wlv17a.filter (fun llv17ax3 : Fin Nlv17a => (Clv17a.wires (List.ofFn (Fin.append (fun ulv17ax4 : Fin Nlv17a => false) (fun alv17ax6 : Fin Nlv17a => decide (alv17ax6 = llv17ax3))))).getD hlv17ax2 false = true)) = ({wlv17ax3} : Finset (Fin Nlv17a)) ∧ (Relation.ReflTransGen (fun alv17ax7 blv17ax4 : ℕ => ∃ jlv17ax10 < Corlv17a.gates.length, blv17ax4 = Nlv17a + Nlv17a + jlv17ax10 ∧ (0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.range Nlv17a)).getD blv17ax4 0 ∧ 0 < (Corlv17a.lineDegrees (Nlv17a + Nlv17a) (Finset.Ico Nlv17a (Nlv17a + Nlv17a))).getD blv17ax4 0) ∧ alv17ax7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17ax3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17a jlv17ax10).inputs, ilv17ax3 ≠ alv17ax7 → (Corlv17a.wires (List.ofFn (Fin.append xlv17ax3 (fun ulv17ax5 : Fin Nlv17a => false)))).getD ilv17ax3 false = true)) hlv17ax2 Corlv17a.output))))) → ∀ (qlv17b Nlv17b Klv17b mlv17b Dlv17b : ℕ) (Ilv17b : Fin Nlv17b → Fin Nlv17b → Prop) [DecidableRel Ilv17b] (Clv17b Corlv17b : PEqualNP.CircuitLowerBounds.Circuit) (Slv17b Wlv17b : Finset (Fin Nlv17b)), 2 ≤ qlv17b → Nlv17b = qlv17b ^ 2 + qlv17b + 1 → (∀ llv17b : Fin Nlv17b, (Finset.univ.filter (fun plv17b => Ilv17b plv17b llv17b)).card = qlv17b + 1) → (∀ palv17b pblv17b : Fin Nlv17b, palv17b ≠ pblv17b → ∃! lblv17b : Fin Nlv17b, Ilv17b palv17b lblv17b ∧ Ilv17b pblv17b lblv17b) → ((∀ glv17b ∈ Clv17b.gates, (glv17b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv17b + Nlv17b) Clv17b) → Corlv17b = (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv17b : Fin Clv17b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD ilv17b 0 = 0) ∨ (∀ hlv17b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17b 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val).inputs) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17b.val))) Clv17b.output) → Set.ncard {jlv17bx1 : ℕ | jlv17bx1 < Clv17b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv17bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD ilv17bx1 0 = 0) ∨ (∀ hlv17bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx1).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17bx1 0 = 0))} ≤ mlv17b → ((0 < Clv17b.gates.length ∧ (∀ jlv17bx2 < Clv17b.gates.length, ∀ ilv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv17b jlv17bx2).inputs, (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.image (fun plv17bx3 : Fin Nlv17b => (plv17bx3 : ℕ)) (Slv17b)ᶜ ∪ Finset.image (fun llv17bx3 : Fin Nlv17b => Nlv17b + (llv17bx3 : ℕ)) (Wlv17b)ᶜ)).getD ilv17bx2 0 = 0) ∧ (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.image (fun plv17bx4 : Fin Nlv17b => (plv17bx4 : ℕ)) (Slv17b)ᶜ ∪ Finset.image (fun llv17bx4 : Fin Nlv17b => Nlv17b + (llv17bx4 : ℕ)) (Wlv17b)ᶜ)).getD Clv17b.output 0 = 0) ∧ (∀ plv17bx1 ∈ Slv17b, ∀ llv17bx1 ∈ Wlv17b, Ilv17b plv17bx1 llv17bx1 → PEqualNP.MetaComplexity.circuitFun (Nlv17b + Nlv17b) Clv17b (Fin.append (fun plv17bx5 : Fin Nlv17b => decide (plv17bx5 ∈ ({plv17bx1} : Finset (Fin Nlv17b)))) (fun llv17bx5 : Fin Nlv17b => decide (llv17bx5 ∈ ({llv17bx1} : Finset (Fin Nlv17b))))) = true) ∧ (∀ Xlv17b Ylv17b : Finset (Fin Nlv17b), Xlv17b ⊆ Slv17b → Ylv17b ⊆ Wlv17b → Ylv17b.card ≤ Klv17b → (∀ plv17bx2 ∈ Xlv17b, ∀ llv17bx2 ∈ Ylv17b, ¬ Ilv17b plv17bx2 llv17bx2) → PEqualNP.MetaComplexity.circuitFun (Nlv17b + Nlv17b) Clv17b (Fin.append (fun plv17bx6 : Fin Nlv17b => decide (plv17bx6 ∈ Xlv17b)) (fun llv17bx6 : Fin Nlv17b => decide (llv17bx6 ∈ Ylv17b))) = false)) → 2 ^ mlv17b + Dlv17b = Klv17b + 1 → 1 ≤ Dlv17b → Dlv17b * ((Slv17b ×ˢ Wlv17b).filter (fun pllv17b => Ilv17b pllv17b.1 pllv17b.2)).card ≤ max (2 * Dlv17b) (qlv17b + 1) * Set.ncard {jlv17bx3 : ℕ | jlv17bx3 < Clv17b.gates.length ∧ (Clv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD (Nlv17b + Nlv17b + jlv17bx3) 0 = 0} + Dlv17b * ∑ wlv17b ∈ Wlv17b, Set.ncard {ulv17b : Fin Nlv17b | ulv17b ∈ Slv17b ∧ (∃ hlv17bx2 : ℕ, ((Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD hlv17bx2 0 = 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD hlv17bx2 0 ∧ ∃ jlv17bx4 < Corlv17b.gates.length, hlv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx4).inputs ∧ (0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD (Nlv17b + Nlv17b + jlv17bx4) 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD (Nlv17b + Nlv17b + jlv17bx4) 0)) ∧ (Wlv17b.filter (fun llv17bx7 : Fin Nlv17b => (Clv17b.wires (List.ofFn (Fin.append (fun ulv17bx1 : Fin Nlv17b => false) (fun alv17bx1 : Fin Nlv17b => decide (alv17bx1 = llv17bx7))))).getD hlv17bx2 false = true)) = ({wlv17b} : Finset (Fin Nlv17b)) ∧ (Relation.ReflTransGen (fun alv17bx2 blv17b : ℕ => ∃ jlv17bx5 < Corlv17b.gates.length, blv17b = Nlv17b + Nlv17b + jlv17bx5 ∧ (0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.range Nlv17b)).getD blv17b 0 ∧ 0 < (Corlv17b.lineDegrees (Nlv17b + Nlv17b) (Finset.Ico Nlv17b (Nlv17b + Nlv17b))).getD blv17b 0) ∧ alv17bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∀ ilv17bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Corlv17b jlv17bx5).inputs, ilv17bx3 ≠ alv17bx2 → (Corlv17b.wires (List.ofFn (Fin.append (fun alv17b : Fin Nlv17b => decide (alv17b = ulv17b)) (fun ulv17bx2 : Fin Nlv17b => false)))).getD ilv17bx3 false = true)) hlv17bx2 Corlv17b.output))} := by
  intro H1 H2 H3 q N K m D I _ C Cor0 S W hq hN hl hu hC hCor hm hrd h2m hD
  subst hCor
  obtain ⟨hreads, hacc, hrej⟩ := hrd
  obtain ⟨hV1, hV2, hV3⟩ := H2 N C (PEqualNP.Outside.L_meta_1838.Vw N C) hC rfl
  obtain ⟨-, hb, -⟩ := H3 N 0 I C (PEqualNP.Outside.L_meta_1838.Cor N C)
    (PEqualNP.Outside.L_meta_1838.Vw N C) S W hC hreads rfl rfl
  exact PEqualNP.Outside.L_meta_1838.core q N K m D I C S W hq hN hl hu hC.1 hC.2 hm hacc hrej
    h2m hD hV1 (fun sg => (hV2 sg).1)
    (fun sg hP hL => by
      obtain ⟨X, ph, H, -, -, -, h4, h5, h6⟩ :=
        H1 N (PEqualNP.Outside.L_meta_1838.Vw N C sg) (hV2 sg).1.1 (hV2 sg).1.2 (hV2 sg).2.1 hP hL
      exact ⟨X, ph, H, h4, h5, h6⟩)
    (fun sg g h0 h1 => by
      obtain ⟨E, hE1, hE2⟩ := hV3 sg g h0 h1
      exact ⟨E, hE1, fun y => ⟨fun h => of_decide_eq_true ((hE2 y).symm.trans h),
        fun h => (hE2 y).trans (decide_eq_true h)⟩⟩)
    hb
