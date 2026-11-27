import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1834

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

abbrev Fan (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Cross (N : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧
    ¬ ((∃ i ∈ (gateAt C j).inputs,
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
      (∀ h ∈ (gateAt C j).inputs, (C.lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))

noncomputable def vw (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) : Circuit :=
  Circuit.mk (List.ofFn (fun j : Fin C.gates.length =>
    @ite Gate (Cross N C j.val) (Classical.propDecidable _)
      (Gate.mk GateOp.or [(gateAt C j.val).inputs.getD (sg j.val).val 0,
        (gateAt C j.val).inputs.getD (sg j.val).val 0])
      (gateAt C j.val))) C.output

theorem vw_len (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) :
    (vw N C sg).gates.length = C.gates.length := by
  simp [vw]

theorem vw_gate (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (vw N C sg) j = @ite Gate (Cross N C j) (Classical.propDecidable _)
      (Gate.mk GateOp.or [(gateAt C j).inputs.getD (sg j).val 0,
        (gateAt C j).inputs.getD (sg j).val 0]) (gateAt C j) := by
  have h : (vw N C sg).gates[j]? = some (@ite Gate (Cross N C j) (Classical.propDecidable _)
      (Gate.mk GateOp.or [(gateAt C j).inputs.getD (sg j).val 0,
        (gateAt C j).inputs.getD (sg j).val 0]) (gateAt C j)) := by
    show (List.ofFn _)[j]? = _
    rw [List.getElem?_ofFn, dif_pos hj]
  show (vw N C sg).gates.getD j _ = _
  rw [List.getD_eq_getElem?_getD, h, Option.getD_some]

theorem sel (a b : ℕ) (s : Fin 2) : [a, b].getD s.val 0 = a ∨ [a, b].getD s.val 0 = b := by
  obtain ⟨v, hv⟩ := s
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem cases3 (N : ℕ) (C : Circuit) (hg : Fan C) (sg : ℕ → Fin 2) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j = ⟨GateOp.or, [a, b]⟩ ∧ gateAt (vw N C sg) j = ⟨GateOp.or, [a, b]⟩) ∨
      (gateAt C j = ⟨GateOp.and, [a, b]⟩ ∧ ¬ Cross N C j ∧
        gateAt (vw N C sg) j = ⟨GateOp.and, [a, b]⟩) ∨
      (gateAt C j = ⟨GateOp.and, [a, b]⟩ ∧ Cross N C j ∧
        ∃ c, (c = a ∨ c = b) ∧ c = [a, b].getD (sg j).val 0 ∧
          gateAt (vw N C sg) j = ⟨GateOp.or, [c, c]⟩) := by
  obtain ⟨a, b, hab | hab⟩ := gate_shape C hg j hj
  · refine ⟨a, b, ?_⟩
    have e := vw_gate N C sg j hj
    by_cases hc : Cross N C j
    · right; right
      refine ⟨hab, hc, _, sel a b (sg j), rfl, ?_⟩
      rw [if_pos hc] at e
      rw [hab] at e
      exact e
    · right; left
      refine ⟨hab, hc, ?_⟩
      rw [if_neg hc] at e
      exact e.trans hab
  · refine ⟨a, b, Or.inl ⟨hab, ?_⟩⟩
    have hc : ¬ Cross N C j := by
      intro h
      have h1 := h.1
      rw [hab] at h1
      cases h1
    have e := vw_gate N C sg j hj
    rw [if_neg hc] at e
    exact e.trans hab

theorem vw_fan (N : ℕ) (C : Circuit) (hg : Fan C) (sg : ℕ → Fin 2) : Fan (vw N C sg) := by
  intro g hgm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgm
  have hj' : j < C.gates.length := by rw [vw_len] at hj; exact hj
  have e : (vw N C sg).gates[j] = gateAt (vw N C sg) j := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
  rw [e]
  obtain ⟨a, b, h | h | ⟨_, _, c, _, _, h⟩⟩ := cases3 N C hg sg j hj'
  · rw [h.2]; exact ⟨Or.inr rfl, rfl⟩
  · rw [h.2.2]; exact ⟨Or.inl rfl, rfl⟩
  · rw [h]; exact ⟨Or.inr rfl, rfl⟩

theorem vw_rb (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) : ReadsBack (N + N) (vw N C sg) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by rw [vw_len] at hj; exact hj
  obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, _, hV⟩ | ⟨hC, _, c, hc, _, hV⟩⟩ := cases3 N C hg sg j hj'
  · rw [hV] at hi
    exact hrb j hj' i (by rw [hC]; exact hi)
  · rw [hV] at hi
    exact hrb j hj' i (by rw [hC]; exact hi)
  · rw [hV] at hi
    have ha : a < N + N + j := hrb j hj' a (by simp [hC])
    have hb : b < N + N + j := hrb j hj' b (by simp [hC])
    have hic : i = c := by
      rcases List.mem_pair.1 hi with e | e <;> exact e
    rcases hc with e | e <;> omega

theorem wcase (K len w : ℕ) : w < K ∨ (∃ j, j < len ∧ w = K + j) ∨ K + len ≤ w := by
  rcases lt_or_ge w K with h | h
  · exact Or.inl h
  · rcases lt_or_ge w (K + len) with h2 | h2
    · exact Or.inr (Or.inl ⟨w - K, by omega, by omega⟩)
    · exact Or.inr (Or.inr h2)

theorem v_mono (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (X : List Bool) (hX : X.length = N + N) :
    ∀ w, VV C X w = true → VV (vw N C sg) X w = true := by
  have hrbV := vw_rb N C hg hrb sg
  have hlen := vw_len N C sg
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    rcases wcase (N + N) C.gates.length w with h1 | ⟨j, hj, rfl⟩ | h3
    · rw [VV_in C X w (by omega)] at hw
      rw [VV_in (vw N C sg) X w (by omega)]
      exact hw
    · have hjV : j < (vw N C sg).gates.length := by omega
      obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, _, hV⟩ | ⟨hC, _, c, hc, _, hV⟩⟩ := cases3 N C hg sg j hj
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [V_or (N + N) C hrb X hX j hj a b hC, Bool.or_eq_true] at hw
        rw [V_or (N + N) (vw N C sg) hrbV X hX j hjV a b hV, Bool.or_eq_true]
        rcases hw with h | h
        · exact Or.inl (ih a ha h)
        · exact Or.inr (ih b hb h)
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [V_and (N + N) C hrb X hX j hj a b hC, Bool.and_eq_true] at hw
        rw [V_and (N + N) (vw N C sg) hrbV X hX j hjV a b hV, Bool.and_eq_true]
        exact ⟨ih a ha hw.1, ih b hb hw.2⟩
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [V_and (N + N) C hrb X hX j hj a b hC, Bool.and_eq_true] at hw
        rw [V_or (N + N) (vw N C sg) hrbV X hX j hjV c c hV, Bool.or_self]
        rcases hc with e | e
        · rw [e]; exact ih a ha hw.1
        · rw [e]; exact ih b hb hw.2
    · rw [VV_out C X w (by omega)] at hw
      exact absurd hw (by simp)

theorem v_dmono (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (mk : Finset ℕ) :
    ∀ w, DD (N + N) mk (vw N C sg) w ≤ DD (N + N) mk C w := by
  have hrbV := vw_rb N C hg hrb sg
  have hlen := vw_len N C sg
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wcase (N + N) C.gates.length w with h1 | ⟨j, hj, rfl⟩ | h3
    · rw [DD_in (N + N) mk (vw N C sg) w h1, DD_in (N + N) mk C w h1]
    · have hjV : j < (vw N C sg).gates.length := by omega
      obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, _, hV⟩ | ⟨hC, _, c, hc, _, hV⟩⟩ := cases3 N C hg sg j hj
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_or (N + N) mk (vw N C sg) hrbV j hjV a b hV, D_or (N + N) mk C hrb j hj a b hC]
        exact max_le_max (ih a ha) (ih b hb)
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_and (N + N) mk (vw N C sg) hrbV j hjV a b hV, D_and (N + N) mk C hrb j hj a b hC]
        exact Nat.add_le_add (ih a ha) (ih b hb)
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_or (N + N) mk (vw N C sg) hrbV j hjV c c hV, D_and (N + N) mk C hrb j hj a b hC,
          max_self]
        rcases hc with e | e
        · rw [e]; exact le_trans (ih a ha) (Nat.le_add_right _ _)
        · rw [e]; exact le_trans (ih b hb) (Nat.le_add_left _ _)
    · rw [DD_out (N + N) mk (vw N C sg) w (by omega), DD_out (N + N) mk C w h3]

def sg0 (C : Circuit) (X : List Bool) : ℕ → Fin 2 :=
  fun j => if VV C X ((gateAt C j).inputs.getD 0 0) = true then 1 else 0

theorem v_eq (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (X : List Bool) (hX : X.length = N + N) :
    ∀ w, VV (vw N C (sg0 C X)) X w = VV C X w := by
  have hrbV := vw_rb N C hg hrb (sg0 C X)
  have hlen := vw_len N C (sg0 C X)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases wcase (N + N) C.gates.length w with h1 | ⟨j, hj, rfl⟩ | h3
    · rw [VV_in (vw N C (sg0 C X)) X w (by omega), VV_in C X w (by omega)]
    · have hjV : j < (vw N C (sg0 C X)).gates.length := by omega
      obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, _, hV⟩ | ⟨hC, _, c, hc, hcs, hV⟩⟩ :=
        cases3 N C hg (sg0 C X) j hj
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [V_or (N + N) (vw N C (sg0 C X)) hrbV X hX j hjV a b hV,
          V_or (N + N) C hrb X hX j hj a b hC, ih a ha, ih b hb]
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [V_and (N + N) (vw N C (sg0 C X)) hrbV X hX j hjV a b hV,
          V_and (N + N) C hrb X hX j hj a b hC, ih a ha, ih b hb]
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        have hcj : c < N + N + j := by
          rcases hc with e | e <;> omega
        rw [V_or (N + N) (vw N C (sg0 C X)) hrbV X hX j hjV c c hV,
          V_and (N + N) C hrb X hX j hj a b hC, Bool.or_self, ih c hcj, hcs]
        by_cases h : VV C X a = true
        · have e : sg0 C X j = 1 := by
            unfold sg0
            rw [hC]
            exact if_pos h
          rw [e]
          show VV C X b = (VV C X a && VV C X b)
          rw [h, Bool.true_and]
        · have e : sg0 C X j = 0 := by
            unfold sg0
            rw [hC]
            exact if_neg h
          rw [e]
          show VV C X a = (VV C X a && VV C X b)
          rw [Bool.eq_false_iff.2 h, Bool.false_and]
    · rw [VV_out (vw N C (sg0 C X)) X w (by omega), VV_out C X w (by omega)]

theorem partA (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (z : Fin (N + N) → Bool) :
    circuitFun (N + N) C z = true ↔
      ∀ sg : ℕ → Fin 2, circuitFun (N + N) (vw N C sg) z = true := by
  constructor
  · intro h sg
    exact v_mono N C hg hrb sg (List.ofFn z) (by simp) C.output h
  · intro h
    have h1 := h (sg0 C (List.ofFn z))
    have e := v_eq N C hg hrb (List.ofFn z) (by simp) C.output
    exact e.symm.trans h1

theorem partB (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) :
    ((∀ g ∈ (vw N C sg).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        ReadsBack (N + N) (vw N C sg)) ∧
      (∀ j < (vw N C sg).gates.length, (gateAt (vw N C sg) j).op = GateOp.and →
        ((∃ i ∈ (gateAt (vw N C sg) j).inputs,
            ((vw N C sg).lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 = 0) ∨
          (∀ h ∈ (gateAt (vw N C sg) j).inputs,
            ((vw N C sg).lineDegrees (N + N) (Finset.range N)).getD h 0 = 0))) ∧
      (vw N C sg).size = C.size ∧
      ∀ (z : Fin (N + N) → Bool) (w : ℕ), (C.wires (List.ofFn z)).getD w false = true →
        ((vw N C sg).wires (List.ofFn z)).getD w false = true := by
  refine ⟨⟨vw_fan N C hg sg, vw_rb N C hg hrb sg⟩, ?_, vw_len N C sg,
    fun z w h => v_mono N C hg hrb sg (List.ofFn z) (by simp) w h⟩
  intro j hj hop
  have hj' : j < C.gates.length := by rw [vw_len] at hj; exact hj
  obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, hnc, hV⟩ | ⟨hC, _, c, _, _, hV⟩⟩ := cases3 N C hg sg j hj'
  · rw [hV] at hop
    cases hop
  · have hk : (∃ i ∈ (gateAt C j).inputs, DD (N + N) (Finset.Ico N (N + N)) C i = 0) ∨
        (∀ h ∈ (gateAt C j).inputs, DD (N + N) (Finset.range N) C h = 0) := by
      by_contra hk
      exact hnc (And.intro (congrArg Gate.op hC) hk)
    rw [hV, ← hC]
    rcases hk with ⟨i, hi, h0⟩ | hk
    · refine Or.inl ⟨i, hi, ?_⟩
      have h1 := v_dmono N C hg hrb sg (Finset.Ico N (N + N)) i
      exact Nat.eq_zero_of_le_zero (le_of_le_of_eq h1 h0)
    · refine Or.inr fun h hh => ?_
      have h1 := v_dmono N C hg hrb sg (Finset.range N) h
      exact Nat.eq_zero_of_le_zero (le_of_le_of_eq h1 (hk h hh))
  · rw [hV] at hop
    cases hop

theorem v_same (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (X : List Bool) (hX : X.length = N + N) :
    ∀ w, DD (N + N) (Finset.range N) C w = 0 → VV (vw N C sg) X w = VV C X w := by
  have hrbV := vw_rb N C hg hrb sg
  have hlen := vw_len N C sg
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    rcases wcase (N + N) C.gates.length w with h1 | ⟨j, hj, rfl⟩ | h3
    · rw [VV_in (vw N C sg) X w (by omega), VV_in C X w (by omega)]
    · have hjV : j < (vw N C sg).gates.length := by omega
      obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, _, hV⟩ | ⟨hC, hcr, _⟩⟩ := cases3 N C hg sg j hj
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_or (N + N) _ C hrb j hj a b hC] at hd
        have l1 := le_max_left (DD (N + N) (Finset.range N) C a)
          (DD (N + N) (Finset.range N) C b)
        have l2 := le_max_right (DD (N + N) (Finset.range N) C a)
          (DD (N + N) (Finset.range N) C b)
        rw [V_or (N + N) (vw N C sg) hrbV X hX j hjV a b hV,
          V_or (N + N) C hrb X hX j hj a b hC, ih a ha (by omega), ih b hb (by omega)]
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_and (N + N) _ C hrb j hj a b hC] at hd
        rw [V_and (N + N) (vw N C sg) hrbV X hX j hjV a b hV,
          V_and (N + N) C hrb X hX j hj a b hC, ih a ha (by omega), ih b hb (by omega)]
      · exfalso
        rw [D_and (N + N) _ C hrb j hj a b hC] at hd
        apply hcr.2
        right
        intro h hh
        rw [hC] at hh
        show DD (N + N) (Finset.range N) C h = 0
        rcases List.mem_pair.1 hh with e | e
        · rw [e]; omega
        · rw [e]; omega
    · rw [VV_out (vw N C sg) X w (by omega), VV_out C X w (by omega)]

theorem v_off (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) (y : Fin N → Bool) :
    ∀ w, DD (N + N) (Finset.Ico N (N + N)) C w = 0 →
      VV (vw N C sg) (List.ofFn (Fin.append (fun _ : Fin N => false) y)) w = false := by
  have hrbV := vw_rb N C hg hrb sg
  have hlen := vw_len N C sg
  have hX : (List.ofFn (Fin.append (fun _ : Fin N => false) y)).length = N + N := by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hd
    rcases wcase (N + N) C.gates.length w with h1 | ⟨j, hj, rfl⟩ | h3
    · rw [DD_in (N + N) _ C w h1] at hd
      have hwm : w ∉ Finset.Ico N (N + N) := by
        intro hc
        rw [ifp hc] at hd
        omega
      have hwN : w < N := by
        rw [Finset.mem_Ico] at hwm
        omega
      rw [VV_in (vw N C sg) _ w (by omega)]
      have e := app_getD (fun _ : Fin N => false) y w
      rw [difp hwN] at e
      exact e
    · have hjV : j < (vw N C sg).gates.length := by omega
      obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, _, hV⟩ | ⟨hC, _, c, hc, _, hV⟩⟩ := cases3 N C hg sg j hj
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_or (N + N) _ C hrb j hj a b hC] at hd
        have l1 := le_max_left (DD (N + N) (Finset.Ico N (N + N)) C a)
          (DD (N + N) (Finset.Ico N (N + N)) C b)
        have l2 := le_max_right (DD (N + N) (Finset.Ico N (N + N)) C a)
          (DD (N + N) (Finset.Ico N (N + N)) C b)
        rw [V_or (N + N) (vw N C sg) hrbV _ hX j hjV a b hV, ih a ha (by omega),
          ih b hb (by omega), Bool.or_false]
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_and (N + N) _ C hrb j hj a b hC] at hd
        rw [V_and (N + N) (vw N C sg) hrbV _ hX j hjV a b hV, ih a ha (by omega),
          Bool.false_and]
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_and (N + N) _ C hrb j hj a b hC] at hd
        rw [V_or (N + N) (vw N C sg) hrbV _ hX j hjV c c hV, Bool.or_self]
        rcases hc with e | e
        · rw [e]; exact ih a ha (by omega)
        · rw [e]; exact ih b hb (by omega)
    · exact VV_out (vw N C sg) _ w (by omega)

def Rel (N : ℕ) (C : Circuit) (sg : ℕ → Fin 2) (a b : ℕ) : Prop :=
  ∃ j < (vw N C sg).gates.length, b = N + N + j ∧ a ∈ (gateAt (vw N C sg) j).inputs ∧
    (gateAt (vw N C sg) j).op = GateOp.or ∧
    0 < (C.lineDegrees (N + N) (Finset.range N)).getD b 0 ∧
    0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD b 0

theorem partC (N : ℕ) (C : Circuit) (hg : Fan C) (hrb : ReadsBack (N + N) C)
    (sg : ℕ → Fin 2) :
    ∀ g, DD (N + N) (Finset.range N) (vw N C sg) g = 0 →
      ∃ E : Finset ℕ, (∀ h ∈ E, DD (N + N) (Finset.range N) C h = 0 ∧
          Relation.ReflTransGen (Rel N C sg) h g) ∧
        ∀ y : Fin N → Bool,
          (VV (vw N C sg) (List.ofFn (Fin.append (fun _ : Fin N => false) y)) g = true ↔
            ∃ h ∈ E, VV C (List.ofFn (Fin.append (fun _ : Fin N => false) y)) h = true) := by
  have hrbV := vw_rb N C hg hrb sg
  have hlen := vw_len N C sg
  have hXl : ∀ y : Fin N → Bool,
      (List.ofFn (Fin.append (fun _ : Fin N => false) y)).length = N + N := by
    intro y
    simp
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hd
    by_cases hL : DD (N + N) (Finset.Ico N (N + N)) C g = 0
    · refine ⟨∅, fun h hh => absurd hh (Finset.notMem_empty h), fun y => ?_⟩
      rw [v_off N C hg hrb sg y g hL]
      constructor
      · intro h
        cases h
      · rintro ⟨h, hh, _⟩
        exact absurd hh (Finset.notMem_empty h)
    by_cases hP : DD (N + N) (Finset.range N) C g = 0
    · refine ⟨{g}, ?_, fun y => ?_⟩
      · intro h hh
        rw [Finset.mem_singleton] at hh
        rw [hh]
        exact ⟨hP, Relation.ReflTransGen.refl⟩
      · rw [v_same N C hg hrb sg _ (hXl y) g hP]
        constructor
        · intro h
          exact ⟨g, Finset.mem_singleton_self g, h⟩
        · rintro ⟨h, hh, hv⟩
          rw [Finset.mem_singleton] at hh
          rw [hh] at hv
          exact hv
    rcases wcase (N + N) C.gates.length g with h1 | ⟨j, hj, rfl⟩ | h3
    · exfalso
      rw [DD_in (N + N) _ C g h1] at hL hP
      by_cases m1 : g ∈ Finset.Ico N (N + N)
      · by_cases m2 : g ∈ Finset.range N
        · rw [Finset.mem_Ico] at m1
          rw [Finset.mem_range] at m2
          omega
        · exact hP (ifn m2)
      · exact hL (ifn m1)
    · have hjV : j < (vw N C sg).gates.length := by omega
      have hPpos : 0 < (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 :=
        Nat.pos_of_ne_zero hP
      have hLpos : 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 :=
        Nat.pos_of_ne_zero hL
      obtain ⟨a, b, ⟨hC, hV⟩ | ⟨hC, hnc, hV⟩ | ⟨hC, hcr, c, hc, _, hV⟩⟩ := cases3 N C hg sg j hj
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        rw [D_or (N + N) _ (vw N C sg) hrbV j hjV a b hV] at hd
        have l1 := le_max_left (DD (N + N) (Finset.range N) (vw N C sg) a)
          (DD (N + N) (Finset.range N) (vw N C sg) b)
        have l2 := le_max_right (DD (N + N) (Finset.range N) (vw N C sg) a)
          (DD (N + N) (Finset.range N) (vw N C sg) b)
        obtain ⟨Ea, hEa, hva⟩ := ih a ha (by omega)
        obtain ⟨Eb, hEb, hvb⟩ := ih b hb (by omega)
        have Ra : Rel N C sg a (N + N + j) := by
          unfold Rel
          exact ⟨j, hjV, rfl, by simp [hV], congrArg Gate.op hV, hPpos, hLpos⟩
        have Rb : Rel N C sg b (N + N + j) := by
          unfold Rel
          exact ⟨j, hjV, rfl, by simp [hV], congrArg Gate.op hV, hPpos, hLpos⟩
        refine ⟨Ea ∪ Eb, ?_, fun y => ?_⟩
        · intro h hh
          rcases Finset.mem_union.1 hh with hh | hh
          · exact ⟨(hEa h hh).1, (hEa h hh).2.tail Ra⟩
          · exact ⟨(hEb h hh).1, (hEb h hh).2.tail Rb⟩
        · rw [V_or (N + N) (vw N C sg) hrbV _ (hXl y) j hjV a b hV, Bool.or_eq_true,
            hva y, hvb y]
          constructor
          · rintro (⟨h, hh, hv⟩ | ⟨h, hh, hv⟩)
            · exact ⟨h, Finset.mem_union_left _ hh, hv⟩
            · exact ⟨h, Finset.mem_union_right _ hh, hv⟩
          · rintro ⟨h, hh, hv⟩
            rcases Finset.mem_union.1 hh with hh | hh
            · exact Or.inl ⟨h, hh, hv⟩
            · exact Or.inr ⟨h, hh, hv⟩
      · have hk : (∃ i ∈ (gateAt C j).inputs, DD (N + N) (Finset.Ico N (N + N)) C i = 0) ∨
            (∀ h ∈ (gateAt C j).inputs, DD (N + N) (Finset.range N) C h = 0) := by
          by_contra hk
          exact hnc (And.intro (congrArg Gate.op hC) hk)
        rcases hk with ⟨i, hi, h0⟩ | hk
        · refine ⟨∅, fun h hh => absurd hh (Finset.notMem_empty h), fun y => ?_⟩
          have hv : VV (vw N C sg) (List.ofFn (Fin.append (fun _ : Fin N => false) y))
              (N + N + j) = false := by
            have hi0 := v_off N C hg hrb sg y i h0
            rw [hC] at hi
            rw [V_and (N + N) (vw N C sg) hrbV _ (hXl y) j hjV a b hV]
            rcases List.mem_pair.1 hi with e | e
            · rw [← e, hi0, Bool.false_and]
            · rw [← e, hi0, Bool.and_false]
          rw [hv]
          constructor
          · intro h
            cases h
          · rintro ⟨h, hh, _⟩
            exact absurd hh (Finset.notMem_empty h)
        · exfalso
          apply hP
          have ea := hk a (by simp [hC])
          have eb := hk b (by simp [hC])
          rw [D_and (N + N) _ C hrb j hj a b hC]
          omega
      · have ha : a < N + N + j := hrb j hj a (by simp [hC])
        have hb : b < N + N + j := hrb j hj b (by simp [hC])
        have hcj : c < N + N + j := by
          rcases hc with e | e <;> omega
        rw [D_or (N + N) _ (vw N C sg) hrbV j hjV c c hV, max_self] at hd
        obtain ⟨Ec, hEc, hvc⟩ := ih c hcj hd
        have Rc : Rel N C sg c (N + N + j) := by
          unfold Rel
          exact ⟨j, hjV, rfl, by simp [hV], congrArg Gate.op hV, hPpos, hLpos⟩
        refine ⟨Ec, fun h hh => ⟨(hEc h hh).1, (hEc h hh).2.tail Rc⟩, fun y => ?_⟩
        rw [V_or (N + N) (vw N C sg) hrbV _ (hXl y) j hjV c c hV, Bool.or_self]
        exact hvc y
    · exfalso
      exact hL (DD_out (N + N) _ C g h3)

end PEqualNP.Outside.L_meta_1834

theorem PEqualNP.Outside.L_meta_1834 : ∀ (Nlv16 : ℕ) (Clv16 : PEqualNP.CircuitLowerBounds.Circuit) (Vlv16 : (ℕ → Fin 2) → PEqualNP.CircuitLowerBounds.Circuit), ((∀ glv16x2 ∈ Clv16.gates, (glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x2.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) Clv16) → Vlv16 = (fun sglv16x3 : ℕ → Fin 2 => (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv16x2 : Fin Clv16.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv16x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16x1 0 = 0) ∨ (∀ hlv16x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x3 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val).inputs.getD (sglv16x3 jlv16x2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv16 jlv16x2.val))) Clv16.output)) → (∀ zlv16 : Fin (Nlv16 + Nlv16) → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) Clv16 zlv16 = true ↔ ∀ sglv16 : ℕ → Fin 2, PEqualNP.MetaComplexity.circuitFun (Nlv16 + Nlv16) (Vlv16 sglv16) zlv16 = true) ∧ (∀ sglv16x1 : ℕ → Fin 2, ((∀ glv16x1 ∈ (Vlv16 sglv16x1).gates, (glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv16x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv16x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv16 + Nlv16) (Vlv16 sglv16x1)) ∧ (∀ jlv16 < (Vlv16 sglv16x1).gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).op = PEqualNP.CircuitLowerBounds.GateOp.and → ((∃ ilv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD ilv16 0 = 0) ∨ (∀ hlv16x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x1) jlv16).inputs, ((Vlv16 sglv16x1).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16x2 0 = 0))) ∧ (Vlv16 sglv16x1).size = Clv16.size ∧ ∀ (zlv16x1 : Fin (Nlv16 + Nlv16) → Bool) (wlv16 : ℕ), (Clv16.wires (List.ofFn zlv16x1)).getD wlv16 false = true → ((Vlv16 sglv16x1).wires (List.ofFn zlv16x1)).getD wlv16 false = true) ∧ (∀ (sglv16x2 : ℕ → Fin 2) (glv16 : ℕ), ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD glv16 0 = 0 → 0 < ((Vlv16 sglv16x2).lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD glv16 0 → ∃ Elv16 : Finset ℕ, (∀ hlv16 ∈ Elv16, (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD hlv16 0 = 0 ∧ (Relation.ReflTransGen (fun alv16 blv16 : ℕ => ∃ jlv16x1 < (Vlv16 sglv16x2).gates.length, blv16 = Nlv16 + Nlv16 + jlv16x1 ∧ alv16 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).inputs ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt (Vlv16 sglv16x2) jlv16x1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.range Nlv16)).getD blv16 0 ∧ 0 < (Clv16.lineDegrees (Nlv16 + Nlv16) (Finset.Ico Nlv16 (Nlv16 + Nlv16))).getD blv16 0) hlv16 glv16)) ∧ ∀ ylv16 : Fin Nlv16 → Bool, ((Vlv16 sglv16x2).wires (List.ofFn (Fin.append (fun ulv16 : Fin Nlv16 => false) ylv16))).getD glv16 false = decide (∃ hlv16x1 ∈ Elv16, (Clv16.wires (List.ofFn (Fin.append (fun ulv16x1 : Fin Nlv16 => false) ylv16))).getD hlv16x1 false = true)) := by
  intro N C V hC hV
  subst hV
  obtain ⟨hg, hrb⟩ := hC
  refine ⟨fun z => PEqualNP.Outside.L_meta_1834.partA N C hg hrb z,
    fun sg => PEqualNP.Outside.L_meta_1834.partB N C hg hrb sg, ?_⟩
  intro sg g hd _
  obtain ⟨E, hE, hv⟩ := PEqualNP.Outside.L_meta_1834.partC N C hg hrb sg g hd
  refine ⟨E, hE, fun y => ?_⟩
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact hv y
