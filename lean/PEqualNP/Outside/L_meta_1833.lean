import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1833

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

abbrev Bin (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def rebuild (C : Circuit) (f : ℕ → Gate) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => f j), C.output⟩

theorem rlen (C : Circuit) (f : ℕ → Gate) : (rebuild C f).gates.length = C.gates.length := by
  simp [rebuild]

theorem rat (C : Circuit) (f : ℕ → Gate) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (rebuild C f) j = f j := by
  simp [gateAt, rebuild, List.getD_eq_getElem?_getD, hj]

def goodG (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem oldgood {C : Circuit} (hc : Bin C) {j : ℕ} (hj : j < C.gates.length) :
    goodG (gateAt C j) := by
  apply hc
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem buildOK {n : ℕ} {C : Circuit} {f : ℕ → Gate}
    (h : ∀ j < C.gates.length, goodG (f j) ∧ ∀ i ∈ (f j).inputs, i < n+j) :
    Bin (rebuild C f) ∧ ReadsBack n (rebuild C f) := by
  constructor
  · intro g hg
    change g ∈ List.ofFn _ at hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact (h j j.isLt).1
  · intro j hj
    rw [rlen] at hj
    rw [rat _ _ hj]
    exact (h j hj).2

def dup (a : ℕ) : Gate := ⟨GateOp.or, [a,a]⟩

abbrev readG (g : Gate) (v : ℕ → Bool) := g.op.eval (g.inputs.map v)

theorem read_dup (a : ℕ) (v : ℕ → Bool) : readG (dup a) v = v a := by
  simp [readG, dup, GateOp.eval]

theorem Zgate {n : ℕ} {C : Circuit} (hr : ReadsBack n C) (M : Finset ℕ) {j : ℕ}
    (hj : j < C.gates.length) (hg : goodG (gateAt C j)) :
    DD n M C (n+j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, DD n M C i = 0 := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hg.2
  rw [DD_gate n M C hr j hj, Gate.lineDegree, hab]
  split_ifs <;> simp [DD]

def Cross (n : ℕ) (L P : Finset ℕ) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ ((∃ i ∈ (gateAt C j).inputs, DD n L C i = 0) ∨
    (∀ i ∈ (gateAt C j).inputs, DD n P C i = 0))

def bads (n : ℕ) (L P : Finset ℕ) (C : Circuit) : Set ℕ :=
  {j | j < C.gates.length ∧ Cross n L P C j}

def pick (g : Gate) (s : Fin 2) := g.inputs.getD s.val 0

theorem pick_mem {g : Gate} (hg : goodG g) (s : Fin 2) : pick g s ∈ g.inputs := by
  unfold pick
  have h : s.val < g.inputs.length := hg.2.symm ▸ s.isLt
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

noncomputable def viewG (n : ℕ) (L P : Finset ℕ) (C : Circuit) (sg : ℕ → Fin 2) (j : ℕ) : Gate :=
  @ite Gate (Cross n L P C j) (Classical.propDecidable _) (dup (pick (gateAt C j) (sg j))) (gateAt C j)

theorem viewKill {n : ℕ} {L P : Finset ℕ} {C : Circuit} (hc : Bin C) (hr : ReadsBack n C)
    (sg : ℕ → Fin 2) (X : List Bool) (hx : X.length = n)
    (hdiff : VV (rebuild C (viewG n L P C sg)) X C.output ≠ VV C X C.output) :
    ∃ j ∈ bads n L P C, ∃ i ∈ (gateAt C j).inputs, VV C X i = true := by
  classical
  by_contra! H
  let f := viewG n L P C sg
  let B := rebuild C f
  have sub (j : ℕ) (hj : j < C.gates.length) : ∀ i ∈ (f j).inputs, i ∈ (gateAt C j).inputs := by
    dsimp [f, viewG]
    split_ifs
    · simpa [dup] using pick_mem (oldgood hc hj) (sg j)
    · exact fun _ h => h
  have br : ReadsBack n B := by
    intro j hj
    change j < (rebuild C f).gates.length at hj
    rw [rlen] at hj
    change ∀ i ∈ (gateAt (rebuild C f) j).inputs, _
    rw [rat _ _ hj]
    exact fun i hi => hr j hj i (sub j hj i hi)
  apply hdiff
  suffices ∀ w, VV B X w = VV C X w from this _
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h : w < n
    · rw [VV_in B X w (by omega), VV_in C X w (by omega)]
    by_cases h' : w < n + C.gates.length
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hb : j < B.gates.length := by simpa [B, rlen] using hj
      rw [VV_gate n B br X hx j hb, VV_gate n C hr X hx j hj]
      change readG (gateAt (rebuild C f) j) _ = _
      rw [rat _ _ hj]
      have eqv := List.map_congr_left (f := VV B X) (g := VV C X)
        (fun i (hi : i ∈ (f j).inputs) => ih i (hr j hj i (sub j hj i hi)))
      unfold readG
      rw [eqv]
      dsimp [f, viewG]
      split_ifs with hcj
      · have hz := H j (show j ∈ bads n L P C from ⟨hj,hcj⟩)
        have hz' := hz _ (pick_mem (oldgood hc hj) (sg j))
        obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (oldgood hc hj).2
        have ha := hz a (by simp [hab])
        change readG (dup _) (VV C X) = _
        rw [read_dup, Bool.eq_false_iff.mpr hz']
        rw [hcj.1, hab]
        change false = (VV C X a && (VV C X b && true))
        rw [Bool.eq_false_iff.mpr ha]
        rfl
      · rfl
    · have hl : B.gates.length = C.gates.length := rlen _ _
      rw [VV_out B X w (by omega), VV_out C X w (by omega)]

def Varies {α : Type} (v : α → Bool) : Prop := ∃ t u, v t ≠ v u

theorem stable {α : Type} {v : α → Bool} (h : ¬ Varies v) (t u : α) : v t = v u :=
  by_contra fun h' => h ⟨t,u,h'⟩

def combine (op : GateOp) (a b : Bool) : Bool := op.eval [a,b]

theorem from_left {α : Type} (op : GateOp) (ho : op = GateOp.and ∨ op = GateOp.or)
    (A B : α → Bool) (hb : ¬ Varies B) (hp : Varies fun t => combine op (A t) (B t)) :
    ∀ t, A t = combine op (A t) (B t) := by
  obtain ⟨u,w,hw⟩ := hp
  intro t
  have h1 := stable hb u t
  have h2 := stable hb w t
  dsimp only at hw
  rw [h1,h2] at hw
  rcases ho with rfl | rfl <;> cases h : B t <;> simp_all [combine, GateOp.eval]

theorem from_right {α : Type} (op : GateOp) (ho : op = GateOp.and ∨ op = GateOp.or)
    (A B : α → Bool) (ha : ¬ Varies A) (hp : Varies fun t => combine op (A t) (B t)) :
    ∀ t, B t = combine op (A t) (B t) := by
  obtain ⟨u,w,hw⟩ := hp
  intro t
  have h1 := stable ha u t
  have h2 := stable ha w t
  dsimp only at hw
  rw [h1,h2] at hw
  rcases ho with rfl | rfl <;> cases h : A t <;> simp_all [combine, GateOp.eval]

noncomputable def trim (live : ℕ → Prop) (d : ℕ) (g : Gate) : Gate := by
  classical
  exact match g.inputs with
    | [a,b] => if live a then (if live b then g else dup a)
               else (if live b then dup b else dup d)
    | _ => dup d

theorem trimFacts {α : Type} (v : ℕ → α → Bool) (d : ℕ) (g : Gate) (hg : goodG g) :
    let live := fun i => Varies (v i)
    let k := trim live d g
    goodG k ∧
    (∀ i ∈ k.inputs, i = d ∨ i ∈ g.inputs ∧ live i) ∧
    (k.op = GateOp.and → k = g ∧ ∀ i ∈ g.inputs, live i) ∧
    (Varies (fun t => readG g (fun i => v i t)) →
      (∀ i ∈ k.inputs, i ∈ g.inputs ∧ live i) ∧
      ∀ t, readG k (fun i => v i t) = readG g (fun i => v i t)) := by
  classical
  obtain ⟨op,ins⟩ := g
  obtain ⟨a,b,hi⟩ := List.length_eq_two.mp hg.2
  change ins = [a,b] at hi
  subst ins
  have ho : op = GateOp.and ∨ op = GateOp.or := hg.1
  dsimp only
  by_cases ha : Varies (v a) <;> by_cases hb : Varies (v b)
  · simp [trim, ha, hb, goodG, ho]
  · have h := from_left op ho (v a) (v b) hb
    simpa [trim, ha, hb, dup, goodG, readG, GateOp.eval, combine] using h
  · have h := from_right op ho (v a) (v b) ha
    simpa [trim, ha, hb, dup, goodG, readG, GateOp.eval, combine] using h
  · have hn : ¬ Varies (fun t => combine op (v a t) (v b t)) := by
      rintro ⟨t,u,h⟩
      exact h (by dsimp only; rw [stable ha t u, stable hb t u])
    simp [trim, ha, hb, dup, goodG, readG, combine] at hn ⊢
    tauto

theorem restrictCore {α : Type} {n m : ℕ} {L P M : Finset ℕ} {C : Circuit}
    (hc : Bin C) (hr : ReadsBack n C) (hcnt : (bads n L P C).ncard ≤ m+1)
    (X Y : α → List Bool) (hx : ∀ t, (X t).length = n) (hy : ∀ t, (Y t).length = n)
    (d : ℕ) (hd : d < n) (hdM : d ∉ M)
    (hf : ∀ i < n, Varies (fun t => VV C (Y t) i) →
      i ∉ M ∧ ∀ t, (X t).getD i false = (Y t).getD i false)
    (hout : Varies (fun t => VV C (Y t) C.output))
    (hkill : ∃ j ∈ bads n L P C, ∃ i ∈ (gateAt C j).inputs, ¬ Varies (fun t => VV C (Y t) i)) :
    ∃ D : Circuit, (Bin D ∧ ReadsBack n D) ∧ (bads n L P D).ncard ≤ m ∧ D.size ≤ C.size ∧
      (0 < D.gates.length ∧ (∀ j < D.gates.length, ∀ i ∈ (gateAt D j).inputs, DD n M D i = 0) ∧
      DD n M D D.output = 0) ∧ ∀ t, VV D (X t) D.output = VV C (Y t) C.output := by
  classical
  let v := fun i t => VV C (Y t) i
  let live := fun i => Varies (v i)
  let f := fun j => trim live d (gateAt C j)
  let B := rebuild C f
  have hl : B.gates.length = C.gates.length := rlen _ _
  have atB (j : ℕ) (hj : j < C.gates.length) : gateAt B j = f j := rat C f hj
  have facts (j : ℕ) (hj : j < C.gates.length) := trimFacts v d (gateAt C j) (oldgood hc hj)
  have bOk : Bin B ∧ ReadsBack n B := by
    apply buildOK
    intro j hj
    refine ⟨(facts j hj).1, ?_⟩
    intro i hi
    rcases (facts j hj).2.1 i hi with rfl | ⟨hin,_⟩
    · omega
    · exact hr j hj i hin
  have inv (w : ℕ) : live w →
      DD n M B w = 0 ∧ (∀ A, DD n A C w = 0 → DD n A B w = 0) ∧
      ∀ t, VV B (X t) w = v w t := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hi : w < n
      · obtain ⟨hn,he⟩ := hf w hi hw
        refine ⟨by rw [DD_in n M B w hi, ifn hn], fun A => ?_, fun t => ?_⟩
        · rw [DD_in n A B w hi, DD_in n A C w hi]
          exact id
        · dsimp [v]
          rw [VV_in B _ _ (by simpa [hx] using hi), VV_in C _ _ (by simpa [hy] using hi)]
          exact he t
      by_cases hh : w < n + C.gates.length
      · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hj' : j < B.gates.length := hl.symm ▸ hj
        have eqv (t : α) : v (n+j) t = readG (gateAt C j) (fun i => v i t) :=
          VV_gate n C hr (Y t) (hy t) j hj
        have hv : Varies (fun t => readG (gateAt C j) (fun i => v i t)) := by
          change Varies (v (n+j)) at hw
          rwa [show v (n+j) = _ from funext eqv] at hw
        obtain ⟨hin,hev⟩ := (facts j hj).2.2.2 hv
        have childInv (i : ℕ) (h : i ∈ (gateAt B j).inputs) :=
          ih i (bOk.2 j hj' i h) (hin i (by rwa [atB j hj] at h)).2
        have z (A : Finset ℕ) := Zgate bOk.2 A hj' (oldgood bOk.1 hj')
        refine ⟨(z M).2 fun i h => (childInv i h).1, ?_, ?_⟩
        · intro A ha
          have hz := (Zgate hr A hj (oldgood hc hj)).1 ha
          exact (z A).2 fun i h => (childInv i h).2.1 A (hz i (hin i (by rwa [atB j hj] at h)).1)
        · intro t
          rw [VV_gate n B bOk.2 _ (hx t) _ hj', eqv t,
            List.map_congr_left (fun i (hi : i ∈ (gateAt B j).inputs) => (childInv i hi).2.2 t), atB j hj]
          exact hev t
      · obtain ⟨t,u,htu⟩ := hw
        have hv (s : α) : v w s = false := VV_out C _ _ (by rw [hy]; omega)
        exact False.elim (htu ((hv t).trans (hv u).symm))
  have incl : bads n L P B ⊆ bads n L P C := by
    rintro j ⟨hj,hand,hn⟩
    have hjc : j < C.gates.length := hl ▸ hj
    obtain ⟨he,hKids⟩ := (facts j hjc).2.2.1 (by rwa [atB j hjc] at hand)
    have eqg : gateAt B j = gateAt C j := (atB j hjc).trans he
    refine ⟨hjc, eqg ▸ hand, ?_⟩
    rw [eqg] at hn
    rintro (⟨i,hi,h0⟩ | hall)
    · exact hn (Or.inl ⟨i,hi,(inv i (hKids i hi)).2.1 L h0⟩)
    · exact hn (Or.inr fun i hi => (inv i (hKids i hi)).2.1 P (hall i hi))
  obtain ⟨j,hj,i,hi,hn⟩ := hkill
  have strict : bads n L P B ⊂ bads n L P C := by
    refine ⟨incl, fun h => ?_⟩
    have hand := (h hj).2.1
    have hKids := ((facts j hj.1).2.2.1 (by rwa [atB j hj.1] at hand)).2
    exact hn (hKids i hi)
  have fin : (bads n L P C).Finite :=
    (Set.finite_lt_nat C.gates.length).subset fun _ h => h.1
  have count := Set.ncard_lt_ncard strict fin
  refine ⟨B, bOk, by omega, hl.le, ⟨by have := hj.1; omega, ?_, (inv C.output hout).1⟩,
    (inv C.output hout).2.2⟩
  intro k hk a ha
  have hk' : k < C.gates.length := hl ▸ hk
  rcases (facts k hk').2.1 a (by rwa [atB k hk'] at ha) with rfl | ⟨_,ha'⟩
  · rw [DD_in n M B a hd, ifn hdM]
  · exact (inv a ha').1

abbrev Assign (N : ℕ) := (Fin N → Bool) × (Fin N → Bool)

def raw {N : ℕ} (t : Assign N) := List.ofFn (Fin.append t.1 t.2)

def fixed {N : ℕ} (S W : Finset (Fin N)) (p q : Fin N → Bool) (t : Assign N) :=
  List.ofFn (Fin.append (fun a => if a ∈ S then t.1 a else p a)
    (fun a => if a ∈ W then t.2 a else q a))

def marked {N : ℕ} (S W : Finset (Fin N)) :=
  Sᶜ.image Fin.val ∪ Wᶜ.image (fun l : Fin N => N + l.val)

def botA (N : ℕ) : Assign N := ⟨fun _ => false, fun _ => false⟩

theorem mask_left {N : ℕ} (S W : Finset (Fin N)) (a : Fin N) :
    a.val ∈ marked S W ↔ a ∉ S := by
  simp only [marked, Finset.mem_union, Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro (⟨i,hi,he⟩ | ⟨i,_,he⟩)
    · exact Fin.ext he ▸ hi
    · have := a.isLt
      omega
  · exact fun h => Or.inl ⟨a,h,rfl⟩

theorem mask_right {N : ℕ} (S W : Finset (Fin N)) (a : Fin N) :
    N + a.val ∈ marked S W ↔ a ∉ W := by
  simp only [marked, Finset.mem_union, Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro (⟨i,_,he⟩ | ⟨i,hi,he⟩)
    · have := i.isLt
      omega
    · exact Fin.ext (Nat.add_left_cancel he) ▸ hi
  · exact fun h => Or.inr ⟨a,h,rfl⟩

theorem coords {N : ℕ} (S W : Finset (Fin N)) (p q : Fin N → Bool) (i : ℕ) (hi : i < N+N) :
    let Y := fixed S W p q
    (i ∈ marked S W ∧ ∀ t, (Y t).getD i false = (Y (botA N)).getD i false) ∨
    (i ∉ marked S W ∧ (Y (botA N)).getD i false = false ∧
      ∀ t, (raw t).getD i false = (Y t).getD i false) := by
  dsimp only
  by_cases h : i < N
  · have hm := mask_left S W (⟨i,h⟩ : Fin N)
    change i ∈ marked S W ↔ _ at hm
    by_cases ha : (⟨i,h⟩ : Fin N) ∈ S
    · exact Or.inr ⟨fun hc => (hm.mp hc) ha, by simp only [fixed, app_getD]; simp [h, ha, botA],
        fun t => by simp only [raw, fixed, app_getD]; simp [h, ha]⟩
    · exact Or.inl ⟨hm.mpr ha, fun t => by simp only [fixed, app_getD]; simp [h, ha]⟩
  · have h2 : i-N < N := by omega
    have hm := mask_right S W (⟨i-N,h2⟩ : Fin N)
    change N + (i-N) ∈ marked S W ↔ _ at hm
    rw [show N + (i-N) = i by omega] at hm
    by_cases ha : (⟨i-N,h2⟩ : Fin N) ∈ W
    · exact Or.inr ⟨fun hc => (hm.mp hc) ha, by simp only [fixed, app_getD]; simp [h, h2, ha, botA],
        fun t => by simp only [raw, fixed, app_getD]; simp [h, h2, ha]⟩
    · exact Or.inl ⟨hm.mpr ha, fun t => by simp only [fixed, app_getD]; simp [h, h2, ha]⟩

theorem varying_input {α : Type} {n : ℕ} (C : Circuit) (Y : α → List Bool)
    (hy : ∀ t, (Y t).length = n) (hout : Varies fun t => VV C (Y t) C.output) :
    ∃ i < n, Varies fun t => VV C (Y t) i := by
  classical
  obtain ⟨t,u,hu⟩ := hout
  by_contra! hh
  apply hu
  have he : Y t = Y u := by
    apply List.ext_getElem (by rw [hy, hy])
    intro i ht hU
    have hi : i < n := hy t ▸ ht
    have h := stable (hh i hi) t u
    change VV C (Y t) i = VV C (Y u) i at h
    rw [VV_in C _ _ ht, VV_in C _ _ hU, List.getD_eq_getElem _ _ ht,
      List.getD_eq_getElem _ _ hU] at h
    exact h
  dsimp only
  rw [he]

end PEqualNP.Outside.L_meta_1833

theorem PEqualNP.Outside.L_meta_1833 : ∀ (Nlv15 mlv15 : ℕ) (Clv15 : PEqualNP.CircuitLowerBounds.Circuit) (Slv15 Wlv15 : Finset (Fin Nlv15)) (pilv15 nulv15 : Fin Nlv15 → Bool) (sglv15 : ℕ → Fin 2), ((∀ glv15 ∈ Clv15.gates, (glv15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Clv15) → Set.ncard {jlv15 : ℕ | jlv15 < Clv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15 0 = 0) ∨ (∀ hlv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15 0 = 0))} ≤ mlv15 + 1 → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15x1 : Fin Clv15.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x1 0 = 0) ∨ (∀ hlv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val))) Clv15.output) (Fin.append (fun plv15 : Fin Nlv15 => if plv15 ∈ Slv15 then (fun ulv15 : Fin Nlv15 => false) plv15 else pilv15 plv15) (fun llv15 : Fin Nlv15 => if llv15 ∈ Wlv15 then (fun ulv15x1 : Fin Nlv15 => false) llv15 else nulv15 llv15)) = true → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x1 : Fin Nlv15 => if plv15x1 ∈ Slv15 then (fun ulv15x2 : Fin Nlv15 => false) plv15x1 else pilv15 plv15x1) (fun llv15x1 : Fin Nlv15 => if llv15x1 ∈ Wlv15 then (fun ulv15x3 : Fin Nlv15 => false) llv15x1 else nulv15 llv15x1)) = false → (∃ xlv15 ylv15 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x2 : Fin Nlv15 => if plv15x2 ∈ Slv15 then xlv15 plv15x2 else pilv15 plv15x2) (fun llv15x2 : Fin Nlv15 => if llv15x2 ∈ Wlv15 then ylv15 llv15x2 else nulv15 llv15x2)) = true) → ∃ Dlv15 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15x1 ∈ Dlv15.gates, (glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Dlv15) ∧ Set.ncard {jlv15x2 : ℕ | jlv15x2 < Dlv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x2 0 = 0) ∨ (∀ hlv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x2 0 = 0))} ≤ mlv15 ∧ Dlv15.size ≤ Clv15.size ∧ (0 < Dlv15.gates.length ∧ (∀ jlv15x3 < Dlv15.gates.length, ∀ ilv15x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x3).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x3 : Fin Nlv15 => (plv15x3 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x3 : Fin Nlv15 => Nlv15 + (llv15x3 : ℕ)) (Wlv15)ᶜ)).getD ilv15x3 0 = 0) ∧ (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x4 : Fin Nlv15 => (plv15x4 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x4 : Fin Nlv15 => Nlv15 + (llv15x4 : ℕ)) (Wlv15)ᶜ)).getD Dlv15.output 0 = 0) ∧ ∀ xlv15x1 ylv15x1 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Dlv15 (Fin.append xlv15x1 ylv15x1) = PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x5 : Fin Nlv15 => if plv15x5 ∈ Slv15 then xlv15x1 plv15x5 else pilv15 plv15x5) (fun llv15x5 : Fin Nlv15 => if llv15x5 ∈ Wlv15 then ylv15x1 llv15x5 else nulv15 llv15x5)) := by
  classical
  open PEqualNP.Outside.L_meta_1833 in
    intro N m C S W p q sg hc hcnt hv h0 hex
    let X := @raw N
    let Y := fixed S W p q
    let z := botA N
    have hx (t : Assign N) : (X t).length = N+N := List.length_ofFn
    have hy (t : Assign N) : (Y t).length = N+N := List.length_ofFn
    change VV C (Y z) C.output = false at h0
    obtain ⟨x,y,hxy⟩ := hex
    change VV C (Y (x,y)) C.output = true at hxy
    have hout : Varies (fun t => VV C (Y t) C.output) := ⟨z,(x,y),by simp only [h0,hxy]; decide⟩
    have hf (i : ℕ) (hi : i < N+N) (hvi : Varies (fun t => VV C (Y t) i)) :
        i ∉ marked S W ∧ ∀ t, (X t).getD i false = (Y t).getD i false := by
      rcases coords S W p q i hi with ⟨_,he⟩ | ⟨hn,_,he⟩
      · obtain ⟨t,u,htu⟩ := hvi
        apply False.elim
        apply htu
        dsimp only
        rw [VV_in C _ _ (by rw [hy]; exact hi), VV_in C _ _ (by rw [hy]; exact hi)]
        exact (he t).trans (he u).symm
      · exact ⟨hn,he⟩
    obtain ⟨d,hd,hdv⟩ := varying_input C Y hy hout
    let L := Finset.Ico N (N+N)
    let P := Finset.range N
    change VV (rebuild C (viewG (N+N) L P C sg)) (Y z) C.output = true at hv
    obtain ⟨j,hj,i,hi,ht⟩ := viewKill (L := L) (P := P) hc.1 hc.2 sg (Y z) (hy z)
      (by rw [hv,h0]; decide)
    have alwaysT (t : Assign N) : VV C (Y t) i = true := by
      apply mono C.gates (Y z) (Y t) (by rw [hy,hy]) (fun g hg => (hc.1 g hg).1) _ i ht
      intro k hk
      by_cases hb : k < N+N
      · rcases coords S W p q k hb with ⟨_,he⟩ | ⟨_,he,_⟩
        · exact (he t).trans hk
        · exact False.elim (Bool.noConfusion (he.symm.trans hk))
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hy]; omega)] at hk
        contradiction
    obtain ⟨D,hD,hcD,hsD,hcl,he⟩ := restrictCore (M := marked S W) hc.1 hc.2 hcnt
      X Y hx hy d hd (hf d hd hdv).1 hf hout ⟨j,hj,i,hi,by
        rintro ⟨t,u,h⟩
        exact h ((alwaysT t).trans (alwaysT u).symm)⟩
    exact ⟨D,hD,hcD,hsD,hcl,fun x y => he (x,y)⟩
