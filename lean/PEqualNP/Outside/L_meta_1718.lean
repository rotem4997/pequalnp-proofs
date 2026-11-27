import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1718

def fo {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) : List α :=
  G.foldl (fun w g => w ++ [Φ g (g.inputs.map fun i => w.getD i dflt)]) x

def gv {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ) : α :=
  (fo dflt Φ G x).getD i dflt

def gd : Gate := ⟨GateOp.or, []⟩

def Φb (g : Gate) (l : List Bool) : Bool := g.op.eval l

def Φd (g : Gate) (l : List ℕ) : ℕ :=
  @ite ℕ (g.op = GateOp.and) (lineDegreeGateOpDecEq g.op GateOp.and) l.sum (l.foldr max 0)

theorem hA_fo_append {α : Type} (dflt : α) (Φ : Gate → List α → α) (G1 G2 : List Gate) (x : List α) :
    fo dflt Φ (G1 ++ G2) x = fo dflt Φ G2 (fo dflt Φ G1 x) := by
  unfold fo
  rw [List.foldl_append]

theorem hA_fo_pre {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) :
    ∀ x : List α, ∃ t, fo dflt Φ G x = x ++ t ∧ t.length = G.length := by
  induction G with
  | nil => intro x; exact ⟨[], by simp [fo], rfl⟩
  | cons g G ih =>
    intro x
    obtain ⟨t, ht, hl⟩ := ih (x ++ [Φ g (g.inputs.map fun i => x.getD i dflt)])
    refine ⟨Φ g (g.inputs.map fun i => x.getD i dflt) :: t, ?_, by simp [hl]⟩
    show fo dflt Φ G (x ++ [Φ g (g.inputs.map fun i => x.getD i dflt)]) = _
    rw [ht]
    simp

theorem hA_fo_len {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) :
    (fo dflt Φ G x).length = x.length + G.length := by
  obtain ⟨t, ht, hl⟩ := hA_fo_pre dflt Φ G x
  rw [ht, List.length_append, hl]

theorem gv_stable {α : Type} (dflt : α) (Φ : Gate → List α → α) (G1 G2 : List Gate) (x : List α) (i : ℕ)
    (h : i < x.length + G1.length) : gv dflt Φ (G1 ++ G2) x i = gv dflt Φ G1 x i := by
  have hl := hA_fo_len dflt Φ G1 x
  obtain ⟨t, ht, _⟩ := hA_fo_pre dflt Φ G2 (fo dflt Φ G1 x)
  show (fo dflt Φ (G1 ++ G2) x).getD i dflt = (fo dflt Φ G1 x).getD i dflt
  rw [hA_fo_append, ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega)]

theorem gv_input {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ)
    (h : i < x.length) : gv dflt Φ G x i = x.getD i dflt := by
  obtain ⟨t, ht, _⟩ := hA_fo_pre dflt Φ G x
  show (fo dflt Φ G x).getD i dflt = x.getD i dflt
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gv_oob {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α) (i : ℕ)
    (h : x.length + G.length ≤ i) : gv dflt Φ G x i = dflt := by
  have hl := hA_fo_len dflt Φ G x
  show (fo dflt Φ G x).getD i dflt = dflt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem gv_snoc {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (g : Gate) (x : List α) :
    gv dflt Φ (G ++ [g]) x (x.length + G.length) = Φ g (g.inputs.map (gv dflt Φ G x)) := by
  have hl := hA_fo_len dflt Φ G x
  show (fo dflt Φ (G ++ [g]) x).getD (x.length + G.length) dflt =
    Φ g (g.inputs.map fun i => (fo dflt Φ G x).getD i dflt)
  rw [hA_fo_append]
  show ((fo dflt Φ G x) ++ [Φ g (g.inputs.map fun i => (fo dflt Φ G x).getD i dflt)]).getD
    (x.length + G.length) dflt = _
  rw [← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem gv_gate {α : Type} (dflt : α) (Φ : Gate → List α → α) (G : List Gate) (x : List α)
    (hrb : ∀ j < G.length, ∀ i ∈ (G.getD j gd).inputs, i < x.length + j) (j : ℕ) (hj : j < G.length) :
    gv dflt Φ G x (x.length + j) = Φ (G.getD j gd) ((G.getD j gd).inputs.map (gv dflt Φ G x)) := by
  have hsplit : (G.take j ++ [G.getD j gd]) ++ G.drop (j + 1) = G := by
    have hg : G.getD j gd = G[j] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg]
    simp
  have hlen : (G.take j).length = j := by
    rw [List.length_take]
    omega
  have h1 : gv dflt Φ ((G.take j ++ [G.getD j gd]) ++ G.drop (j + 1)) x (x.length + j) =
      gv dflt Φ (G.take j ++ [G.getD j gd]) x (x.length + j) :=
    gv_stable dflt Φ _ _ x _ (by rw [List.length_append, hlen, List.length_singleton]; omega)
  rw [hsplit] at h1
  have h2 := gv_snoc dflt Φ (G.take j) (G.getD j gd) x
  rw [hlen] at h2
  rw [h1, h2]
  congr 1
  apply List.map_congr_left
  intro i hi
  have h3 := gv_stable dflt Φ (G.take j) (G.drop j) x i (by rw [hlen]; exact hrb j hj i hi)
  rw [List.take_append_drop] at h3
  exact h3.symm
theorem hA_getD_lt (G : List Gate) (g : Gate) (j : ℕ) (h : j < G.length) :
    (G ++ [g]).getD j gd = G.getD j gd := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem hA_getD_eq (G : List Gate) (g : Gate) : (G ++ [g]).getD G.length gd = g := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

def d0 (N : ℕ) (M : Finset ℕ) : List ℕ := (List.range (N + N)).map fun i => if i ∈ M then 1 else 0

def dg (N : ℕ) (M : Finset ℕ) (G : List Gate) (i : ℕ) : ℕ := gv 0 Φd G (d0 N M) i

theorem d0_len (N : ℕ) (M : Finset ℕ) : (d0 N M).length = N + N := by simp [d0]

def absb : GateOp → Bool
  | GateOp.or => true
  | _ => false

def comb (op : GateOp) (va vb : Bool ⊕ ℕ) (k : ℕ) : List Gate × (Bool ⊕ ℕ) :=
  match va, vb with
  | Sum.inl c, v => if c = absb op then ([], Sum.inl c) else ([], v)
  | Sum.inr w, Sum.inl c => if c = absb op then ([], Sum.inl c) else ([], Sum.inr w)
  | Sum.inr wa, Sum.inr wb => ([⟨op, [wa, wb]⟩], Sum.inr k)

def rin (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool) (x y : Fin N → Bool) : List Bool :=
  List.ofFn (Fin.append (fun u => decide (u ∈ S) && x u) (fun t => if t ∈ W then y t else nu t))

def ov (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool) (D : Circuit) (x y : Fin N → Bool)
    (i : ℕ) : Bool := gv false Φb D.gates (rin N S W nu x y) i

def nv (N : ℕ) (H : List Gate) (x y : Fin N → Bool) (w : ℕ) : Bool :=
  gv false Φb H (List.ofFn (Fin.append x y)) w

def V0 (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool) (i : ℕ) : Bool ⊕ ℕ :=
  if h : i < N then (if (⟨i, h⟩ : Fin N) ∈ S then Sum.inr i else Sum.inl false)
  else if h2 : i < N + N then
    (if (⟨i - N, by omega⟩ : Fin N) ∈ W then Sum.inr i else Sum.inl (nu ⟨i - N, by omega⟩))
  else Sum.inl false

def build (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool) (D : Circuit) :
    ℕ → List Gate × (ℕ → Bool ⊕ ℕ)
  | 0 => ([], V0 N S W nu)
  | j + 1 =>
    ((build N S W nu D j).1 ++ (comb (D.gates.getD j gd).op
        ((build N S W nu D j).2 ((D.gates.getD j gd).inputs.getD 0 0))
        ((build N S W nu D j).2 ((D.gates.getD j gd).inputs.getD 1 0))
        (N + N + (build N S W nu D j).1.length)).1,
      fun i => if i = N + N + j then (comb (D.gates.getD j gd).op
        ((build N S W nu D j).2 ((D.gates.getD j gd).inputs.getD 0 0))
        ((build N S W nu D j).2 ((D.gates.getD j gd).inputs.getD 1 0))
        (N + N + (build N S W nu D j).1.length)).2 else (build N S W nu D j).2 i)

def Good (N : ℕ) (S W : Finset (Fin N)) (nu : Fin N → Bool) (D : Circuit) (H : List Gate)
    (v : Bool ⊕ ℕ) (i : ℕ) : Prop :=
  (∀ c, v = Sum.inl c → ∀ x y, ov N S W nu D x y i = c) ∧
  (∀ w, v = Sum.inr w → w < N + N + H.length ∧ (∀ x y, nv N H x y w = ov N S W nu D x y i) ∧
     ∀ M, dg N M H w ≤ dg N M D.gates i)

def OkH (N : ℕ) (H : List Gate) : Prop :=
  (∀ g ∈ H, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < H.length, ∀ i ∈ (H.getD j gd).inputs, i < N + N + j) ∧
  (∀ j < H.length, (H.getD j gd).op = GateOp.and →
    (∃ i ∈ (H.getD j gd).inputs, dg N (Finset.Ico N (N + N)) H i = 0) ∨
    (∀ h ∈ (H.getD j gd).inputs, dg N (Finset.range N) H h = 0))

theorem good_ext {N : ℕ} {S W : Finset (Fin N)} {nu : Fin N → Bool} {D : Circuit} {H : List Gate}
    {v : Bool ⊕ ℕ} {i : ℕ} (E : List Gate) (h : Good N S W nu D H v i) :
    Good N S W nu D (H ++ E) v i := by
  refine ⟨h.1, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 w hw
  refine ⟨by rw [List.length_append]; omega, fun x y => ?_, fun M => ?_⟩
  · rw [← h2 x y]
    exact gv_stable false Φb H E _ w (by rw [List.length_ofFn]; exact h1)
  · have := gv_stable 0 Φd H E (d0 N M) w (by rw [d0_len]; exact h1)
    show gv 0 Φd (H ++ E) (d0 N M) w ≤ _
    rw [this]
    exact h3 M

theorem ok_snoc {N : ℕ} {H : List Gate} (hH : OkH N H) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (wa wb : ℕ)
    (ha : wa < N + N + H.length) (hb : wb < N + N + H.length)
    (hk : op = GateOp.and → (dg N (Finset.Ico N (N + N)) H wa = 0 ∨
        dg N (Finset.Ico N (N + N)) H wb = 0) ∨
      (dg N (Finset.range N) H wa = 0 ∧ dg N (Finset.range N) H wb = 0)) :
    OkH N (H ++ [⟨op, [wa, wb]⟩]) := by
  obtain ⟨h1, h2, h3⟩ := hH
  have hst : ∀ M i, i < N + N + H.length → dg N M (H ++ [⟨op, [wa, wb]⟩]) i = dg N M H i :=
    fun M i hi => gv_stable 0 Φd H _ (d0 N M) i (by rw [d0_len]; exact hi)
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      exact ⟨hop, rfl⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [hA_getD_lt _ _ _ hj] at hi
      have := h2 j hj i hi
      omega
    · subst hj
      rw [hA_getD_eq] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [hA_getD_lt _ _ _ hj] at hand ⊢
      rcases h3 j hj hand with ⟨i, hi, hz⟩ | hz
      · left
        exact ⟨i, hi, by rw [hst _ _ (by have := h2 j hj i hi; omega)]; exact hz⟩
      · right
        intro h hh
        rw [hst _ _ (by have := h2 j hj h hh; omega)]
        exact hz h hh
    · subst hj
      rw [hA_getD_eq] at hand ⊢
      rcases hk hand with (hz | hz) | ⟨hz1, hz2⟩
      · left
        exact ⟨wa, by simp, by rw [hst _ _ ha]; exact hz⟩
      · left
        exact ⟨wb, by simp, by rw [hst _ _ hb]; exact hz⟩
      · right
        intro h hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl
        · rw [hst _ _ ha]; exact hz1
        · rw [hst _ _ hb]; exact hz2

theorem eval_abs_l (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (q : Bool) :
    op.eval [absb op, q] = absb op := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, absb]

theorem eval_abs_r (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p : Bool) :
    op.eval [p, absb op] = absb op := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, absb]

theorem eval_neu_l (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (c q : Bool)
    (hc : c ≠ absb op) : op.eval [c, q] = q := by
  rcases hop with rfl | rfl <;> cases c <;> simp_all [GateOp.eval, absb]

theorem eval_neu_r (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (p c : Bool)
    (hc : c ≠ absb op) : op.eval [p, c] = p := by
  rcases hop with rfl | rfl <;> cases c <;> simp_all [GateOp.eval, absb]

theorem Φd_ge (g : Gate) (p q : ℕ) : p ≤ Φd g [p, q] ∧ q ≤ Φd g [p, q] := by
  unfold Φd
  split_ifs
  · simp only [List.sum_cons, List.sum_nil]
    omega
  · simp only [List.foldr_cons, List.foldr_nil]
    omega

theorem Φd_mono (g g' : Gate) (h : g.op = g'.op) {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') :
    Φd g [p, q] ≤ Φd g' [p', q'] := by
  unfold Φd
  rw [h]
  split_ifs
  · simp only [List.sum_cons, List.sum_nil]
    omega
  · simp only [List.foldr_cons, List.foldr_nil]
    omega

theorem nv_snoc (N : ℕ) (H : List Gate) (g : Gate) (x y : Fin N → Bool) :
    nv N (H ++ [g]) x y (N + N + H.length) = g.op.eval (g.inputs.map (nv N H x y)) := by
  have := gv_snoc false Φb H g (List.ofFn (Fin.append x y))
  rw [List.length_ofFn] at this
  exact this

theorem dg_snoc (N : ℕ) (M : Finset ℕ) (H : List Gate) (g : Gate) :
    dg N M (H ++ [g]) (N + N + H.length) = Φd g (g.inputs.map (dg N M H)) := by
  have := gv_snoc 0 Φd H g (d0 N M)
  rw [d0_len] at this
  exact this

theorem old_gate {N : ℕ} {S W : Finset (Fin N)} {nu : Fin N → Bool} {D : Circuit}
    (hR : ∀ j < D.gates.length, ∀ i ∈ (D.gates.getD j gd).inputs, i < N + N + j) (j : ℕ)
    (hj : j < D.gates.length) :
    (∀ x y, ov N S W nu D x y (N + N + j) =
      (D.gates.getD j gd).op.eval ((D.gates.getD j gd).inputs.map (ov N S W nu D x y))) ∧
    (∀ M, dg N M D.gates (N + N + j) =
      Φd (D.gates.getD j gd) ((D.gates.getD j gd).inputs.map (dg N M D.gates))) := by
  constructor
  · intro x y
    have hl : (rin N S W nu x y).length = N + N := List.length_ofFn
    have := gv_gate false Φb D.gates (rin N S W nu x y) (by rw [hl]; exact hR) j hj
    rw [hl] at this
    exact this
  · intro M
    have := gv_gate 0 Φd D.gates (d0 N M) (by rw [d0_len]; exact hR) j hj
    rw [d0_len] at this
    exact this

theorem comb_ok {N : ℕ} {S W : Finset (Fin N)} {nu : Fin N → Bool} {D : Circuit} {H : List Gate}
    (hH : OkH N H) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b i : ℕ) (va vb : Bool ⊕ ℕ) (ga : Good N S W nu D H va a) (gb : Good N S W nu D H vb b)
    (hval : ∀ x y, ov N S W nu D x y i = op.eval [ov N S W nu D x y a, ov N S W nu D x y b])
    (hdeg : ∀ M, dg N M D.gates i = Φd ⟨op, [a, b]⟩ [dg N M D.gates a, dg N M D.gates b])
    (hk : op = GateOp.and → (dg N (Finset.Ico N (N + N)) D.gates a = 0 ∨
        dg N (Finset.Ico N (N + N)) D.gates b = 0) ∨
      (dg N (Finset.range N) D.gates a = 0 ∧ dg N (Finset.range N) D.gates b = 0)) :
    OkH N (H ++ (comb op va vb (N + N + H.length)).1) ∧
    (comb op va vb (N + N + H.length)).1.length ≤ 1 ∧
    Good N S W nu D (H ++ (comb op va vb (N + N + H.length)).1)
      (comb op va vb (N + N + H.length)).2 i := by
  rcases va with c | wa <;> rcases vb with d | wb
  · simp only [comb]
    split_ifs with hc
    · simp only [List.append_nil, List.length_nil, zero_le, true_and]
      refine ⟨hH, fun c' hc' x y => ?_, fun w hw => by cases hw⟩
      cases hc'
      rw [hval, ga.1 c rfl x y, hc, eval_abs_l op hop]
    · simp only [List.append_nil, List.length_nil, zero_le, true_and]
      refine ⟨hH, fun c' hc' x y => ?_, fun w hw => by cases hw⟩
      cases hc'
      rw [hval, ga.1 c rfl x y, gb.1 d rfl x y, eval_neu_l op hop c d hc]
  · simp only [comb]
    split_ifs with hc
    · simp only [List.append_nil, List.length_nil, zero_le, true_and]
      refine ⟨hH, fun c' hc' x y => ?_, fun w hw => by cases hw⟩
      cases hc'
      rw [hval, ga.1 c rfl x y, hc, eval_abs_l op hop]
    · simp only [List.append_nil, List.length_nil, zero_le, true_and]
      refine ⟨hH, (fun c' hc' => by cases hc'), fun w hw => ?_⟩
      cases hw
      obtain ⟨h1, h2, h3⟩ := gb.2 wb rfl
      refine ⟨h1, fun x y => ?_, fun M => ?_⟩
      · rw [hval, h2, ga.1 c rfl x y, eval_neu_l op hop c _ hc]
      · rw [hdeg]
        exact le_trans (h3 M) (Φd_ge _ _ _).2
  · simp only [comb]
    split_ifs with hc
    · simp only [List.append_nil, List.length_nil, zero_le, true_and]
      refine ⟨hH, fun c' hc' x y => ?_, fun w hw => by cases hw⟩
      cases hc'
      rw [hval, gb.1 d rfl x y, hc, eval_abs_r op hop]
    · simp only [List.append_nil, List.length_nil, zero_le, true_and]
      refine ⟨hH, (fun c' hc' => by cases hc'), fun w hw => ?_⟩
      cases hw
      obtain ⟨h1, h2, h3⟩ := ga.2 wa rfl
      refine ⟨h1, fun x y => ?_, fun M => ?_⟩
      · rw [hval, h2, gb.1 d rfl x y, eval_neu_r op hop _ d hc]
      · rw [hdeg]
        exact le_trans (h3 M) (Φd_ge _ _ _).1
  · simp only [comb]
    obtain ⟨ha1, ha2, ha3⟩ := ga.2 wa rfl
    obtain ⟨hb1, hb2, hb3⟩ := gb.2 wb rfl
    refine ⟨ok_snoc hH op hop wa wb ha1 hb1 ?_, by simp, (fun c' hc' => by cases hc'), fun w hw => ?_⟩
    · intro hand
      have z : ∀ M u v, dg N M H u ≤ dg N M D.gates v → dg N M D.gates v = 0 →
          dg N M H u = 0 := fun M u v h1 h2 => by omega
      rcases hk hand with (hz | hz) | ⟨hz1, hz2⟩
      · exact Or.inl (Or.inl (z _ _ _ (ha3 _) hz))
      · exact Or.inl (Or.inr (z _ _ _ (hb3 _) hz))
      · exact Or.inr ⟨z _ _ _ (ha3 _) hz1, z _ _ _ (hb3 _) hz2⟩
    · cases hw
      refine ⟨by simp, fun x y => ?_, fun M => ?_⟩
      · rw [nv_snoc, hval]
        simp only [List.map_cons, List.map_nil]
        rw [ha2, hb2]
      · rw [dg_snoc, hdeg]
        exact Φd_mono _ _ rfl (ha3 M) (hb3 M)

theorem app_left {N : ℕ} (x y : Fin N → Bool) (i : ℕ) (h : i < N) :
    (List.ofFn (Fin.append x y)).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (by omega : i < N + N)]
  exact Fin.append_left x y ⟨i, h⟩

theorem app_right {N : ℕ} (x y : Fin N → Bool) (i : ℕ) (h1 : N ≤ i) (h2 : i < N + N) :
    (List.ofFn (Fin.append x y)).getD i false = y ⟨i - N, by omega⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h2]
  have e : (⟨i, h2⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := Fin.ext (by simp; omega)
  show Fin.append x y ⟨i, h2⟩ = _
  rw [e]
  exact Fin.append_right x y _

theorem ok_nil (N : ℕ) : OkH N [] := ⟨by simp, by simp, by simp⟩

theorem base_good {N : ℕ} {S W : Finset (Fin N)} {nu : Fin N → Bool} {D : Circuit} (i : ℕ)
    (hi : i < N + N + 0) : Good N S W nu D [] (V0 N S W nu i) i := by
  have hl : ∀ x y : Fin N → Bool, (List.ofFn (Fin.append x y)).length = N + N :=
    fun _ _ => List.length_ofFn
  have hnv : ∀ x y, nv N [] x y i = (List.ofFn (Fin.append x y)).getD i false := fun x y =>
    gv_input false Φb [] _ i (by rw [hl]; omega)
  have hov : ∀ x y, ov N S W nu D x y i = (rin N S W nu x y).getD i false := fun x y =>
    gv_input false Φb D.gates _ i (by rw [rin, hl]; omega)
  have hdg : ∀ M, dg N M [] i ≤ dg N M D.gates i := fun M => by
    have e1 := gv_input 0 Φd [] (d0 N M) i (by rw [d0_len]; omega)
    have e2 := gv_input 0 Φd D.gates (d0 N M) i (by rw [d0_len]; omega)
    show gv 0 Φd [] (d0 N M) i ≤ gv 0 Φd D.gates (d0 N M) i
    rw [e1, e2]
  unfold V0
  split_ifs with h1 hS h2 hW
  · refine ⟨(fun c hc => by cases hc), fun w hw => ?_⟩
    cases hw
    refine ⟨by simpa using hi, fun x y => ?_, hdg⟩
    rw [hnv, hov, rin, app_left _ _ _ h1, app_left _ _ _ h1]
    simp [hS]
  · refine ⟨fun c hc x y => ?_, fun w hw => by cases hw⟩
    cases hc
    rw [hov, rin, app_left _ _ _ h1]
    simp [hS]
  · refine ⟨(fun c hc => by cases hc), fun w hw => ?_⟩
    cases hw
    refine ⟨by simpa using hi, fun x y => ?_, hdg⟩
    rw [hnv, hov, rin, app_right _ _ _ (by omega) h2, app_right _ _ _ (by omega) h2]
    simp only [hW, if_true]
  · refine ⟨fun c hc x y => ?_, fun w hw => by cases hw⟩
    cases hc
    rw [hov, rin, app_right _ _ _ (by omega) h2]
    simp only [hW, if_false]
  · omega

theorem build_inv {N : ℕ} {S W : Finset (Fin N)} {nu : Fin N → Bool} {D : Circuit}
    (hD : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ∀ j < D.gates.length, ∀ i ∈ (D.gates.getD j gd).inputs, i < N + N + j)
    (hK : ∀ j < D.gates.length, (D.gates.getD j gd).op = GateOp.and →
      (∃ i ∈ (D.gates.getD j gd).inputs, dg N (Finset.Ico N (N + N)) D.gates i = 0) ∨
      (∀ h ∈ (D.gates.getD j gd).inputs, dg N (Finset.range N) D.gates h = 0)) :
    ∀ j ≤ D.gates.length, OkH N (build N S W nu D j).1 ∧ (build N S W nu D j).1.length ≤ j ∧
      (∀ i < N + N + j, Good N S W nu D (build N S W nu D j).1 ((build N S W nu D j).2 i) i) ∧
      (∀ i, N + N + j ≤ i → (build N S W nu D j).2 i = Sum.inl false) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨ok_nil N, le_refl _, fun i hi => base_good i hi, fun i hi => ?_⟩
    show V0 N S W nu i = Sum.inl false
    unfold V0
    rw [dif_neg (by omega), dif_neg (by omega)]
  | succ j ih =>
    intro hj
    obtain ⟨hO, hL, hG, hB⟩ := ih (by omega)
    have hjl : j < D.gates.length := by omega
    have hmem : D.gates.getD j gd ∈ D.gates := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
      exact List.getElem_mem hjl
    obtain ⟨hop, hlen⟩ := hD _ hmem
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
    have ha : a < N + N + j := hR j hjl a (by rw [hab]; simp)
    have hb : b < N + N + j := hR j hjl b (by rw [hab]; simp)
    obtain ⟨hval, hdeg⟩ := old_gate (S := S) (W := W) (nu := nu) hR j hjl
    have hc := comb_ok hO (D.gates.getD j gd).op hop a b (N + N + j)
      ((build N S W nu D j).2 a) ((build N S W nu D j).2 b) (hG a (by omega)) (hG b (by omega))
      (fun x y => by rw [hval x y, hab]; rfl) (fun M => by rw [hdeg M, hab]; rfl)
      (fun hand => by
        rcases hK j hjl hand with ⟨i, hi, hz⟩ | hz
        · rw [hab] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact Or.inl (Or.inl hz)
          · exact Or.inl (Or.inr hz)
        · rw [hab] at hz
          exact Or.inr ⟨hz a (by simp), hz b (by simp)⟩)
    have e1 : (build N S W nu D (j + 1)).1 = (build N S W nu D j).1 ++
        (comb (D.gates.getD j gd).op ((build N S W nu D j).2 a) ((build N S W nu D j).2 b)
          (N + N + (build N S W nu D j).1.length)).1 := by
      simp only [build, hab, List.getD_cons_zero, List.getD_cons_succ]
    have e2 : ∀ i, (build N S W nu D (j + 1)).2 i = if i = N + N + j then
        (comb (D.gates.getD j gd).op ((build N S W nu D j).2 a) ((build N S W nu D j).2 b)
          (N + N + (build N S W nu D j).1.length)).2 else (build N S W nu D j).2 i := by
      intro i
      simp only [build, hab, List.getD_cons_zero, List.getD_cons_succ]
    rw [e1]
    refine ⟨hc.1, by rw [List.length_append]; have := hc.2.1; omega, fun i hi => ?_, fun i hi => ?_⟩
    · rw [e2]
      by_cases hij : i = N + N + j
      · rw [if_pos hij]
        subst hij
        exact hc.2.2
      · rw [if_neg hij]
        exact good_ext _ (hG i (by omega))
    · rw [e2, if_neg (by omega)]
      exact hB i (by omega)

end PEqualNP.Outside.L_meta_1718

theorem PEqualNP.Outside.L_meta_1718 : ∀ (N121 : ℕ) (D121 : PEqualNP.CircuitLowerBounds.Circuit) (S121 W121 : Finset (Fin N121)) (nu121 : Fin N121 → Bool), (∀ g121 ∈ D121.gates, (g121.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g121.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g121.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N121 + N121) D121 → (∀ j121 < D121.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i121 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).inputs, (D121.lineDegrees (N121 + N121) (Finset.Ico N121 (N121 + N121))).getD i121 0 = 0) ∨ (∀ h121 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D121 j121).inputs, (D121.lineDegrees (N121 + N121) (Finset.range N121)).getD h121 0 = 0)) → (∃ x121 y121 xa121 ya121 : Fin N121 → Bool, PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121 => decide (u121 ∈ S121) && x121 u121) (fun t121 => if t121 ∈ W121 then y121 t121 else nu121 t121)) ≠ PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121a => decide (u121a ∈ S121) && xa121 u121a) (fun t121a => if t121a ∈ W121 then ya121 t121a else nu121 t121a))) → ∃ E121 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ g121a ∈ E121.gates, (g121a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g121a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g121a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N121 + N121) E121) ∧ (∀ j121a < E121.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i121a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).inputs, (E121.lineDegrees (N121 + N121) (Finset.Ico N121 (N121 + N121))).getD i121a 0 = 0) ∨ (∀ h121a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt E121 j121a).inputs, (E121.lineDegrees (N121 + N121) (Finset.range N121)).getD h121a 0 = 0)) ∧ E121.size ≤ D121.size ∧ ∀ x121a y121a : Fin N121 → Bool, PEqualNP.MetaComplexity.circuitFun (N121 + N121) E121 (Fin.append x121a y121a) = PEqualNP.MetaComplexity.circuitFun (N121 + N121) D121 (Fin.append (fun u121b => decide (u121b ∈ S121) && x121a u121b) (fun t121b => if t121b ∈ W121 then y121a t121b else nu121 t121b)) := by
  intro N D S W nu hD hR hK hne
  obtain ⟨hO, hL, hG, hB⟩ := PEqualNP.Outside.L_meta_1718.build_inv (S := S) (W := W) (nu := nu) hD hR hK D.gates.length le_rfl
  have hconst : ∀ c, (∀ x y, PEqualNP.Outside.L_meta_1718.ov N S W nu D x y D.output = c) → False := by
    intro c hc
    obtain ⟨x, y, xa, ya, h⟩ := hne
    exact h ((hc x y).trans (hc xa ya).symm)
  rcases hv : (PEqualNP.Outside.L_meta_1718.build N S W nu D D.gates.length).2 D.output with c | w
  · exfalso
    by_cases ho : D.output < N + N + D.gates.length
    · exact hconst c ((hG _ ho).1 c hv)
    · have hb := hB D.output (by omega)
      rw [hv] at hb
      cases hb
      apply hconst false
      intro x y
      exact PEqualNP.Outside.L_meta_1718.gv_oob false PEqualNP.Outside.L_meta_1718.Φb D.gates _ _
        (by rw [PEqualNP.Outside.L_meta_1718.rin, List.length_ofFn]; omega)
  · have ho : D.output < N + N + D.gates.length := by
      by_contra ho
      have hb := hB D.output (by omega)
      rw [hv] at hb
      cases hb
    obtain ⟨_, h2, _⟩ := (hG _ ho).2 w hv
    exact ⟨⟨_, w⟩, ⟨hO.1, hO.2.1⟩, hO.2.2, hL, fun x y => h2 x y⟩
