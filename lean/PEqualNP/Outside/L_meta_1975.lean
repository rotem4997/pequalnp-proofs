import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1975

-- Gate deletion and evaluation agreement adapted from the upstream L-meta-522 proof.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))


private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

private lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]


-- Vertex-cover circuit construction adapted from the upstream L-meta-173 proof.
namespace Builder
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp


def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩

    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edgeBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption


end Builder

-- Count the input slots of all gates, with one additional slot for the output.
private def slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

private lemma gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g tail ih =>
    have hg := h g List.mem_cons_self
    have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private lemma countBound (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

private def reads (v : ℕ) (g : Gate) :=
  (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v

private lemma filteredSlots (v : ℕ) (gs : List Gate) :
    (gs.filter (reads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.count_append, List.filter_cons]
    split
    next h =>
      have hm : v ∈ g.inputs := List.mem_of_mem_take (List.contains_iff_mem.mp h)
      have hp := List.count_pos_iff.mpr hm
      simp only [List.length_cons]
      omega
    next => omega

private lemma essentialSlot {n : ℕ} (C : Circuit) (a : Fin n)
    (dep : ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
    (a : ℕ) ∈ slots C := by
  obtain ⟨x, y, hagree, hne⟩ := dep
  by_contra hn
  have hout : C.output ≠ (a : ℕ) := by
    intro he
    exact hn (by simp [slots, he])
  have noRead : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({↑a} : Set ℕ) := by
    intro g hg i hi hia
    have hi' : i = (a : ℕ) := hia
    exact hn (by apply List.mem_cons_of_mem; exact List.mem_flatMap.mpr ⟨g,hg,hi' ▸ hi⟩)
  apply hne
  apply (wiresFrom_agree C.gates ({↑a} : Set ℕ) (List.ofFn x) (List.ofFn y)
    (by simp) (by simp) ?_ noRead).2 C.output hout
  intro i hi
  by_cases h : i < n
  · rw [ofFn_getD_lt _ _ _ h, ofFn_getD_lt _ _ _ h]
    exact hagree _ (fun he => hi (congrArg Fin.val he))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma internalSlot {n : ℕ} (C : Circuit) (hC : FanInTwo C)
    (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
    (i : ℕ) (hi : i < C.gates.length) : n+i ∈ slots C := by
  by_contra hn
  have hout : C.output ≠ n+i := fun e => hn (by simp [slots,e])
  have hno : ∀ j, (hj : j < C.gates.length) → i < j → n+i ∉ C.gates[j].inputs := by
    intro j hj _ hm
    exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.getElem_mem hj,hm⟩))
  have bad := hmin _ (deleteDeadGate C hC i hi hout hno)
  change C.gates.length ≤ C.gates.length - 1 at bad
  omega

private lemma markedUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (hE : ∃ i j, G.Adj i j) (hc : ∀ i j, G.Adj i j → i ∉ A)
    (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) :
    HasCircuitSize n f (A.card + G.edgeFinset.card + Aᶜ.card - 1) := by
  classical
  have b := Builder.edgeBuilder n G Aᶜ hE (fun i j h => Or.inl (Finset.mem_compl.mpr (hc i j h)))
  obtain ⟨i,j,hij⟩ := hE
  have epos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(i,j),by simpa using hij⟩
  apply Builder.bld_hasCircuitSize
  by_cases ha : A.Nonempty
  · have ap := ha.card_pos
    apply Builder.bld_congr (Builder.bld_mono (Builder.bld_or (Builder.bld_anyFinset A ha) b) (by omega))
    intro x
    rw [Bool.eq_iff_iff, hf]
    simp
  · have he := Finset.not_nonempty_iff_eq_empty.mp ha
    apply Builder.bld_congr (Builder.bld_mono b (by simp [he]))
    intro x
    rw [Bool.eq_iff_iff, hf]
    simp [he]

end PEqualNP.Outside.L_meta_1975

open PEqualNP.Outside.L_meta_1975

theorem PEqualNP.Outside.L_meta_1975 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length = (3 : ℕ) ∧ ∀ x17 ∈ x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro n G A f C hdeg _ hc hE hf hC heval hmin hread
  -- The vertex-cover circuit gives an upper bound strictly below the mandatory slot count.
  exfalso
  have ub := hmin _ (markedUpper G A f hE hc hf)
  let cnt : ℕ → ℕ := fun i => (slots C).count i
  have marked (a : Fin n) (ha : a ∈ A) : 1 ≤ cnt a := by
    apply List.count_pos_iff.mpr
    apply essentialSlot
    let z : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a)
    refine ⟨z,y,fun i hi => by simp [z,y,hi],?_⟩
    rw [heval]
    have hz : f z ≠ true := by simp [hf,z]
    have hy : f y = true := (hf y).mpr (Or.inl ⟨a,ha,by simp [y]⟩)
    exact fun eq => hz (eq.trans hy)
  have unmarked (a : Fin n) (ha : a ∈ Aᶜ) : 3 ≤ cnt a := by
    have eq := (hread a (Finset.mem_compl.mp ha)).1
    have h := filteredSlots (a : ℕ) C.gates
    change (C.gates.filter (reads ↑a)).length = 3 at eq
    simp only [cnt, slots, List.count_cons]
    omega
  have internal (i : ℕ) (hi : i ∈ Finset.range C.gates.length) : 1 ≤ cnt (n+i) :=
    List.count_pos_iff.mpr (internalSlot C hC (by simpa [heval] using hmin) i (Finset.mem_range.mp hi))
  have lowerA := Finset.sum_le_sum marked
  have lowerB := Finset.sum_le_sum unmarked
  have lowerI := Finset.sum_le_sum internal
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at lowerA lowerB lowerI
  have inSum := A.sum_add_sum_compl (fun a => cnt (a : ℕ))
  rw [Fin.sum_univ_eq_sum_range] at inSum
  have countAll := countBound (slots C) (Finset.range (n+C.gates.length))
  change ∑ i ∈ Finset.range (n+C.gates.length), cnt i ≤ (slots C).length at countAll
  rw [Finset.sum_range_add] at countAll
  have len := gateSlotBound C.gates (fun g hg => (hC g hg).2)
  simp only [slots,List.length_cons] at countAll
  have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 := by
    apply (G.degree_eq_zero a).mpr
    exact fun j h => hc a j h ha
  have dB (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 := by
    rw [← G.ncard_neighborSet]
    exact hdeg a (Finset.mem_compl.mp ha)
  have degreeSum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degreeSum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
  obtain ⟨i,j,hij⟩ := hE
  have hp : 0 < Aᶜ.card := Finset.card_pos.mpr ⟨i, Finset.mem_compl.mpr (hc i j hij)⟩
  change C.gates.length ≤ _ at ub
  omega
