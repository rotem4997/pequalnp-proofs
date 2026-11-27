import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2432

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

lemma merge_card {α : Type} [DecidableEq α] (c : α → α) (u v : α) (X : Finset α) :
    (X.image c).card ≤ (X.image (fun z => if c z = v then u else c z)).card + 1 := by
  calc (X.image c).card ≤ (insert v (X.image (fun z => if c z = v then u else c z))).card := by
        apply Finset.card_le_card
        intro k hk
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
        by_cases h : c z = v
        · rw [h]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, by simp [h]⟩)
    _ ≤ _ := Finset.card_insert_le _ _

/-- Union-find invariant: classes of darts (centre, leaf). -/
lemma inv {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (h4c : ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False)
    (S : ℕ → Finset V) (P : ℕ → Prop)
    (hA : ∀ w, (S w).card ≤ 1 ∨ (P w ∧ ∃ a b, a < w ∧ b < w ∧ S w = S a ∪ S b)) :
    ∀ N, ∃ (r : V × V → V × V) (FD : Finset ℕ), (∀ w ∈ FD, w < N ∧ P w) ∧
      (∀ w, w < N → ∀ c, (∀ x ∈ S w, G.Adj c x) → ∃ d, ∀ x ∈ S w, r (c, x) = d) ∧
      (∀ X : Finset (V × V), X.card ≤ (X.image r).card + FD.card) := by
  intro N
  induction N with
  | zero =>
    refine ⟨id, ∅, ?_, ?_, ?_⟩
    · intro w hw; simp at hw
    · intro w hw; omega
    · intro X; simp
  | succ N ih =>
    obtain ⟨r, FD, h1, h2, h3⟩ := ih
    by_cases hmerge : ∃ a b c, a < N ∧ b < N ∧ S N = S a ∪ S b ∧ P N ∧ 1 < (S N).card ∧
        (∀ x ∈ S N, G.Adj c x)
    · obtain ⟨a, b, c, ha, hb, hS, hP, hcard, hc⟩ := hmerge
      obtain ⟨da, hda⟩ := h2 a ha c (fun x hx => hc x (by rw [hS]; exact Finset.mem_union_left _ hx))
      obtain ⟨db, hdb⟩ := h2 b hb c (fun x hx => hc x (by rw [hS]; exact Finset.mem_union_right _ hx))
      have hni : N ∉ FD := fun h => lt_irrefl _ (h1 N h).1
      have hcardI : (insert N FD).card = FD.card + 1 := by simp [hni]
      refine ⟨fun z => if r z = db then da else r z, insert N FD, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with hw | hw
        · rw [hw]; exact ⟨Nat.lt_succ_self _, hP⟩
        · exact ⟨Nat.lt_succ_of_lt (h1 w hw).1, (h1 w hw).2⟩
      · intro w hw c' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | hw
        · obtain ⟨d, hd⟩ := h2 w hw c' hc'
          refine ⟨if d = db then da else d, fun x hx => ?_⟩
          show (if r (c', x) = db then da else r (c', x)) = _
          rw [hd x hx]
        · rw [hw] at hc' ⊢
          have hcc : c' = c := by
            obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
            by_contra hne
            exact h4c c x c' y (hc x hx) (hc' x hx).symm (hc' y hy) (hc y hy).symm
              (fun h => hne h.symm) hxy
          rw [hcc]
          refine ⟨da, fun x hx => ?_⟩
          rw [hS] at hx
          show (if r (c, x) = db then da else r (c, x)) = da
          rcases Finset.mem_union.mp hx with hx | hx
          · rw [hda x hx]; split_ifs <;> rfl
          · rw [hdb x hx]; simp
      · intro X
        have m1 := merge_card r da db X
        have m2 := h3 X
        rw [hcardI]; omega
    · refine ⟨r, FD, ?_, ?_, h3⟩
      · intro w hw
        exact ⟨Nat.lt_succ_of_lt (h1 w hw).1, (h1 w hw).2⟩
      · intro w hw c' hc'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | hw
        · exact h2 w hw c' hc'
        · rw [hw] at hc' ⊢
          by_cases hc1 : (S N).card ≤ 1
          · rcases (S N).eq_empty_or_nonempty with he | ⟨x0, hx0⟩
            · refine ⟨r (c', c'), fun x hx => ?_⟩
              rw [he] at hx; simp at hx
            · refine ⟨r (c', x0), fun x hx => ?_⟩
              rw [Finset.card_le_one.mp hc1 x hx x0 hx0]
          · exfalso
            rcases hA N with h | ⟨hP, a, b, ha, hb, hS⟩
            · exact hc1 h
            · exact hmerge ⟨a, b, c', ha, hb, hS, hP, by omega, hc'⟩

def dd {V : Type} (S : ℕ → Finset V) (b : ℕ) (u v : V) : V × V :=
  if 1 < (S b).card then (u, v) else (v, u)

lemma dd_sym {V : Type} (S : ℕ → Finset V) (b : ℕ) (u v : V) :
    s((dd S b u v).1, (dd S b u v).2) = s(u, v) := by
  unfold dd
  split_ifs
  · rfl
  · exact Sym2.eq_swap

lemma core {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (h4c : ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False)
    (S : ℕ → Finset V) (P : ℕ → Prop)
    (hA : ∀ w, (S w).card ≤ 1 ∨ (P w ∧ ∃ a b, a < w ∧ b < w ∧ S w = S a ∪ S b))
    (N0 : ℕ) (Q : ℕ → ℕ → ℕ → Prop)
    (hQfun : ∀ j a b a' b', Q j a b → Q j a' b' → a = a' ∧ b = b')
    (hQlt : ∀ j a b, Q j a b → a < N0 ∧ b < N0)
    (hQadj : ∀ j a b, Q j a b → ∀ u ∈ S a, ∀ v ∈ S b, G.Adj u v)
    (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ∃ (j a b : ℕ) (u v : V), e = s(u, v) ∧ Q j a b ∧ u ∈ S a ∧ v ∈ S b)
    (FA : Finset ℕ) (hFA : ∀ j a b, Q j a b → j ∈ FA) :
    ∃ FD : Finset ℕ, (∀ w ∈ FD, P w) ∧ E.card ≤ FA.card + FD.card := by
  classical
  obtain ⟨r, FD, h1, h2, h3⟩ := inv G h4c S P hA N0
  refine ⟨FD, fun w hw => (h1 w hw).2, ?_⟩
  have claim : ∀ (j a b : ℕ) (u v : V) (a' b' : ℕ) (u' v' : V), Q j a b → u ∈ S a → v ∈ S b →
      Q j a' b' → u' ∈ S a' → v' ∈ S b' → r (dd S b u v) = r (dd S b' u' v') := by
    intro j a b u v a' b' u' v' hQ hu hv hQ' hu' hv'
    obtain ⟨e1, e2⟩ := hQfun j a b a' b' hQ hQ'
    rw [← e1] at hu'
    rw [← e2] at hv'
    rw [← e2]
    by_cases hc : 1 < (S b).card
    · simp only [dd, if_pos hc]
      have huu : u = u' := by
        obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hc
        by_contra hne
        exact h4c u y u' z (hQadj j a b hQ u hu y hy) (hQadj j a b hQ u' hu' y hy).symm
          (hQadj j a b hQ u' hu' z hz) (hQadj j a b hQ u hu z hz).symm hne hyz
      rw [← huu]
      obtain ⟨d, hd⟩ := h2 b (hQlt j a b hQ).2 u (fun x hx => hQadj j a b hQ u hu x hx)
      rw [hd v hv, hd v' hv']
    · simp only [dd, if_neg hc]
      have hvv : v = v' := Finset.card_le_one.mp (not_lt.mp hc) v hv v' hv'
      rw [← hvv]
      obtain ⟨d, hd⟩ := h2 a (hQlt j a b hQ).1 v (fun x hx => (hQadj j a b hQ x hx v hv).symm)
      rw [hd u hu, hd u' hu']
  have hE' : ∀ e : Sym2 V, ∃ (j a b : ℕ) (u v : V), e ∈ E →
      (e = s(u, v) ∧ Q j a b ∧ u ∈ S a ∧ v ∈ S b) := by
    intro e
    by_cases he : e ∈ E
    · obtain ⟨j, a, b, u, v, h⟩ := hE e he
      exact ⟨j, a, b, u, v, fun _ => h⟩
    · exact ⟨0, 0, 0, (Quot.out e).1, (Quot.out e).2, fun h => absurd h he⟩
  choose jf af bf uf vf hch using hE'
  have hs : ∀ e ∈ E, s((dd S (bf e) (uf e) (vf e)).1, (dd S (bf e) (uf e) (vf e)).2) = e := by
    intro e he
    rw [dd_sym]
    exact (hch e he).1.symm
  have hXcard : (E.image (fun e => dd S (bf e) (uf e) (vf e))).card = E.card := by
    apply Finset.card_image_of_injOn
    intro e1 he1 e2 he2 h
    have h' : dd S (bf e1) (uf e1) (vf e1) = dd S (bf e2) (uf e2) (vf e2) := h
    calc e1 = s((dd S (bf e1) (uf e1) (vf e1)).1, (dd S (bf e1) (uf e1) (vf e1)).2) :=
          (hs e1 (by simpa using he1)).symm
      _ = s((dd S (bf e2) (uf e2) (vf e2)).1, (dd S (bf e2) (uf e2) (vf e2)).2) := by rw [h']
      _ = e2 := hs e2 (by simpa using he2)
  have hmem : ∀ d ∈ (E.image (fun e => dd S (bf e) (uf e) (vf e))).image r,
      ∃ e, e ∈ E ∧ r (dd S (bf e) (uf e) (vf e)) = d := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨e, he, rfl⟩
  have hcls : ((E.image (fun e => dd S (bf e) (uf e) (vf e))).image r).card ≤ FA.card := by
    apply Finset.card_le_card_of_injOn
      (fun d => if h : ∃ e, e ∈ E ∧ r (dd S (bf e) (uf e) (vf e)) = d then jf (Classical.choose h)
        else 0)
    · intro d hd
      have h := hmem d (by simpa using hd)
      have hsp := Classical.choose_spec h
      have hq := (hch _ hsp.1).2.1
      have : (if h : ∃ e, e ∈ E ∧ r (dd S (bf e) (uf e) (vf e)) = d then jf (Classical.choose h)
        else 0) = jf (Classical.choose h) := dif_pos h
      show (if h : ∃ e, e ∈ E ∧ r (dd S (bf e) (uf e) (vf e)) = d then jf (Classical.choose h)
        else 0) ∈ _
      rw [this]
      simpa using hFA _ _ _ hq
    · intro d1 hd1 d2 hd2 hg
      have g1 := hmem d1 (by simpa using hd1)
      have g2 := hmem d2 (by simpa using hd2)
      have s1 := Classical.choose_spec g1
      have s2 := Classical.choose_spec g2
      have t1 : (if h : ∃ e, e ∈ E ∧ r (dd S (bf e) (uf e) (vf e)) = d1 then
          jf (Classical.choose h) else 0) = jf (Classical.choose g1) := dif_pos g1
      have t2 : (if h : ∃ e, e ∈ E ∧ r (dd S (bf e) (uf e) (vf e)) = d2 then
          jf (Classical.choose h) else 0) = jf (Classical.choose g2) := dif_pos g2
      have hg' : jf (Classical.choose g1) = jf (Classical.choose g2) := by
        rw [← t1, ← t2]; exact hg
      have q1 := hch _ s1.1
      have q2 := hch _ s2.1
      have q2' := q2.2.1
      rw [← hg'] at q2'
      rw [← s1.2, ← s2.2]
      exact claim _ _ _ _ _ _ _ _ _ q1.2.1 q1.2.2.1 q1.2.2.2 q2' q2.2.2.1 q2.2.2.2
  have h3' := h3 (E.image (fun e => dd S (bf e) (uf e) (vf e)))
  omega

def Sg (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => val C (List.ofFn (pairInput v v)) w = true

lemma mem_Sg {n : ℕ} {C : Circuit} {w : ℕ} {v : Fin n} :
    v ∈ Sg n C w ↔ val C (List.ofFn (pairInput v v)) w = true := by
  simp [Sg]

lemma pair_self {n : ℕ} (v i : Fin n) : pairInput v v i = true ↔ i = v := by
  simp [pairInput]

lemma val_mono {n : ℕ} {C : Circuit} (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases hw : w < n
    · have hx : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have hy : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [hx] at h
      rw [hy]
      exact hxy _ h
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases hj : j < C.gates.length
      · rw [val_gate (n := n) (by simp) hj] at h ⊢
        have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
          simpa using (hM _ (gateAt_mem hj)).1
        refine opMono_imp _ hop _ _ _ (fun i _ => ?_) h
        by_cases hlt : i < n + j
        · simp only [if_pos hlt]; exact ih i hlt
        · simp [hlt]
      · rw [val_ge (n := n) (by simp) (by omega)] at h; cases h

lemma Sg_input {n : ℕ} {C : Circuit} (w : ℕ) (hw : w < n) : (Sg n C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  rw [mem_Sg] at ha hb
  have ha' : val C (List.ofFn (pairInput a a)) w = pairInput a a ⟨w, hw⟩ := val_ofFn C _ ⟨w, hw⟩
  have hb' : val C (List.ofFn (pairInput b b)) w = pairInput b b ⟨w, hw⟩ := val_ofFn C _ ⟨w, hw⟩
  rw [ha', pair_self] at ha
  rw [hb', pair_self] at hb
  exact ha.symm.trans hb

lemma Sg_small {n : ℕ} {C : Circuit} {w : ℕ}
    (h : ∀ v : Fin n, val C (List.ofFn (pairInput v v)) w = false) : (Sg n C w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha
  rw [mem_Sg, h a] at ha
  cases ha

def IsOrW (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ j, w = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or

def QQ (n : ℕ) (C : Circuit) (j a b : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs = [a, b] ∧
    a < n + j ∧ b < n + j

lemma hA_lemma {n : ℕ} {C : Circuit} (hM : Monotone2 C)
    (hand : ∀ j, (gateAt C j).op = GateOp.and →
      ∀ v : Fin n, val C (List.ofFn (pairInput v v)) (n + j) = false) (w : ℕ) :
    (Sg n C w).card ≤ 1 ∨
      (IsOrW n C w ∧ ∃ a b, a < w ∧ b < w ∧ Sg n C w = Sg n C a ∪ Sg n C b) := by
  by_cases hw : w < n
  · exact Or.inl (Sg_input w hw)
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  by_cases hj : j < C.gates.length
  swap
  · exact Or.inl (Sg_small (fun v => val_ge (n := n) (by simp) (by omega)))
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    simpa using (hM _ (gateAt_mem hj)).1
  rcases hop with hop | hop
  · exact Or.inl (Sg_small (hand j hop))
  have key : ∀ v : Fin n, v ∈ Sg n C (n + j) ↔
      ∃ i ∈ (gateAt C j).inputs, i < n + j ∧ v ∈ Sg n C i := by
    intro v
    simp only [mem_Sg]
    exact val_or (n := n) (by simp) hj hop
  have h2 := (hM _ (gateAt_mem hj)).2
  obtain ⟨l', hl'⟩ : ∃ l', l' = (gateAt C j).inputs.filter (fun i => decide (i < n + j)) :=
    ⟨_, rfl⟩
  have key' : ∀ v : Fin n, v ∈ Sg n C (n + j) ↔ ∃ i ∈ l', v ∈ Sg n C i := by
    intro v
    rw [key, hl']
    constructor
    · rintro ⟨i, hi, hlt, hv⟩
      exact ⟨i, List.mem_filter.mpr ⟨hi, by simpa using hlt⟩, hv⟩
    · rintro ⟨i, hi, hv⟩
      obtain ⟨h1, h2'⟩ := List.mem_filter.mp hi
      exact ⟨i, h1, by simpa using h2', hv⟩
  have hlt : ∀ i ∈ l', i < n + j := by
    intro i hi
    rw [hl'] at hi
    simpa using (List.mem_filter.mp hi).2
  have hlen : l'.length ≤ 2 := by
    rw [hl']
    exact (List.length_filter_le _ _).trans h2
  clear hl'
  rcases l' with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · left
    apply Finset.card_le_one.mpr
    intro a ha
    obtain ⟨i, hi, _⟩ := (key' a).mp ha
    simp at hi
  · right
    refine ⟨⟨j, rfl, hj, hop⟩, a, a, hlt a (by simp), hlt a (by simp), ?_⟩
    ext v
    rw [key' v]
    simp
  · right
    refine ⟨⟨j, rfl, hj, hop⟩, a, b, hlt a (by simp), hlt b (by simp), ?_⟩
    ext v
    rw [key' v]
    simp [Finset.mem_union]
  · exfalso
    simp only [List.length_cons] at hlen
    omega

lemma adjB {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (hM : Monotone2 C)
    (h4 : ∀ j, ¬((gateAt C j).op = GateOp.and ∧ ∃ (u v : Fin n), ¬G.Adj u v ∧
      val C (List.ofFn (pairInput u v)) (n + j) = true))
    {j a b : ℕ} (hQ : QQ n C j a b) {u v : Fin n} (hu : u ∈ Sg n C a) (hv : v ∈ Sg n C b) :
    G.Adj u v := by
  obtain ⟨hj, hop, hin, ha, hb⟩ := hQ
  by_contra hna
  apply h4 j
  refine ⟨hop, u, v, hna, ?_⟩
  rw [val_and (n := n) (by simp) hj hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi
  · rw [hi]
    exact ⟨ha, val_mono hM _ _ (fun k hk => by
      simp [pairInput] at hk ⊢; exact Or.inl hk) _ (mem_Sg.mp hu)⟩
  · rw [hi]
    exact ⟨hb, val_mono hM _ _ (fun k hk => by
      simp [pairInput] at hk ⊢; exact Or.inr hk) _ (mem_Sg.mp hv)⟩

lemma trace {n : ℕ} {C : Circuit} (hM : Monotone2 C) (u v : Fin n) :
    ∀ w, val C (List.ofFn (pairInput u v)) w = true →
      (u ∈ Sg n C w ∨ v ∈ Sg n C w ∨ ∃ j a b, QQ n C j a b ∧
        ((u ∈ Sg n C a ∧ v ∈ Sg n C b) ∨ (v ∈ Sg n C a ∧ u ∈ Sg n C b))) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases hw : w < n
    · have hx : val C (List.ofFn (pairInput u v)) w = pairInput u v ⟨w, hw⟩ :=
        val_ofFn C _ ⟨w, hw⟩
      rw [hx] at h
      have h' : (⟨w, hw⟩ : Fin n) = u ∨ (⟨w, hw⟩ : Fin n) = v := by
        simpa [pairInput] using h
      rcases h' with h' | h'
      · left
        have hy : val C (List.ofFn (pairInput u u)) w = pairInput u u ⟨w, hw⟩ :=
          val_ofFn C _ ⟨w, hw⟩
        rw [mem_Sg, hy, pair_self]
        exact h'
      · right; left
        have hy : val C (List.ofFn (pairInput v v)) w = pairInput v v ⟨w, hw⟩ :=
          val_ofFn C _ ⟨w, hw⟩
        rw [mem_Sg, hy, pair_self]
        exact h'
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    by_cases hj : j < C.gates.length
    swap
    · rw [val_ge (n := n) (by simp) (by omega)] at h; cases h
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
      simpa using (hM _ (gateAt_mem hj)).1
    rcases hop with hop | hop
    · rw [val_and (n := n) (by simp) hj hop] at h
      have h2 := (hM _ (gateAt_mem hj)).2
      have up : ∀ z : Fin n, (∀ i ∈ (gateAt C j).inputs, z ∈ Sg n C i) →
          z ∈ Sg n C (n + j) := by
        intro z hz
        rw [mem_Sg, val_and (n := n) (by simp) hj hop]
        intro i hi
        exact ⟨(h i hi).1, mem_Sg.mp (hz i hi)⟩
      rcases hl : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
      · left
        apply up
        rw [hl]
        intro i hi
        simp at hi
      · rw [hl] at h
        have ha := h a (by simp)
        rcases ih a ha.1 ha.2 with h1 | h1 | h1
        · left
          apply up
          rw [hl]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rw [hi]; exact h1
        · right; left
          apply up
          rw [hl]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rw [hi]; exact h1
        · right; right; exact h1
      · rw [hl] at h
        have ha := h a (by simp)
        have hb := h b (by simp)
        have hQ : QQ n C j a b := ⟨hj, hop, hl, ha.1, hb.1⟩
        rcases ih a ha.1 ha.2 with h1 | h1 | h1
        · rcases ih b hb.1 hb.2 with h2' | h2' | h2'
          · left
            apply up
            rw [hl]
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi
            · rw [hi]; exact h1
            · rw [hi]; exact h2'
          · right; right; exact ⟨j, a, b, hQ, Or.inl ⟨h1, h2'⟩⟩
          · right; right; exact h2'
        · rcases ih b hb.1 hb.2 with h2' | h2' | h2'
          · right; right; exact ⟨j, a, b, hQ, Or.inr ⟨h1, h2'⟩⟩
          · right; left
            apply up
            rw [hl]
            intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with hi | hi
            · rw [hi]; exact h1
            · rw [hi]; exact h2'
          · right; right; exact h2'
        · right; right; exact h1
      · rw [hl] at h2
        simp only [List.length_cons] at h2
        omega
    · rw [val_or (n := n) (by simp) hj hop] at h
      obtain ⟨i, hi, hlt, hv⟩ := h
      have up : ∀ z : Fin n, z ∈ Sg n C i → z ∈ Sg n C (n + j) := by
        intro z hz
        rw [mem_Sg, val_or (n := n) (by simp) hj hop]
        exact ⟨i, hi, hlt, mem_Sg.mp hz⟩
      rcases ih i hlt hv with h1 | h1 | h1
      · exact Or.inl (up u h1)
      · exact Or.inr (Or.inl (up v h1))
      · exact Or.inr (Or.inr h1)

lemma main {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (C : Circuit) (hM : Monotone2 C)
    (h3 : ∀ v : Fin n, val C (List.ofFn (pairInput v v)) C.output = false)
    (h4 : ∀ j, ¬((gateAt C j).op = GateOp.and ∧ ∃ (u v : Fin n), ¬G.Adj u v ∧
      val C (List.ofFn (pairInput u v)) (n + j) = true))
    (E : Finset (Sym2 (Fin n)))
    (hE : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧
      val C (List.ofFn (pairInput u v)) C.output = true) :
    E.card ≤ C.gates.length := by
  classical
  have h4c : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c →
      b ≠ d → False := fun a b c d p1 p2 p3 p4 p5 p6 => no4 G hg a b c d p1 p2 p3 p4 p5 p6
  have hand : ∀ j, (gateAt C j).op = GateOp.and →
      ∀ v : Fin n, val C (List.ofFn (pairInput v v)) (n + j) = false := by
    intro j hop v
    cases hval : val C (List.ofFn (pairInput v v)) (n + j) with
    | false => rfl
    | true => exact absurd ⟨hop, v, v, fun h => G.ne_of_adj h rfl, hval⟩ (h4 j)
  have hE2 : ∀ e ∈ E, ∃ (j a b : ℕ) (u v : Fin n), e = s(u, v) ∧ QQ n C j a b ∧
      u ∈ Sg n C a ∧ v ∈ Sg n C b := by
    intro e he
    obtain ⟨u, v, rfl, hout⟩ := hE e he
    rcases trace hM u v _ hout with h1 | h1 | ⟨j, a, b, hQ, h1 | h1⟩
    · exfalso
      rw [mem_Sg, h3 u] at h1
      cases h1
    · exfalso
      rw [mem_Sg, h3 v] at h1
      cases h1
    · exact ⟨j, a, b, u, v, rfl, hQ, h1.1, h1.2⟩
    · exact ⟨j, a, b, v, u, Sym2.eq_swap, hQ, h1.1, h1.2⟩
  have hQfun : ∀ j a b a' b', QQ n C j a b → QQ n C j a' b' → a = a' ∧ b = b' := by
    intro j a b a' b' h h'
    have e := h.2.2.1.symm.trans h'.2.2.1
    simpa using e
  have hQlt : ∀ j a b, QQ n C j a b → a < n + C.gates.length ∧ b < n + C.gates.length := by
    intro j a b h
    obtain ⟨p1, _, _, p4, p5⟩ := h
    constructor <;> omega
  obtain ⟨FD, hFD, hcard⟩ := core G h4c (Sg n C) (IsOrW n C) (hA_lemma hM hand)
    (n + C.gates.length) (QQ n C) hQfun hQlt
    (fun j a b hQ u hu v hv => adjB G hM h4 hQ hu hv) E hE2
    ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and))
    (fun j a b h => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2.1⟩)
  have hFDle : FD.card ≤
      ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or)).card := by
    apply Finset.card_le_card_of_injOn (fun w => w - n)
    · intro w hw
      obtain ⟨j, e, hj, hop⟩ := hFD w (by simpa using hw)
      have e2 : w - n = j := by omega
      show w - n ∈ _
      rw [e2]
      simpa using And.intro hj hop
    · intro w1 hw1 w2 hw2 h
      obtain ⟨j1, e1, _, _⟩ := hFD w1 (by simpa using hw1)
      obtain ⟨j2, e2, _, _⟩ := hFD w2 (by simpa using hw2)
      have h' : w1 - n = w2 - n := h
      omega
  have hdis : (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and) ∩
      (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or) = ∅ := by
    apply Finset.disjoint_iff_inter_eq_empty.mp
    apply Finset.disjoint_filter.mpr
    intro j _ p1 p2
    rw [p1] at p2
    cases p2
  have hun := Finset.card_union_add_card_inter
    ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and))
    ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or))
  rw [hdis, Finset.card_empty] at hun
  have hsub : (((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)) ∪
      ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or))).card ≤
      (Finset.range C.gates.length).card :=
    Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  rw [Finset.card_range] at hsub
  omega

end PEqualNP.Outside.L_meta_2432

theorem PEqualNP.Outside.L_meta_2432 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x7 : Fin x1), PEqualNP.MetaComplexity.circuitFun x1 x5 (PEqualNP.EdgeOwnership.pairInput x7 x7) = Bool.false) → (∀ (x8 : ℕ), ¬((PEqualNP.MetaComplexity.NestedCover.gateAt x5 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x9 : Fin x1) (x10 : Fin x1), ¬x2.Adj x9 x10 ∧ PEqualNP.EdgeOwnership.gateVal x1 x5 x8 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true)) → {x9 ∈ x2.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x1 x5 fun (x10 : Fin x1) => Decidable.decide (x10 ∈ x9)) = Bool.true}.card ≤ x5.size := by
  intro n G _ hg C hM h3 h4
  refine PEqualNP.Outside.L_meta_2432.main G hg C hM h3 h4 _ ?_
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨_, hacc⟩ := he
  induction e using Sym2.ind with
  | _ u v =>
    refine ⟨u, v, rfl, ?_⟩
    have hacc2 : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v)
        = Bool.true := by
      rw [← hacc]
      congr 1
    exact hacc2
