import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14656

-- Wire support agreement and counting follow PEqualNP.MetaComplexity.Helpers.Support.

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

-- The support of a gate: the union of the supports of the wires it reads.
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

-- The supports of all wires, starting from the supports `L` of the wires present.
def run (gs : List Gate) (ws : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

-- The supports of the input wires: input `i` has support `{i}`.
def inputSupps (n : ℕ) : List (Finset (Fin (n + 1))) := List.ofFn fun i : Fin n => {i.castSucc}

-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
-- `y` agree on.
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_run (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (run gs w) (run gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) (z z' : Bool) :
    Agree (Fin.snoc x z) (Fin.snoc y z') (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx := hj (Fin.castSucc ⟨j, hjn⟩) (by simp [inputSupps, hjn])
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hx
    simpa [hjn] using hx
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- Any set `W` of wires has a joint support of size at most `t + |W|`.
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


theorem agree_extra (x y : Fin n → Bool) (z z' : Bool)
    (L : List (Finset (Fin (n + 1)))) (a b : List Bool)
    (h : Agree (Fin.snoc x z) (Fin.snoc y z') L a b) :
    Agree (Fin.snoc x z) (Fin.snoc y z') (L ++ [{Fin.last n}]) (a ++ [z]) (b ++ [z']) := by
  obtain ⟨ha, hb, h⟩ := h
  refine ⟨by simp [ha], by simp [hb], ?_⟩
  intro j hj
  by_cases he : j = L.length
  · subst j
    have hz := hj (Fin.last n) (by simp)
    rw [ha, getD_snoc_eq, hb, getD_snoc_eq]
    simpa using hz
  · rw [getD_snoc_ne _ _ _ _ he] at hj
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    exact h j hj

theorem cnt_extra (t : ℕ) (L : List (Finset (Fin n))) (i : Fin n) (h : Cnt t L) :
    Cnt t (L ++ [{i}]) := by
  intro W
  by_cases hw : L.length ∈ W
  · have hs : (W.biUnion fun j => (L ++ [{i}]).getD j ∅)
        ⊆ {i} ∪ ((W.erase L.length).biUnion fun j => L.getD j ∅) := by
      intro k hk
      obtain ⟨j, hj, hk⟩ := Finset.mem_biUnion.mp hk
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
      by_cases he : j = L.length
      · subst j
        left
        simpa using hk
      · exact Or.inr ⟨j, Finset.mem_erase.mpr ⟨he, hj⟩,
          getD_snoc_ne _ _ _ _ he ▸ hk⟩
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le ({i} : Finset (Fin n))
      ((W.erase L.length).biUnion fun j => L.getD j ∅)
    have h3 := h (W.erase L.length)
    rw [Finset.card_singleton] at h2
    rw [Finset.card_erase_of_mem hw] at h3
    have h4 : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hw⟩
    omega
  · have heq : (W.biUnion fun j => (L ++ [{i}]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hw (e ▸ hj))
    rw [heq]
    exact h W

def positive (g : Gate) : Prop := g.op = .and ∨ g.op = .or

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def wireLE (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ j, a.getD j false = true → b.getD j false = true

theorem wireLE_snoc {a b : List Bool} {p q : Bool} (hw : wireLE a b)
    (h : p = true → q = true) : wireLE (a ++ [p]) (b ++ [q]) := by
  obtain ⟨hlen, hw⟩ := hw
  refine ⟨by simp [hlen], ?_⟩
  intro j hj
  by_cases he : j = a.length
  · subst j
    rw [getD_snoc_eq] at hj
    rw [hlen, getD_snoc_eq]
    exact h hj
  · rw [getD_snoc_ne _ _ _ _ he] at hj
    rw [getD_snoc_ne _ _ _ _ (by omega)]
    exact hw j hj

theorem inputs_le {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
    wireLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  by_cases he : j < n
  · exact (by simpa [he] using h ⟨j, he⟩ (by simpa [he] using hj))
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    contradiction

theorem value_mono {a b : List Bool} (hw : wireLE a b) (g : Gate) (hp : positive g) :
    value g a = true → value g b = true := by
  rcases hp with ho | ho
  · simp only [value, ho, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro ha _ hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hw.2 i (ha _ ⟨i, hi, rfl⟩)
  · simp only [value, ho, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, ha⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hw.2 i ha⟩

theorem value_anti {a b : List Bool} (hw : wireLE a b) (g : Gate) (hg : g.op = .not) :
    value g b = true → value g a = true := by
  unfold value
  rw [hg]
  cases hs : g.inputs with
  | nil => simp [GateOp.eval]
  | cons i is =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true']
    intro hb
    cases ha : a.getD i false
    · rfl
    · have hc := hw.2 i ha
      rw [hb] at hc
      contradiction

theorem run_mono (gs : List Gate) (hp : ∀ g ∈ gs, positive g)
    (a b : List Bool) (hw : wireLE a b) : wireLE (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact hw
  | cons g gs ih =>
    exact ih (fun g' h => hp g' (List.mem_cons_of_mem _ h)) _ _
      (wireLE_snoc hw (value_mono hw g (hp g List.mem_cons_self)))

def front {n : ℕ} (pre : List Gate) (x : Fin n → Bool) : List Bool := run pre (List.ofFn x)

def cut {n : ℕ} (pre post : List Gate) (o : ℕ) (x : Fin n → Bool) (z : Bool) : Bool :=
  (run post (front pre x ++ [z])).getD o false

def cutSupport (n : ℕ) (pre post : List Gate) (o : ℕ) : Finset (Fin (n + 1)) :=
  (suppsFrom post (suppsFrom pre (inputSupps n) ++ [{Fin.last n}])).getD o ∅

theorem cut_agree {n : ℕ} (pre post : List Gate) (o : ℕ) (x y : Fin n → Bool) (z z' : Bool)
    (h : ∀ i ∈ cutSupport n pre post o, Fin.snoc (α := fun _ => Bool) x z i = Fin.snoc (α := fun _ => Bool) y z' i) :
    cut pre post o x z = cut pre post o y z' :=
  (agree_run _ _ post _ _ _ (agree_extra x y z z' _ _ _
    (agree_run _ _ pre _ _ _ (agree_inputs x y z z')))).2.2 o h

theorem cut_count (n : ℕ) (pre post : List Gate) (o : ℕ)
    (hp : ∀ g ∈ pre, g.inputs.length ≤ 2) (hq : ∀ g ∈ post, g.inputs.length ≤ 2) :
    (cutSupport n pre post o).card ≤ pre.length + post.length + 1 := by
  have hc := cnt_suppsFrom post (0 + pre.length) _ hq
    (cnt_extra _ _ (Fin.last n) (cnt_suppsFrom pre 0 _ hp cnt_inputs))
    {o}
  simpa only [cutSupport, Finset.singleton_biUnion, zero_add, Finset.card_singleton] using hc

theorem cut_mono {n : ℕ} (pre post : List Gate) (o : ℕ) (hp : ∀ g ∈ post, positive g)
    (x : Fin n → Bool) {z z' : Bool} (h : z = true → z' = true) :
    cut pre post o x z = true → cut pre post o x z' = true :=
  (run_mono post hp _ _ (wireLE_snoc ⟨rfl, fun _ e => e⟩ h)).2 o

theorem eval_split {n : ℕ} (pre post : List Gate) (g : Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨pre ++ g :: post, o⟩ (List.ofFn x) =
      cut pre post o x (value g (front pre x)) := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append]
  rfl

theorem split_not (gs : List Gate)
    (h : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    (∀ g ∈ gs, g.op ≠ .not) ∨
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = .not ∧
      (∀ a ∈ pre, a.op ≠ .not) ∧ (∀ a ∈ post, a.op ≠ .not) := by
  induction gs with
  | nil => exact Or.inl (by simp)
  | cons a gs ih =>
    by_cases ha : a.op = .not
    · refine Or.inr ⟨[], a, gs, rfl, ha, by simp, ?_⟩
      intro g hg hgn
      obtain ⟨i, hi⟩ := List.get_of_mem hg
      have hz := h 0 i.succ ha (by simpa only [List.get_cons_succ', hi] using hgn)
      have he := congrArg Fin.val hz
      change 0 = i.val + 1 at he
      omega
    · have ht : ∀ i j : Fin gs.length, (gs.get i).op = .not →
          (gs.get j).op = .not → i = j := by
        intro i j hi hj
        apply Fin.succ_injective _
        exact h i.succ j.succ
          (by simpa only [List.get_cons_succ'] using hi)
          (by simpa only [List.get_cons_succ'] using hj)
      rcases ih ht with hn | ⟨pre, g, post, hs, hg, hp, hq⟩
      · exact Or.inl (by simpa [List.mem_cons, ha] using hn)
      · refine Or.inr ⟨a :: pre, g, post, congrArg (List.cons a) hs, hg, ?_, hq⟩
        intro g' hg'
        rcases List.mem_cons.mp hg' with he | hm
        · exact he ▸ ha
        · exact hp g' hm

def binary (gs : List Gate) : Prop := ∀ g ∈ gs, positive g ∧ g.inputs.length ≤ 2

theorem eliminate {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ j, x j = true → y j = true) ∧ (∀ j, j ≠ i → x j = y j) ∧
      f x = false ∧ f y = true)
    (hsmall : ∃ gs o, binary gs ∧ gs.length ≤ n + 1 ∧
      ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x)
    (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (positive g ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j)
    (hev : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∃ gs' o', binary gs' ∧ gs'.length ≤ gs.length ∧
      ∀ x, Circuit.eval ⟨gs', o'⟩ (List.ofFn x) = f x := by
  rcases split_not gs hn with hall | ⟨pre, neg, post, rfl, hneg, hpre, hpost⟩
  · refine ⟨gs, o, ?_, le_rfl, hev⟩
    exact fun g hm => ⟨(hg g hm).1.resolve_right (hall g hm), (hg g hm).2⟩
  have hp : binary pre := by
    intro g hm
    obtain ⟨h, hlen⟩ := hg g (List.mem_append_left _ hm)
    exact ⟨h.resolve_right (hpre g hm), hlen⟩
  have hq : binary post := by
    intro g hm
    obtain ⟨h, hlen⟩ := hg g (List.mem_append_right _ (List.mem_cons_of_mem _ hm))
    exact ⟨h.resolve_right (hpost g hm), hlen⟩
  let z := fun x : Fin n → Bool => value neg (front pre x)
  have hc (x : Fin n → Bool) : cut pre post o x (z x) = f x :=
    (eval_split pre post neg o x).symm.trans (hev x)
  have hmembers (i : Fin n) : i.castSucc ∈ cutSupport n pre post o := by
    by_contra hi
    obtain ⟨x, y, hxy, hsame, hx, hy⟩ := hdep i
    have hza : z y = true → z x = true :=
      value_anti (run_mono pre (fun g hm => (hp g hm).1) _ _ (inputs_le hxy)) neg hneg
    have he := cut_agree pre post o x y (z y) (z y) (by
      intro k hk
      revert hk
      refine Fin.lastCases (by simp) (fun j hj => ?_) k
      have hji : j ≠ i := fun he => hi (he ▸ hj)
      simpa only [Fin.snoc_castSucc] using hsame j hji)
    have htrue : cut pre post o x (z y) = true := he.trans ((hc y).trans hy)
    have hh := cut_mono pre post o (fun g hm => (hq g hm).1) x hza htrue
    rw [hc x, hx] at hh
    contradiction
  by_cases hd : Fin.last n ∈ cutSupport n pre post o
  · have hcount := cut_count n pre post o (fun g hm => (hp g hm).2) (fun g hm => (hq g hm).2)
    have heq : cutSupport n pre post o = Finset.univ :=
      Finset.eq_univ_of_forall (fun i => Fin.lastCases hd hmembers i)
    rw [heq, Finset.card_univ, Fintype.card_fin] at hcount
    obtain ⟨gs', o', hbinary, hl, heval⟩ := hsmall
    refine ⟨gs', o', hbinary, ?_, heval⟩
    simp only [List.length_append, List.length_cons]
    omega
  · let zero : Gate := ⟨.or, []⟩
    refine ⟨pre ++ zero :: post, o, ?_, by simp, ?_⟩
    · intro g hm
      rcases List.mem_append.mp hm with h | h
      · exact hp g h
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨Or.inr rfl, by simp [zero]⟩
        · exact hq g h
    · intro x
      rw [eval_split]
      change cut pre post o x false = f x
      rw [← hc x]
      apply cut_agree
      intro i hi
      revert hi
      refine Fin.lastCases (fun hin => (hd hin).elim) (fun j _ => by simp) i


def edgeFunction (x : Fin 8 → Bool) : Bool :=
  decide (∃ j < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * j) 0) false = true ∧
    (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * j + 1) 0) false = true)

def neighbor (i : Fin 8) : Fin 8 := ![5, 5, 5, 6, 6, 0, 0, 0] i

def oneVertex (i : Fin 8) (j : Fin 8) : Bool := decide (j = neighbor i)

def twoVertices (i : Fin 8) (j : Fin 8) : Bool := decide (j = neighbor i ∨ j = i)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem witnesses_dependence : ∀ i : Fin 8,
    (∀ j, oneVertex i j = true → twoVertices i j = true) ∧
    (∀ j, j ≠ i → oneVertex i j = twoVertices i j) ∧
    edgeFunction (oneVertex i) = false ∧ edgeFunction (twoVertices i) = true := by
  decide +kernel

def witness : List Gate := [⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [12, 10]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [14, 15]⟩]

theorem witness_binary : binary witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [positive]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem witness_evaluates : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 16⟩ (List.ofFn x) = edgeFunction x := by
  decide +kernel

end PEqualNP.Outside.L_meta_14656

open PEqualNP.Outside.L_meta_14656 in
theorem PEqualNP.Outside.L_meta_14656 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg hn he
  exact eliminate edgeFunction (fun i => ⟨oneVertex i, twoVertices i, witnesses_dependence i⟩)
    ⟨witness, 16, witness_binary, by decide, witness_evaluates⟩ gates o
    (fun g hm => ⟨or_assoc.mpr (hg g hm).1, (hg g hm).2⟩) hn he
