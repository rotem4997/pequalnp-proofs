import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5552

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The eight input wires and at most seven gate wires use labels below fifteen.
-- Label fifteen represents a missing wire.
abbrev Wire := Fin 16
abbrev Expr := DMFormula 16
def dummy : Wire := 15

def support : Expr → Finset Wire
  | .lit w _ => if w = dummy then ∅ else {w}
  | .and a b | .or a b => support a ∪ support b

def clean : Expr → Prop
  | .lit w p => p = true ∨ w = dummy
  | .and a b | .or a b => clean a ∧ clean b

def linear (f : Expr) : Prop := (support f).card = f.leaves

theorem support_le (f : Expr) : (support f).card ≤ f.leaves := by
  induction f with
  | lit w pol => simp only [support, DMFormula.leaves]; split <;> simp
  | and a b ha hb | or a b ha hb =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

theorem union_linear (a b : Expr)
    (h : (support a ∪ support b).card = a.leaves + b.leaves) :
    linear a ∧ linear b ∧ Disjoint (support a) (support b) := by
  have h1 := support_le a
  have h2 := support_le b
  have h3 := Finset.card_union_add_card_inter (support a) (support b)
  rw [h] at h3
  unfold linear
  refine ⟨by omega, by omega, ?_⟩
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))

def plug (k : Wire) (v : Expr) : Expr → Expr
  | .lit i b => if i = k then v else .lit i b
  | .and a b => .and (plug k v a) (plug k v b)
  | .or a b => .or (plug k v a) (plug k v b)

theorem plug_clean (k : Wire) (v f : Expr) (hv : clean v) (hf : clean f) :
    clean (plug k v f) := by
  induction f with
  | lit i b => simp only [plug]; split <;> assumption
  | and a b ha hb | or a b ha hb => exact ⟨ha hf.1, hb hf.2⟩

theorem plug_eq (k : Wire) (v f : Expr) (hk : k ≠ dummy) (hn : k ∉ support f) :
    plug k v f = f := by
  induction f with
  | lit i b =>
    have hne : i ≠ k := by
      intro e
      subst i
      exact hn (by simp [support, hk])
    simp [plug, hne]
  | and a b ha hb | or a b ha hb =>
    have h : k ∉ support a ∧ k ∉ support b := by
      simpa [support] using hn
    simp [plug, ha h.1, hb h.2]

theorem plug_subset (k : Wire) (v f : Expr) :
    support (plug k v f) ⊆ (support f).erase k ∪ support v := by
  induction f with
  | lit i b =>
    by_cases hi : i = k
    · simp [plug, hi]
    · simp only [plug, ite_eq_right hi, support]
      split
      · simp
      · intro j hj
        have e : j = i := Finset.mem_singleton.mp hj
        subst j
        simp [hi]
  | and a b ha hb | or a b ha hb =>
    intro i hi
    simp only [plug, support, Finset.mem_union, Finset.mem_erase] at hi ⊢
    have aa : i ∈ support (plug k v a) → (i ≠ k ∧ (i ∈ support a ∨ i ∈ support b)) ∨ i ∈ support v := by
      intro hm
      have hm' := ha hm
      simp only [Finset.mem_union, Finset.mem_erase] at hm'
      tauto
    have bb : i ∈ support (plug k v b) → (i ≠ k ∧ (i ∈ support a ∨ i ∈ support b)) ∨ i ∈ support v := by
      intro hm
      have hm' := hb hm
      simp only [Finset.mem_union, Finset.mem_erase] at hm'
      tauto
    tauto

theorem plug_grow (k : Wire) (v f : Expr) (hk : k ≠ dummy) (hv : v.leaves ≤ 2) :
    (support (plug k v f)).card ≤ (support f).card + 1 := by
  by_cases h : k ∈ support f
  · have h1 := Finset.card_le_card (plug_subset k v f)
    have h2 := Finset.card_union_le ((support f).erase k) (support v)
    have h3 := support_le v
    have he := Finset.card_erase_add_one h
    omega
  · rw [plug_eq k v f hk h]
    omega

theorem plug_leaves (k : Wire) (v f : Expr) (hk : k ≠ dummy) (hv : v.leaves ≤ 2)
    (hlin : linear f) : (plug k v f).leaves ≤ f.leaves + 1 := by
  induction f with
  | lit i b =>
    simp only [plug, DMFormula.leaves]
    split
    · exact hv
    · change 1 ≤ 2; decide
  | and a b ha hb | or a b ha hb =>
    have h : (support a ∪ support b).card = a.leaves + b.leaves := hlin
    obtain ⟨la, lb, hd⟩ := union_linear a b h
    by_cases hm : k ∈ support a
    · have hn : k ∉ support b := fun hr => Finset.disjoint_left.mp hd hm hr
      have aa := ha la
      simp only [plug, DMFormula.leaves, plug_eq k v b hk hn]
      omega
    · have bb := hb lb
      simp only [plug, DMFormula.leaves, plug_eq k v a hk hm]
      omega

theorem plug_eval (k : Wire) (v f : Expr) (x : Wire → Bool) (hk : k ≠ dummy)
    (hv : v.eval x = x k) (hf : clean f) : (plug k v f).eval x = f.eval x := by
  induction f with
  | lit i b =>
    by_cases hi : i = k
    · subst i
      have hb : b = true := hf.resolve_right hk
      simp [plug, DMFormula.eval, hb, hv]
    · simp [plug, hi]
  | and a b ha hb | or a b ha hb =>
    simp [plug, DMFormula.eval, ha hf.1, hb hf.2]

theorem eval_congr_support (f : Expr) (x y : Wire → Bool) (h0 : x dummy = y dummy)
    (h : ∀ i ∈ support f, x i = y i) : f.eval x = f.eval y := by
  induction f with
  | lit i b =>
    by_cases hi : i = dummy
    · subst i; simp [DMFormula.eval, h0]
    · have he := h i (by simp [support, hi])
      simp [DMFormula.eval, he]
  | and a b ha hb | or a b ha hb =>
    simp only [DMFormula.eval]
    rw [ha (fun i hi => h i (Finset.mem_union_left _ hi)),
      hb (fun i hi => h i (Finset.mem_union_right _ hi))]

def on (f : Expr) (S : Finset Wire) : Bool := f.eval (fun i => decide (i ∈ S ∧ i ≠ dummy))

theorem on_congr (f : Expr) (S T : Finset Wire)
    (h : ∀ x ∈ support f, x ∈ S ↔ x ∈ T) :
    on f S = on f T := by
  apply eval_congr_support
  · simp
  · intro x hx
    simp [(h x hx)]

theorem on_empty (f : Expr) (hf : clean f) (hl : linear f) : on f ∅ = false := by
  induction f with
  | lit i b =>
    have hi : i ≠ dummy := by
      intro hi
      simp [linear, support, hi, DMFormula.leaves] at hl
    have hb := hf.resolve_right hi
    simp [on, DMFormula.eval, hb]
  | and a b ha hb =>
    obtain ⟨la, lb, _⟩ := union_linear a b hl
    change (on a ∅ && on b ∅) = false
    rw [ha hf.1 la, hb hf.2 lb]
    rfl
  | or a b ha hb =>
    obtain ⟨la, lb, _⟩ := union_linear a b hl
    change (on a ∅ || on b ∅) = false
    rw [ha hf.1 la, hb hf.2 lb]
    rfl

theorem drop_pair (f : Expr) (u v : Wire) (hn : u ∉ support f) :
    on f {u, v} = on f {v} := by
  apply on_congr
  intro x hx
  have hne : x ≠ u := by intro e; subst x; exact hn hx
  simp [hne]

theorem pair_comm (f : Expr) (u v : Wire) : on f {u, v} = on f {v, u} := by
  rw [Finset.pair_comm]

theorem single_support (f : Expr) (hf : clean f) (hl : linear f) (a : Wire)
    (h : on f {a} = true) : a ∈ support f := by
  by_contra hn
  have he : on f {a} = on f ∅ := on_congr f _ _ (by
    intro x hx
    have hne : x ≠ a := by intro e; subst x; exact hn hx
    simp [hne])
  rw [he, on_empty f hf hl] at h
  contradiction

theorem pair_hits (f : Expr) (hf : clean f) (hl : linear f) (a b : Wire)
    (h : on f {a, b} = true) : a ∈ support f ∨ b ∈ support f := by
  by_cases hmem : a ∈ support f
  · exact Or.inl hmem
  · exact Or.inr (single_support f hf hl b (by rwa [drop_pair f a b hmem] at h))

theorem both_support (f : Expr) (hf : ∀ i, on f {i} = false) (a b : Wire)
    (h : on f {a, b} = true) : a ∈ support f ∧ b ∈ support f := by
  constructor
  · by_contra hn
    rw [drop_pair f a b hn, hf b] at h
    contradiction
  · by_contra hn
    rw [pair_comm f a b, drop_pair f b a hn, hf a] at h
    contradiction

theorem on_mono (f : Expr) (hf : clean f) {S T : Finset Wire} (h : S ⊆ T) :
    on f S = true → on f T = true := by
  induction f with
  | lit i b =>
    rcases hf with e | e
    · subst b
      simpa [on, DMFormula.eval] using (fun hm : i ∈ S ∧ i ≠ dummy => ⟨h hm.1, hm.2⟩ :
        (i ∈ S ∧ i ≠ dummy) → i ∈ T ∧ i ≠ dummy)
    · subst i; simp [on, DMFormula.eval]
  | and a b ha hb =>
    have ha := ha hf.1
    have hb := hb hf.2
    simp only [on, DMFormula.eval, Bool.and_eq_true] at ha hb ⊢
    exact fun h => ⟨ha h.1, hb h.2⟩
  | or a b ha hb =>
    have ha := ha hf.1
    have hb := hb hf.2
    simp only [on, DMFormula.eval, Bool.or_eq_true] at ha hb ⊢
    exact Or.imp ha hb

theorem and_cross (f g : Expr) (hf : clean f) (hg : clean g)
    (d : Disjoint (support f) (support g)) (a b c e : Wire)
    (ha : a ∈ support f) (hb : b ∈ support g)
    (h1 : on f {c,b} = true) (h2 : on g {a,e} = true) :
    on f {c,e} = true ∧ on g {c,e} = true := by
  have hnb : b ∉ support f := fun hc => Finset.disjoint_left.mp d hc hb
  have hna : a ∉ support g := fun hc => Finset.disjoint_left.mp d ha hc
  rw [pair_comm f c b, drop_pair f b c hnb] at h1
  rw [drop_pair g a e hna] at h2
  exact ⟨on_mono f hf (by simp) h1, on_mono g hg (by simp) h2⟩

-- In a read-once formula that rejects singleton inputs, three corners force the fourth.
theorem rectangle (f : Expr) (hf : clean f) (hl : linear f)
    (hn : ∀ i, on f {i} = false) (a b c e : Wire)
    (h1 : on f {a,b} = true) (h2 : on f {c,b} = true) (h3 : on f {a,e} = true) :
    on f {c,e} = true := by
  induction f with
  | lit i pol =>
    have hi : i ≠ dummy := by
      intro e
      simp [linear, support, e, DMFormula.leaves] at hl
    have hn := hn i
    simp [on, DMFormula.eval, hi, hf.resolve_right hi] at hn
  | and f g ihf ihg =>
    obtain ⟨lf, lg, d⟩ := union_linear f g hl
    change clean f ∧ clean g at hf
    have andEval (S : Finset Wire) : on (.and f g) S = true ↔ on f S = true ∧ on g S = true := by
      simp [on, DMFormula.eval, Bool.and_eq_true]
    rw [andEval] at h1 h2 h3 ⊢
    have x := pair_hits f hf.1 lf a b h1.1
    have y := pair_hits g hf.2 lg a b h1.2
    rcases x with xa | xb <;> rcases y with ya | yb
    · exact (Finset.disjoint_left.mp d xa ya).elim
    · exact and_cross f g hf.1 hf.2 d a b c e xa yb h2.1 h3.2
    · exact (and_cross g f hf.2 hf.1 d.symm a b c e ya xb h2.2 h3.1).symm
    · exact (Finset.disjoint_left.mp d xb yb).elim
  | or f g ihf ihg =>
    obtain ⟨lf, lg, d⟩ := union_linear f g hl
    change clean f ∧ clean g at hf
    have nf (i) : on f {i} = false := (Bool.or_eq_false_iff.mp (hn i)).1
    have ng (i) : on g {i} = false := (Bool.or_eq_false_iff.mp (hn i)).2
    have orEval (S : Finset Wire) : on (.or f g) S = true ↔ on f S = true ∨ on g S = true := by
      simp [on, DMFormula.eval, Bool.or_eq_true]
    rw [orEval] at h1 h2 h3 ⊢
    rcases h1 with ht | ht
    · obtain ⟨pa, pb⟩ := both_support f nf a b ht
      have q2 : on f {c,b} = true := h2.resolve_right fun q =>
        Finset.disjoint_left.mp d pb (both_support g ng c b q).2
      have q3 : on f {a,e} = true := h3.resolve_right fun q =>
        Finset.disjoint_left.mp d pa (both_support g ng a e q).1
      exact Or.inl (ihf hf.1 lf nf ht q2 q3)
    · obtain ⟨pa, pb⟩ := both_support g ng a b ht
      have q2 : on g {c,b} = true := h2.resolve_left fun q =>
        Finset.disjoint_left.mp d (both_support f nf c b q).2 pb
      have q3 : on g {a,e} = true := h3.resolve_left fun q =>
        Finset.disjoint_left.mp d (both_support f nf a e q).1 pa
      exact Or.inr (ihg hf.2 lg ng ht q2 q3)

open PEqualNP.MetaComplexity.NestedCover

-- The wire evaluation lemmas follow L-meta-2668, whose bypass helpers credit L-meta-1499.
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

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

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

def ref (cutoff i : ℕ) : Wire :=
  if h : i < cutoff ∧ i < 15 then ⟨i, by omega⟩ else dummy

theorem ref_val (cutoff i : ℕ) (h : i < cutoff) (h15 : i < 15) :
    (ref cutoff i).val = i := by simp [ref, h, h15]

theorem ref_bad (cutoff i : ℕ) (h : cutoff ≤ i) : ref cutoff i = dummy := by
  simp [ref, show ¬ i < cutoff from Nat.not_lt.mpr h]

theorem ref_ne (cutoff i : ℕ) (h : i < cutoff) (h15 : i < 15) :
    ref cutoff i ≠ dummy := by
  intro e
  have eq := congrArg Fin.val e
  rw [ref_val cutoff i h h15] at eq
  change i = 15 at eq
  omega

def valuation (C : Circuit) (x : Fin 8 → Bool) (i : Wire) : Bool :=
  val C (List.ofFn x) i.val

theorem dummy_false (C : Circuit) (hs : C.gates.length ≤ 7) (x : Fin 8 → Bool) :
    valuation C x dummy = false := by
  apply val_ge (n := 8) List.length_ofFn
  change 8 + C.gates.length ≤ 15
  omega

theorem ref_eval (C : Circuit) (hs : C.gates.length ≤ 7) (x : Fin 8 → Bool)
    (cutoff i : ℕ) (hcut : cutoff ≤ 15) :
    valuation C x (ref cutoff i) = if i < cutoff then val C (List.ofFn x) i else false := by
  by_cases h : i < cutoff
  · simp [valuation, h, ref_val cutoff i h (by omega)]
  · rw [ite_eq_right h, ref_bad cutoff i (by omega), dummy_false C hs x]

def atom (j i : ℕ) : Expr := .lit (ref (8 + j) i) true

def gateExpr (j : ℕ) (g : Gate) : Expr :=
  match g.inputs with
  | [] => .lit dummy (match g.op with | .and => false | _ => true)
  | [i] => atom j i
  | i :: k :: _ => match g.op with
    | .and => .and (atom j i) (atom j k)
    | _ => .or (atom j i) (atom j k)

theorem ref_used (cutoff i : ℕ) (h : ref cutoff i ≠ dummy) : (ref cutoff i).val < cutoff := by
  by_cases hp : i < cutoff ∧ i < 15
  · rw [ref_val cutoff i hp.1 hp.2]
    exact hp.1
  · exact (h (by simp [ref, hp])).elim

theorem atom_support (j i : ℕ) {k : Wire} (h : k ∈ support (atom j i)) :
    k.val < 8 + j := by
  by_cases e : ref (8 + j) i = dummy
  · simp [atom, support, e] at h
  · have t : k = ref (8 + j) i := by simpa [atom, support, e] using h
    rw [t]
    exact ref_used _ _ e

theorem gate_shape (j : ℕ) (g : Gate) :
    clean (gateExpr j g) ∧ (gateExpr j g).leaves ≤ 2 ∧
      (∀ i ∈ support (gateExpr j g), i.val < 8 + j) := by
  rcases g with ⟨op, l⟩
  rcases l with _ | ⟨i, _ | ⟨k, l⟩⟩
  · simp [gateExpr, clean, DMFormula.leaves, support]
  · exact ⟨Or.inl rfl, by change 1 ≤ 2; decide, fun _ h => atom_support j i h⟩
  · cases op <;>
    simpa only [gateExpr, clean, atom, DMFormula.leaves, support, true_or, and_self,
      Nat.reduceAdd, le_refl, true_and] using
      (fun a (ha : a ∈ support (atom j i) ∪ support (atom j k)) =>
        (Finset.mem_union.mp ha).elim (atom_support j i) (atom_support j k) :
        ∀ a ∈ support (atom j i) ∪ support (atom j k), a.val < 8+j)

theorem gate_value (C : Circuit) (hs : C.gates.length ≤ 7) (hm : Monotone2 C)
    (x : Fin 8 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (gateExpr j (gateAt C j)).eval (valuation C x) = valuation C x (ref 15 (8 + j)) := by
  have cut : 8 + j ≤ 15 := by omega
  have hr : (ref 15 (8 + j)).val = 8 + j := ref_val 15 _ (by omega) (by omega)
  have rr : valuation C x (ref 15 (8 + j)) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => if i < 8+j then val C (List.ofFn x) i else false) := by
    unfold valuation
    rw [hr]
    exact val_gate (n := 8) List.length_ofFn hj
  rw [rr]
  have he (i : ℕ) : (atom j i).eval (valuation C x) =
      if i < 8 + j then val C (List.ofFn x) i else false :=
    ref_eval C hs x (8 + j) i cut
  have hd := dummy_false C hs x
  have splitGate (g : Gate) (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
      (gateExpr j g).eval (valuation C x) =
        g.op.eval (g.inputs.map fun i => if i < 8+j then val C (List.ofFn x) i else false) := by
    rcases g with ⟨op, l⟩
    change op = .and ∨ op = .or at hop
    change l.length ≤ 2 at hlen
    rcases l with _ | ⟨i, _ | ⟨k, _ | ⟨z, rest⟩⟩⟩
    · rcases hop with rfl | rfl <;> simp [gateExpr, DMFormula.eval, GateOp.eval, hd]
    · rcases hop with rfl | rfl <;> simp [gateExpr, GateOp.eval, he]
    · rcases hop with rfl | rfl <;> simp [gateExpr, DMFormula.eval, GateOp.eval, he]
    · simp at hlen
  exact splitGate _ (hm _ (gateAt_mem hj)).1 (hm _ (gateAt_mem hj)).2

def expand (C : Circuit) : ℕ → Expr → Expr
  | 0, f => f
  | j + 1, f => expand C j (plug (ref 15 (8 + j)) (gateExpr j (gateAt C j)) f)

theorem expand_card (C : Circuit) (hs : C.gates.length ≤ 7) (j : ℕ)
    (hj : j ≤ C.gates.length) (f : Expr) :
    (support (expand C j f)).card ≤ (support f).card + j := by
  induction j generalizing f with
  | zero => simp [expand]
  | succ j ih =>
    rw [expand]
    have h := ih (by omega) (plug (ref 15 (8 + j)) (gateExpr j (gateAt C j)) f)
    have h' := plug_grow (ref 15 (8 + j)) (gateExpr j (gateAt C j)) f
      (ref_ne 15 _ (by omega) (by omega)) (gate_shape j (gateAt C j)).2.1
    omega

-- Substitution for one gate adds at most one variable. Equality preserves linearity.
theorem expand_linear (C : Circuit) (hs : C.gates.length ≤ 7) (j : ℕ)
    (hj : j ≤ C.gates.length) (f : Expr) (hf : linear f)
    (hfull : (support (expand C j f)).card = (support f).card + j) :
    linear (expand C j f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih =>
    let k := ref 15 (8 + j)
    let v := gateExpr j (gateAt C j)
    let g := plug k v f
    have kn : k ≠ dummy := ref_ne 15 _ (by omega) (by omega)
    have v2 := (gate_shape j (gateAt C j)).2.1
    have h1 : (support g).card ≤ (support f).card + 1 := plug_grow k v f kn v2
    have h2 := expand_card C hs j (by omega) g
    change (support (expand C j g)).card = (support f).card + (j + 1) at hfull
    have hg : linear g := by
      have ht := plug_leaves k v f kn v2 hf
      have hbound := support_le g
      unfold linear at hf ⊢
      change g.leaves ≤ f.leaves + 1 at ht
      omega
    have heq : (support (expand C j g)).card = (support g).card + j := by omega
    exact ih (by omega) g hg heq

theorem expand_prior (C : Circuit) (hs : C.gates.length ≤ 7) (j : ℕ)
    (hj : j ≤ C.gates.length) (f : Expr)
    (hf : ∀ i ∈ support f, i.val < 8 + j) :
    ∀ i ∈ support (expand C j f), i.val < 8 := by
  induction j generalizing f with
  | zero => simpa [expand] using hf
  | succ j ih =>
    rw [expand]
    apply ih (by omega)
    intro w hw
    have look := plug_subset (ref 15 (8 + j)) (gateExpr j (gateAt C j)) f hw
    rcases Finset.mem_union.mp look with first | second
    · obtain ⟨hne, hm⟩ := Finset.mem_erase.mp first
      have hlt := hf _ hm
      have hr := ref_val 15 (8 + j) (by omega) (by omega)
      by_contra lower
      have he : w = ref 15 (8 + j) := by apply Fin.ext; omega
      exact hne he
    · exact (gate_shape j (gateAt C j)).2.2 w second

theorem expand_eval (C : Circuit) (hs : C.gates.length ≤ 7) (hm : Monotone2 C)
    (j : ℕ) (hj : j ≤ C.gates.length) (f : Expr) (hf : clean f) :
    clean (expand C j f) ∧
      ∀ x : Fin 8 → Bool, (expand C j f).eval (valuation C x) = f.eval (valuation C x) := by
  induction j generalizing f with
  | zero => exact ⟨hf, fun _ => rfl⟩
  | succ j ih =>
    rw [expand]
    have kg := (gate_shape j (gateAt C j)).1
    have hk := ref_ne 15 (8 + j) (by omega) (by omega)
    obtain ⟨hc, e⟩ := ih (by omega) _ (plug_clean _ _ _ kg hf)
    exact ⟨hc, fun x => (e x).trans
      (plug_eval _ _ _ _ hk (gate_value C hs hm x j (by omega)) hf)⟩

def rootExpr (C : Circuit) : Expr := .lit (ref (8 + C.gates.length) C.output) true
def formula (C : Circuit) : Expr := expand C C.gates.length (rootExpr C)

theorem formula_card (C : Circuit) (hs : C.gates.length ≤ 7) :
    (support (formula C)).card ≤ (support (rootExpr C)).card + C.gates.length :=
  expand_card C hs C.gates.length (by rfl) (rootExpr C)

theorem formula_prior (C : Circuit) (hs : C.gates.length ≤ 7) :
    ∀ i ∈ support (formula C), i.val < 8 := by
  apply expand_prior C hs _ le_rfl
  intro i h
  by_cases e : ref (8 + C.gates.length) C.output = dummy
  · simp [rootExpr, support, e] at h
  · have t : i = ref (8 + C.gates.length) C.output := by
      simpa [rootExpr, support, e] using h
    rw [t]
    exact ref_used _ _ e

theorem formula_spec (C : Circuit) (hs : C.gates.length ≤ 7) (hmono : Monotone2 C) :
    clean (formula C) ∧
      ∀ x : Fin 8 → Bool, (formula C).eval (valuation C x) = C.eval (List.ofFn x) := by
  obtain ⟨hc, he⟩ := expand_eval C hs hmono _ le_rfl (rootExpr C) (Or.inl rfl)
  refine ⟨hc, ?_⟩
  intro x
  rw [show formula C = expand C C.gates.length (rootExpr C) from rfl, he x]
  change valuation C x (ref (8 + C.gates.length) C.output) = val C (List.ofFn x) C.output
  rw [ref_eval C hs x (8 + C.gates.length) C.output (by omega)]
  by_cases h : C.output < 8 + C.gates.length
  · simp [h]
  · rw [ite_eq_right h]
    symm
    exact val_ge (n := 8) List.length_ofFn (by omega)

def embed (i : Fin 8) : Wire := ⟨i.val, by omega⟩

theorem input_value (C : Circuit) (x : Fin 8 → Bool) (i : Fin 8) :
    valuation C x (embed i) = x i := by
  unfold valuation embed
  rw [val_input (n := 8) List.length_ofFn i.2]
  fin_cases i <;> rfl

theorem on_formula (C : Circuit) (hs : C.gates.length ≤ 7) (hm : Monotone2 C) (S : Finset Wire) :
    on (formula C) S = C.eval (List.ofFn fun i : Fin 8 => decide (embed i ∈ S)) := by
  let x := fun i : Fin 8 => decide (embed i ∈ S)
  rw [← (formula_spec C hs hm).2 x]
  apply eval_congr_support
  · simp [dummy_false C hs x]
  · intro w hw
    have hlt := formula_prior C hs w hw
    let i : Fin 8 := ⟨w.val, hlt⟩
    have he : w = embed i := Fin.ext rfl
    have hd : w ≠ dummy := by
      intro e
      rw [e] at hlt
      change 15 < 8 at hlt
      omega
    change decide (w ∈ S ∧ w ≠ dummy) = valuation C x w
    have ht : (w ∈ S ∧ w ≠ dummy) ↔ w ∈ S := ⟨And.left, fun h => ⟨h, hd⟩⟩
    calc
      decide (w ∈ S ∧ w ≠ dummy) = decide (w ∈ S) := decide_eq_decide.mpr ht
      _ = decide (embed i ∈ S) := congrArg (fun v : Wire => decide (v ∈ S)) he
      _ = valuation C x (embed i) := (input_value C x i).symm
      _ = valuation C x w := (congrArg (valuation C x) he).symm

theorem on_support_mono (f : Expr) (hf : clean f) (X Y : Finset Wire)
    (h : ∀ w ∈ support f, w ∈ X → w ∈ Y) : on f X = true → on f Y = true := by
  have ea : on f X = on f (X ∩ support f) := on_congr f _ _ (by
    intro w hw
    simp [hw])
  have eb : on f Y = on f (Y ∩ support f) := on_congr f _ _ (by
    intro w hw
    simp [hw])
  rw [ea, eb]
  apply on_mono f hf
  intro w hw
  obtain ⟨hwx, hws⟩ := Finset.mem_inter.mp hw
  exact Finset.mem_inter.mpr ⟨h w hws hwx, hws⟩


def A (u v : Fin 4) : Bool := (4398 : ℕ).testBit (4 * u.val + v.val)

def edgeSet (u v : Fin 4) : Finset Wire :=
  {embed (Fin.castAdd 4 u), embed (Fin.natAdd 4 v)}

theorem oneEach_edge : ∀ (u v : Fin 4),
    (List.ofFn fun i : Fin 8 => decide (embed i ∈ edgeSet u v)) = oneEach u v := by
  unfold edgeSet embed oneEach
  decide +kernel

-- For each input there is an accepted row dominated by a rejected row off that input.
theorem separates (i : Fin 8) :
    ∃ u v p q : Fin 4, A u v = true ∧ A p q = false ∧
      ∀ w : Wire, w ≠ embed i → w ∈ edgeSet u v → w ∈ edgeSet p q := by
  fin_cases i
  · exact ⟨0, 2, 1, 2, by decide +kernel⟩
  · exact ⟨1, 1, 2, 1, by decide +kernel⟩
  · exact ⟨2, 0, 0, 0, by decide +kernel⟩
  · exact ⟨3, 0, 0, 0, by decide +kernel⟩
  · exact ⟨2, 0, 2, 1, by decide +kernel⟩
  · exact ⟨1, 1, 1, 0, by decide +kernel⟩
  · exact ⟨0, 2, 0, 0, by decide +kernel⟩
  · exact ⟨0, 3, 0, 0, by decide +kernel⟩

theorem zero_row (i : Fin 8) : ∃ u v : Fin 4, A u v = false ∧ embed i ∈ edgeSet u v := by
  revert i
  unfold A edgeSet embed
  decide +kernel

theorem notRep7 : ¬ RepSizeAtMost A 7 := by
  rintro ⟨C, hm, hsize, hr⟩
  have hs : C.gates.length ≤ 7 := hsize
  let f := formula C
  have hc : clean f := (formula_spec C hs hm).1
  have edge (u v : Fin 4) : on f (edgeSet u v) = A u v := by
    rw [show f = formula C from rfl, on_formula C hs hm, oneEach_edge]
    exact hr u v
  have raw (i : Fin 8) : embed i ∈ support f := by
    by_contra hn
    obtain ⟨u, v, p, q, hy, hn0, htest⟩ := separates i
    have hv : ∀ w ∈ support f, w ∈ edgeSet u v → w ∈ edgeSet p q := by
      intro w hw
      exact htest w (fun e => hn (e ▸ hw))
    have true0 : on f (edgeSet u v) = true := (edge u v).trans hy
    have true1 := on_support_mono f hc _ _ hv true0
    rw [edge p q, hn0] at true1
    contradiction
  have inj : Function.Injective embed := by
    intro a b h
    exact Fin.ext (congrArg (fun w : Wire => w.val) h)
  have many : 8 ≤ (support f).card := by
    calc
      8 = ((Finset.univ : Finset (Fin 8)).image embed).card := by
        rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin]
      _ ≤ (support f).card := Finset.card_le_card (by
        intro w hw
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
        exact raw i)
  have hbound := formula_card C hs
  change (support f).card ≤ (support (rootExpr C)).card + C.gates.length at hbound
  have cap : (support (rootExpr C)).card ≤ 1 := support_le (rootExpr C)
  have root : linear (rootExpr C) := by
    change (support (rootExpr C)).card = 1
    omega
  have equality : (support f).card = (support (rootExpr C)).card + C.gates.length := by omega
  have hl : linear f := expand_linear C hs _ le_rfl _ root equality
  have allFalse (w : Wire) : on f {w} = false := by
    by_cases hw : w.val < 8
    · let i : Fin 8 := ⟨w.val, hw⟩
      have he : w = embed i := Fin.ext rfl
      obtain ⟨u, v, hfalse, hi⟩ := zero_row i
      have hsub : {w} ⊆ edgeSet u v := by simpa [he] using hi
      cases hval : on f {w} with
      | false => rfl
      | true =>
        have htrue := on_mono f hc hsub hval
        rw [edge, hfalse] at htrue
        contradiction
    · have he : on f {w} = on f ∅ := on_congr f _ _ (by
        intro x hx
        have p : x.val < 8 := formula_prior C hs x hx
        have no : x ≠ w := by intro e; rw [e] at p; contradiction
        simp [no])
      rw [he, on_empty f hc hl]
  have h01 : on f {0, 5} = true := by
    change on f (edgeSet 0 1) = true
    rw [edge]
    decide
  have h11 : on f {1, 5} = true := by
    change on f (edgeSet 1 1) = true
    rw [edge]
    decide
  have h02 : on f {0, 6} = true := by
    change on f (edgeSet 0 2) = true
    rw [edge]
    decide
  have h12 : on f {1, 6} = false := by
    change on f (edgeSet 1 2) = false
    rw [edge]
    decide
  have h := rectangle f hc hl allFalse 0 5 1 6 h01 h11 h02
  rw [h12] at h
  contradiction

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [4, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

theorem rep8 : RepSizeAtMost A 8 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩
  · unfold A Represents witness
    decide +kernel


end PEqualNP.Outside.L_meta_5552

theorem PEqualNP.Outside.L_meta_5552 :
  PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4398 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4398 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  ⟨PEqualNP.Outside.L_meta_5552.rep8, PEqualNP.Outside.L_meta_5552.notRep7⟩
