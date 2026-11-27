import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13341

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, htl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t,
      by simpa [wiresFrom, List.append_assoc] using ht, by simp [htl]⟩

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, htl⟩ := wiresFrom_prefix gs w
  rw [ht, List.length_append, htl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def OkG (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def NOk (g : Gate) : Prop :=
  OkG g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : OkG g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    change wiresFrom (gs.map normGate) (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) =
           wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    rw [normGate_eval, ih]

lemma getD_snoc_eq {α : Type} (L : List α) (x d : α) : (L ++ [x]).getD L.length d = x := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_len {α : Type} (L : List α) (x d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [x]).getD k d = x := by
  subst h; exact getD_snoc_eq L x d

lemma getD_snoc_ne {α : Type} (L : List α) (x d : α) (i : ℕ) (hi : i ≠ L.length) :
    (L ++ [x]).getD i d = L.getD i d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hlt : i < L.length
  · rw [List.getElem?_append_left hlt]
  · rw [List.getElem?_eq_none (by simp only [List.length_append, List.length_singleton]; omega),
        List.getElem?_eq_none (by omega)]

lemma getD_snoc_ne_len {α : Type} (L : List α) (x d : α) (i k : ℕ) (h : L.length = k) (hi : i ≠ k) :
    (L ++ [x]).getD i d = L.getD i d := by
  subst h; exact getD_snoc_ne L x d i hi

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

lemma rel_wiresFrom (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, n ≤ W.length → W'.length + n = W.length + m →
    (∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false) →
    ∀ w : ℕ, (wiresFrom (gs.map (relGate n m π)) W').getD (wmap n m π w) false =
      (wiresFrom gs W).getD w false := by
  induction gs with
  | nil => intro W W' _ _ h w; exact h w
  | cons g gs ih =>
    intro W W' h1 h2 h3
    have hv : (relGate n m π g).op.eval ((relGate n m π g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [relGate, List.map_map]
      congr 1; apply List.map_congr_left; intro a _; exact h3 a
    change ∀ w, (wiresFrom (gs.map (relGate n m π)) (W' ++ [_])).getD (wmap n m π w) false =
                (wiresFrom gs (W ++ [_])).getD w false
    rw [hv]
    apply ih _ _ (by simp; omega) (by simp; omega)
    intro w
    rcases Nat.lt_trichotomy w W.length with hw | hw | hw
    · have hlt : wmap n m π w < W'.length := by
        unfold wmap; split
        · have := (π ⟨w, by assumption⟩).2; omega
        · omega
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 w
    · have he : wmap n m π w = W'.length := by unfold wmap; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ wmap n m π w := by unfold wmap; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show (wiresFrom (C.gates.map (relGate n m π)) (List.ofFn x)).getD (wmap n m π C.output) false = h (x ∘ π)
    rw [← hev (x ∘ π)]
    apply rel_wiresFrom n m π C.gates (List.ofFn (x ∘ π)) (List.ofFn x) (by simp) (by simp; omega)
    intro w
    unfold wmap
    split
    · rename_i hw
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
      simp
    · rename_i hw
      rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

def statVal (w : List Bool) : ℕ → Bool
  | 0 => false
  | 1 => true
  | j + 2 => w.getD j false

def statValid (m s : ℕ) : Prop := 2 ≤ s → s - 2 < m

def simpNot (m : ℕ) : List ℕ → Option Gate × ℕ
  | [] => (none, 1)
  | 0 :: _ => (none, 1)
  | 1 :: _ => (none, 0)
  | (j + 2) :: _ => (some ⟨GateOp.not, [j]⟩, m + 2)

def simpAnd (m : ℕ) : List ℕ → Option Gate × ℕ
  | [] => (none, 1)
  | [a] => (none, a)
  | [0, _] => (none, 0)
  | [_, 0] => (none, 0)
  | [1, b] => (none, b)
  | [a, 1] => (none, a)
  | [j + 2, k + 2] => (some ⟨GateOp.and, [j, k]⟩, m + 2)
  | _ => (none, 0)

def simpOr (m : ℕ) : List ℕ → Option Gate × ℕ
  | [] => (none, 0)
  | [a] => (none, a)
  | [1, _] => (none, 1)
  | [_, 1] => (none, 1)
  | [0, b] => (none, b)
  | [a, 0] => (none, a)
  | [j + 2, k + 2] => (some ⟨GateOp.or, [j, k]⟩, m + 2)
  | _ => (none, 0)

def simplify (op : GateOp) (m : ℕ) (ins : List ℕ) : Option Gate × ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, 0)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List ℕ) :
    ∀ g ∈ (simplify op m ins).1, OkG g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · simp [simpAnd] at hg
    · rcases a with _ | _ | j <;> rcases b with _ | _ | k <;> simp [simpAnd] at hg
      subst hg; simp [OkG]
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · simp [simpOr] at hg
    · rcases a with _ | _ | j <;> rcases b with _ | _ | k <;> simp [simpOr] at hg
      subst hg; simp [OkG]
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · rcases a with _ | _ | j <;> simp [simpNot] at hg
      subst hg; simp [OkG]
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c ∈ ins, c < 2) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hcm, hc2⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd]
    · simp [simplify, simpAnd]
    · rcases a with _ | _ | j <;> rcases b with _ | _ | k <;> simp_all [simplify, simpAnd]
      omega
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr]
    · simp [simplify, simpOr]
    · rcases a with _ | _ | j <;> rcases b with _ | _ | k <;> simp_all [simplify, simpOr]
      omega
    · simp at hlen
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simplify, simpNot]
    · rcases a with _ | _ | j <;> simp_all [simplify, simpNot]
    · simp at this

lemma simplify_kill_const (op : GateOp) (m : ℕ) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1)
    (hk : (op = GateOp.and ∧ 0 ∈ ins) ∨ (op = GateOp.or ∧ 1 ∈ ins) ∨ (op = GateOp.not ∧ (0 ∈ ins ∨ 1 ∈ ins))) :
    (simplify op m ins).1 = none ∧ (simplify op m ins).2 < 2 := by
  rcases hk with ⟨rfl, h0⟩ | ⟨rfl, h1⟩ | ⟨rfl, h01⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at h0
    · simp only [List.mem_singleton] at h0; subst h0; simp [simplify, simpAnd]
    · rcases a with _ | _ | j <;> rcases b with _ | _ | k <;> simp_all [simplify, simpAnd]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at h1
    · simp only [List.mem_singleton] at h1; subst h1; simp [simplify, simpOr]
    · rcases a with _ | _ | j <;> rcases b with _ | _ | k <;> simp_all [simplify, simpOr]
    · simp at hlen
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at h01
    · rcases h01 with h0 | h1
      · simp only [List.mem_singleton] at h0; subst h0; simp [simplify, simpNot]
      · simp only [List.mem_singleton] at h1; subst h1; simp [simplify, simpNot]
    · simp at this

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List ℕ) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  have hget : ∀ (g : Gate), (wiresFrom [g] w).getD w.length false =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro g; simp [wiresFrom, List.getD_eq_getElem?_getD]
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · have hva := hv a List.mem_cons_self
      rcases a with _ | _ | j
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        exact hva (by omega)
    · have hva := hv a List.mem_cons_self
      have hvb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases a with _ | _ | j <;> rcases b with _ | _ | k
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        exact hvb (by omega)
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        exact hva (by omega)
      · refine ⟨by simp [simplify, simpAnd, statValid], ?_⟩
        simp only [simplify, simpAnd, Option.toList_some, statVal, hget, List.map_cons, List.map_nil, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · have hva := hv a List.mem_cons_self
      rcases a with _ | _ | j
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        exact hva (by omega)
    · have hva := hv a List.mem_cons_self
      have hvb := hv b (List.mem_cons_of_mem _ List.mem_cons_self)
      rcases a with _ | _ | j <;> rcases b with _ | _ | k
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        exact hvb (by omega)
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        exact hva (by omega)
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · refine ⟨by simp [simplify, simpOr, statValid], ?_⟩
        simp only [simplify, simpOr, Option.toList_some, statVal, hget, List.map_cons, List.map_nil, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · rcases a with _ | _ | j
      · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
      · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
      · refine ⟨by simp [simplify, simpNot, statValid], ?_⟩
        simp only [simplify, simpNot, Option.toList_some, statVal, hget, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]

def elimStep (n : ℕ) (acc : List ℕ × List Gate) (g : Gate) : List ℕ × List Gate :=
  let r := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List ℕ × List Gate) : List ℕ × List Gate :=
  gs.foldl (elimStep n) acc

lemma elim_append (n : ℕ) (L1 L2 : List Gate) (acc : List ℕ × List Gate) :
    elim n (L1 ++ L2) acc = elim n L2 (elim n L1 acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc; change (elim n gs (elimStep n acc g)).1.length = _; rw [ih]; simp [elimStep]; omega

lemma elim_getD (n k : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k 0 = acc.1.getD k 0 := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    change (elim n gs (elimStep n acc g)).1.getD k 0 = acc.1.getD k 0
    rw [ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    (∀ g ∈ acc.2, OkG g) → ∀ g ∈ (elim n gs acc).2, OkG g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1
      omega
    change (elim n gs (elimStep n acc g)).2.length ≤ _
    rw [List.length_cons]; omega

lemma elim_len_sub_one (n k : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → acc.1.getD k 0 < 2 →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ ⟨g, hg, _⟩; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    change (elim n gs (elimStep n acc g)).2.length + 1 ≤ acc.2.length + (g :: gs).length
    rw [List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1 = none :=
        simplify_count _ _ _ hnok.1.1 (by simpa using hnok.1.2) (fun h => by simpa using hnok.2 h)
          ⟨acc.1.getD k 0, List.mem_map.2 ⟨k, hkg, rfl⟩, hc⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc) hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1
        omega
      omega

lemma elim_len_sub_two_multi (n k : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → acc.1.getD k 0 < 2 →
    2 ≤ (gs.filter fun g => decide (k ∈ g.inputs)).length →
    (elim n gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; simp at h
  | cons g gs ih =>
    intro acc hok hk hc h2cnt
    change (elim n gs (elimStep n acc g)).2.length + 2 ≤ acc.2.length + (g :: gs).length
    rw [List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1 = none :=
        simplify_count _ _ _ hnok.1.1 (by simpa using hnok.1.2) (fun h => by simpa using hnok.2 h)
          ⟨acc.1.getD k 0, List.mem_map.2 ⟨k, hkg, rfl⟩, hc⟩
      have hstep : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hrest_pos : 1 ≤ (gs.filter fun g' => decide (k ∈ g'.inputs)).length := by
        simp only [List.filter_cons, decide_eq_true hkg, ite_true, List.length_cons] at h2cnt; omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : (gs.filter fun g' => decide (k ∈ g'.inputs)) ≠ [] := by
          intro he; rw [he] at hrest_pos; simp at hrest_pos
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter, decide_eq_true_eq] at hg'
        exact ⟨g', hg'.1, hg'.2⟩
      have h1 := elim_len_sub_one n k gs (elimStep n acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc) hex'
      omega
    · have hrest : 2 ≤ (gs.filter fun g' => decide (k ∈ g'.inputs)).length := by
        simpa [List.filter_cons, hkg] using h2cnt
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc) hrest
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1
        omega
      omega

lemma elim_len_sub_two_pair (n k1 k2 : ℕ) (gs : List Gate) : ∀ acc : List ℕ × List Gate,
    (∀ g ∈ gs, NOk g) → k1 < acc.1.length → k2 < acc.1.length →
    acc.1.getD k1 0 < 2 → acc.1.getD k2 0 < 2 →
    ∀ (a b : ℕ) (ha : a < gs.length) (hb : b < gs.length), a ≠ b →
    k1 ∈ (gs[a]'ha).inputs → k2 ∈ (gs[b]'hb).inputs →
    (elim n gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ _ _ a _ ha; simp at ha
  | cons g gs ih =>
    intro acc hok hk1 hk2 hc1 hc2 a b ha hb hab hka hkb
    change (elim n gs (elimStep n acc g)).2.length + 2 ≤ acc.2.length + (g :: gs).length
    rw [List.length_cons]
    cases a with
    | zero =>
      cases b with
      | zero => exact absurd rfl hab
      | succ b' =>
        simp only [List.getElem_cons_zero] at hka
        simp only [List.getElem_cons_succ] at hkb
        have hnok := hok g List.mem_cons_self
        have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1 = none :=
          simplify_count _ _ _ hnok.1.1 (by simpa using hnok.1.2) (fun h => by simpa using hnok.2 h)
            ⟨acc.1.getD k1 0, List.mem_map.2 ⟨k1, hka, rfl⟩, hc1⟩
        have hstep : (elimStep n acc g).2.length = acc.2.length := by
          simp only [elimStep, hnone, Option.toList_none, List.append_nil]
        have h1 := elim_len_sub_one n k2 gs (elimStep n acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by simp [elimStep]; omega)
          (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc2)
          ⟨gs[b']'(by simp at hb; omega), List.getElem_mem _, hkb⟩
        omega
    | succ a' =>
      cases b with
      | zero =>
        simp only [List.getElem_cons_succ] at hka
        simp only [List.getElem_cons_zero] at hkb
        have hnok := hok g List.mem_cons_self
        have hnone : (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1 = none :=
          simplify_count _ _ _ hnok.1.1 (by simpa using hnok.1.2) (fun h => by simpa using hnok.2 h)
            ⟨acc.1.getD k2 0, List.mem_map.2 ⟨k2, hkb, rfl⟩, hc2⟩
        have hstep : (elimStep n acc g).2.length = acc.2.length := by
          simp only [elimStep, hnone, Option.toList_none, List.append_nil]
        have h1 := elim_len_sub_one n k1 gs (elimStep n acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by simp [elimStep]; omega)
          (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc1)
          ⟨gs[a']'(by simp at ha; omega), List.getElem_mem _, hka⟩
        omega
      | succ b' =>
        simp only [List.getElem_cons_succ] at hka hkb
        have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by simp [elimStep]; omega) (by simp [elimStep]; omega)
          (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc1)
          (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc2)
          a' b' (by simp at ha; omega) (by simp at hb; omega) (by omega) hka hkb
        have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i 0)).1
          omega
        omega

lemma elim_len_sub_two_chain (n k : ℕ) (gs : List Gate) : ∀ (acc : List ℕ × List Gate) (i : ℕ),
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    (hi : i < gs.length) →
    k ∈ (gs[i]'hi).inputs →
    (((gs[i]'hi).op = GateOp.and ∧ acc.1.getD k 0 = 0) ∨
     ((gs[i]'hi).op = GateOp.or  ∧ acc.1.getD k 0 = 1) ∨
     ((gs[i]'hi).op = GateOp.not ∧ (acc.1.getD k 0 = 0 ∨ acc.1.getD k 0 = 1))) →
    (∃ g' ∈ gs.drop (i + 1), acc.1.length + i ∈ g'.inputs) →
    (elim n gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc i _ _ hi; simp at hi
  | cons g gs ih =>
    intro acc i hok hk hi hki hkill hlater
    change (elim n gs (elimStep n acc g)).2.length + 2 ≤ acc.2.length + (g :: gs).length
    rw [List.length_cons]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero, Nat.add_zero] at hki hkill hlater
      have hnok := hok g List.mem_cons_self
      have hks : (simplify g.op (n + acc.2.length) (g.inputs.map fun x => acc.1.getD x 0)).1 = none ∧
                 (simplify g.op (n + acc.2.length) (g.inputs.map fun x => acc.1.getD x 0)).2 < 2 := by
        apply simplify_kill_const _ _ _ hnok.1.1 (by simpa using hnok.1.2) (fun h => by simpa using hnok.2 h)
        rcases hkill with ⟨ho, hv⟩ | ⟨ho, hv⟩ | ⟨ho, hv⟩
        · exact Or.inl ⟨ho, List.mem_map.2 ⟨k, hki, hv⟩⟩
        · exact Or.inr (Or.inl ⟨ho, List.mem_map.2 ⟨k, hki, hv⟩⟩)
        · rcases hv with hv | hv
          · exact Or.inr (Or.inr ⟨ho, Or.inl (List.mem_map.2 ⟨k, hki, hv⟩)⟩)
          · exact Or.inr (Or.inr ⟨ho, Or.inr (List.mem_map.2 ⟨k, hki, hv⟩)⟩)
      have hstep : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hks.1, Option.toList_none, List.append_nil]
      have hwire_c : (elimStep n acc g).1.getD acc.1.length 0 < 2 := by
        simp only [elimStep]; rw [getD_snoc_eq]; exact hks.2
      have h1 := elim_len_sub_one n acc.1.length gs (elimStep n acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]) hwire_c hlater
      omega
    | succ i' =>
      simp only [List.getElem_cons_succ, List.drop_succ_cons] at hki hkill hlater
      have hi' : i' < gs.length := by simp at hi; omega
      have hlen1 : (elimStep n acc g).1.length = acc.1.length + 1 := by simp [elimStep]
      have hk_same : (elimStep n acc g).1.getD k 0 = acc.1.getD k 0 := by
        simp only [elimStep]; exact getD_snoc_ne _ _ _ _ (by omega)
      have h1 := ih (elimStep n acc g) i' (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by omega) hi' hki (by rwa [hk_same])
        (by rw [hlen1]; simpa [Nat.add_assoc, Nat.add_comm 1 i'] using hlater)
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length) (g.inputs.map fun x => acc.1.getD x 0)).1
        omega
      omega

lemma statValid_mono {m m' s : ℕ} (h : m ≤ m') (hv : statValid m s) : statValid m' s :=
  fun h2 => lt_of_lt_of_le (hv h2) h

lemma statVal_append (w t : List Bool) : ∀ s : ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | 0, _ => rfl
  | 1, _ => rfl
  | j + 2, hv => by
    have hlt : j < w.length := by simpa [statValid] using hv (by omega)
    simp only [statVal, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List ℕ × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i 0) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i 0) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List ℕ × List Gate), (∀ g ∈ gs, OkG g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i 0 with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by intro s hs; obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs; rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _; exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := wiresFrom_append _ _ _
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i 0) ∧
         statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i 0) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

lemma wiresFrom_agree_except (gs : List Gate) (bad : Finset ℕ) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
    (∀ i, i ∉ bad → w1.getD i false = w2.getD i false) →
    (∀ g ∈ gs, ∀ a ∈ g.inputs, a ∉ bad) →
    ∀ i, i ∉ bad → (wiresFrom gs w1).getD i false = (wiresFrom gs w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ h _; exact h
  | cons g gs ih =>
    intro w1 w2 hlen hagree hno
    apply ih
    · simp [hlen]
    · intro i hi
      by_cases hil : i = w1.length
      · subst hil
        rw [getD_snoc_eq, hlen, getD_snoc_eq]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact hagree a (hno g List.mem_cons_self a ha)
      · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
        exact hagree i hi
    · intro g' hg' a ha
      exact hno g' (List.mem_cons_of_mem _ hg') a ha

def initFix (m p : ℕ) (b : Bool) : List ℕ :=
  List.ofFn (fun i : Fin m => if i.val = p then (if b then 1 else 0) else i.val + 2)

lemma initFix_len (m p : ℕ) (b : Bool) : (initFix m p b).length = m := by simp [initFix]

lemma initFix_getD_self {m : ℕ} (p : Fin m) (b : Bool) :
    (initFix m p.val b).getD p.val 0 = if b then 1 else 0 := by
  rw [initFix, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]; simp

lemma inv_initFix {m : ℕ} (p : Fin m) (b : Bool) (x : Fin m → Bool) :
    Inv m (List.ofFn x) (List.ofFn (Function.update x p b)) (initFix m p.val b, []) := by
  refine ⟨by simp [initFix], ?_⟩
  intro i
  by_cases hlt : i < m
  · have hget : (initFix m p.val b).getD i 0 = if i = p.val then (if b then 1 else 0) else i + 2 := by
      rw [initFix, List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
    have hgety : (List.ofFn (Function.update x p b)).getD i false = Function.update x p b ⟨i, hlt⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
    rw [hget, hgety]
    by_cases hip : i = p.val
    · have hfin : (⟨i, hlt⟩ : Fin m) = p := Fin.ext hip
      rw [hfin]
      simp only [hip, ite_true, Function.update_self]
      cases b <;> simp [statValid, statVal]
    · have hfin : (⟨i, hlt⟩ : Fin m) ≠ p := fun e => hip (congrArg Fin.val e)
      simp only [hip, ite_false, Function.update_of_ne hfin]
      refine ⟨fun _ => by simp; omega, ?_⟩
      change (List.ofFn x).getD i false = x ⟨i, hlt⟩
      rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp [initFix]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    simp [statValid, statVal]

lemma mkCirc_from_elim {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) (b : Bool) (s : ℕ)
    (gs : List Gate) (out : ℕ) (hnok : ∀ g ∈ gs, NOk g)
    (hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = f x)
    (hnc : ∃ x y : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (hlen : (elim m gs (initFix m p.val b, [])).2.length ≤ s) :
    HasCircuitSize m (fun x => f (Function.update x p b)) s := by
  set acc := elim m gs (initFix m p.val b, []) with hacc
  have hinv : ∀ x : Fin m → Bool,
      Inv m (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x p b))) acc := fun x =>
    inv_elim m _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initFix p b x)
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD out 0) = f (Function.update x p b) := by
    intro x; rw [((hinv x).2 out).2, hevg]
  have hst2 : ¬ acc.1.getD out 0 < 2 := by
    intro hlt; obtain ⟨x, y, hne⟩ := hnc; apply hne
    rw [← hval x, ← hval y]; interval_cases (acc.1.getD out 0) <;> rfl
  refine ⟨⟨acc.2, acc.1.getD out 0 - 2⟩, ?_, hlen, ?_⟩
  · intro g hg
    have := elim_ok m gs (initFix m p.val b, []) (by simp) g hg
    exact ⟨by simpa using this.1, this.2⟩
  · intro x
    have hv := hval x
    obtain ⟨j, hj⟩ : ∃ j, acc.1.getD out 0 = j + 2 := ⟨acc.1.getD out 0 - 2, by omega⟩
    rw [hj] at hv ⊢
    exact hv

lemma exists_two_filter {k : ℕ} (L : List Gate) (a b : ℕ) (ha : a < L.length) (hb : b < L.length)
    (hab : a ≠ b) (hka : k ∈ (L[a]'ha).inputs) (hkb : k ∈ (L[b]'hb).inputs) :
    2 ≤ (L.filter fun g => decide (k ∈ g.inputs)).length := by
  have hlt : ∀ (M : List Gate) (u v : ℕ) (hu : u < M.length) (hv : v < M.length),
      u < v → k ∈ (M[u]'hu).inputs → k ∈ (M[v]'hv).inputs →
      2 ≤ (M.filter fun g => decide (k ∈ g.inputs)).length := by
    intro M; induction M with
    | nil => intro u v hu; simp at hu
    | cons g0 rest ih =>
      intro u v hu hv huv hku hkv
      cases u with
      | zero =>
        cases v with
        | zero => omega
        | succ v' =>
          simp only [List.getElem_cons_zero] at hku
          simp only [List.getElem_cons_succ] at hkv
          simp only [List.filter_cons, decide_eq_true hku, ite_true, List.length_cons]
          have hmem : rest[v']'(by simp at hv; omega) ∈ rest.filter (fun g => decide (k ∈ g.inputs)) :=
            List.mem_filter.2 ⟨List.getElem_mem _, decide_eq_true hkv⟩
          have hpos := List.length_pos_of_mem hmem
          omega
      | succ u' =>
        cases v with
        | zero => omega
        | succ v' =>
          simp only [List.getElem_cons_succ] at hku hkv
          have hih := ih u' v' (by simp at hu; omega) (by simp at hv; omega) (by omega) hku hkv
          by_cases hg0 : k ∈ g0.inputs <;> simp [hg0] <;> omega
  rcases lt_or_gt_of_ne hab with h | h
  · exact hlt L a b ha hb h hka hkb
  · exact hlt L b a hb ha h hkb hka

lemma out_ne_input_of_nc {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) (b : Bool)
    (gs : List Gate) (out : ℕ)
    (hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = f x)
    (hnc : ∃ x y : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) :
    out ≠ p.val := by
  intro hout
  obtain ⟨x, y, hne⟩ := hnc
  apply hne
  rw [← hevg, ← hevg, hout]
  rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
      List.getElem_ofFn, List.getElem_ofFn]
  simp

theorem one_gate_at {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize m f (s + 1)) :
    HasCircuitSize m (fun x => f (Function.update x p b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := ok g0 hg0; exact normGate_nok g0 ⟨by simpa using this.1, this.2⟩
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x; rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hout : C.output ≠ p.val := out_ne_input_of_nc f p b gs C.output hevg hnc
  have hread : ∃ g ∈ gs, p.val ∈ g.inputs := by
    by_contra hno; push Not at hno
    obtain ⟨x, hx⟩ := hdep; apply hx; rw [← hevg, ← hevg]
    refine wiresFrom_agree_except gs {p.val} _ _ (by simp) ?_ ?_ C.output (by simp [hout])
    · intro i hi; simp only [Finset.mem_singleton] at hi
      by_cases hlt : i < m
      · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
            List.getElem_ofFn, List.getElem_ofFn]
        have hne : (⟨i, hlt⟩ : Fin m) ≠ p := fun e => hi (congrArg Fin.val e)
        simp [Function.update_of_ne hne]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · intro g hg a ha hmem; simp only [Finset.mem_singleton] at hmem; subst hmem; exact hno g hg ha
  apply mkCirc_from_elim f p b s gs C.output hnok hevg hnc
  have h1 := elim_len_sub_one m p.val gs (initFix m p.val b, []) hnok
    (by simp [initFix]) (by rw [initFix_getD_self]; cases b <;> simp) hread
  have hsz' : C.gates.length ≤ s + 1 := hsz
  have hl : gs.length = C.gates.length := by simp [hgs]
  simp only [List.length_nil, zero_add] at h1; omega

theorem two_gate_elim_at {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) (s : ℕ)
    (hdep : ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc0 : ∃ x y : Fin m → Bool, f (Function.update x p false) ≠ f (Function.update y p false))
    (hnc1 : ∃ x y : Fin m → Bool, f (Function.update x p true) ≠ f (Function.update y p true))
    (h : HasCircuitSize m f (s + 2)) :
    HasCircuitSize m (fun x => f (Function.update x p false)) s ∨
    HasCircuitSize m (fun x => f (Function.update x p true)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := ok g0 hg0; exact normGate_nok g0 ⟨by simpa using this.1, this.2⟩
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x; rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hsz' : C.gates.length ≤ s + 2 := hsz
  have hlen_gs : gs.length ≤ s + 2 := by simpa [hgs] using hsz'
  have hout_ne_p : C.output ≠ p.val := out_ne_input_of_nc f p false gs C.output hevg hnc0
  by_cases h2 : 2 ≤ (gs.filter fun g => decide (p.val ∈ g.inputs)).length
  · left
    apply mkCirc_from_elim f p false s gs C.output hnok hevg hnc0
    have h1 := elim_len_sub_two_multi m p.val gs (initFix m p.val false, []) hnok
      (by simp [initFix]) (by rw [initFix_getD_self]; simp) h2
    simp only [List.length_nil, zero_add] at h1; omega
  · have h1ex : ∃ i : ℕ, ∃ hi : i < gs.length, p.val ∈ (gs[i]'hi).inputs := by
      by_contra hnone; push Not at hnone
      obtain ⟨x, hx⟩ := hdep; apply hx; rw [← hevg, ← hevg]
      refine wiresFrom_agree_except gs {p.val} _ _ (by simp) ?_ ?_ C.output (by simp [hout_ne_p])
      · intro i hi; simp only [Finset.mem_singleton] at hi
        by_cases hlt : i < m
        · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
              List.getElem_ofFn, List.getElem_ofFn]
          have hne : (⟨i, hlt⟩ : Fin m) ≠ p := fun e => hi (congrArg Fin.val e)
          simp [Function.update_of_ne hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro g hg a ha hmem; simp only [Finset.mem_singleton] at hmem; subst hmem
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg; exact hnone idx hidx ha
    obtain ⟨i, hi, hpi⟩ := h1ex
    have huniq : ∀ j (hj : j < gs.length), j ≠ i → p.val ∉ (gs[j]'hj).inputs :=
      fun j hj hji hpj => h2 (exists_two_filter gs j i hj hi hji hpj hpi)
    set g_i := gs[i]'hi
    have hnok_i := hnok g_i (List.getElem_mem hi)
    have hlater : ∃ g' ∈ gs.drop (i + 1), m + i ∈ g'.inputs := by
      by_contra hno_later; push Not at hno_later
      have hout_ne : C.output ≠ m + i := by
        intro hout_eq
        have kill_const : ∀ b : Bool,
            ((g_i.op = GateOp.and ∧ b = false) ∨ (g_i.op = GateOp.or ∧ b = true) ∨ (g_i.op = GateOp.not ∧ b = false)) →
            (∃ x y : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update y p b)) → False := by
          intro b hkb hnc
          set acc0 := elim m (gs.take i) (initFix m p.val b, [])
          have hacc0_len : acc0.1.length = m + i := by
            rw [elim_fst_len, initFix_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
          have hacc0_p : acc0.1.getD p.val 0 = if b then 1 else 0 := by
            rw [elim_getD m p.val (gs.take i) _ (by simp [initFix]), initFix_getD_self]
          have hsplit : gs = gs.take i ++ g_i :: gs.drop (i + 1) := by
            have := List.take_append_drop i gs; rw [List.drop_eq_getElem_cons hi] at this; exact this.symm
          have hstep_c : (elimStep m acc0 g_i).1.getD (m + i) 0 < 2 := by
            simp only [elimStep]; rw [← hacc0_len, getD_snoc_eq]
            refine (simplify_kill_const _ _ _ hnok_i.1.1 (by simpa using hnok_i.1.2)
              (fun h => by simpa using hnok_i.2 h) ?_).2
            rcases hkb with ⟨ho, rfl⟩ | ⟨ho, rfl⟩ | ⟨ho, rfl⟩
            · exact Or.inl ⟨ho, List.mem_map.2 ⟨p.val, hpi, by simpa using hacc0_p⟩⟩
            · exact Or.inr (Or.inl ⟨ho, List.mem_map.2 ⟨p.val, hpi, by simpa using hacc0_p⟩⟩)
            · exact Or.inr (Or.inr ⟨ho, Or.inl (List.mem_map.2 ⟨p.val, hpi, by simpa using hacc0_p⟩)⟩)
          have hfull_c : (elim m gs (initFix m p.val b, [])).1.getD (m + i) 0 < 2 := by
            conv_lhs => rw [hsplit]
            rw [elim_append]
            change (elim m (gs.drop (i + 1)) (elimStep m acc0 g_i)).1.getD (m + i) 0 < 2
            rw [elim_getD m (m + i) (gs.drop (i + 1)) _ (by simp [elimStep, hacc0_len])]
            exact hstep_c
          obtain ⟨x, y, hne⟩ := hnc; apply hne
          have hinv := fun z : Fin m → Bool => inv_elim m (List.ofFn z) (by simp) gs _ _
            (fun g hg => (hnok g hg).1) (inv_initFix p b z)
          have hv1 := ((hinv x).2 C.output).2
          have hv2 := ((hinv y).2 C.output).2
          rw [hevg] at hv1 hv2
          rw [← hv1, ← hv2, hout_eq]
          interval_cases ((elim m gs (initFix m p.val b, [])).1.getD (m + i) 0) <;> rfl
        rcases hnok_i.1.1 with ho | ho | ho
        · exact kill_const false (Or.inl ⟨ho, rfl⟩) hnc0
        · exact kill_const true (Or.inr (Or.inl ⟨ho, rfl⟩)) hnc1
        · exact kill_const false (Or.inr (Or.inr ⟨ho, rfl⟩)) hnc0
      obtain ⟨x, hx⟩ := hdep; apply hx; rw [← hevg, ← hevg]
      have hsplit : gs = gs.take i ++ g_i :: gs.drop (i + 1) := by
        have := List.take_append_drop i gs; rw [List.drop_eq_getElem_cons hi] at this; exact this.symm
      rw [hsplit, wiresFrom_append, wiresFrom_append]
      set x' := Function.update x p (!x p)
      set w1 := wiresFrom (gs.take i) (List.ofFn x')
      set w2 := wiresFrom (gs.take i) (List.ofFn x)
      have hw12_len : w1.length = m + i ∧ w2.length = m + i := by
        simp [w1, w2, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
      have hw12_agree : ∀ k, k ∉ ({p.val} : Finset ℕ) → w1.getD k false = w2.getD k false := by
        refine wiresFrom_agree_except (gs.take i) {p.val} _ _ (by simp) ?_ ?_
        · intro k hk; simp only [Finset.mem_singleton] at hk
          by_cases hlt : k < m
          · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
                List.getElem_ofFn, List.getElem_ofFn]
            have hne : (⟨k, hlt⟩ : Fin m) ≠ p := fun e => hk (congrArg Fin.val e)
            simp [x', Function.update_of_ne hne]
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        · intro g hg a ha hmem; simp only [Finset.mem_singleton] at hmem; subst hmem
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
          have hj_lt : j < i := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] at hj; exact hj
          rw [List.getElem_take] at ha
          exact huniq j (by omega) (by omega) ha
      change (wiresFrom (gs.drop (i + 1)) _).getD C.output false = (wiresFrom (gs.drop (i + 1)) _).getD C.output false
      refine wiresFrom_agree_except (gs.drop (i + 1)) {p.val, m + i} _ _ (by simp [hw12_len.1, hw12_len.2]) ?_ ?_
        C.output (by simp [hout_ne_p, hout_ne])
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
        exact hw12_agree k (by simp [hk.1])
      · intro g hg a ha hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg; rw [List.getElem_drop] at ha
          exact huniq (i + 1 + j) (by simp at hj; omega) (by omega) ha
        · exact hno_later g hg ha
    rcases hnok_i.1.1 with ho | ho | ho
    · left; apply mkCirc_from_elim f p false s gs C.output hnok hevg hnc0
      have h1 := elim_len_sub_two_chain m p.val gs (initFix m p.val false, []) i hnok
        (by simp [initFix]) hi hpi (Or.inl ⟨ho, by rw [initFix_getD_self]; simp⟩) (by simpa [initFix] using hlater)
      simp only [List.length_nil, zero_add] at h1; omega
    · right; apply mkCirc_from_elim f p true s gs C.output hnok hevg hnc1
      have h1 := elim_len_sub_two_chain m p.val gs (initFix m p.val true, []) i hnok
        (by simp [initFix]) hi hpi (Or.inr (Or.inl ⟨ho, by rw [initFix_getD_self]; simp⟩)) (by simpa [initFix] using hlater)
      simp only [List.length_nil, zero_add] at h1; omega
    · left; apply mkCirc_from_elim f p false s gs C.output hnok hevg hnc0
      have h1 := elim_len_sub_two_chain m p.val gs (initFix m p.val false, []) i hnok
        (by simp [initFix]) hi hpi (Or.inr (Or.inr ⟨ho, Or.inl (by rw [initFix_getD_self]; simp)⟩)) (by simpa [initFix] using hlater)
      simp only [List.length_nil, zero_add] at h1; omega

def shiftDown (m w : ℕ) : ℕ := if w < m then w else w - 1

def shiftGate (m : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shiftDown m)⟩

lemma bypass_dead_zero_wires (m : ℕ) (gs : List Gate) :
    ∀ W1 W2 : List Bool, W1.length + 1 = W2.length → m ≤ W1.length →
    (∀ w, w ≠ m → W1.getD (shiftDown m w) false = W2.getD w false) →
    (∀ g ∈ gs, m ∉ g.inputs) →
    ∀ w, w ≠ m → (wiresFrom (gs.map (shiftGate m)) W1).getD (shiftDown m w) false =
      (wiresFrom gs W2).getD w false := by
  induction gs with
  | nil => intro W1 W2 _ _ h _ w hw; exact h w hw
  | cons g gs ih =>
    intro W1 W2 hlen hm hagree hno
    have hmg : m ∉ g.inputs := hno g List.mem_cons_self
    have hv : (shiftGate m g).op.eval ((shiftGate m g).inputs.map fun i => W1.getD i false) =
        g.op.eval (g.inputs.map fun i => W2.getD i false) := by
      simp only [shiftGate, List.map_map]; congr 1; apply List.map_congr_left
      intro a ha; exact hagree a (fun e => hmg (e ▸ ha))
    change ∀ w, w ≠ m → (wiresFrom (gs.map (shiftGate m)) (W1 ++ [_])).getD (shiftDown m w) false =
                        (wiresFrom gs (W2 ++ [_])).getD w false
    rw [hv]
    apply ih _ _ (by simp; omega) (by simp; omega) _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro w hw
    rcases Nat.lt_trichotomy w W2.length with hlt | heq | hgt
    · have hlt1 : shiftDown m w < W1.length := by unfold shiftDown; split <;> omega
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hagree w hw
    · have he1 : shiftDown m w = W1.length := by unfold shiftDown; split <;> omega
      rw [he1, heq, getD_snoc_eq, getD_snoc_eq]
    · have hge1 : W1.length + 1 ≤ shiftDown m w := by unfold shiftDown; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma bypass_dead_zero {m : ℕ} (f : (Fin m → Bool) → Bool) (s : ℕ)
    (g0 : Gate) (rest : List Gate) (out : ℕ) (hok : ∀ g ∈ rest, OkG g) (hlen : rest.length ≤ s)
    (hev : ∀ x : Fin m → Bool, (wiresFrom (g0 :: rest) (List.ofFn x)).getD out false = f x)
    (hout : out ≠ m) (hno : ∀ g ∈ rest, m ∉ g.inputs) :
    HasCircuitSize m f s := by
  refine ⟨⟨rest.map (shiftGate m), shiftDown m out⟩, ?_, by simpa [Circuit.size] using hlen, ?_⟩
  · intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    have := hok g' hg'; exact ⟨by simpa [shiftGate] using this.1, by simpa [shiftGate] using this.2⟩
  · intro x
    show (wiresFrom (rest.map (shiftGate m)) (List.ofFn x)).getD (shiftDown m out) false = f x
    rw [← hev x]
    change _ = (wiresFrom rest (List.ofFn x ++ [_])).getD out false
    apply bypass_dead_zero_wires m rest (List.ofFn x) (List.ofFn x ++ [_]) (by simp) (by simp) _ hno out hout
    intro w hw
    unfold shiftDown
    by_cases hlt : w < m
    · simp only [hlt, ite_true]
      exact (getD_snoc_ne_len _ _ _ _ m (by simp) (by omega)).symm
    · simp only [hlt, ite_false]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma bypass_gate_at {m : ℕ} (f : (Fin m → Bool) → Bool) (s : ℕ)
    (gs : List Gate) (out : ℕ) (hok : ∀ g ∈ gs, OkG g) (hlen : gs.length ≤ s + 1)
    (hev : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD out false = f x)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y)
    (k : ℕ) (hk : k < gs.length) (st : ℕ) (hst_valid : statValid (m + k) st)
    (hst_eq : ∀ x : Fin m → Bool,
      statVal (wiresFrom (gs.take k) (List.ofFn x)) st =
      (wiresFrom (gs.take (k + 1)) (List.ofFn x)).getD (m + k) false) :
    HasCircuitSize m f s := by
  set pre := gs.take k with hpre
  set post := gs.drop (k + 1) with hpost
  have hlpre : pre.length = k := by simp [hpre, Nat.le_of_lt hk]
  have hlpost : post.length = gs.length - (k + 1) := by simp [hpost]
  set init := List.ofFn (fun i : Fin (m + k) => i.val + 2) ++ [st] with hinit
  set acc := elim m post (init, pre) with hacc
  have htake1 : gs.take (k + 1) = pre ++ [gs[k]'hk] := List.take_succ_eq_append_getElem hk
  have hgs_eq : gs = gs.take (k + 1) ++ post := (List.take_append_drop (k + 1) gs).symm
  have hinv_init : ∀ x : Fin m → Bool,
      Inv m (List.ofFn x) (wiresFrom (gs.take (k + 1)) (List.ofFn x)) (init, pre) := by
    intro x
    have l1 : (List.ofFn (fun i : Fin (m + k) => i.val + 2)).length = m + k := by simp
    have lpre : (wiresFrom pre (List.ofFn x)).length = m + k := by rw [length_wiresFrom]; simp [hlpre]
    have ltake : (wiresFrom (gs.take (k + 1)) (List.ofFn x)).length = m + k + 1 := by
      rw [htake1, wiresFrom_append, length_wiresFrom, lpre]; simp
    refine ⟨by simp [hinit, ltake], ?_⟩
    intro i
    by_cases himk : i = m + k
    · subst himk
      simp only [hinit]
      rw [getD_snoc_len _ _ _ _ l1]
      exact ⟨by simpa [hlpre] using hst_valid, hst_eq x⟩
    · simp only [hinit]
      rw [getD_snoc_ne_len _ _ _ _ _ l1 himk]
      by_cases hlt : i < m + k
      · have hget : (List.ofFn (fun j : Fin (m + k) => j.val + 2)).getD i 0 = i + 2 := by
          rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn]
        rw [hget]
        refine ⟨fun _ => by simp [hlpre]; omega, ?_⟩
        rw [htake1, wiresFrom_append]
        exact (getD_wiresFrom [gs[k]'hk] (wiresFrom pre (List.ofFn x)) i (by omega)).symm
      · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by omega)]
        simp [statValid, statVal]
  have hinv : ∀ x : Fin m → Bool, Inv m (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x
    conv_lhs => rw [hgs_eq]
    rw [wiresFrom_append]
    exact inv_elim m _ (by simp) post _ _ (fun g hg => hok g (List.mem_of_mem_drop hg)) (hinv_init x)
  have hval : ∀ x : Fin m → Bool, statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD out 0) = f x := by
    intro x; rw [((hinv x).2 out).2, hev x]
  have hst2 : ¬ acc.1.getD out 0 < 2 := by
    intro hlt; obtain ⟨x, y, hne⟩ := hnc; apply hne
    rw [← hval x, ← hval y]; interval_cases (acc.1.getD out 0) <;> rfl
  have hacc_len : acc.2.length ≤ s := by
    have h1 := elim_len m post (init, pre)
    rw [← hacc] at h1
    change acc.2.length ≤ pre.length + post.length at h1
    rw [hlpre, hlpost] at h1; omega
  refine ⟨⟨acc.2, acc.1.getD out 0 - 2⟩, ?_, hacc_len, ?_⟩
  · intro g hg
    have := elim_ok m post (init, pre) (fun g' hg' => hok g' (List.mem_of_mem_take hg')) g hg
    exact ⟨by simpa using this.1, this.2⟩
  · intro x
    have hv := hval x
    obtain ⟨j, hj⟩ : ∃ j, acc.1.getD out 0 = j + 2 := ⟨acc.1.getD out 0 - 2, by omega⟩
    rw [hj] at hv ⊢; exact hv

theorem three_gate_elim_bottom {m : ℕ} (hm : 2 ≤ m) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hdep : ∀ p : Fin m, ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ (p : Fin m) (b : Bool),
      ∃ x y : Fin m → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (hnoAnd : ∀ (i j : Fin m), i ≠ j →
      ∃ x x' : Fin m → Bool, (∀ k, k ≠ i → k ≠ j → x k = x' k) ∧
        (x i && x j) = (x' i && x' j) ∧ f x ≠ f x')
    (hnoOr : ∀ (i j : Fin m), i ≠ j →
      ∃ x x' : Fin m → Bool, (∀ k, k ≠ i → k ≠ j → x k = x' k) ∧
        (x i || x j) = (x' i || x' j) ∧ f x ≠ f x')
    (h : HasCircuitSize m f (s + 3)) :
    ∃ (p : Fin m) (b : Bool),
      HasCircuitSize m (fun x => f (Function.update x p b)) s := by
  have hnc_f : ∃ x y : Fin m → Bool, f x ≠ f y := by
    obtain ⟨x, hx⟩ := hdep ⟨0, by omega⟩; exact ⟨_, x, hx⟩

  have from_s2 : HasCircuitSize m f (s + 2) →
      ∃ (p : Fin m) (b : Bool), HasCircuitSize m (fun x => f (Function.update x p b)) s := by
    intro hs2
    let p0 : Fin m := ⟨0, by omega⟩
    rcases two_gate_elim_at f p0 s (hdep p0) (hnc p0 false) (hnc p0 true) hs2 with h0 | h1
    · exact ⟨p0, false, h0⟩
    · exact ⟨p0, true, h1⟩
  obtain ⟨C, ok, hsz, hev⟩ := h
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := ok g0 hg0; exact normGate_nok g0 ⟨by simpa using this.1, this.2⟩
  have hok_gs : ∀ g ∈ gs, OkG g := fun g hg => (hnok g hg).1
  have hevg : ∀ x : Fin m → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x; rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hsz' : C.gates.length ≤ s + 3 := hsz
  have hlen_gs : gs.length ≤ s + 3 := by simpa [hgs] using hsz'

  cases hgs_cases : gs with
  | nil =>
    exfalso
    have h01 : ∃ p : Fin m, p.val ≠ C.output := by
      by_cases h0 : C.output = 0
      · exact ⟨⟨1, by omega⟩, by simp [h0]⟩
      · exact ⟨⟨0, by omega⟩, by simpa using Ne.symm h0⟩
    obtain ⟨p, hp⟩ := h01
    obtain ⟨x, hx⟩ := hdep p
    apply hx; rw [← hevg, ← hevg, hgs_cases]
    simp only [wiresFrom, List.foldl_nil]
    by_cases hlt : C.output < m
    · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
          List.getElem_ofFn, List.getElem_ofFn]
      have hne : (⟨C.output, hlt⟩ : Fin m) ≠ p := fun e => hp (congrArg Fin.val e).symm
      simp [Function.update_of_ne hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  | cons g0 rest =>
    rw [hgs_cases] at hnok hok_gs hevg hlen_gs
    have hnok0 : NOk g0 := hnok g0 List.mem_cons_self
    have hnok_rest : ∀ g ∈ rest, NOk g := fun g hg => hnok g (List.mem_cons_of_mem _ hg)
    have hok_rest : ∀ g ∈ rest, OkG g := fun g hg => (hnok_rest g hg).1
    have hlen_rest : rest.length ≤ s + 2 := by simp at hlen_gs; omega

    have bypass0 : ∀ st : ℕ, statValid m st →
        (∀ x : Fin m → Bool, statVal (List.ofFn x) st =
          g0.op.eval (g0.inputs.map fun a => (List.ofFn x).getD a false)) →
        ∃ (p : Fin m) (b : Bool), HasCircuitSize m (fun x => f (Function.update x p b)) s := by
      intro st hsv hseq
      apply from_s2
      apply bypass_gate_at f (s + 2) (g0 :: rest) C.output hok_gs hlen_gs hevg hnc_f 0 (by simp) st
        (by simpa using hsv)
      intro x
      have hval0 : (wiresFrom [g0] (List.ofFn x)).getD m false =
          g0.op.eval (g0.inputs.map fun a => (List.ofFn x).getD a false) := by
        change (List.ofFn x ++ [_]).getD m false = _
        exact getD_snoc_len _ _ _ _ (by simp)
      change statVal (List.ofFn x) st = (wiresFrom [g0] (List.ofFn x)).getD m false
      rw [hval0]
      exact hseq x

    by_cases hdead0 : C.output ≠ m ∧ ∀ g ∈ rest, m ∉ g.inputs
    · exact from_s2 (bypass_dead_zero f (s + 2) g0 rest C.output hok_rest hlen_rest hevg hdead0.1 hdead0.2)

    have finish_pb : ∀ (p : Fin m) (b : Bool),
        (elim m (g0 :: rest) (initFix m p.val b, [])).2.length ≤ s →
        ∃ (p' : Fin m) (b' : Bool), HasCircuitSize m (fun x => f (Function.update x p' b')) s :=
      fun p b hl => ⟨p, b, mkCirc_from_elim f p b s (g0 :: rest) C.output hnok hevg (hnc p b) hl⟩

    rcases hnok0.1.1 with hop0 | hop0 | hop0
    ·
      rcases hins0 : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact bypass0 1 (by simp [statValid]) (fun x => by simp [hop0, hins0, statVal, GateOp.eval])
      · by_cases ha : a < m
        · exact bypass0 (a + 2) (by intro _; omega) (fun x => by simp [hop0, hins0, statVal, GateOp.eval])
        · exact bypass0 0 (by simp [statValid]) (fun x => by
            simp [hop0, hins0, statVal, GateOp.eval, ha])
      · by_cases ha : a < m
        swap
        · exact bypass0 0 (by simp [statValid]) (fun x => by
            simp [hop0, hins0, statVal, GateOp.eval, ha])
        by_cases hb : b < m
        swap
        · exact bypass0 0 (by simp [statValid]) (fun x => by
            simp [hop0, hins0, statVal, GateOp.eval, hb])
        by_cases hab : a = b
        · subst hab
          exact bypass0 (a + 2) (by intro _; omega) (fun x => by
            simp [hop0, hins0, statVal, GateOp.eval])

        let pa : Fin m := ⟨a, ha⟩
        let pb : Fin m := ⟨b, hb⟩
        have hpab : pa ≠ pb := fun e => hab (congrArg Fin.val e)

        have hout_ne_m : C.output ≠ m := by
          intro hout_m
          obtain ⟨x, x', hagree, heq_ab, hne⟩ := hnoAnd pa pb hpab
          apply hne; rw [← hevg, ← hevg, hout_m]
          change (wiresFrom rest (List.ofFn x ++ [_])).getD m false = (wiresFrom rest (List.ofFn x' ++ [_])).getD m false
          rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
          rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
          simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
          rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
              List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
              List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
          exact heq_ab

        have hm_read : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs := by
          by_contra hno; push Not at hno
          exact hdead0 ⟨hout_ne_m, fun g hg => by obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg; exact hno idx hidx⟩

        have step0_kill : ∀ (p : Fin m), p.val ∈ g0.inputs →
            (elimStep m (initFix m p.val false, []) g0).2.length = 0 ∧
            (elimStep m (initFix m p.val false, []) g0).1.length = m + 1 ∧
            (elimStep m (initFix m p.val false, []) g0).1.getD m 0 = 0 ∧
            (elimStep m (initFix m p.val false, []) g0).1.getD p.val 0 = 0 := by
          intro p hp
          have h0mem : 0 ∈ g0.inputs.map (fun i => (initFix m p.val false).getD i 0) :=
            List.mem_map.2 ⟨p.val, hp, by rw [initFix_getD_self]; simp⟩
          have hks := simplify_kill_const g0.op (m + 0) _ hnok0.1.1 (by simpa using hnok0.1.2)
            (fun h => by simpa using hnok0.2 h) (Or.inl ⟨hop0, h0mem⟩)
          have hval0 : (simplify g0.op (m + 0) (g0.inputs.map fun i => (initFix m p.val false).getD i 0)).2 = 0 := by
            rw [hins0] at h0mem
            rw [hop0, hins0]
            simp only [List.map_cons, List.map_nil] at h0mem ⊢
            rcases List.mem_cons.1 h0mem with h1 | h1
            · rw [← h1]; simp [simplify, simpAnd]
            · simp only [List.mem_singleton] at h1; rw [← h1]
              rcases (initFix m p.val false).getD a 0 with _ | _ | _ <;> simp [simplify, simpAnd]
          refine ⟨by simp only [elimStep, List.length_nil, hks.1, Option.toList_none, List.append_nil],
            by simp [elimStep, initFix_len], ?_, ?_⟩
          · simp only [elimStep, List.length_nil]; rw [getD_snoc_len _ _ _ _ (initFix_len _ _ _)]; exact hval0
          · simp only [elimStep]; rw [getD_snoc_ne_len _ _ _ _ _ (initFix_len _ _ _) (by omega), initFix_getD_self]; simp

        have absorb_and : ∀ (c : ℕ) (hc : c < m), (c = a ∨ c = b) →
            ∀ (idx : ℕ) (hidx : idx < rest.length),
            m ∈ (rest[idx]'hidx).inputs → c ∈ (rest[idx]'hidx).inputs →
            HasCircuitSize m f (s + 2) := by
          intro c hc hcab idx hidx hgm hgc
          set g1 := rest[idx]'hidx
          have hnok1 := hnok_rest g1 (List.getElem_mem hidx)
          have hg1_op : g1.op = GateOp.and ∨ g1.op = GateOp.or := by
            rcases hnok1.1.1 with ho | ho | ho
            · exact Or.inl ho
            · exact Or.inr ho
            · exfalso; have hl1 := hnok1.2 ho
              rcases hgi : g1.inputs with _ | ⟨u, _ | ⟨v, l⟩⟩
              · simp [hgi] at hgm
              · simp [hgi] at hgm hgc; omega
              · simp [hgi] at hl1
          have hg1_ins : g1.inputs = [m, c] ∨ g1.inputs = [c, m] := by
            have hl2 := hnok1.1.2
            rcases hgi : g1.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩
            · simp [hgi] at hgm
            · simp [hgi] at hgm hgc; omega
            · simp [hgi] at hgm hgc
              rcases hgm with rfl | rfl <;> rcases hgc with rfl | rfl <;> (try omega)
              · exact Or.inl rfl
              · exact Or.inr rfl
            · simp [hgi] at hl2
          have htake_eq : (g0 :: rest).take (idx + 1 + 1) = (g0 :: rest).take (idx + 1) ++ [g1] := by
            have hlt : idx + 1 < (g0 :: rest).length := by simp; omega
            exact List.take_succ_eq_append_getElem (l := g0 :: rest) hlt
          have hpre_vals : ∀ x : Fin m → Bool,
              (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).length = m + (idx + 1) ∧
              (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD m false = (x pa && x pb) ∧
              (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD c false = x ⟨c, hc⟩ := by
            intro x
            refine ⟨?_, ?_, ?_⟩
            · rw [length_wiresFrom, List.length_ofFn, List.length_take, Nat.min_eq_left (by simp; omega)]
            · have hsplit_tk : (g0 :: rest).take (idx + 1) = [g0] ++ rest.take idx := rfl
              rw [hsplit_tk, wiresFrom_append, getD_wiresFrom _ _ _ (by simp [wiresFrom])]
              change (List.ofFn x ++ [_]).getD m false = _
              rw [getD_snoc_len _ _ _ _ (by simp)]
              simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
              rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
                  List.getElem_ofFn, List.getElem_ofFn]
            · rw [getD_wiresFrom _ _ _ (by simp [hc]), List.getD_eq_getElem _ _ (by simp [hc]), List.getElem_ofFn]
          rcases hg1_op with ho1 | ho1
          · apply bypass_gate_at f (s + 2) (g0 :: rest) C.output hok_gs hlen_gs hevg hnc_f (idx + 1)
              (by simp; omega) (m + 2) (by intro _; omega)
            intro x
            obtain ⟨hlen_tk, hwm, hwc⟩ := hpre_vals x
            rw [htake_eq, wiresFrom_append]
            change (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD m false =
                   (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x) ++ [_]).getD (m + (idx + 1)) false
            rw [getD_snoc_len _ _ _ _ hlen_tk]
            rcases hcab with rfl | rfl <;> rcases hg1_ins with hgi | hgi <;>
              (simp only [ho1, hgi, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, hwm, hwc];
               cases x pa <;> cases x pb <;> rfl)
          · apply bypass_gate_at f (s + 2) (g0 :: rest) C.output hok_gs hlen_gs hevg hnc_f (idx + 1)
              (by simp; omega) (c + 2) (by intro _; omega)
            intro x
            obtain ⟨hlen_tk, hwm, hwc⟩ := hpre_vals x
            rw [htake_eq, wiresFrom_append]
            change (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD c false =
                   (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x) ++ [_]).getD (m + (idx + 1)) false
            rw [getD_snoc_len _ _ _ _ hlen_tk]
            rcases hcab with rfl | rfl <;> rcases hg1_ins with hgi | hgi <;>
              (simp only [ho1, hgi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, hwm, hwc];
               cases x pa <;> cases x pb <;> rfl)

        by_cases hm2 : 2 ≤ (rest.filter fun g => decide (m ∈ g.inputs)).length
        · apply finish_pb pa false
          obtain ⟨hs2, hs1, hsm, _⟩ := step0_kill pa (by simp [hins0, pa])
          change (elim m rest (elimStep m (initFix m pa.val false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_multi m m rest (elimStep m (initFix m pa.val false, []) g0)
            hnok_rest (by omega) (by omega) hm2
          omega

        by_cases habs_a : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs ∧ a ∈ (rest[idx]'hidx).inputs
        · obtain ⟨idx, hidx, hgm, hga⟩ := habs_a
          exact from_s2 (absorb_and a ha (Or.inl rfl) idx hidx hgm hga)
        by_cases habs_b : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs ∧ b ∈ (rest[idx]'hidx).inputs
        · obtain ⟨idx, hidx, hgm, hgb⟩ := habs_b
          exact from_s2 (absorb_and b hb (Or.inr rfl) idx hidx hgm hgb)

        obtain ⟨idxm, hidxm, hgm⟩ := hm_read
        by_cases ha_rest : ∃ idxa : ℕ, ∃ hidxa : idxa < rest.length, a ∈ (rest[idxa]'hidxa).inputs
        · obtain ⟨idxa, hidxa, hga⟩ := ha_rest
          have hne : idxm ≠ idxa := by intro e; subst e; exact habs_a ⟨idxm, hidxm, hgm, hga⟩
          apply finish_pb pa false
          obtain ⟨hs2, hs1, hsm, hsa⟩ := step0_kill pa (by simp [hins0, pa])
          change (elim m rest (elimStep m (initFix m pa.val false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_pair m m pa.val rest (elimStep m (initFix m pa.val false, []) g0)
            hnok_rest (by omega) (by omega) (by omega) (by omega) idxm idxa hidxm hidxa hne hgm hga
          omega
        by_cases hb_rest : ∃ idxb : ℕ, ∃ hidxb : idxb < rest.length, b ∈ (rest[idxb]'hidxb).inputs
        · obtain ⟨idxb, hidxb, hgb⟩ := hb_rest
          have hne : idxm ≠ idxb := by intro e; subst e; exact habs_b ⟨idxm, hidxm, hgm, hgb⟩
          apply finish_pb pb false
          obtain ⟨hs2, hs1, hsm, hsb⟩ := step0_kill pb (by simp [hins0, pb])
          change (elim m rest (elimStep m (initFix m pb.val false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_pair m m pb.val rest (elimStep m (initFix m pb.val false, []) g0)
            hnok_rest (by omega) (by omega) (by omega) (by omega) idxm idxb hidxm hidxb hne hgm hgb
          omega

        exfalso
        push Not at ha_rest hb_rest
        have hout_ne_a : C.output ≠ a := out_ne_input_of_nc f pa false (g0 :: rest) C.output hevg (hnc pa false)
        have hout_ne_b : C.output ≠ b := out_ne_input_of_nc f pb false (g0 :: rest) C.output hevg (hnc pb false)
        obtain ⟨x, x', hagree, heq_ab, hne⟩ := hnoAnd pa pb hpab
        apply hne; rw [← hevg, ← hevg]
        change (wiresFrom rest (List.ofFn x ++ [_])).getD C.output false =
               (wiresFrom rest (List.ofFn x' ++ [_])).getD C.output false
        refine wiresFrom_agree_except rest {a, b} _ _ (by simp) ?_ ?_ C.output (by simp [hout_ne_a, hout_ne_b])
        · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          by_cases hkm : k = m
          · subst hkm
            rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
            simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
            rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
                List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
                List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
            exact heq_ab
          · rw [getD_snoc_ne_len _ _ _ _ _ (by simp) hkm, getD_snoc_ne_len _ _ _ _ _ (by simp) hkm]
            by_cases hlt : k < m
            · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
                  List.getElem_ofFn, List.getElem_ofFn]
              exact hagree ⟨k, hlt⟩ (fun e => hk.1 (congrArg Fin.val e)) (fun e => hk.2 (congrArg Fin.val e))
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        · intro g hg w hw hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
          rcases hmem with rfl | rfl
          · exact ha_rest idx hidx hw
          · exact hb_rest idx hidx hw
      · have := hnok0.1.2; simp [hins0] at this
    ·
      rcases hins0 : g0.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact bypass0 0 (by simp [statValid]) (fun x => by simp [hop0, hins0, statVal, GateOp.eval])
      · by_cases ha : a < m
        · exact bypass0 (a + 2) (by intro _; omega) (fun x => by simp [hop0, hins0, statVal, GateOp.eval])
        · exact bypass0 0 (by simp [statValid]) (fun x => by simp [hop0, hins0, statVal, GateOp.eval, ha])
      · by_cases ha : a < m
        swap
        · by_cases hb : b < m
          · exact bypass0 (b + 2) (by intro _; omega) (fun x => by simp [hop0, hins0, statVal, GateOp.eval, ha])
          · exact bypass0 0 (by simp [statValid]) (fun x => by simp [hop0, hins0, statVal, GateOp.eval, ha, hb])
        by_cases hb : b < m
        swap
        · exact bypass0 (a + 2) (by intro _; omega) (fun x => by simp [hop0, hins0, statVal, GateOp.eval, hb])
        by_cases hab : a = b
        · subst hab
          exact bypass0 (a + 2) (by intro _; omega) (fun x => by simp [hop0, hins0, statVal, GateOp.eval])
        let pa : Fin m := ⟨a, ha⟩
        let pb : Fin m := ⟨b, hb⟩
        have hpab : pa ≠ pb := fun e => hab (congrArg Fin.val e)
        have hout_ne_m : C.output ≠ m := by
          intro hout_m
          obtain ⟨x, x', hagree, heq_ab, hne⟩ := hnoOr pa pb hpab
          apply hne; rw [← hevg, ← hevg, hout_m]
          change (wiresFrom rest (List.ofFn x ++ [_])).getD m false = (wiresFrom rest (List.ofFn x' ++ [_])).getD m false
          rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
          rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
          simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
          rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
              List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
              List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
          exact heq_ab
        have hm_read : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs := by
          by_contra hno; push Not at hno
          exact hdead0 ⟨hout_ne_m, fun g hg => by obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg; exact hno idx hidx⟩
        have step0_kill : ∀ (p : Fin m), p.val ∈ g0.inputs →
            (elimStep m (initFix m p.val true, []) g0).2.length = 0 ∧
            (elimStep m (initFix m p.val true, []) g0).1.length = m + 1 ∧
            (elimStep m (initFix m p.val true, []) g0).1.getD m 0 = 1 ∧
            (elimStep m (initFix m p.val true, []) g0).1.getD p.val 0 = 1 := by
          intro p hp
          have h1mem : 1 ∈ g0.inputs.map (fun i => (initFix m p.val true).getD i 0) :=
            List.mem_map.2 ⟨p.val, hp, by rw [initFix_getD_self]; simp⟩
          have hks := simplify_kill_const g0.op (m + 0) _ hnok0.1.1 (by simpa using hnok0.1.2)
            (fun h => by simpa using hnok0.2 h) (Or.inr (Or.inl ⟨hop0, h1mem⟩))
          have hval1 : (simplify g0.op (m + 0) (g0.inputs.map fun i => (initFix m p.val true).getD i 0)).2 = 1 := by
            rw [hins0] at h1mem
            rw [hop0, hins0]
            simp only [List.map_cons, List.map_nil] at h1mem ⊢
            rcases List.mem_cons.1 h1mem with h1 | h1
            · rw [← h1]; simp [simplify, simpOr]
            · simp only [List.mem_singleton] at h1; rw [← h1]
              rcases (initFix m p.val true).getD a 0 with _ | _ | _ <;> simp [simplify, simpOr]
          refine ⟨by simp only [elimStep, List.length_nil, hks.1, Option.toList_none, List.append_nil],
            by simp [elimStep, initFix_len], ?_, ?_⟩
          · simp only [elimStep, List.length_nil]; rw [getD_snoc_len _ _ _ _ (initFix_len _ _ _)]; exact hval1
          · simp only [elimStep]; rw [getD_snoc_ne_len _ _ _ _ _ (initFix_len _ _ _) (by omega), initFix_getD_self]; simp
        have absorb_or : ∀ (c : ℕ) (hc : c < m), (c = a ∨ c = b) →
            ∀ (idx : ℕ) (hidx : idx < rest.length),
            m ∈ (rest[idx]'hidx).inputs → c ∈ (rest[idx]'hidx).inputs →
            HasCircuitSize m f (s + 2) := by
          intro c hc hcab idx hidx hgm hgc
          set g1 := rest[idx]'hidx
          have hnok1 := hnok_rest g1 (List.getElem_mem hidx)
          have hg1_op : g1.op = GateOp.and ∨ g1.op = GateOp.or := by
            rcases hnok1.1.1 with ho | ho | ho
            · exact Or.inl ho
            · exact Or.inr ho
            · exfalso; have hl1 := hnok1.2 ho
              rcases hgi : g1.inputs with _ | ⟨u, _ | ⟨v, l⟩⟩
              · simp [hgi] at hgm
              · simp [hgi] at hgm hgc; omega
              · simp [hgi] at hl1
          have hg1_ins : g1.inputs = [m, c] ∨ g1.inputs = [c, m] := by
            have hl2 := hnok1.1.2
            rcases hgi : g1.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩
            · simp [hgi] at hgm
            · simp [hgi] at hgm hgc; omega
            · simp [hgi] at hgm hgc
              rcases hgm with rfl | rfl <;> rcases hgc with rfl | rfl <;> (try omega)
              · exact Or.inl rfl
              · exact Or.inr rfl
            · simp [hgi] at hl2
          have htake_eq : (g0 :: rest).take (idx + 1 + 1) = (g0 :: rest).take (idx + 1) ++ [g1] := by
            have hlt : idx + 1 < (g0 :: rest).length := by simp; omega
            exact List.take_succ_eq_append_getElem (l := g0 :: rest) hlt
          have hpre_vals : ∀ x : Fin m → Bool,
              (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).length = m + (idx + 1) ∧
              (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD m false = (x pa || x pb) ∧
              (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD c false = x ⟨c, hc⟩ := by
            intro x
            refine ⟨?_, ?_, ?_⟩
            · rw [length_wiresFrom, List.length_ofFn, List.length_take, Nat.min_eq_left (by simp; omega)]
            · have hsplit_tk : (g0 :: rest).take (idx + 1) = [g0] ++ rest.take idx := rfl
              rw [hsplit_tk, wiresFrom_append, getD_wiresFrom _ _ _ (by simp [wiresFrom])]
              change (List.ofFn x ++ [_]).getD m false = _
              rw [getD_snoc_len _ _ _ _ (by simp)]
              simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
              rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
                  List.getElem_ofFn, List.getElem_ofFn]
            · rw [getD_wiresFrom _ _ _ (by simp [hc]), List.getD_eq_getElem _ _ (by simp [hc]), List.getElem_ofFn]
          rcases hg1_op with ho1 | ho1
          · apply bypass_gate_at f (s + 2) (g0 :: rest) C.output hok_gs hlen_gs hevg hnc_f (idx + 1)
              (by simp; omega) (c + 2) (by intro _; omega)
            intro x
            obtain ⟨hlen_tk, hwm, hwc⟩ := hpre_vals x
            rw [htake_eq, wiresFrom_append]
            change (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD c false =
                   (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x) ++ [_]).getD (m + (idx + 1)) false
            rw [getD_snoc_len _ _ _ _ hlen_tk]
            rcases hcab with rfl | rfl <;> rcases hg1_ins with hgi | hgi <;>
              (simp only [ho1, hgi, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, hwm, hwc];
               cases x pa <;> cases x pb <;> rfl)
          · apply bypass_gate_at f (s + 2) (g0 :: rest) C.output hok_gs hlen_gs hevg hnc_f (idx + 1)
              (by simp; omega) (m + 2) (by intro _; omega)
            intro x
            obtain ⟨hlen_tk, hwm, hwc⟩ := hpre_vals x
            rw [htake_eq, wiresFrom_append]
            change (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x)).getD m false =
                   (wiresFrom ((g0 :: rest).take (idx + 1)) (List.ofFn x) ++ [_]).getD (m + (idx + 1)) false
            rw [getD_snoc_len _ _ _ _ hlen_tk]
            rcases hcab with rfl | rfl <;> rcases hg1_ins with hgi | hgi <;>
              (simp only [ho1, hgi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, hwm, hwc];
               cases x pa <;> cases x pb <;> rfl)
        by_cases hm2 : 2 ≤ (rest.filter fun g => decide (m ∈ g.inputs)).length
        · apply finish_pb pa true
          obtain ⟨hs2, hs1, hsm, _⟩ := step0_kill pa (by simp [hins0, pa])
          change (elim m rest (elimStep m (initFix m pa.val true, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_multi m m rest (elimStep m (initFix m pa.val true, []) g0)
            hnok_rest (by omega) (by omega) hm2
          omega
        by_cases habs_a : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs ∧ a ∈ (rest[idx]'hidx).inputs
        · obtain ⟨idx, hidx, hgm, hga⟩ := habs_a
          exact from_s2 (absorb_or a ha (Or.inl rfl) idx hidx hgm hga)
        by_cases habs_b : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs ∧ b ∈ (rest[idx]'hidx).inputs
        · obtain ⟨idx, hidx, hgm, hgb⟩ := habs_b
          exact from_s2 (absorb_or b hb (Or.inr rfl) idx hidx hgm hgb)
        obtain ⟨idxm, hidxm, hgm⟩ := hm_read
        by_cases ha_rest : ∃ idxa : ℕ, ∃ hidxa : idxa < rest.length, a ∈ (rest[idxa]'hidxa).inputs
        · obtain ⟨idxa, hidxa, hga⟩ := ha_rest
          have hne : idxm ≠ idxa := by intro e; subst e; exact habs_a ⟨idxm, hidxm, hgm, hga⟩
          apply finish_pb pa true
          obtain ⟨hs2, hs1, hsm, hsa⟩ := step0_kill pa (by simp [hins0, pa])
          change (elim m rest (elimStep m (initFix m pa.val true, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_pair m m pa.val rest (elimStep m (initFix m pa.val true, []) g0)
            hnok_rest (by omega) (by omega) (by omega) (by omega) idxm idxa hidxm hidxa hne hgm hga
          omega
        by_cases hb_rest : ∃ idxb : ℕ, ∃ hidxb : idxb < rest.length, b ∈ (rest[idxb]'hidxb).inputs
        · obtain ⟨idxb, hidxb, hgb⟩ := hb_rest
          have hne : idxm ≠ idxb := by intro e; subst e; exact habs_b ⟨idxm, hidxm, hgm, hgb⟩
          apply finish_pb pb true
          obtain ⟨hs2, hs1, hsm, hsb⟩ := step0_kill pb (by simp [hins0, pb])
          change (elim m rest (elimStep m (initFix m pb.val true, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_pair m m pb.val rest (elimStep m (initFix m pb.val true, []) g0)
            hnok_rest (by omega) (by omega) (by omega) (by omega) idxm idxb hidxm hidxb hne hgm hgb
          omega
        exfalso
        push Not at ha_rest hb_rest
        have hout_ne_a : C.output ≠ a := out_ne_input_of_nc f pa false (g0 :: rest) C.output hevg (hnc pa false)
        have hout_ne_b : C.output ≠ b := out_ne_input_of_nc f pb false (g0 :: rest) C.output hevg (hnc pb false)
        obtain ⟨x, x', hagree, heq_ab, hne⟩ := hnoOr pa pb hpab
        apply hne; rw [← hevg, ← hevg]
        change (wiresFrom rest (List.ofFn x ++ [_])).getD C.output false =
               (wiresFrom rest (List.ofFn x' ++ [_])).getD C.output false
        refine wiresFrom_agree_except rest {a, b} _ _ (by simp) ?_ ?_ C.output (by simp [hout_ne_a, hout_ne_b])
        · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          by_cases hkm : k = m
          · subst hkm
            rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
            simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
            rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
                List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [hb]),
                List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
            exact heq_ab
          · rw [getD_snoc_ne_len _ _ _ _ _ (by simp) hkm, getD_snoc_ne_len _ _ _ _ _ (by simp) hkm]
            by_cases hlt : k < m
            · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
                  List.getElem_ofFn, List.getElem_ofFn]
              exact hagree ⟨k, hlt⟩ (fun e => hk.1 (congrArg Fin.val e)) (fun e => hk.2 (congrArg Fin.val e))
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        · intro g hg w hw hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg
          rcases hmem with rfl | rfl
          · exact ha_rest idx hidx hw
          · exact hb_rest idx hidx hw
      · have := hnok0.1.2; simp [hins0] at this
    ·
      have hnot_len := hnok0.2 hop0
      rcases hins0 : g0.inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
      · exact bypass0 1 (by simp [statValid]) (fun x => by simp [hop0, hins0, statVal, GateOp.eval])
      · by_cases ha : a < m
        swap
        · exact bypass0 1 (by simp [statValid]) (fun x => by simp [hop0, hins0, statVal, GateOp.eval, ha])
        let pa : Fin m := ⟨a, ha⟩

        have hout_ne_m : C.output ≠ m := by
          intro hout_m
          obtain ⟨x, y, hne⟩ := hnc pa false; apply hne
          rw [← hevg, ← hevg, hout_m]
          change (wiresFrom rest (List.ofFn (Function.update x pa false) ++ [_])).getD m false =
                 (wiresFrom rest (List.ofFn (Function.update y pa false) ++ [_])).getD m false
          rw [getD_wiresFrom _ _ _ (by simp), getD_wiresFrom _ _ _ (by simp)]
          rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
          simp only [hop0, hins0, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
          rw [List.getD_eq_getElem _ _ (by simp [ha]), List.getD_eq_getElem _ _ (by simp [ha]),
              List.getElem_ofFn, List.getElem_ofFn]
          simp [pa]
        have hm_read : ∃ idx : ℕ, ∃ hidx : idx < rest.length, m ∈ (rest[idx]'hidx).inputs := by
          by_contra hno; push Not at hno
          exact hdead0 ⟨hout_ne_m, fun g hg => by obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hg; exact hno idx hidx⟩

        have step0_not : ∀ b : Bool,
            (elimStep m (initFix m a b, []) g0).2.length = 0 ∧
            (elimStep m (initFix m a b, []) g0).1.length = m + 1 ∧
            (elimStep m (initFix m a b, []) g0).1.getD m 0 = (if b then 0 else 1) ∧
            (elimStep m (initFix m a b, []) g0).1.getD a 0 = (if b then 1 else 0) := by
          intro b
          have hva : (initFix m a b).getD a 0 = if b then 1 else 0 := initFix_getD_self pa b
          have hr : simplify g0.op (m + 0) (g0.inputs.map fun i => (initFix m a b).getD i 0) =
              (none, if b then 0 else 1) := by
            rw [hop0, hins0]; simp only [List.map_cons, List.map_nil, hva]
            cases b <;> simp [simplify, simpNot]
          refine ⟨by simp only [elimStep, List.length_nil, hr, Option.toList_none, List.append_nil],
            by simp [elimStep, initFix_len], ?_, ?_⟩
          · simp only [elimStep, List.length_nil]; rw [getD_snoc_len _ _ _ _ (initFix_len _ _ _), hr]
          · simp only [elimStep]; rw [getD_snoc_ne_len _ _ _ _ _ (initFix_len _ _ _) (by omega), hva]

        by_cases hm2 : 2 ≤ (rest.filter fun g => decide (m ∈ g.inputs)).length
        · apply finish_pb pa false
          obtain ⟨hs2, hs1, hsm, _⟩ := step0_not false
          change (elim m rest (elimStep m (initFix m a false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_multi m m rest (elimStep m (initFix m a false, []) g0)
            hnok_rest (by omega) (by rw [hsm]; decide) hm2
          omega
        obtain ⟨idx1, hidx1, hgm1⟩ := hm_read

        have huniq_m : ∀ j (hj : j < rest.length), j ≠ idx1 → m ∉ (rest[j]'hj).inputs :=
          fun j hj hji hjm => hm2 (exists_two_filter rest j idx1 hj hidx1 hji hjm hgm1)

        by_cases ha_other : ∃ idxa : ℕ, ∃ hidxa : idxa < rest.length, idxa ≠ idx1 ∧ a ∈ (rest[idxa]'hidxa).inputs
        · obtain ⟨idxa, hidxa, hne, hga⟩ := ha_other
          apply finish_pb pa false
          obtain ⟨hs2, hs1, hsm, hsa⟩ := step0_not false
          change (elim m rest (elimStep m (initFix m a false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_pair m m a rest (elimStep m (initFix m a false, []) g0)
            hnok_rest (by omega) (by omega)
            (by rw [hsm]; decide) (by rw [hsa]; decide) idx1 idxa hidx1 hidxa hne.symm hgm1 hga
          omega

        push Not at ha_other
        set g1 := rest[idx1]'hidx1
        have hnok1 := hnok_rest g1 (List.getElem_mem hidx1)
        have hout_ne_a : C.output ≠ a := out_ne_input_of_nc f pa false (g0 :: rest) C.output hevg (hnc pa false)

        have hlater : ∃ g' ∈ rest.drop (idx1 + 1), m + 1 + idx1 ∈ g'.inputs := by
          by_contra hno_later; push Not at hno_later
          have hout_ne_w1 : C.output ≠ m + 1 + idx1 := by
            intro hout_eq
            have kill_w1 : ∀ b : Bool,
                ((g1.op = GateOp.and ∧ b = true) ∨ (g1.op = GateOp.or ∧ b = false) ∨ (g1.op = GateOp.not ∧ b = false)) →
                False := by
              intro b hkb
              obtain ⟨_, hs1, hsm, _⟩ := step0_not b
              set acc0 := elim m (rest.take idx1) (elimStep m (initFix m a b, []) g0)
              have hacc0_len : acc0.1.length = m + 1 + idx1 := by
                rw [elim_fst_len, hs1, List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx1)]
              have hacc0_m : acc0.1.getD m 0 = if b then 0 else 1 := by
                rw [elim_getD m m (rest.take idx1) _ (by omega), hsm]
              have hsplit_r : rest = rest.take idx1 ++ g1 :: rest.drop (idx1 + 1) := by
                have := List.take_append_drop idx1 rest; rw [List.drop_eq_getElem_cons hidx1] at this; exact this.symm
              have hstep_c : (elimStep m acc0 g1).1.getD (m + 1 + idx1) 0 < 2 := by
                simp only [elimStep]; rw [← hacc0_len, getD_snoc_eq]
                refine (simplify_kill_const _ _ _ hnok1.1.1 (by simpa using hnok1.1.2)
                  (fun h => by simpa using hnok1.2 h) ?_).2
                rcases hkb with ⟨ho, rfl⟩ | ⟨ho, rfl⟩ | ⟨ho, rfl⟩
                · exact Or.inl ⟨ho, List.mem_map.2 ⟨m, hgm1, by simpa using hacc0_m⟩⟩
                · exact Or.inr (Or.inl ⟨ho, List.mem_map.2 ⟨m, hgm1, by simpa using hacc0_m⟩⟩)
                · exact Or.inr (Or.inr ⟨ho, Or.inr (List.mem_map.2 ⟨m, hgm1, by simpa using hacc0_m⟩)⟩)
              have hfull_c : (elim m (g0 :: rest) (initFix m a b, [])).1.getD (m + 1 + idx1) 0 < 2 := by
                change (elim m rest (elimStep m (initFix m a b, []) g0)).1.getD (m + 1 + idx1) 0 < 2
                conv_lhs => rw [hsplit_r]
                rw [elim_append]
                change (elim m (rest.drop (idx1 + 1)) (elimStep m acc0 g1)).1.getD (m + 1 + idx1) 0 < 2
                rw [elim_getD m (m + 1 + idx1) (rest.drop (idx1 + 1)) _ (by simp [elimStep, hacc0_len])]
                exact hstep_c
              obtain ⟨x, y, hne⟩ := hnc pa b; apply hne
              have hinv := fun z : Fin m → Bool => inv_elim m (List.ofFn z) (by simp) (g0 :: rest) _ _
                hok_gs (inv_initFix pa b z)
              have hv1 := ((hinv x).2 C.output).2
              have hv2 := ((hinv y).2 C.output).2
              rw [hevg] at hv1 hv2
              rw [← hv1, ← hv2, hout_eq]
              interval_cases ((elim m (g0 :: rest) (initFix m a b, [])).1.getD (m + 1 + idx1) 0) <;> rfl
            rcases hnok1.1.1 with ho | ho | ho
            · exact kill_w1 true (Or.inl ⟨ho, rfl⟩)
            · exact kill_w1 false (Or.inr (Or.inl ⟨ho, rfl⟩))
            · exact kill_w1 false (Or.inr (Or.inr ⟨ho, rfl⟩))

          obtain ⟨x, hx⟩ := hdep pa; apply hx; rw [← hevg, ← hevg]
          have hsplit_r : rest = rest.take idx1 ++ g1 :: rest.drop (idx1 + 1) := by
            have := List.take_append_drop idx1 rest; rw [List.drop_eq_getElem_cons hidx1] at this; exact this.symm
          set x' := Function.update x pa (!x pa)
          change (wiresFrom rest (List.ofFn x' ++ [_])).getD C.output false =
                 (wiresFrom rest (List.ofFn x ++ [_])).getD C.output false
          rw [hsplit_r, wiresFrom_append, wiresFrom_append]
          set w1 := wiresFrom (rest.take idx1) (List.ofFn x' ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x').getD i false)])
          set w2 := wiresFrom (rest.take idx1) (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)])
          have hw12_len : w1.length = m + 1 + idx1 ∧ w2.length = m + 1 + idx1 := by
            simp [w1, w2, length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx1)]
          have hw12_agree : ∀ k, k ∉ ({a, m} : Finset ℕ) → w1.getD k false = w2.getD k false := by
            refine wiresFrom_agree_except (rest.take idx1) {a, m} _ _ (by simp) ?_ ?_
            · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
              rw [getD_snoc_ne_len _ _ _ _ _ (by simp) hk.2, getD_snoc_ne_len _ _ _ _ _ (by simp) hk.2]
              by_cases hlt : k < m
              · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
                    List.getElem_ofFn, List.getElem_ofFn]
                have hne : (⟨k, hlt⟩ : Fin m) ≠ pa := fun e => hk.1 (congrArg Fin.val e)
                simp [x', Function.update_of_ne hne]
              · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
            · intro g hg w hw hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
              have hj_lt : j < idx1 := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx1)] at hj; exact hj
              rw [List.getElem_take] at hw
              rcases hmem with rfl | rfl
              · exact ha_other j (by omega) (by omega) hw
              · exact huniq_m j (by omega) (by omega) hw
          change (wiresFrom (rest.drop (idx1 + 1)) _).getD C.output false =
                 (wiresFrom (rest.drop (idx1 + 1)) _).getD C.output false
          refine wiresFrom_agree_except (rest.drop (idx1 + 1)) {a, m, m + 1 + idx1} _ _
            (by simp [hw12_len.1, hw12_len.2]) ?_ ?_ C.output (by simp [hout_ne_a, hout_ne_m, hout_ne_w1])
          · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hw12_agree k (by simp [hk.1, hk.2.1])
          · intro g hg w hw hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl | rfl
            · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg; rw [List.getElem_drop] at hw
              exact ha_other (idx1 + 1 + j) (by simp at hj; omega) (by omega) hw
            · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg; rw [List.getElem_drop] at hw
              exact huniq_m (idx1 + 1 + j) (by simp at hj; omega) (by omega) hw
            · exact hno_later g hg hw

        rcases hnok1.1.1 with ho | ho | ho
        · apply finish_pb pa true
          obtain ⟨hs2, hs1, hsm, _⟩ := step0_not true
          change (elim m rest (elimStep m (initFix m a true, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_chain m m rest (elimStep m (initFix m a true, []) g0) idx1
            hnok_rest (by omega) hidx1 hgm1
            (Or.inl ⟨ho, by simpa using hsm⟩) (by simpa [hs1] using hlater)
          omega
        · apply finish_pb pa false
          obtain ⟨hs2, hs1, hsm, _⟩ := step0_not false
          change (elim m rest (elimStep m (initFix m a false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_chain m m rest (elimStep m (initFix m a false, []) g0) idx1
            hnok_rest (by omega) hidx1 hgm1
            (Or.inr (Or.inl ⟨ho, by simpa using hsm⟩)) (by simpa [hs1] using hlater)
          omega
        · apply finish_pb pa false
          obtain ⟨hs2, hs1, hsm, _⟩ := step0_not false
          change (elim m rest (elimStep m (initFix m a false, []) g0)).2.length ≤ s
          have h1 := elim_len_sub_two_chain m m rest (elimStep m (initFix m a false, []) g0) idx1
            hnok_rest (by omega) hidx1 hgm1
            (Or.inr (Or.inr ⟨ho, Or.inr (by simpa using hsm)⟩)) (by simpa [hs1] using hlater)
          omega
      · simp [hins0] at hnot_len

theorem size_zero_no_two_dep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (p q : Fin m) (hpq : p ≠ q)
    (hp : ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hq : ∃ x : Fin m → Bool, f (Function.update x q (!x q)) ≠ f x) :
    ¬ HasCircuitSize m f 0 := by
  rintro ⟨C, _, hsz, hev⟩
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hsz)
  have h0 : ∀ x : Fin m → Bool, (List.ofFn x).getD C.output false = f x := fun x => by
    have := hev x
    simpa [Circuit.eval, Circuit.wires, hnil] using this
  have hkill : ∀ r : Fin m, r.val ≠ C.output →
      ∀ x : Fin m → Bool, f (Function.update x r (!x r)) = f x := by
    intro r hr x
    rw [← h0, ← h0]
    by_cases hlt : C.output < m
    · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
          List.getElem_ofFn, List.getElem_ofFn]
      have hne : (⟨C.output, hlt⟩ : Fin m) ≠ r := fun e => hr (congrArg Fin.val e).symm
      simp [Function.update_of_ne hne]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  by_cases hpo : p.val = C.output
  · obtain ⟨x, hx⟩ := hq
    exact hx (hkill q (fun hqo => hpq (Fin.ext (hpo.trans hqo.symm))) x)
  · obtain ⟨x, hx⟩ := hp
    exact hx (hkill p hpo x)

theorem hasCircuitSize_le {m : ℕ} {f : (Fin m → Bool) → Bool} {s₁ s₂ : ℕ} (hle : s₁ ≤ s₂)
    (h : HasCircuitSize m f s₁) : HasCircuitSize m f s₂ := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  exact ⟨C, ok, hsz.trans hle, hev⟩

theorem k3_lb_4 :
    ¬ HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)) 3 := by
  intro h
  obtain ⟨p, b, h0⟩ := three_gate_elim_bottom (by omega : 2 ≤ 3) _ 0
    (by decide) (by decide) (by decide) (by decide) h
  fin_cases p <;> cases b
  · exact size_zero_no_two_dep _ 1 2 (by decide) (by decide) (by decide) h0
  · exact size_zero_no_two_dep _ 1 2 (by decide) (by decide) (by decide) h0
  · exact size_zero_no_two_dep _ 0 2 (by decide) (by decide) (by decide) h0
  · exact size_zero_no_two_dep _ 0 2 (by decide) (by decide) (by decide) h0
  · exact size_zero_no_two_dep _ 0 1 (by decide) (by decide) (by decide) h0
  · exact size_zero_no_two_dep _ 0 1 (by decide) (by decide) (by decide) h0

def targetF (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3937069192 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem targetF_lb_8 : ¬ HasCircuitSize 6 targetF 7 := by
  intro h
  have h1 : HasCircuitSize 6 (fun x => targetF (Function.update x 4 false)) 6 :=
    one_gate_at targetF 4 false 6
      ⟨fun i : Fin 6 => i == 0, by decide⟩
      ⟨fun _ : Fin 6 => false, fun i : Fin 6 => i == 0 || i == 1 || i == 2, by decide⟩ h
  have h2 := two_gate_elim_at (fun x => targetF (Function.update x 4 false)) 5 4
    ⟨fun i : Fin 6 => i == 0 || i == 1, by decide⟩
    ⟨fun _ : Fin 6 => false, fun i : Fin 6 => i == 0 || i == 1 || i == 2, by decide⟩
    ⟨fun _ : Fin 6 => false, fun i : Fin 6 => i == 0 || i == 1, by decide⟩ h1
  let g : (Fin 3 → Bool) → Bool := fun y => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)
  let π : Fin 6 → Fin 3 := fun i =>
    match i.val with
    | 0 => 0
    | 1 => 1
    | 3 => 2
    | _ => 0
  rcases h2 with h2f | h2t
  · have h3 : HasCircuitSize 6 (fun x => targetF (Function.update (Function.update (Function.update x 2 true) 5 false) 4 false)) 3 :=
      one_gate_at (fun x => targetF (Function.update (Function.update x 5 false) 4 false)) 2 true 3
        ⟨fun i : Fin 6 => i == 0 || i == 1, by decide⟩
        ⟨fun _ : Fin 6 => false, fun i : Fin 6 => i == 0 || i == 1, by decide⟩ h2f
    have hr := relabel_size π _ 3 h3
    have heq : (fun y : Fin 3 → Bool => targetF (Function.update (Function.update (Function.update (y ∘ π) 2 true) 5 false) 4 false)) = g := by
      funext y
      revert y
      decide
    rw [heq] at hr
    exact k3_lb_4 hr
  · have h3 : HasCircuitSize 6 (fun x => targetF (Function.update (Function.update (Function.update x 2 true) 5 true) 4 false)) 3 :=
      one_gate_at (fun x => targetF (Function.update (Function.update x 5 true) 4 false)) 2 true 3
        ⟨fun i : Fin 6 => i == 0 || i == 3, by decide⟩
        ⟨fun _ : Fin 6 => false, fun i : Fin 6 => i == 0 || i == 1, by decide⟩ h2t
    have hr := relabel_size π _ 3 h3
    have heq : (fun y : Fin 3 → Bool => targetF (Function.update (Function.update (Function.update (y ∘ π) 2 true) 5 true) 4 false)) = g := by
      funext y
      revert y
      decide
    rw [heq] at hr
    exact k3_lb_4 hr

def witGates : List Gate :=
  [ { op := GateOp.and, inputs := [3, 2] }
  , { op := GateOp.or,  inputs := [5, 2] }
  , { op := GateOp.and, inputs := [7, 1] }
  , { op := GateOp.or,  inputs := [4, 8] }
  , { op := GateOp.and, inputs := [0, 9] }
  , { op := GateOp.or,  inputs := [0, 1] }
  , { op := GateOp.or,  inputs := [10, 6] }
  , { op := GateOp.and, inputs := [11, 12] } ]

def witCirc : Circuit := ⟨witGates, 13⟩

lemma witCirc_mono : Monotone2 witCirc := by
  intro g hg
  simp only [witCirc, witGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

lemma witCirc_eval : ∀ x : Fin 6 → Bool, witCirc.eval (List.ofFn x) = targetF x := by
  decide +kernel

lemma main_proof (s : ℕ) (h : HasCircuitSize 6 targetF s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetF x := by
  have hge : 8 ≤ s := by
    by_contra hlt
    exact targetF_lb_8 (hasCircuitSize_le (by omega) h)
  exact ⟨witCirc, witCirc_mono, hge, witCirc_eval⟩

end PEqualNP.Outside.L_meta_13341

theorem PEqualNP.Outside.L_meta_13341 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069192 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069192 * 2 ^ 32 + 3937067136) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_13341.main_proof
