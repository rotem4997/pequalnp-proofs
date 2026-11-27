import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10980

open PEqualNP.MetaComplexity

-- C10980.Helpers.Shannon
namespace C10980.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

end C10980.Helpers

-- C10980.Helpers.Support
namespace C10980.Helpers

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
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

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end C10980.Helpers

-- C10980.Helpers.Elim
namespace C10980.Helpers

open PEqualNP.CircuitLowerBounds

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

end C10980.Helpers

-- C10980.Helpers.Parity
namespace C10980.Helpers

open PEqualNP.CircuitLowerBounds

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

end C10980.Helpers

-- C10980.Helpers.Parity3
namespace C10980.Helpers

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)

theorem statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]

theorem statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]

theorem statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]

theorem inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)

theorem stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]

theorem elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)

theorem const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'

theorem elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega

theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c

end C10980.Helpers

-- C10980.Helpers.Parity4
namespace C10980.Helpers

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]

abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y

def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2

def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c

theorem inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)

theorem st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm

theorem st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm

theorem st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]

theorem simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩

theorem st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩

theorem const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h

section

variable {n : ℕ} {gs : List Gate} {o : ℕ}

end

end C10980.Helpers

-- C10980.Helpers.PermInputs
namespace C10980.Helpers.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end C10980.Helpers.PermInputs

-- C10980.Helpers.Readers
namespace C10980.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.PermInputs

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x

def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ HasCircuitSize m (fun x => f (Function.update x y b)) s'

structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩

theorem has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

theorem vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl

theorem exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega

theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩

theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end

theorem upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm

theorem restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _

theorem save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  C10980.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS

theorem Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this

theorem Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this

theorem rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩

theorem rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩

theorem Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩

end

end C10980.Helpers.Readers

-- C10980.Helpers.ReadersPat
namespace C10980.Helpers.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers

theorem gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _

section

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

end

section

variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)

end

end C10980.Helpers.Readers

-- C10980.Helpers.EdgeFnPlan
namespace C10980.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers

def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1

def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩

def TailOK (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧ ∀ x : Fin N → Bool, vl gs x (N + j) = true → F x = true))

def TailGE (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK N F gs j

def StmtLift : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p l h : ℕ) (g : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) →
    gs[p]? = some g → g.op = GateOp.or → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    (∀ x : Fin N → Bool, vl gs x h = true → F x = true) →
    Least N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (N + (gs.length - 1)) ∧
    (¬ TailOK N F gs p → ∀ t, TailGE N F gs t →
      TailGE N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (t + 1))

end C10980.EdgeFn

-- C10980.Helpers.EdgeFnModel
namespace C10980.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers

theorem rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega

theorem rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

theorem rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

theorem vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]

theorem rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]

theorem rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]

theorem rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega

theorem rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩

theorem rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)

theorem rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]

theorem TailGE.zero (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) : TailGE N F gs 0 :=
  ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega)⟩

theorem TailGE.le {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t : ℕ}
    (h : TailGE N F gs t) : t ≤ gs.length := h.1

theorem TailGE.lt_of_not {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE N F gs t) (hp : p < gs.length) (hn : ¬ TailOK N F gs p) : p + t < gs.length := by
  by_contra hc
  exact hn (h.2 p (by omega) hp)

theorem tailGE_rdel_app (N : ℕ) (F : (Fin N → Bool) → Bool) (gs new : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE N F gs t) (hpt : p + t < gs.length)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a) (hF : ∀ x, ¬ S x → F x = true)
    (hnew : ∀ i, i < new.length → TailOK N F (rdel N p a gs ++ new) (gs.length - 1 + i)) :
    TailGE N F (rdel N p a gs ++ new) (t + new.length) := by
  have hlen := rdel_length N p a gs hp
  have hl' : (rdel N p a gs ++ new).length = gs.length - 1 + new.length := by
    simp; omega
  refine ⟨by rw [hl']; omega, ?_⟩
  intro j h1 h2
  rw [hl'] at h1 h2
  by_cases hj : gs.length - 1 ≤ j
  · have := hnew (j - (gs.length - 1)) (by omega)
    rwa [show gs.length - 1 + (j - (gs.length - 1)) = j by omega] at this
  · have hok := ht.2 (j + 1) (by omega) (by omega)
    obtain ⟨g, hg, hop⟩ := hok
    have hj' : (rdel N p a gs ++ new)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [List.getElem?_append_left (by omega), rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, fun x hx => ?_⟩
      by_cases hSx : S x
      · apply hbel x
        rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
          rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega,
          ← vl_append_lt (rdel N p a gs) new x (N + j) (by omega)]
        exact hx
      · exact hF x hSx

theorem least_of {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs0 : List Gate} {o o0 : ℕ}
    (h0 : Least N F gs0 o0) (hcl : CleanL N gs) (hev : ∀ x, vl gs x o = F x)
    (hle : gs.length ≤ gs0.length) : Least N F gs o :=
  ⟨hcl, hev, fun gs' o' hc he => le_trans hle (h0.hmin gs' o' hc he)⟩

end C10980.EdgeFn

-- C10980.Helpers.EdgeFnLift
namespace C10980.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers

theorem out_lt_of_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, vl gs x o = F x) (hnc : ∃ x y : Fin N → Bool, F x ≠ F y) :
    o < N + gs.length := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]

theorem stmtLift : StmtLift := by
  intro N F gs o p l h g hle hnc hg hop hin hbel
  have hcl := hle.hcl
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen := rdel_length N p l gs hp
  have ho := out_lt_of_nc hle.hev hnc
  
  have hlh : l < N + p ∧ h < N + p := by
    rcases hcl p g hg with ⟨h1, _⟩ | ⟨_, j, k, hj, hk, h2⟩
    · rw [hop] at h1; cases h1
    · rcases hin with e | e <;> rw [e] at h2 <;> simp at h2 <;> omega
  obtain ⟨hl, hh⟩ := hlh
  
  have hS : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N + p) = vl gs x l := by
    intro x hx
    rw [vl_gate _ hcl x p g hg, hop]
    rcases hin with e | e <;> rw [e] <;> simp [hx, GateOp.eval]
  have hro : rd N p l o < N + (gs.length - 1) := by
    unfold rd; split_ifs <;> omega
  set gs2 := rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩] with hgs2
  have hcl' := rdel_clean N p l gs hcl hp hl
  have hcl2 : CleanL N gs2 := by
    intro j g' hj
    by_cases hj' : j < (rdel N p l gs).length
    · rw [hgs2, List.getElem?_append_left hj'] at hj
      exact hcl' j g' hj
    · rw [hgs2, List.getElem?_append_right (by omega)] at hj
      obtain ⟨e1, e2⟩ := List.getElem?_eq_some_iff.1 hj
      simp at e1
      have ej : j = (rdel N p l gs).length := by omega
      subst ej
      simp at e2
      subst e2
      exact Or.inr ⟨Or.inr rfl, rd N p l o, h, by omega, by omega, rfl⟩
  have hlast : (gs2)[gs.length - 1]? = some ⟨GateOp.or, [rd N p l o, h]⟩ := by
    rw [hgs2, List.getElem?_append_right (by omega)]
    rw [show gs.length - 1 - (rdel N p l gs).length = 0 by omega]; rfl
  have hval : ∀ x : Fin N → Bool, vl gs2 x (N + (gs.length - 1)) = F x := by
    intro x
    rw [vl_gate _ hcl2 x _ _ hlast]
    have e1 : vl gs2 x (rd N p l o) = vl (rdel N p l gs) x (rd N p l o) :=
      vl_append_lt _ _ x _ (by omega)
    have e2 : vl gs2 x h = vl gs x h := by
      rw [vl_append_lt _ _ x _ (by omega), rdel_prefix N p l gs hcl hp hl x h hh]
    simp only [List.map, GateOp.eval, e1, e2]
    cases hx : vl gs x h
    · rw [rdel_all N p l gs hcl hp hl x (hS x hx) o, hle.hev x]; simp
    · rw [hbel x hx]; simp
  refine ⟨least_of hle hcl2 hval (by simp [hgs2]; omega), ?_⟩
  intro hnt t ht
  have hpt := ht.lt_of_not hp hnt
  have := tailGE_rdel_app N F gs [⟨GateOp.or, [rd N p l o, h]⟩] p l t
    (fun x : Fin N → Bool => vl gs x h = false) hcl hp hl ht hpt hS
    (fun x hx => hbel x (by simpa using hx)) ?_
  · simpa using this
  · intro i hi
    simp at hi
    subst hi
    refine ⟨_, by simpa using hlast, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
    rw [← hval x]; simpa using hx

end C10980.EdgeFn

-- C10980.Helpers.LocPlan
namespace C10980.Loc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers
open SimpleGraph

def ToolProp : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (x x' : Fin m → Bool) (D : Set ℕ) (K : ℕ), CleanL m gs →
    (∀ i : Fin m, (i : ℕ) ∉ D → x i = x' i) →
    (∀ p g, gs[p]? = some g → m + p < K → m + p ∉ D →
      (∀ w ∈ g.inputs, w ∉ D) ∨ vl gs x (m + p) = vl gs x' (m + p)) →
    ∀ j, j < K → j ∉ D → vl gs x j = vl gs x' j

end C10980.Loc

-- C10980.Helpers.LocWires
namespace C10980.Loc.Wires

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers
open C10980.Loc

theorem ToolProp_proof : ToolProp := by
  intro m gs x x' D K hcl hin hg j hj hjD
  refine agree_B gs hcl x x' (fun j => j ∈ D) K ?_ ?_ j hj hjD
  · intro j hjm hjD
    rw [vl_input gs x j hjm, vl_input gs x' j hjm]
    exact hin ⟨j, hjm⟩ hjD
  · intro p g hp hpK hpD hr _
    rcases hg p g hp hpK hpD with h1 | h1
    · obtain ⟨a, ha, haD⟩ := hr
      exact absurd haD (h1 a ha)
    · exact h1

end C10980.Loc.Wires

namespace C10981.Signed
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)



private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 152) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def prefixWidth (d : Nat) := 10*(d-1)
def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16
def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*prefixWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*prefixWidth d
    packedAt word (pre*prefixWidth d) (prefixWidth d) |||
      (last <<< prefixWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := forestRecord (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forceDatum {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)

def readSortedHints (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    forceDatum st fun pos => forceDatum first fun base =>
    forceDatum (packedAt data pos 32) fun head =>
    forceDatum (Nat.log2 (head ^^^ (head+1))) fun ones =>
    forceDatum (base+(ones <<< gapBits)+packedAt data (pos+ones+1) gapBits) fun key =>
    forceDatum (packedAt data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        readSortedHints data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)

def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 6) (pos+6+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+packedAt data (off+i*ow) ow
    let n := packedAt data pos 5
    let gap := packedAt data (pos+5) 3
    if !priority || decide (n≤1) then readSortedHints data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := packedAt data (pos+8) width
      let b := if n=2 then 1-a else packedAt data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := readSortedHints data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old
theorem extend_ok {u old L m carries} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => carryOK v.1 m v.2) = true) :
    Known u (extendKnown old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact carry_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known true [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^153*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
def fullMarks (r packed : Nat) := ((packed+r) >>> 152) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 153) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
theorem force_eq {β : Type} (n : Nat) (f : Nat → β) : force n f = f n := by cases n <;> rfl
noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
theorem forceMap_eq {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : forceMap f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change force (f a) (fun x => forceMap f l fun xs => k (x::xs)) = _
    rw [force_eq,ih]
    rfl
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
theorem nmask_eq (d a : Sig) : nmask d.toNat a = (masked d a).toNat := (BitVec.toNat_and _ _).symm
theorem beq_toNat (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj
theorem nconst_eq (d a : Sig) : nconst d.toNat (nmask d.toNat a) = isMaskedConstant d a := by
  rw [nmask_eq]
  have e : Nat.beq (masked d a).toNat 0 = (masked d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←beq_toNat,z0]
  rw [nconst,e,beq_toNat]
  rfl
theorem anyEq_eq (x d : Sig) (pool : List Sig) : anyEq x.toNat (pool.map (nmask d.toNat)) = (pool.map (masked d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (nmask d.toNat a)) (anyEq x.toNat (l.map (nmask d.toNat))) = _
    rw [ih,nmask_eq,beq_toNat,List.map_cons,List.any_cons,Bool.beq_comm]
theorem navail_eq (u : Bool) (d a : Sig) (pool : List Sig) :
    navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a) = availableB u d pool a := by
  have x : Nat.xor d.toNat (masked d a).toNat = (masked d (neg a)).toNat := by
    rw [masked_comp]
    exact (BitVec.toNat_xor _ _).symm
  rw [navail,nconst_eq,nmask_eq,x,anyEq_eq,anyEq_eq]
  simp only [availableB,isMaskedConstant]
def unav (u : Bool) (p : BoundPool) (w : Decor) : Nat := cond (availableB u p.domain p.wires w.1) 0 1
def slowCost (u : Bool) (p : BoundPool) (ws : List Decor) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - constantLoss const a ka - constantLoss const b kb + (isMaskedConstant p.domain z).toNat
  (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
    decide (k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+cm)) &&
    (availableB u p.domain p.wires z || (availableB u p.domain p.wires a.1 && availableB u p.domain p.wires b.1))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem zN_eq (op : Nat) (d a b : Sig) : zN op (nmask d.toNat a) (nmask d.toNat b) = nmask d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [nmask_eq]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply bit_ext
    intro r
    simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply bit_ext
  intro r
  simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
theorem nloss_eq (d : Sig) (a : Decor) (keep : Bool) :
    nloss d.toNat (nmask d.toNat a.1) keep = constantLoss (fun w : Decor => isMaskedConstant d w.1) a keep := by
  rw [nloss,nconst_eq,constantLoss]
  cases keep
  · cases isMaskedConstant d a.1 <;> rfl
  · rfl
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def quickSpec (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : Decor => nmask d w.1)
  (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
theorem forcePool_eq {β : Type} (u k ws p) (f : QS → β) : forcePool u k ws p f = f (quickSpec u k ws p) := by
  have e (b : Bool) (f : Bool → β) : forceBool b f = f b := by cases b <;> rfl
  simp only [forcePool,force_eq,forceMap_eq,e]
  rfl
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
theorem forcePools_eq {β : Type} (u k ws ps) (f : List QS → β) : forcePools u k ws ps f = f (ps.map (quickSpec u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change forcePool u k ws p (fun q => forcePools u k ws ps fun qs => f (q::qs)) = _
    rw [forcePool_eq,ih]
    rfl
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => forceLanes cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,ih]
    rfl
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem spec_get {d : Nat} (ws : List Decor) (i : Nat) (hd : nmask d zero=0) :
    (ws.map (fun w : Decor => nmask d w.1)).getD i 0 = nmask d (ws.getD i defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl
theorem fast_slow {u k p ws i j op ka kb} (h : fastCost (quickSpec u k ws p) i j op ka kb=true) :
    slowCost u p ws k (ws.getD i defaultDecor) (ws.getD j defaultDecor) op ka kb=true := by
  have z0 : nmask p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [nmask,this]
  have su : (((ws.map (fun w : Decor => nmask p.domain.toNat w.1)).map fun m => cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
      (ws.map (unav u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1 = _
    rw [navail_eq]
    rfl
  simp only [fastCost,quickSpec,force_eq,spec_get _ _ z0,su,List.countP_map,Function.comp_def,nconst_eq] at h
  generalize ws.getD i defaultDecor=a at h ⊢
  generalize ws.getD j defaultDecor=b at h ⊢
  replace h : and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
    (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : Decor => isMaskedConstant p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false)) = true := h
  rw [zN_eq,nconst_eq,navail_eq,navail_eq,navail_eq,nloss_eq,nloss_eq] at h
  have ca : isMaskedConstant p.domain (bin op a.1 b.1)=true → availableB u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => isMaskedConstant p.domain w.1) - constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) a ka -
      constantLoss (fun w : Decor => isMaskedConstant p.domain w.1) b kb = c at h ⊢
    generalize isMaskedConstant p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize availableB u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]

theorem anyEq_iff (m : Nat) (l : List Nat) : anyEq m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [anyEq]
  | cons a l ih =>
    change or (Nat.beq m a) (anyEq m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem keySet_sum (xs : List Sig) : keySet xs = (xs.map keyWord).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+keyWord x) a = a+(xs.map keyWord).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)
theorem delTwo_sum (f : Decor → Nat) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List Decor} {x : Decor} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [delTwo,delOne,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega
theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : allowedB u op=true)
    (h : slowCost u p ws k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := bin op a.1 b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  simp only [slowCost,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := delTwo_sum (unav u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((delTwo ws a b ka kb).map (unav u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : availableB u p.domain p.wires w.1
    · simp [unav,e] at v
    · rfl
  have opOK : (!(!availableB u p.domain p.wires z) || choiceOK u p.domain p.wires (movedChoice op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [choiceOK,movedChoice,x,y,al]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : choiceVal (movedChoice op a b)=z := rfl
  simp only [scalarPoolCut,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
  cases hc' : isMaskedConstant p.domain z <;> simp [hc'] at hc ⊢ <;> omega

theorem zN_full (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : nmask one.toNat v = v.toNat := by
    rw [nmask_eq]
    congr 1
    exact BitVec.and_allOnes
  have := zN_eq op one a b
  rwa [e,e,e] at this
theorem getW (ws : List Decor) (i : Nat) :
    (ws.map (fun w : Decor => w.1.toNat)).getD i 0 = (ws.getD i defaultDecor).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl
theorem wire_ne {c : NodeContext} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (contextWire c i).1 ≠ (contextWire c j).1 := by
  have gi : contextWire c i = c.2.2.1[i] := by simp [contextWire,List.getD_eq_getElem?_getD,hi]
  have gj : contextWire c j = c.2.2.1[j] := by simp [contextWire,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e
theorem link_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))).any (sameWords
      (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  have hne := wire_ne nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : contextWire c i ≠ contextWire c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := kept_value nd ha hb ka kb v
  have sum := delTwo_sum (fun w : Decor => keyWord w.1) ha hb hab ka kb
  have wi : contextWire c i = c.2.2.1.getD i defaultDecor := rfl
  have wj : contextWire c j = c.2.2.1.getD j defaultDecor := rfl
  simp only [linkAt,laneOf,force_eq,getW,←wi,←wj,zN_full] at h
  generalize contextWire c i=a at *
  generalize contextWire c j=b at *
  change Option.rec false _ (fl (keyWord (bin op a.1 b.1)+(((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum -
    (cond ka 0 (keyWord a.1)) - (cond kb 0 (keyWord b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : Decor => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : Decor => keyWord w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst) =
      keyWord (bin op a.1 b.1)+((delTwo c.2.2.1 a b ka kb).map (fun w : Decor => keyWord w.1)).sum := by
    rw [keySet_sum,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize keySet (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : allowedB c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [allowedB] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
      simp [contextWire,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := wire_ne nd hi hj (fun e => by simp [e] at hn)
    have closed := fastCost_good (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (fast_slow ok)
    have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
        ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
        (movedChoice op (contextWire c i) (contextWire c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := link_sound nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [checkAt,evalMove,closeChild,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem swap_table : ∀ v : Fin 144, validSwap v.val=true → ∀ t : Fin 9, swapIdx v.val t.val<9 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<9) : swapIdx v t<9 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<144 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<9) :
    movedWord (perm.map swapRows).reverse (inputs.getD t zero) = inputs.getD (idxOf perm t) zero := by
  rw [movedWord,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := swap_input ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
theorem decodeN_eq (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List Decor) :
    (decodeBank n bits ds).map (fun w => F w.1) = decodeN n bits (ds.map fun w => F w.1) := by
  have gd (ds : List Decor) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i defaultDecor).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [decodeN,force_eq,decodeBank,ih,gd,gd,←Fb,List.map_append]
    rfl
theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (selectLive bits ws).map f = selectLive bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,selectLive,selectLive]
    split
    · rw [List.map_cons,ih]
    · exact ih _
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (forestRecord (g.levels k) (selected g.mask).length i) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
theorem fastState_eq (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all validSwap=true) :
    fastState g k i perm = ((stateSet g k i).map (movedWord (perm.map swapRows).reverse)).map BitVec.toNat := by
  let ms := (perm.map swapRows).reverse
  let F (a : Sig) : Nat := (movedWord ms a).toNat
  have F0 : F zero=0 := by
    change (movedWord ms zero).toNat=0
    rw [moved_eq_rename,(rename_constants _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (movedWord ms (bin op a b)).toNat = zN op (movedWord ms a).toNat (movedWord ms b).toNat
    rw [zN_full,moved_eq_rename,rename_bin,moved_eq_rename,moved_eq_rename]
  have raw : (wiresOf g).map (fun w => F w.1) = (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat := by
    simp only [wiresOf,rawDecor,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := selected_entry hm
    exact congrArg BitVec.toNat (idx_move ok hj)
  have len : (wiresOf g).length = (selected g.mask).length := by simp [wiresOf,rawDecor]
  unfold fastState stateSet readNode
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [force_eq,storedDepth,len]
  rw [List.map_map,List.map_map,selectLive_map,←raw,←decodeN_eq F F0 Fb]
  rfl
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

theorem batchMove_at {fl u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : batchMove fl u (makeBatch k n xs) (xs.map laneOf) i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) (xs.map laneOf)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply fallback_sound nd hfl
      have m := marked_ok _ _ _ q (by simpa using hq) (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
noncomputable def batchRows (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) : List Nat → Bool
  | [] => true
  | i::js => batchRow fl u b xs i js && batchRows fl u b xs js

theorem batchRows_at {fl u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows fl u (makeBatch k n xs) (xs.map laneOf) js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at fl u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩

noncomputable def runBatch (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows fl u (makeBatch k n xs) (xs.map laneOf) (List.range n)
theorem runBatch_at {fl u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : runBatch fl u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, _
  unfold flOf at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,linkedFast] at h
    simp only [Option.bind_some,linkedSet]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all validSwap with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(stateSet g (k-1) pair.1).map (movedWord (perm.map swapRows).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (fastState_eq g _ _ hv)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (flOf g k) g.mode (makeBatch k ar (contexts g k start n)) ((contexts g k start n).map laneOf)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [rowCut,forceLanes_eq] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  simp only [rowCut,forceLanes_eq]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch (flOf g k) g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (flOf g k) g.mode (makeBatch k ar xs) (xs.map laneOf) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => flOf_ok g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm nd hfl hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def g7Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (j : Nat) : Nat := 0x7
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=1) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[]),(25,[49,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[(0xfd587fff83fffff3fab0ffff07ffffe7f561ff,0x9241082080200001248210410040000249),(0x3baf81fffc0fc7fc775f03fff81f8ff8eebe07,0x818d249212411241031a492424822482063492),(0xc6b78e3ffff007ff8d6f1c7fffe00fff1ade38,0x16324924208a24802c6492484114490058c924),(0x64c703ffffff8000c98e07ffffff0001931c0,0x264f6db8430c070a4c9edb7086180e14993db6),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(8,0,7,0,4)]
def g15A : List (List Nat) := [[],[33]]
def g15D4 (j : Nat) : Nat := 0x1f
def g15L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g15D4)
  | _ => emptyPacking
def g15I (_ _ : Nat) : Option (Nat × Nat) := none
def g15 : Forest := ⟨15,4,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 1=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact (rfl : block g15 3 0 0 = true)
  · exact g15B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=1) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 5 [(15,[]),(23,[67]),(27,[49,66]),(29,[49,66,33]),(39,[16,83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[(0xe7ce3fff03ffe3ffe7ce3fff03ffe3ffe7ce3f,0x5489242882049100548924288204910054892),(0xff33c7fffc0ffff8ff33c7fffc0ffff8ff33c7,0x2324914114280220232491411428022023249),(0x0,0x0),(0xaec38fffff003ff0aec38fffff003ff0aec38,0x4aa56d98218b12404aa56d98218b12404aa56d),(0x0,0x0),(0x193dc0fffffffc00193dc0fffffffc00193dc0,0x990db6e0c20c0384990db6e0c20c0384990db6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[16,83]]
def g43D3 (j : Nat) : Nat := 0xf
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=1048577) (before_sound K15 V15) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K15 4 [(43,[]),(51,[67]),(77,[33,101]),(85,[33,67,101]),(102,[16,32,83,67,100]),(163,[16,80,48,67,116,100]),(166,[16,80,32,50,67,116,100]),(197,[32,97,16,48,67,117]),(198,[32,97,49,67,117]),(226,[80,113,32,49,66,100,67]),(228,[96,113,32,50,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V15 low43 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(0x7fe01fffffffe01fffffffe3fc9594400fffff,0x404020100040402010004000000002108421),(0x7fffe00ff87fffe00ff87ffc3f436d41f0001f,0x248492412124888a4421248082032d54a5294a),(0x7ffffff0007ffffff0007fffc3da7081f003e0,0x4909048a424911108942490009d850a94a5294),(0x80000000007fffffffff8000007f0bbe007c00,0xe0e0703840e020301800e091057038c6318c6),(0xffffffffff8000000000000003289bfe0f8000,0x7010180c00701c1c0e047012232898718c6318),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(2,0,29,0,5),(4,0,27,0,5),(8,0,23,0,5),(16,0,15,0,5),(6,0,25,0,4),(24,0,7,0,4)]
def g31A : List (List Nat) := [[],[67],[33],[33,67],[49,66],[49,66,33],[65,50,33],[65,50]]
def g31D4 (j : Nat) : Nat := 0x31826d62141318fd91538426f6254d10
def g31D5 (j : Nat) : Nat := 0x310402003040184208228851040db4e6c278b10910c02fea098df14131bfa9c217d53842fea6885f54d10f7a9221f531443ec20885bd4910
def g31H5 (j : Nat) : Nat := 0x30050000000000000000000001040000003c80000004880000000000000
def g31D6 (j : Nat) : Nat := 0x5408c9033240e4480fd31fe10fd10
def g31H6 (j : Nat) : Nat := 0x65ec4800909c480048390e202c0800b110180b00000061400295528003e1082700c
def g31D7 (j : Nat) : Nat := 0x1605f
def g31H7 (j : Nat) : Nat := 0x932c3d5f90000322e00000391b8000009cc2007045310
def g31L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g31D4)
  | 5 => (10,2,3,0,0,7,0,g31D5)
  | 6 => (3,1,3,0,0,6,0,g31D6)
  | 7 => (1,0,3,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 29 0 9 2 3 g31H5
  | 6 => lookupWord 4 23 4 11 4 3 g31H6
  | 7 => lookupWord 3 19 3 9 2 3 g31H7
  | _ => fun _ => none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 3=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_1 : block g31 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 10=true := (@block_merge g31 5 0 1 9 g31P5_0 g31P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 3=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 1=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=1) (before_sound K43 V43) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end C10981.Signed


namespace C10981.Signed

def butterfly : Sig := graphGoal 31
def bfInputs : List Sig := varsX 31

def splitOK (T block : Sig) : List Sig → Bool
  | [] => (block &&& T == zero) || (block &&& ~~~T == zero)
  | a :: ws =>
      ((block &&& T == zero) || (block &&& ~~~T == zero)) ||
      (splitOK T (block &&& a) ws && splitOK T (block &&& ~~~a) ws)

theorem bit_not (r : Row) (a : Sig) : bit r (~~~a) = !bit r a := by
  exact bit_neg r a

theorem bit_and (r : Row) (a b : Sig) : bit r (a &&& b) = (bit r a && bit r b) := by
  exact bit_bin r 0 a b

theorem exists_bit_of_ne {a : Sig} (h : a ≠ zero) : ∃ r : Row, bit r a = true := by
  by_contra! none
  apply h
  apply bit_ext
  intro r
  rw [bit_zero]
  cases e : bit r a
  · rfl
  · exact False.elim (none r e)

theorem splitOK_correct {T block : Sig} {ws : List Sig}
    (h : ∀ r s : Row, bit r block = true → bit s block = true →
       bit r T = true → bit s T = false → ∃ w ∈ ws, bit r w ≠ bit s w) :
    splitOK T block ws = true := by
  induction ws generalizing block with
  | nil =>
    simp only [splitOK,Bool.or_eq_true,beq_iff_eq]
    by_cases p : block &&& T = zero
    · exact Or.inl p
    · refine Or.inr ?_
      by_contra n
      obtain ⟨r,hr⟩ := exists_bit_of_ne p
      obtain ⟨s,hs⟩ := exists_bit_of_ne n
      rw [bit_and,Bool.and_eq_true] at hr hs
      rw [bit_not] at hs
      obtain ⟨w,hw,_⟩ := h r s hr.1 hs.1 hr.2 (by simpa using hs.2)
      simpa using hw
  | cons a ws ih =>
    simp only [splitOK,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
    right
    constructor
    · apply ih
      intro r s hr hs hp hn
      rw [bit_and,Bool.and_eq_true] at hr hs
      obtain ⟨w,hw,hd⟩ := h r s hr.1 hs.1 hp hn
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact False.elim (hd (hr.2.trans hs.2.symm))
      · exact ⟨w,hw,hd⟩
    · apply ih
      intro r s hr hs hp hn
      rw [bit_and,Bool.and_eq_true,bit_not] at hr hs
      obtain ⟨w,hw,hd⟩ := h r s hr.1 hs.1 hp hn
      simp only [List.mem_cons] at hw
      rcases hw with eq | hw
      · have zr : bit r a = false := by simpa using hr.2
        have zs : bit s a = false := by simpa using hs.2
        exact False.elim (hd (by simpa only [eq] using zr.trans zs.symm))
      · exact ⟨w,hw,hd⟩

theorem splitOK_live {T block : Sig} {u k ws} (h : Live u T k ws.toFinset) :
    splitOK T block ws = true := by
  apply splitOK_correct
  intro r s hr hs hp hn
  obtain ⟨w,hw,hd⟩ := live_row_difference h (r:=r) (s:=s) (by simp [hp,hn])
  exact ⟨w,List.mem_toFinset.mp hw,hd⟩

def lowWord : Sig := BitVec.ofNat 512 4294967295

def blocked (T : Sig) : Nat → List Sig → Bool
  | 0, ws => !ws.contains T
  | cap+1, ws =>
      !ws.contains T &&
      (!(splitOK T lowWord ws) ||
       ws.all fun a => ws.all fun b =>
         if a.toNat < b.toNat then
           [0,1,2,3].all fun d =>
             [false,true].all fun ka =>
               [false,true].all fun kb =>
                 let z := bin d a b
                 let next := childTwo ws a b d ka kb
                 if z == zero || z == one || ws.contains z || cap+1 < next.length
                 then true else blocked T cap next
         else true)

theorem childTwo_nodup_bf' {ws : List Sig} (nd : ws.Nodup) (a b : Sig)
    (am : a ∈ ws) (bm : b ∈ ws) (hab : a ≠ b) (d : Nat) (ka kb : Bool) (hf : bin d a b ∉ ws) :
    (childTwo ws a b d ka kb).Nodup := by
  have rn : ((ws.erase a).erase b).Nodup := (nd.erase _).erase _
  have ar : a ∉ (ws.erase a).erase b := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
  have br : b ∉ (ws.erase a).erase b := (nd.erase a).not_mem_erase
  have nk := kept_nd kb b _ rn br
  have ax : a ∉ kept kb b ((ws.erase a).erase b) := by cases kb <;> simp [kept,ar,hab]
  refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
  intro hz
  apply hf
  cases ka <;> cases kb <;> simp [kept] at hz
  · exact List.mem_of_mem_erase (List.mem_of_mem_erase hz)
  · exact hz.elim (fun e => e.symm ▸ bm) (fun m => List.mem_of_mem_erase (List.mem_of_mem_erase m))
  · exact hz.elim (fun e => e.symm ▸ am) (fun m => List.mem_of_mem_erase (List.mem_of_mem_erase m))
  · rcases hz with e | e | h
    · exact e.symm ▸ am
    · exact e.symm ▸ bm
    · exact List.mem_of_mem_erase (List.mem_of_mem_erase h)

theorem blocked_sound {T : Sig} (k : Nat) (ws : List Sig)
    (nd : ws.Nodup) (hc : blocked T k ws = true) : Impossible true T k ws.toFinset := by
  induction k generalizing ws with
  | zero =>
    simp [blocked] at hc
    exact enum_step nd hc (by intros; simp [childTwo] at *)
  | succ k ih =>
    simp only [blocked,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at hc
    rcases hc with ⟨out,bad | steps⟩
    · intro m hm h
      exact Bool.noConfusion (bad.symm.trans (splitOK_live (block:=lowWord) h))
    · have hout : T ∉ ws := by simpa using out
      apply enum_step nd hout
      intro a ha b hb d hd ka kb hab hf hz hsize
      have dom (a b) (am : a ∈ ws) (bm : b ∈ ws) (hlt : a.toNat < b.toNat)
          (d : Nat) (hdm : d ∈ ([0,1,2,3] : List Nat)) (ka kb : Bool)
          (hf' : bin d a b ∉ ws) (hz' : proper (bin d a b))
          (hsize' : (childTwo ws a b d ka kb).length ≤ k+1) :
          Impossible true T k (childTwo ws a b d ka kb).toFinset := by
        have h0 := List.all_eq_true.mp steps a am
        have h1 := List.all_eq_true.mp h0 b bm
        simp only [if_pos hlt] at h1
        have h2 := List.all_eq_true.mp h1 d hdm
        have h3 := List.all_eq_true.mp h2 ka (by cases ka <;> simp)
        have h4 := List.all_eq_true.mp h3 kb (by cases kb <;> simp)
        have hnot : ¬ k + 1 < (childTwo ws a b d ka kb).length := by omega
        simp [hz'.1,hz'.2,hf',hnot] at h4
        exact ih _ (childTwo_nodup_bf' nd _ _ am bm (fun e => (Nat.ne_of_lt hlt) (congrArg BitVec.toNat e)) _ _ _ hf') h4
      have hdm : d ∈ ([0,1,2,3] : List Nat) := by
        rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
      have hl : a.toNat ≠ b.toNat := fun h => hab (BitVec.eq_of_toNat_eq h)
      rcases lt_or_gt_of_ne hl with hlt | hlt
      · exact dom a b ha hb hlt d hdm ka kb hf hz hsize
      · have hs := childTwo_swap (u:=true) ws nd a b d hd ka kb
        have hbin := bin_flip hd a b
        have hlen : (childTwo ws b a (flipOp d) kb ka).length ≤ k+1 := by
          have na := childTwo_nodup_bf' nd a b ha hb hab d ka kb hf
          have nb := childTwo_nodup_bf' nd b a hb ha (Ne.symm hab) (flipOp d) kb ka (by rw [← hbin]; exact hf)
          rw [←List.toFinset_card_of_nodup nb,← hs,List.toFinset_card_of_nodup na]
          exact hsize
        have dm : flipOp d ∈ ([0,1,2,3] : List Nat) := by
          rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
        simpa only [Nat.succ_sub_one, hs] using
          (dom b a hb ha hlt (flipOp d) dm kb ka (by rwa [← hbin]) (by rwa [← hbin]) hlen)


theorem bf_low : Lower true bfInputs butterfly 8 := low31

end C10981.Signed

namespace C10981.Signed

theorem butterfly_lower (hcert : blocked butterfly 7 bfInputs = true) :
    Lower true bfInputs butterfly 8 := by
  have hp : proper butterfly := by unfold proper; decide +kernel
  have ht : plainWord butterfly = true := by decide +kernel
  have hv : bfInputs.all plainWord = true := by decide +kernel
  apply lower_impossible hp ht hv
  · intro a ha
    obtain ⟨i,rfl⟩ : ∃ i : Fin 5, a = bfInputs.getD i.val zero := by
      have hl : bfInputs = List.ofFn (fun j : Fin 5 => bfInputs.getD j.val zero) := rfl
      rw [hl] at ha
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp ha
      exact ⟨j,hj.symm⟩
    have ess : ∀ i : Fin 5, ∃ r s : Fin 32, bit (Fin.ofNat 512 r.val) butterfly ≠ bit (Fin.ofNat 512 s.val) butterfly ∧
      ∀ j : Fin 5, (bfInputs.getD j.val zero) ≠ (bfInputs.getD i.val zero) →
        bit (Fin.ofNat 512 r.val) (bfInputs.getD j.val zero) =
        bit (Fin.ofNat 512 s.val) (bfInputs.getD j.val zero) := by decide +kernel
    obtain ⟨r,s,hd,he⟩ := ess i
    refine ⟨Fin.ofNat 512 r.val,Fin.ofNat 512 s.val,hd,?_⟩
    intro v hv hn
    have hl : bfInputs = List.ofFn (fun j : Fin 5 => bfInputs.getD j.val zero) := rfl
    rw [hl] at hv
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
    exact he j hn
  · exact blocked_sound 7 bfInputs (by decide +kernel) hcert

def wi : List Sig := varsX 127
def wireAt (i : Fin 7) : Sig := inputs.getD i.val zero

def wind : Sig :=
  let x := wireAt
  (x 0 &&& (x 1 ||| x 2 ||| x 3 ||| x 4 ||| x 5 ||| x 6)) |||
  (x 1 &&& x 2) ||| (x 3 &&& x 4) ||| (x 5 &&& x 6)

def zeroVar (i : Fin 7) : List Move := fixRows (1 <<< i.val) 0
def windCut (i : Fin 7) : Sig := movedWord (zeroVar i) wind
def coreRoots (i : Fin 7) : List Sig := varsX (127 ^^^ (1 <<< i.val))

def mate : Fin 7 → Fin 7 := ![0,2,1,4,3,6,5]

def rotateWing (i : Fin 7) : List Move :=
  let swap (a b : Nat) := swapRows (a + 16*b)
  if i.val ≤ 2 then [swap 1 5, swap 2 6]
  else if i.val ≤ 4 then [swap 3 5, swap 4 6]
  else []

def toButter (i : Fin 7) : List Move := rotateWing i ++ zeroVar (mate i)

def mateWitness (i : Fin 7) : List (Sig × Row × Row) :=
  [(wireAt (mate i), 1, Fin.ofNat 512 (1 ||| (1 <<< (mate i).val)))]

theorem peripheral_lower (hbut : Lower true bfInputs butterfly 8) (i : Fin 7) (hi : i ≠ 0) :
    Lower true (coreRoots i) (windCut i) 9 := by
  have bitcert : ∀ j : Fin 7, j ≠ 0 →
    checkLift (toButter j) (windCut j) (coreRoots j) bfInputs butterfly (mateWitness j) = true := by
    decide +kernel
  have hp : ∀ j : Fin 7, j ≠ 0 → proper (windCut j) := by simp only [proper]; decide +kernel
  have h1 : ∀ j : Fin 7, j ≠ 0 → ((mateWitness j).map Prod.fst).toFinset.card = 1 := by decide +kernel
  have pre := lift_ok (bitcert i hi) (hp i hi) (show proper butterfly by unfold proper; decide +kernel) hbut
  rwa [h1 i hi] at pre

def coreWord : Sig := BitVec.ofNat 512 ((1 <<< 128) - 1)

def goodProject (ws : List Sig) (i : Fin 7) : Bool :=
  ws.all (fun a => freeWord (coreRoots i) (movedWord (zeroVar i) a)) &&
  ws.any (fun a => movedWord (zeroVar i) a == zero)

theorem finiteFirst :
    ∀ i j : Fin 7, ∀ d : Fin 4, ∀ a b : Bool, i ≠ j →
      let ws := childTwo wi (wireAt i) (wireAt j) d.val a b
      splitOK wind coreWord ws = false ∨ ∃ v : Fin 7, v ≠ 0 ∧ goodProject ws v = true := by
  decide +kernel

theorem wind_finiteLower (hbut : Lower true bfInputs butterfly 8) : Lower true wi wind 11 := by
  have hp : proper wind := by unfold proper; decide +kernel
  have ht : plainWord wind = true := by decide +kernel
  have hv : wi.all plainWord = true := by decide +kernel
  apply lower_impossible hp ht hv
  · intro a ha
    have hl : wi = List.ofFn (fun j : Fin 7 => wireAt j) := rfl
    rw [hl] at ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    have ess : ∀ i : Fin 7, ∃ r s : Fin 128,
      bit (Fin.ofNat 512 r.val) wind ≠ bit (Fin.ofNat 512 s.val) wind ∧
      ∀ j : Fin 7, wireAt j ≠ wireAt i →
        bit (Fin.ofNat 512 r.val) (wireAt j) = bit (Fin.ofNat 512 s.val) (wireAt j) := by decide +kernel
    obtain ⟨r,s,hd,he⟩ := ess i
    refine ⟨Fin.ofNat 512 r.val,Fin.ofNat 512 s.val,hd,?_⟩
    intro b hb hn
    rw [hl] at hb
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    exact he j hn
  · apply enum_step (ws:=wi) (cap:=10) (by decide +kernel) (by decide +kernel)
    intro a ha b hb d hd ka kb hab hf hz hl
    have hw : wi = List.ofFn (fun j : Fin 7 => wireAt j) := rfl
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (hw ▸ ha)
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp (hw ▸ hb)
    subst a b
    have hij : i ≠ j := fun e => hab (congrArg wireAt e)
    have dd : d < 4 := by rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
    set ws := childTwo wi (wireAt i) (wireAt j) d ka kb
    have nd : ws.Nodup := childTwo_nodup_bf' (by decide +kernel) _ _ ha hb hab d ka kb hf
    intro k hk run
    rcases finiteFirst i j ⟨d,dd⟩ ka kb hij with hsep | ⟨v,hv,good⟩
    · exact Bool.noConfusion (hsep.symm.trans (splitOK_live (block:=coreWord) run))
    · have gc : restrictRows (movedRow (zeroVar v)) (observe wind) = observe (windCut v) := by
        rw [←observe_rename,←moved_eq_rename]
        rfl
      have hp' : ∀ v : Fin 7, v ≠ 0 → proper (windCut v) := by simp only [proper]; decide +kernel
      have rp := list_run run ws nd rfl
      have L := peripheral_lower hbut v hv
      simp only [goodProject,Bool.and_eq_true] at good
      have sup : supply true ((coreRoots v).map observe)
          ((ws.map observe).map (restrictRows (movedRow (zeroVar v)))) := by
        intro b hb
        obtain ⟨_,he,rfl⟩ := List.mem_map.mp hb
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
        rw [←observe_rename,←moved_eq_rename]
        exact freeWord_ok (List.all_eq_true.mp good.1 a ha)
      obtain ⟨z,hz,hzero⟩ := List.any_eq_true.mp good.2
      have hzero' : restrictRows (movedRow (zeroVar v)) (observe z) = observe zero := by
        rw [←observe_rename,←moved_eq_rename,beq_iff_eq.mp hzero]
      have hmem : observe zero ∈ ((ws.map observe).map (restrictRows (movedRow (zeroVar v)))) := by
        rw [← hzero']
        exact List.mem_map_of_mem (f:=restrictRows _) (List.mem_map_of_mem (f:=observe) hz)
      have hc : cost (observe zero) = 1 := by
        have h : Constant (observe zero) := ⟨false,funext bit_zero⟩
        simp [cost,h]
      have hmass : 1 ≤ mass ((ws.map observe).map (restrictRows (movedRow (zeroVar v)))) := by
        obtain ⟨l,r,h⟩ := List.mem_iff_append.mp hmem
        rw [h,mass_append,mass_cons,hc]
        omega
      have bound := projected_bound (movedRow (zeroVar v)) rp (gc ▸ observe_proper (hp' v hv))
        Reach.start sup (L:=9) (gc ▸ L)
      omega

end C10981.Signed

namespace C10981.Signed

open PEqualNP.CircuitLowerBounds

def windF (x : Fin 7 → Bool) : Bool :=
  (x 0 && (x 1 || x 2 || x 3 || x 4 || x 5 || x 6)) ||
  (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)

def sampled7 (r : Row) (j : Fin 7) : Bool := bit r (wireAt j)

theorem bit_or (r : Row) (a b : Sig) : bit r (a ||| b) = (bit r a || bit r b) := by
  exact bit_bin r 1 a b

theorem wind_table : ∀ r : Row, bit r wind = windF (sampled7 r) := by
  intro r
  simp only [wind,windF,sampled7,bit_and,bit_or]

def binaryCount (C : Circuit) : Nat := C.gates.countP fun g => !isNot g

theorem signed_windmill_any (hbut : Lower true bfInputs butterfly 8) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C) (raw : List Sig)
    (raw_pos : raw.all plainWord = true) (raw_sub : ∀ a ∈ raw, a = zero ∨ a ∈ wi)
    (computes : ∀ r : Row, C.eval (raw.map (bit r)) = windF (sampled7 r)) :
    11 ≤ binaryCount C := by
  have goalEq : (execute C.gates raw).getD C.output zero = wind := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),wind_table]
    exact computes r
  have hp : proper wind := by unfold proper; decide +kernel
  have h00 : bit 0 wind = false := by decide +kernel
  have h := get_rep (u:=true) (execute C.gates raw) C.output
  rw [goalEq] at h
  unfold Repr at h
  rw [nrm_id h00] at h
  obtain ⟨k,S,hle,run,sub⟩ := extract (u:=true) C.gates raw legal (by simp) hp
    (h.resolve_right (fun hh => hh hp))
  rw [nrm_map raw_pos] at sub
  let ws := S.toList
  have rf := list_run run ws (Finset.nodup_toList S) (Finset.toList_toFinset S)
  have heq (w : Wire Row) : restrictRows (fun r : Row => r) w = w := rfl
  have covered : supply true (wi.map observe) ((ws.map observe).map (restrictRows fun r : Row => r)) := by
    intro w hw
    obtain ⟨_,hwhat,rfl⟩ := List.mem_map.mp hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hwhat
    rw [heq]
    have ma := Finset.mem_toList.mp ha
    rcases raw_sub a (sub a ma) with z | aWi
    · exact False.elim ((live_proper run a ma).1 z)
    · exact Or.inl (List.mem_map_of_mem (f:=observe) aWi)
  have low := wind_finiteLower hbut
  have nh : ¬ Constant (restrictRows (fun r : Row => r) (observe wind)) := by
    rw [heq]
    exact observe_proper hp
  have bound := projected_bound (fun r : Row => r) rf nh Reach.start covered
    (L:=11) (by simpa only [heq,Lower] using low)
  unfold binaryCount
  omega

def fixedRaw : List Sig :=
  [wireAt 1,wireAt 3,wireAt 5,zero,zero,wireAt 4,wireAt 6,wireAt 2,wireAt 0]

def fixedInputs (x : Fin 7 → Bool) : Fin 9 → Bool :=
  ![x 1,x 3,x 5,false,false,x 4,x 6,x 2,x 0]

theorem signed_windmill_fixed (hbut : Lower true bfInputs butterfly 8) (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn (fixedInputs x)) = windF x) :
    11 ≤ binaryCount C := by
  apply signed_windmill_any hbut C legal fixedRaw (by decide +kernel)
  · intro a ha
    simp only [fixedRaw,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  intro r
  have eq : fixedRaw.map (bit r) = List.ofFn (fixedInputs (sampled7 r)) := by
    simp only [fixedRaw,List.map_cons, List.map_nil,bit_zero]
    rfl
  rw [eq]
  exact computes (sampled7 r)

end C10981.Signed

namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open C10980.Helpers C10980.Helpers.Readers
open C10980.EdgeFn C10980.Loc.Wires

abbrev Bits := Fin 9 → Bool
def f : Bits → Bool := fun x =>
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) ||
  (x 3 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 2 && x 8) ||
  (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)

def single (v : Fin 9) : Bits := fun i => decide (i = v)
def onlyReader (gs : List Gate) (v : Fin 9) (r : ℕ) : Prop :=
  ∀ p, Reads gs p v → p = r

lemma before_agree {gs : List Gate} (hcl : CleanL 9 gs)
    {v : Fin 9} {r j : ℕ} (hreader : onlyReader gs v r)
    (hj : j < 9 + r) (hne : j ≠ v.val)
    (x y : Bits) (outside : ∀ i : Fin 9, i ≠ v → x i = y i) :
    vl gs x j = vl gs y j := by
  refine ToolProp_proof 9 gs x y ({v.val} : Set ℕ) (9+r) hcl ?_ ?_ j hj ?_
  · intro i hi
    exact outside i (by rintro rfl; simp at hi)
  · intro p g hp hpbound _
    left
    intro a ha hmem
    have hv : a = v.val := by simpa using hmem
    subst a
    have := hreader p ⟨g,hp,ha⟩
    omega
  · simpa using hne

lemma after_agree {gs : List Gate} (hcl : CleanL 9 gs)
    {v : Fin 9} {r j : ℕ} (hreader : onlyReader gs v r) (hne : j ≠ v.val)
    (x y : Bits) (outside : ∀ i : Fin 9, i ≠ v → x i = y i)
    (gateAgree : vl gs x (9+r) = vl gs y (9+r)) :
    vl gs x j = vl gs y j := by
  refine ToolProp_proof 9 gs x y ({v.val} : Set ℕ) (j+1) hcl ?_ ?_ j (by omega) ?_
  · intro i hi
    exact outside i (by rintro rfl; simp at hi)
  · intro p g hp _ _
    by_cases pr : p = r
    · right
      simpa [pr] using gateAgree
    · left
      intro a ha hmem
      have hv : a = v.val := by simpa using hmem
      subst a
      exact pr (hreader p ⟨g,hp,ha⟩)
  · simpa using hne

set_option maxRecDepth 10000 in
lemma edge_case_three : ∀ x : Bits, f x = false →
    f (Function.update (Function.update x 3 true) 7 false) = false ∧
    f (Function.update (Function.update x 3 true) 7 true) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma edge_case_four : ∀ x : Bits, f x = false →
    f (Function.update (Function.update x 4 true) 0 false) = false ∧
    f (Function.update (Function.update x 4 true) 0 true) = true := by
  decide +kernel

lemma single_false : ∀ v : Fin 9, f (single v) = false := by decide +kernel

lemma out_not_primary {gs : List Gate} {o : ℕ} (L : Least 9 f gs o) (v : Fin 9) :
    o ≠ v.val := by
  intro equal
  have h := L.hev (single v)
  rw [equal, vl_input gs (single v) v.val v.isLt, single_false] at h
  simp [single] at h

lemma partner_below {gs : List Gate} {o r d : ℕ} {g : Gate} {e v : Fin 9}
    (L : Least 9 f gs o) (reader : onlyReader gs v r) (hg : gs[r]? = some g)
    (hor : g.op = GateOp.or)
    (hop : g.inputs = [v.val,d] ∨ g.inputs = [d,v.val])
    (dne : d ≠ v.val)
    (edgeCase : ∀ x : Bits, f x = false →
      f (Function.update (Function.update x e true) v false) = false ∧
      f (Function.update (Function.update x e true) v true) = true)
    (eMono : ∀ x : Bits, vl gs x d = true →
      vl gs (Function.update x e true) d = true) :
    ∀ x : Bits, vl gs x d = true → f x = true := by
  have dl : d < 9+r := (L.hcl _ _ hg).lt d (by
    rcases hop with h | h <;> rw [h] <;> simp)
  intro x hx
  cases hf : f x with
  | true => rfl
  | false =>
    let y := Function.update x e true
    let y0 := Function.update y v false
    let y1 := Function.update y v true
    have eq0 : ∀ i : Fin 9, i ≠ v → y i = y0 i := by
      intro i hi
      simp [y0,Function.update_of_ne hi]
    have eq1 : ∀ i : Fin 9, i ≠ v → y0 i = y1 i := by
      intro i hi
      simp [y0,y1,Function.update_of_ne hi]
    have hy : vl gs y d = true := eMono x hx
    have ht0 : vl gs y0 d = true := (before_agree L.hcl reader dl dne y y0 eq0).symm.trans hy
    have ht1 : vl gs y1 d = true := (before_agree L.hcl reader dl dne y0 y1 eq1).symm.trans ht0
    have hr0 : vl gs y0 (9+r) = true := by
      rw [vl_gate _ L.hcl _ _ _ hg,hor]
      rcases hop with h | h <;> simp [h,GateOp.eval,ht0]
    have hr1 : vl gs y1 (9+r) = true := by
      rw [vl_gate _ L.hcl _ _ _ hg,hor]
      rcases hop with h | h <;> simp [h,GateOp.eval,ht1]
    have hsame := after_agree L.hcl reader (out_not_primary L v) y0 y1 eq1 (hr0.trans hr1.symm)
    have values := edgeCase x hf
    change f y0 = false ∧ f y1 = true at values
    rw [L.hev y0,L.hev y1,values.1,values.2] at hsame
    contradiction

lemma saturated_or_contradiction {gs : List Gate} {o r d t : ℕ} {g : Gate} {e v : Fin 9}
    (L : Least 9 f gs o) (tail : TailGE 9 f gs t)
    (maxTail : ∀ hs out, Least 9 f hs out → ¬ TailGE 9 f hs (t+1))
    (reader : onlyReader gs v r) (hg : gs[r]? = some g)
    (hor : g.op = GateOp.or)
    (hop : g.inputs = [v.val,d] ∨ g.inputs = [d,v.val])
    (dne : d ≠ v.val)
    (edgeCase : ∀ x : Bits, f x = false →
      f (Function.update (Function.update x e true) v false) = false ∧
      f (Function.update (Function.update x e true) v true) = true)
    (eMono : ∀ x : Bits, vl gs x d = true →
      vl gs (Function.update x e true) d = true) : False := by
  have hc : ∃ x y : Bits, f x ≠ f y :=
    ⟨fun i => i == 0 || i == 7, fun _ => false, by decide⟩
  have hbelow := partner_below L reader hg hor hop dne edgeCase eMono
  have hn : ¬ TailOK 9 f gs r := by
    rintro ⟨gate,eq,n | h⟩
    · obtain rfl := Option.some.inj (eq.symm.trans hg)
      rw [hor] at n
      contradiction
    · obtain rfl := Option.some.inj (eq.symm.trans hg)
      have hv : vl gs (single v) v.val = true := by simp [vl_input gs _ _ v.isLt,single]
      have he : vl gs (single v) (9+r) = true := by
        rw [vl_gate _ L.hcl _ _ _ hg,hor]
        rcases hop with hp | hp <;> simp [hp,GateOp.eval,hv]
      have absurd := h.2 (single v) he
      rw [single_false] at absurd
      contradiction
  obtain ⟨hnew,hgrow⟩ := stmtLift 9 f gs o r v.val d g L hc hg hor hop hbelow
  exact maxTail _ _ hnew (hgrow hn t tail)

lemma false_at_neighbour {gs : List Gate} {o r a : ℕ} {e v : Fin 9}
    (L : Least 9 f gs o) (reader : onlyReader gs e r) (earlier : a < 9+r)
    (hne : a ≠ e.val) (edge : f (Function.update (single v) e true) = true)
    (orEval : ∀ x : Bits, vl gs x (9+r) = (x e || vl gs x a)) :
    vl gs (single v) a = false := by
  by_contra h
  have hx : vl gs (single v) a = true := by
    cases hh : vl gs (single v) a <;> simp_all
  let y := Function.update (single v) e true
  have agree : ∀ i : Fin 9, i ≠ e → single v i = y i := by
    intro i hi
    simp [y,Function.update_of_ne hi]
  have hy : vl gs y a = true := (before_agree L.hcl reader earlier hne _ _ agree).symm.trans hx
  have rEq : vl gs (single v) (9+r) = vl gs y (9+r) := by
    rw [orEval,orEval,hx,hy]
    simp
  have he := after_agree L.hcl reader (out_not_primary L e) _ _ agree rEq
  change f y = true at edge
  rw [L.hev,L.hev,single_false,edge] at he
  contradiction

lemma direct_case_impossible {gs : List Gate} {o r3 r4 q3 q4 a3 a4 : ℕ} (L : Least 9 f gs o)
    (r3only : onlyReader gs 3 r3) (r4only : onlyReader gs 4 r4)
    (r0 : onlyReader gs 0 q4) (r7 : onlyReader gs 7 q3)
    (a3early : a3 < 9+r3) (a4early : a4 < 9+r4) (a3beforeQ : a3 < 9+q3)
    (hna3e : a3 ≠ 3) (hna4e : a4 ≠ 4) (hna3v : a3 ≠ 7) (hna3cross : a3 ≠ 0)
    (g3eval : ∀ x : Bits, vl gs x (9+r3) = (x 3 || vl gs x a3))
    (g4eval : ∀ x : Bits, vl gs x (9+r4) = (x 4 || vl gs x a4))
    (q3eval : ∀ x : Bits, vl gs x (9+q3) = ((x 3 || vl gs x a3) && x 7))
    (q4eval : ∀ x : Bits, vl gs x (9+q4) = ((x 4 || vl gs x a4) && x 0)) :
    False := by
  let z : Bits := fun _ => false
  have s0a4 := false_at_neighbour (v:=0) L r4only a4early hna4e (by decide) g4eval
  have s7a3 := false_at_neighbour (v:=7) L r3only a3early hna3e (by decide) g3eval
  have z7 : ∀ i : Fin 9, i ≠ 7 → z i = single 7 i := by
    intro i hi
    simp [z,single,hi]
  have za3 : vl gs z a3 = false :=
    (before_agree L.hcl r7 a3beforeQ hna3v _ _ z7).trans s7a3
  have z0 : ∀ i : Fin 9, i ≠ 0 → z i = single 0 i := by
    intro i hi
    simp [z,single,hi]
  have q4z0 : vl gs z (9+q4) = vl gs (single 0) (9+q4) := by
    rw [q4eval,q4eval,s0a4]
    simp [z,single]
  have s0a3 : vl gs (single 0) a3 = false :=
    (after_agree L.hcl r0 hna3cross _ _ z0 q4z0).symm.trans za3
  let p := Function.update (single 0) 7 true
  have s07 : ∀ i : Fin 9, i ≠ 7 → single 0 i = p i := by
    intro i hi
    simp [p,Function.update_of_ne hi]
  have pa3 : vl gs p a3 = false :=
    (before_agree L.hcl r7 a3beforeQ hna3v _ _ s07).symm.trans s0a3
  have q3pair : vl gs (single 0) (9+q3) = vl gs p (9+q3) := by
    rw [q3eval,q3eval,s0a3,pa3]
    decide
  have he := after_agree L.hcl r7 (out_not_primary L 7) _ _ s07 q3pair
  have on : f p = true := by decide
  rw [L.hev,L.hev,single_false,on] at he
  contradiction

end C10980

namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers

structure TightLeaf {n : ℕ} (gs : List Gate) (e : Fin (n+1)) where
  p : ℕ
  q : ℕ
  a : ℕ
  b : ℕ
  gp : Gate
  gq : Gate
  hp : gs[p]? = some gp
  hq : gs[q]? = some gq
  hop : gp.op = GateOp.or
  hoq : gq.op = GateOp.and
  hip : gp.inputs = [e.val,a] ∨ gp.inputs = [a,e.val]
  hiq : gq.inputs = [n+1+p,b] ∨ gq.inputs = [b,n+1+p]
  only_input : ∀ j, Reads gs j e → j = p
  only_next : ∀ j, Reads gs j (n+1+p) → j = q

lemma tight_leaf_shape {n : ℕ} {f : (Fin (n+1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least (n+1) f gs o) (e : Fin (n+1)) (dep : Dep f e)
    (hc : ∀ c, ∃ x y : Fin (n+1) → Bool, f (Function.update x e c) ≠ f (Function.update y e c))
    (noF : ¬ Drop f e false 2 gs.length) (noT : ¬ Drop f e true 3 gs.length) :
    Nonempty (TightLeaf gs e) := by
  obtain ⟨p,gp,hp,hm⟩ := L.dep_read e dep hc
  have pr : Reads gs p e := ⟨gp,hp,hm⟩
  have plen := reads_len pr
  have onlyp (j : ℕ) (jr : Reads gs j e) : j = p := by
    by_contra neq
    exact noF (L.save2 e false (hc false) j p neq (rc_input false jr) (rc_input false pr))
  have go : gp.op = GateOp.or := by
    rcases L.hcl _ _ hp with ⟨hn, _⟩ | ⟨ha | ho, _⟩
    · exfalso
      have c := isC_reader L.hcl e p gp hp hm false (Or.inl hn)
      obtain ⟨j,pj,_,jRC⟩ := L.next e false (hc false) p plen c
      exact noF (L.save2 e false (hc false) p j pj.ne (rc_input false pr) jRC)
    · exfalso
      have c := isC_reader L.hcl e p gp hp hm false (Or.inr (by simp [fixBit,ha]))
      obtain ⟨j,pj,_,jRC⟩ := L.next e false (hc false) p plen c
      exact noF (L.save2 e false (hc false) p j pj.ne (rc_input false pr) jRC)
    · exact ho
  obtain ⟨a,hpa,hpv⟩ : ∃ a, (gp.inputs = [e.val,a] ∨ gp.inputs = [a,e.val]) ∧
      ∀ x, vl gs x (n+1+p) = (vl gs x e || vl gs x a) := by
    rcases gate_cases gs L.hcl p gp hp e hm with ⟨h,_,_⟩ | ⟨a,ha,⟨h,_⟩ | ⟨_,hv⟩⟩
    · cases go.symm.trans h
    · cases go.symm.trans h
    · exact ⟨a,ha,hv⟩
  have pc := isC_reader L.hcl e p gp hp hm true (Or.inr (by simp [fixBit,go]))
  have pcTrue : stF n gs e true (n+1+p) = Stat.const true := by
    obtain ⟨c,sc⟩ := pc
    have val := st_val_const n gs L.hcl e true (n+1+p) c sc (fun _ => false)
    rw [hpv,vl_input gs _ _ e.isLt] at val
    rw [sc]
    congr 1
    simpa [ins] using val.symm
  obtain ⟨q,pq,qr,qRC⟩ := L.next e true (hc true) p plen pc
  obtain ⟨gq,hq,hqm⟩ := qr
  have onlyq (j : ℕ) (jr : Reads gs j (n+1+p)) : j = q := by
    by_contra neq
    have pj := reads_lt L.hcl jr
    exact noT (L.save3 e true (hc true) p q j pq.ne (by omega) (Ne.symm neq)
      (rc_input true pr) qRC (rc_of_reads jr pc))
  have ga : gq.op = GateOp.and := by
    by_contra neq
    have qc : IsC n gs e true (n+1+q) := by
      rcases L.hcl _ _ hq with ⟨h,j,_,hj⟩ | ⟨h | h,_⟩
      · apply st_allconst n gs L.hcl e true q gq hq
        intro w hw
        rw [hj] at hqm hw
        have eq : w = n+1+p := (List.mem_singleton.mp hw).trans (List.mem_singleton.mp hqm).symm
        simpa only [eq] using pc
      · contradiction
      · apply const_read n gs L.hcl e true q gq hq (n+1+p) hqm
        simpa [fixBit,h] using pcTrue
    obtain ⟨j,qj,_,jRC⟩ := L.next e true (hc true) q (reads_len ⟨gq,hq,hqm⟩) qc
    exact noT (L.save3 e true (hc true) p q j pq.ne (by omega) qj.ne
      (rc_input true pr) qRC jRC)
  obtain ⟨b,hqb⟩ : ∃ b, gq.inputs = [n+1+p,b] ∨ gq.inputs = [b,n+1+p] := by
    rcases gate_cases gs L.hcl q gq hq (n+1+p) hqm with ⟨h,_,_⟩ | ⟨b,hb,_⟩
    · cases ga.symm.trans h
    · exact ⟨b,hb⟩
  exact ⟨⟨p,q,a,b,gp,gq,hp,hq,go,ga,hpa,hqb,onlyp,onlyq⟩⟩

end C10980

namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers C10980.EdgeFn

def notGate (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

lemma rdel_count_not (N : ℕ) (gs : List Gate) {p a : ℕ} {gp : Gate}
    (hp : gs[p]? = some gp) (oper : gp.op ≠ GateOp.not) :
    (rdel N p a gs).countP notGate = gs.countP notGate := by
  have ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp hp
  have split := (List.take_append_drop p gs).symm
  rw [List.drop_eq_getElem_cons bound, eq] at split
  have right : gs.countP notGate = (gs.take p).countP notGate + (gs.drop (p+1)).countP notGate := by
    conv => lhs; rw [split]
    have hg : notGate gp = false := by
      unfold notGate
      cases h : gp.op <;> try rfl
      exact (oper h).elim
    simp [hg]
  rw [rdel,List.countP_append,List.countP_map]
  exact right.symm

lemma rdel_keep_gate (N : ℕ) (gs : List Gate) (hcl : CleanL N gs) {p a q : ℕ} {g : Gate}
    (pl : p < gs.length) (h : gs[q]? = some g) (npq : p ≠ q) :
    (rdel N p a gs)[if q < p then q else q-1]? =
      some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
  by_cases qp : q < p
  · rw [if_pos qp,rdel_get_lt N p a gs pl q qp,h]
    have eq : g.inputs.map (rd N p a) = g.inputs := by
      conv => rhs; rw [← List.map_id g.inputs]
      apply List.map_congr_left
      intro w hw
      have wlt := (hcl q g h).lt w hw
      exact rd_lt _ _ _ _ (by omega)
    simp only [eq]
  · rw [if_neg qp,rdel_get_ge N p a gs pl (q-1) (by omega),show q-1+1=q by omega,h]
    rfl

lemma or_restriction_alias {N : ℕ} {gs : List Gate} {p a : ℕ} {g : Gate} (hcl : CleanL N gs)
    (e : Fin N) (hp : gs[p]? = some g) (oper : g.op = GateOp.or)
    (ports : g.inputs = [e.val,a] ∨ g.inputs = [a,e.val])
    (x : Fin N → Bool) (xe : x e = false) : vl gs x (N+p) = vl gs x a := by
  rw [vl_gate _ hcl x _ _ hp,oper]
  rcases ports with p | p <;> simp [p,GateOp.eval,vl_input gs x _ e.isLt,xe]

lemma remove_two_false_or {N : ℕ} {gs : List Gate} (hcl : CleanL N gs) (o : ℕ)
    (e f : Fin N) {p q a b : ℕ} {gp gq : Gate} (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (different : p ≠ q) (op : gp.op = GateOp.or) (oq : gq.op = GateOp.or)
    (pip : gp.inputs = [e.val,a] ∨ gp.inputs = [a,e.val])
    (piq : gq.inputs = [f.val,b] ∨ gq.inputs = [b,f.val]) :
    ∃ hs v, CleanL N hs ∧ hs.length + 2 = gs.length ∧ hs.countP notGate = gs.countP notGate ∧
      ∀ x : Fin N → Bool, x e = false → x f = false → vl hs x v = vl gs x o := by
  have pl := (List.getElem?_eq_some_iff.mp hp).1
  have al : a < N+p := (hcl p gp hp).lt a (by rcases pip with p | p <;> simp [p])
  let gs' := rdel N p a gs
  let q' := if q < p then q else q - 1
  let b' := rd N p a b
  let gq' : Gate := ⟨gq.op,gq.inputs.map (rd N p a)⟩
  have hq' : gs'[q']? = some gq' := rdel_keep_gate N gs hcl pl hq different
  have hcl' := rdel_clean N p a gs hcl pl al
  have ql := (List.getElem?_eq_some_iff.mp hq').1
  have pip' : gq'.inputs = [f.val,b'] ∨ gq'.inputs = [b',f.val] := by
    have same : rd N p a f = f := rd_lt _ _ _ _ (by have := f.isLt; omega)
    rcases piq with piq | piq <;> simp [gq',piq,b',same]
  have bl : b' < N+q' := (hcl' q' gq' hq').lt b' (by rcases pip' with p | p <;> simp [p])
  let hs := rdel N q' b' gs'
  have len1 := rdel_length N p a gs pl
  have len2 := rdel_length N q' b' gs' ql
  have n1 := rdel_count_not N gs (a:=a) hp (by simp [op])
  have n2 := rdel_count_not N gs' (a:=b') hq' (by simp [gq',oq])
  refine ⟨hs, rd N q' b' (rd N p a o), rdel_clean N q' b' gs' hcl' ql bl, ?_, n2.trans n1, ?_⟩
  · change (rdel N q' b' gs').length + 2 = gs.length
    change gs'.length + 1 = gs.length at len1
    omega
  · intro x xe xf
    rw [rdel_all N q' b' gs' hcl' ql bl x (or_restriction_alias hcl' f hq' oq pip' x xf),
      rdel_all N p a gs hcl pl al x (or_restriction_alias hcl e hp op pip x xe)]

end C10980

namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers C10980.Loc.Wires

lemma distinct_leaf_gates {gs : List Gate} {o : ℕ} (L : Least 9 f gs o)
    (T3 : TightLeaf gs (3 : Fin 9)) (T4 : TightLeaf gs (4 : Fin 9)) : T3.p ≠ T4.p := by
  intro eq
  let x : Bits := fun j => j == 3 || j == 7
  let y : Bits := fun j => j == 4 || j == 7
  have xval : vl gs x (9 + T3.p) = true := by
    rw [vl_gate _ L.hcl x _ _ T3.hp,T3.hop]
    have xe : vl gs x (3 : ℕ) = true := by rw [vl_input _ _ _ (by decide)]; rfl
    rcases T3.hip with h | h <;> simp [h,GateOp.eval,xe]
  have yval : vl gs y (9 + T3.p) = true := by
    rw [eq,vl_gate _ L.hcl y _ _ T4.hp,T4.hop]
    have ye : vl gs y (4 : ℕ) = true := by rw [vl_input _ _ _ (by decide)]; rfl
    rcases T4.hip with h | h <;> simp [h,GateOp.eval,ye]
  have same := ToolProp_proof 9 gs x y ({3,4} : Set ℕ) (o+1) L.hcl (by
    intro i hi
    fin_cases i <;> simp_all [x,y]) (by
    intro p g hp _ _
    by_cases h : p = T3.p
    · right
      simpa only [h] using xval.trans yval.symm
    · left
      intro a ha ham
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ham
      rcases ham with rfl | rfl
      · exact h (T3.only_input p ⟨g,hp,ha⟩)
      · exact h ((T4.only_input p ⟨g,hp,ha⟩).trans eq.symm)) o (by omega) (by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
    exact ⟨out_not_primary L 3,out_not_primary L 4⟩)
  rw [L.hev x,L.hev y] at same
  have xv : f x = true := by decide
  have yv : f y = false := by decide
  rw [xv,yv] at same
  contradiction

lemma original_not_count {gs : List Gate} {o : ℕ} (L : Least 9 f gs o) (sz : gs.length ≤ 14)
    (T3 : TightLeaf gs (3 : Fin 9)) (T4 : TightLeaf gs (4 : Fin 9))
    (hbut : C10981.Signed.Lower true C10981.Signed.bfInputs C10981.Signed.butterfly 8) :
    gs.countP notGate ≤ 1 := by
  open C10981.Signed in
  obtain ⟨hs,v,hc,hl,hn,he⟩ := remove_two_false_or L.hcl o 3 4 T3.hp T4.hp
    (distinct_leaf_gates L T3 T4) T3.hop T4.hop T3.hip T4.hip
  let C : Circuit := ⟨hs,v⟩
  have legal : FanInTwo C := fun g hg => (clean_nok 9 hs hc g hg).1
  have windEval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn (C10981.Signed.fixedInputs x)) = C10981.Signed.windF x := by
    intro x
    have ht : C.eval (List.ofFn (C10981.Signed.fixedInputs x)) = vl hs (C10981.Signed.fixedInputs x) v := rfl
    rw [ht,he _ rfl rfl,L.hev]
    exact (show ∀ x : Fin 7 → Bool, f (C10981.Signed.fixedInputs x) = C10981.Signed.windF x by decide +kernel) x
  have blow := C10981.Signed.signed_windmill_fixed hbut C legal windEval
  have ops : C10981.Signed.binaryCount C = hs.countP (fun g => !notGate g) := rfl
  rw [ops] at blow
  have total := List.length_eq_countP_add_countP notGate (l:=hs)
  have countEq : hs.countP (fun a => decide (¬ (notGate a = true))) =
      hs.countP (fun a => !notGate a) := by
    apply List.countP_congr
    intro a ha
    cases h : notGate a <;> simp [h]
  rw [countEq] at total
  have sum := Nat.add_le_add_left blow (hs.countP notGate)
  omega

end C10980


namespace C10980

open PEqualNP.CircuitLowerBounds C10980.Helpers
open C10980.Helpers.Readers C10980.Loc.Wires

lemma leaf_agree_before_consumer {n : ℕ} {gs : List Gate} {e : Fin n} {r q j : ℕ}
    (hcl : CleanL n gs)
    (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (x : Fin n → Bool) (before : j < n+q) (input : j ≠ e.val) (root : j ≠ n+r) :
    vl gs x j = vl gs (Function.update x e true) j := by
  refine ToolProp_proof n gs x (Function.update x e true) ({e.val,n+r} : Set ℕ) (n+q)
    hcl ?_ ?_ j before (by simpa using And.intro input root)
  · intro i hi
    have ine : i ≠ e := by
      intro he
      subst i
      simp at hi
    simp [Function.update_of_ne ine]
  · intro p gate hp earlier outside
    left
    intro a ha mem
    have eq : a = e.val ∨ a = n+r := by simpa using mem
    rcases eq with rfl | rfl
    · have e' := readerLeaf p ⟨gate,hp,ha⟩
      subst p
      simp at outside
    · have e' := readerRoot p ⟨gate,hp,ha⟩
      omega

lemma leaf_mono_prefix {n : ℕ} {gs : List Gate} {e : Fin n} {r q limit : ℕ} {g : Gate}
    (hcl : CleanL n gs)
    (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (lookupRoot : gs[r]? = some g) (rootNotFree : g.op ≠ GateOp.not)
    (suffix : ∀ p gate, gs[p]? = some gate → q ≤ p → n+p < limit → gate.op ≠ GateOp.not)
    (x : Fin n → Bool) :
    ∀ j < limit, vl gs x j = true → vl gs (Function.update x e true) j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro cutoff old
    by_cases primary : j < n
    · rw [vl_input gs x j primary] at old
      rw [vl_input gs (Function.update x e true) j primary]
      by_cases eq : (⟨j,primary⟩ : Fin n) = e
      · rw [eq,Function.update_self]
      · simpa only [Function.update_of_ne eq] using old
    obtain ⟨p,rfl⟩ : ∃ p, j = n+p := ⟨j-n, by omega⟩
    cases look : gs[p]? with
    | none =>
      have absent : gs.length ≤ p := List.getElem?_eq_none_iff.1 look
      rw [vl_beyond gs x (n+p) (by omega)] at old
      contradiction
    | some gate =>
      rcases hcl p gate look with ⟨nt, a, ha, hin⟩ | ⟨op, a, b, ha, hb, hin⟩
      · have earlier : n+p < n+q := by
          by_contra! late
          exact suffix p gate look (by omega) cutoff nt
        have notLeaf : n+p ≠ e.val := by have := e.isLt; omega
        have notRoot : n+p ≠ n+r := by
          intro he
          have same : p = r := by omega
          subst p
          have eq := Option.some.inj (lookupRoot.symm.trans look)
          exact rootNotFree (eq ▸ nt)
        exact (leaf_agree_before_consumer hcl readerLeaf readerRoot x earlier notLeaf notRoot).symm ▸ old
      · rw [vl_gate gs hcl x p gate look, hin] at old
        rw [vl_gate gs hcl (Function.update x e true) p gate look, hin]
        rcases op with h | h
        · rw [h] at old ⊢
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            Bool.and_true, Bool.and_eq_true, id_eq] at *
          exact ⟨ih a ha (ha.trans cutoff) old.1, ih b hb (hb.trans cutoff) old.2⟩
        · rw [h] at old ⊢
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            Bool.or_false, Bool.or_eq_true, id_eq] at *
          rcases old with ha' | hb'
          · exact Or.inl (ih a ha (ha.trans cutoff) ha')
          · exact Or.inr (ih b hb (hb.trans cutoff) hb')

lemma leaf_mono_before {n : ℕ} {gs : List Gate} {e : Fin n} {r q j : ℕ} {g : Gate}
    (hcl : CleanL n gs)
    (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (lookupRoot : gs[r]? = some g) (rootNotFree : g.op ≠ GateOp.not)
    (before : j < n+q) (x : Fin n → Bool) :
    vl gs x j = true → vl gs (Function.update x e true) j = true :=
  leaf_mono_prefix (limit := n+q) hcl readerLeaf readerRoot lookupRoot rootNotFree
    (fun p _ _ h late => False.elim (by omega)) x j before

lemma leaf_mono_suffix {n : ℕ} {gs : List Gate} {e : Fin n} {r q j : ℕ} {g : Gate}
    (hcl : CleanL n gs)
    (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (lookupRoot : gs[r]? = some g) (rootNotFree : g.op ≠ GateOp.not)
    (suffix : ∀ p gate, gs[p]? = some gate → q ≤ p → gate.op ≠ GateOp.not)
    (x : Fin n → Bool) :
    vl gs x j = true → vl gs (Function.update x e true) j = true :=
  leaf_mono_prefix (limit := j+1) hcl readerLeaf readerRoot lookupRoot rootNotFree
    (fun p gate hp hq _ => suffix p gate hp hq) x j (by omega)

lemma agrees_if_consumer_agrees {n : ℕ} {gs : List Gate} {e : Fin n} {r q j : ℕ}
    (hcl : CleanL n gs) (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (x y : Fin n → Bool) (outside : ∀ i : Fin n, i ≠ e → x i = y i)
    (consumer : vl gs x (n+q) = vl gs y (n+q)) (input : j ≠ e.val) (root : j ≠ n+r) :
    vl gs x j = vl gs y j := by
  refine ToolProp_proof n gs x y ({e.val,n+r} : Set ℕ) (j+1)
    hcl ?_ ?_ j (by omega) (by simpa using And.intro input root)
  · intro i hi
    apply outside
    intro eq
    subst i
    simp at hi
  · intro p gate hp _ hgate
    by_cases hq : p = q
    · right
      simpa only [hq] using consumer
    · left
      intro a ha mem
      have eq : a = e.val ∨ a = n+r := by simpa using mem
      rcases eq with rfl | rfl
      · have same := readerLeaf p ⟨gate,hp,ha⟩
        subst p
        simp at hgate
      · exact hq (readerRoot p ⟨gate,hp,ha⟩)

lemma pivotal_consumer_partner {n : ℕ} {gs : List Gate} {e : Fin n} {r q b o : ℕ}
    (hcl : CleanL n gs) (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (gatePartner : ∀ x : Fin n → Bool, vl gs x (n+q) = (vl gs x (n+r) && vl gs x b))
    (partnerEarlier : b < n+q) (partnerInput : b ≠ e.val) (partnerRoot : b ≠ n+r)
    (outputInput : o ≠ e.val) (outputRoot : o ≠ n+r)
    (x : Fin n → Bool)
    (pivotal : vl gs x o ≠ vl gs (Function.update x e true) o) :
    vl gs x b = true := by
  let y := Function.update x e true
  have partition : ∀ i : Fin n, i ≠ e → x i = y i := by
    intro i hi
    simp [y,Function.update_of_ne hi]
  have agree : vl gs x b = vl gs y b :=
    leaf_agree_before_consumer hcl readerLeaf readerRoot x partnerEarlier partnerInput partnerRoot
  cases old : vl gs x b with
  | true => rfl
  | false =>
    have off := old.symm.trans agree
    have same : vl gs x (n+q) = vl gs y (n+q) := by
      simp only [gatePartner,old,← off,Bool.and_false]
    exact (pivotal (agrees_if_consumer_agrees hcl readerLeaf readerRoot x y partition same
      outputInput outputRoot)).elim

lemma true_at_zero_has_not {n : ℕ} {gs : List Gate} (hcl : CleanL n gs) :
    ∀ j, vl gs (fun _ : Fin n => false) j = true →
      ∃ p gate, gs[p]? = some gate ∧ n+p ≤ j ∧ gate.op = GateOp.not := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro on
    by_cases primary : j < n
    · rw [vl_input gs _ j primary] at on
      contradiction
    obtain ⟨p,rfl⟩ : ∃ p, j = n+p := ⟨j-n, by omega⟩
    cases found : gs[p]? with
    | none =>
      have absent : gs.length ≤ p := List.getElem?_eq_none_iff.1 found
      rw [vl_beyond gs _ (n+p) (by omega)] at on
      contradiction
    | some gate =>
      rcases hcl p gate found with ⟨notop, _⟩ | ⟨op,a,b,ha,hb,ins⟩
      · exact ⟨p,gate,found,le_rfl,notop⟩
      · rw [vl_gate gs hcl _ p gate found,ins] at on
        have pos : ∃ c, c < n+p ∧ vl gs (fun _ : Fin n => false) c = true := by
          rcases op with hop | hop
          · rw [hop] at on
            simp [GateOp.eval] at on
            exact ⟨a,ha,on.1⟩
          · rw [hop] at on
            simp [GateOp.eval] at on
            rcases on with yes | yes
            · exact ⟨a,ha,yes⟩
            · exact ⟨b,hb,yes⟩
        obtain ⟨c, hcb, hc⟩ := pos
        obtain ⟨k,g,hg,kle,hop⟩ := ih c hcb hc
        exact ⟨k,g,hg,kle.trans hcb.le,hop⟩

def isNotOp (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

lemma isNotOp_true {g : Gate} : isNotOp g = true ↔ g.op = GateOp.not := by
  unfold isNotOp
  cases g.op <;> simp

lemma two_counted_indices {α : Type} {xs : List α} {predicate : α → Bool}
    {p q : ℕ} {a b : α} (lt : p < q) (ha : xs[p]? = some a)
    (hb : xs[q]? = some b) (pa : predicate a = true) (pb : predicate b = true) :
    2 ≤ xs.countP predicate := by
  induction xs generalizing p q with
  | nil => simp at ha
  | cons x xs ih =>
    cases p with
    | zero =>
      cases q with
      | zero => omega
      | succ q =>
        have e : x = a := by simpa using ha
        have inside : xs[q]? = some b := by simpa using hb
        have h : 0 < xs.countP predicate := by
          rw [List.countP_pos_iff]
          exact ⟨b,List.mem_of_getElem? inside,pb⟩
        rw [List.countP_cons, e, pa]
        change 2 ≤ xs.countP predicate + 1
        omega
    | succ p =>
      cases q with
      | zero => omega
      | succ q =>
        have h := ih (Nat.lt_of_succ_lt_succ lt) (by simpa using ha) (by simpa using hb)
        rw [List.countP_cons]
        exact h.trans (Nat.le_add_right _ _)

lemma no_not_at_or_after {gs : List Gate} {r q : ℕ} {g : Gate}
    (early : r < q) (get : gs[r]? = some g) (notEarly : g.op = GateOp.not)
    (cap : gs.countP isNotOp ≤ 1) :
    ∀ p gate, gs[p]? = some gate → q ≤ p → gate.op ≠ GateOp.not := by
  intro p gate hp late no
  have two := two_counted_indices (predicate := isNotOp) (early.trans_le late) get hp
    (isNotOp_true.mpr notEarly) (isNotOp_true.mpr no)
  omega

lemma pruned_or_not_output {n : ℕ} {gs : List Gate} {e : Fin n} {r o : ℕ} {g : Gate}
    (hcl : CleanL n gs) (lookupRoot : gs[r]? = some g) (isOr : g.op = GateOp.or)
    (rp : e.val ∈ g.inputs)
    (off : vl gs (fun i : Fin n => decide (i = e)) o = false) :
    o ≠ n+r := by
  intro eq
  subst o
  have on : vl gs (fun i : Fin n => decide (i = e)) (n+r) = true := by
    rw [vl_gate gs hcl _ r g lookupRoot, isOr]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    exact ⟨true, ⟨e.val, rp, by simp [vl_input gs _ _ e.isLt]⟩, rfl⟩
  rw [off] at on
  contradiction

lemma leaf_mono_for_partner {n : ℕ} {gs : List Gate} {e v : Fin n}
    {r q rv b d o : ℕ} {g andGate : Gate}
    (hcl : CleanL n gs)
    (readerLeaf : ∀ p, Reads gs p e.val → p = r)
    (readerRoot : ∀ p, Reads gs p (n+r) → p = q)
    (readerNeighbour : ∀ p, Reads gs p v.val → p = rv)
    (lookupRoot : gs[r]? = some g) (rootNotFree : g.op ≠ GateOp.not)
    (lookupConsumer : gs[q]? = some andGate) (consumerAnd : andGate.op = GateOp.and)
    (consumerReads : andGate.inputs = [n+r,b] ∨ andGate.inputs = [b,n+r])
    (bNotRoot : b ≠ n+r) (count : gs.countP isNotOp ≤ 1)
    (outputInput : o ≠ e.val) (outputRoot : o ≠ n+r)
    (pivotal : vl gs (fun i : Fin n => decide (i = v)) o ≠
      vl gs (Function.update (fun i : Fin n => decide (i = v)) e true) o)
    (beforeNeighbour : d < n+rv) (x : Fin n → Bool) :
    vl gs x d = true → vl gs (Function.update x e true) d = true := by
  by_cases early : d < n+q
  · exact leaf_mono_before hcl readerLeaf readerRoot lookupRoot rootNotFree early x
  have late : q < rv := by omega
  have qReadsRoot : n+r ∈ andGate.inputs := by
    rcases consumerReads with hp | hp <;> simp [hp]
  have qReadsB : b ∈ andGate.inputs := by
    rcases consumerReads with hp | hp <;> simp [hp]
  have rEarlier : r < q := by
    have := (hcl q andGate lookupConsumer).lt (n+r) qReadsRoot
    omega
  have bEarlier : b < n+q := (hcl q andGate lookupConsumer).lt b qReadsB
  have bNotLeaf : b ≠ e.val := by
    intro h
    have rel : Reads gs q e.val := ⟨andGate,lookupConsumer,h ▸ qReadsB⟩
    exact (Nat.ne_of_gt rEarlier) (readerLeaf q rel)
  have bNotNeighbour : b ≠ v.val := by
    intro h
    have rel : Reads gs q v.val := ⟨andGate,lookupConsumer,h ▸ qReadsB⟩
    exact (Nat.ne_of_lt late) (readerNeighbour q rel)
  have gatePartner (y : Fin n → Bool) :
      vl gs y (n+q) = (vl gs y (n+r) && vl gs y b) := by
    rw [vl_gate gs hcl y q andGate lookupConsumer,consumerAnd]
    rcases consumerReads with hp | hp <;> simp [hp,GateOp.eval,Bool.and_comm]
  have bTrue := pivotal_consumer_partner hcl readerLeaf readerRoot gatePartner
    bEarlier bNotLeaf bNotRoot outputInput outputRoot _ pivotal
  have unchanged : vl gs (fun _ : Fin n => false) b =
      vl gs (fun i : Fin n => decide (i = v)) b := by
    refine ToolProp_proof n gs _ _ ({v.val} : Set ℕ) (n+q) hcl ?_ ?_ b bEarlier ?_
    · intro i hi
      have h : i ≠ v := by rintro rfl; simp at hi
      simp [h]
    · intro p gate hp earlier _
      left
      intro a ha mem
      have eq : a = v.val := by simpa using mem
      subst a
      have same := readerNeighbour p ⟨gate,hp,ha⟩
      omega
    · simpa using bNotNeighbour
  obtain ⟨k,gate,hk,earlier,neg⟩ := true_at_zero_has_not hcl b (unchanged.trans bTrue)
  exact leaf_mono_suffix hcl readerLeaf readerRoot lookupRoot rootNotFree
    (no_not_at_or_after (by omega) hk neg count) x

end C10980


namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers C10980.EdgeFn

lemma cut_keep_gate (N : ℕ) (gs : List Gate) (hcl : CleanL N gs) {p a q : ℕ} {g : Gate}
    (pl : p < gs.length) (h : gs[q]? = some g) (npq : p ≠ q) :
    (rdel N p a gs)[if q < p then q else q-1]? =
      some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
  by_cases qp : q < p
  · rw [ite_eq_left qp,rdel_get_lt N p a gs pl q qp,h]
    have eq : g.inputs.map (rd N p a) = g.inputs := by
      conv => rhs; rw [← List.map_id g.inputs]
      apply List.map_congr_left
      intro w hw
      have wlt := (hcl q g h).lt w hw
      exact rd_lt _ _ _ _ (by omega)
    simp only [eq]
  · rw [ite_eq_right qp,rdel_get_ge N p a gs pl (q-1) (by omega),show q-1+1=q by omega,h]
    rfl

open C10980.Loc.Wires

private def cutIndex (p j : ℕ) : ℕ := if j < p then j else j-1

private lemma cutIndex_injective {p j k : ℕ} (hj : j ≠ p) (hk : k ≠ p)
    (heq : cutIndex p j = cutIndex p k) : j = k := by
  unfold cutIndex at heq
  split_ifs at heq <;> omega

private lemma rdel_original_gate (N : ℕ) (gs : List Gate) (hcl : CleanL N gs)
    {p a j : ℕ} {g : Gate} (pl : p < gs.length) (h : (rdel N p a gs)[j]? = some g) :
    ∃ k old, gs[k]? = some old ∧ k ≠ p ∧ cutIndex p k = j ∧
      g = ⟨old.op, old.inputs.map (rd N p a)⟩ := by
  by_cases hj : j < p
  · have hold : gs[j]? = some g := by rwa [rdel_get_lt N p a gs pl j hj] at h
    have keep := cut_keep_gate N gs hcl (a:=a) pl hold (by omega)
    rw [ite_eq_left hj, h] at keep
    exact ⟨j, g, hold, by omega, ite_eq_left hj, Option.some.inj keep⟩
  · rw [rdel_get_ge N p a gs pl j (by omega)] at h
    cases hold : gs[j+1]? with
    | none => simp [hold] at h
    | some old =>
      refine ⟨j+1, old, hold, by omega, ?_, ?_⟩
      · simp [cutIndex, show ¬ j+1 < p by omega]
      · simpa [hold, eq_comm] using h

private lemma rd_primary_iff {N p a w v : ℕ} (hv : v < N) (hav : a ≠ v) :
    rd N p a w = v ↔ w = v := by
  unfold rd
  split_ifs <;> omega

private lemma rd_preceding_iff {N p a w v : ℕ} (hv : v < N + p) (hav : a ≠ v) :
    rd N p a w = v ↔ w = v := by
  unfold rd
  split_ifs <;> omega

private lemma wire_agree_no_input {N : ℕ} {hs : List Gate} (hcl : CleanL N hs) (e : Fin N)
    (noE : ∀ j, ¬ Reads hs j e) (x : Fin N → Bool) (value : Bool) (w : ℕ) (hne : w ≠ e.val) :
    vl hs x w = vl hs (Function.update x e value) w := by
  refine ToolProp_proof N hs x (Function.update x e value) ({e.val} : Set ℕ) (w+1)
    hcl ?_ ?_ w (by omega) (by simpa using hne)
  · intro i hi
    have ine : i ≠ e := fun h => hi (by simp [h])
    simp [Function.update_of_ne ine]
  · intro j g hj _ _
    left
    intro k hk hke
    have eq : k = e.val := by simpa using hke
    exact noE j ⟨g,hj,eq ▸ hk⟩

private lemma or_value_true {N : ℕ} {gs : List Gate} {e : Fin N} {p a : ℕ} {g : Gate}
    (hcl : CleanL N gs) (hp : gs[p]? = some g) (op : g.op = GateOp.or)
    (ports : g.inputs = [e.val,a] ∨ g.inputs = [a,e.val]) (x : Fin N → Bool)
    (xe : x e = true) : vl gs x (N+p) = true := by
  rw [vl_gate gs hcl x p g hp,op]
  rcases ports with h | h <;> simp [h,GateOp.eval,vl_input gs x _ e.isLt,xe]

private lemma and_value_of_true {N : ℕ} {gs : List Gate} {p q b : ℕ} {g : Gate}
    (hcl : CleanL N gs) (hq : gs[q]? = some g) (op : g.op = GateOp.and)
    (ports : g.inputs = [N+p,b] ∨ g.inputs = [b,N+p]) (x : Fin N → Bool)
    (hx : vl gs x (N+p) = true) : vl gs x (N+q) = vl gs x b := by
  rw [vl_gate gs hcl x q g hq,op]
  rcases ports with h | h <;> simp [h,GateOp.eval,hx]

def cutTrue (N p q e b : ℕ) (gs : List Gate) : List Gate :=
  rdel N p e (rdel N q b gs)

def cutWire (N p q e b w : ℕ) : ℕ := rd N p e (rd N q b w)

def cutGate (p q j : ℕ) : ℕ := cutIndex p (cutIndex q j)

lemma cut_gate_injective {p q j k : ℕ} (hpq : p < q)
    (hjp : j ≠ p) (hjq : j ≠ q) (hkp : k ≠ p) (hkq : k ≠ q)
    (heq : cutGate p q j = cutGate p q k) : j = k := by
  have eq : cutIndex q p = p := ite_eq_left hpq
  apply cutIndex_injective hjq hkq
  apply cutIndex_injective _ _ heq
  · intro h
    exact hjp (cutIndex_injective hjq hpq.ne (h.trans eq.symm))
  · intro h
    exact hkp (cutIndex_injective hkq hpq.ne (h.trans eq.symm))

lemma cut_keep {N : ℕ} {gs : List Gate} {p q e b j : ℕ} {g : Gate}
    (hcl : CleanL N gs) (pq : p < q) (ql : q < gs.length) (bl : b < N+q)
    (hj : gs[j]? = some g) (hjp : j ≠ p) (hjq : j ≠ q) :
    (cutTrue N p q e b gs)[cutGate p q j]? = some ⟨g.op,g.inputs.map (cutWire N p q e b)⟩ := by
  have hcl' := rdel_clean N q b gs hcl ql bl
  have pl : p < (rdel N q b gs).length := by have := rdel_length N q b gs ql; omega
  have hj' := cut_keep_gate N gs hcl (a:=b) ql hj hjq.symm
  have hne : p ≠ cutIndex q j := by
    intro eq
    exact hjp (cutIndex_injective hjq pq.ne (eq.symm.trans (ite_eq_left pq).symm))
  have keep := cut_keep_gate N (rdel N q b gs) hcl' (a:=e) pl hj' hne
  simp only [List.map_map, Function.comp_def] at keep
  exact keep

private lemma cut_original {N : ℕ} {gs : List Gate} {p q e b j : ℕ} {g : Gate}
    (hcl : CleanL N gs) (pq : p < q) (ql : q < gs.length) (bl : b < N+q)
    (hj : (cutTrue N p q e b gs)[j]? = some g) :
    ∃ k old, gs[k]? = some old ∧ k ≠ p ∧ k ≠ q ∧ cutGate p q k = j ∧
      g = ⟨old.op,old.inputs.map (cutWire N p q e b)⟩ := by
  have hcl' := rdel_clean N q b gs hcl ql bl
  have pl : p < (rdel N q b gs).length := by have := rdel_length N q b gs ql; omega
  obtain ⟨k,g',hk,ne,idx,e1⟩ := rdel_original_gate N _ hcl' pl hj
  obtain ⟨l,g0,hl,nq,idx',e2⟩ := rdel_original_gate N gs hcl ql hk
  have np : l ≠ p := by
    rintro rfl
    exact ne ((ite_eq_left pq).symm.trans idx').symm
  refine ⟨l,g0,hl,np,nq,?_,?_⟩
  · rw [cutGate,idx',idx]
  · rw [e1,e2]
    simp [cutWire,List.map_map,Function.comp_def]

lemma cut_primary {N : ℕ} {v : Fin N} {p q e b : ℕ} :
    cutWire N p q e b v.val = v.val := by
  have vq := rd_lt N q b v.val (by have := v.isLt; omega)
  have vp := rd_lt N p e v.val (by have := v.isLt; omega)
  rw [cutWire,vq,vp]

lemma cut_redirect_consumer {N : ℕ} {v : Fin N} {p q e : ℕ} :
    cutWire N p q e v.val (N+q) = v.val := by
  rw [cutWire,rd_eq,rd_lt _ _ _ _ (by have := v.isLt; omega)]

lemma cut_reads {N : ℕ} {gs : List Gate} {p q e b j w : ℕ}
    (hcl : CleanL N gs) (pq : p < q) (ql : q < gs.length) (bl : b < N+q)
    (hj : Reads gs j w) (hjp : j ≠ p) (hjq : j ≠ q) :
    Reads (cutTrue N p q e b gs) (cutGate p q j) (cutWire N p q e b w) := by
  obtain ⟨g,hg,hw⟩ := hj
  exact ⟨_,cut_keep hcl pq ql bl hg hjp hjq,List.mem_map.mpr ⟨w,hw,rfl⟩⟩

lemma cut_true_least {N : ℕ} {gs : List Gate} {f : (Fin N → Bool) → Bool} {o : ℕ}
    (L : Least N f gs o) (e : Fin N) {p q a b : ℕ} {gp gq : Gate}
    (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (hop : gp.op = GateOp.or) (hoq : gq.op = GateOp.and)
    (hip : gp.inputs = [e.val,a] ∨ gp.inputs = [a,e.val])
    (hiq : gq.inputs = [N+p,b] ∨ gq.inputs = [b,N+p])
    (onlyP : ∀ j, Reads gs j e → j = p)
    (onlyQ : ∀ j, Reads gs j (N+p) → j = q)
    (hc : ∃ x y, f (Function.update x e true) ≠ f (Function.update y e true))
    (noT : ¬ Drop f e true 3 gs.length) :
    Least N (fun x => f (Function.update x e true)) (cutTrue N p q e.val b gs)
      (cutWire N p q e.val b o) ∧
      (cutTrue N p q e.val b gs).length + 2 = gs.length := by
  have ql := (List.getElem?_eq_some_iff.mp hq).1
  have pr : N+p ∈ gq.inputs := by rcases hiq with h | h <;> simp [h]
  have br : b ∈ gq.inputs := by rcases hiq with h | h <;> simp [h]
  have pq : p < q := by have := (L.hcl q gq hq).lt (N+p) pr; omega
  have bl := (L.hcl q gq hq).lt b br
  have be : b ≠ e.val := by
    intro h
    have := onlyP q ⟨gq,hq,h ▸ br⟩
    omega
  have bp : b ≠ N+p := by
    intro h
    apply L.no_alias (by obtain ⟨x,y,hxy⟩ := hc; exact ⟨_,_,hxy⟩) q ql b bl
    intro x
    rw [vl_gate gs L.hcl x q gq hq,hoq]
    rcases hiq with i | i <;> simp [i,h,GateOp.eval]
  let hs := rdel N q b gs
  let ts := cutTrue N p q e.val b gs
  have hcl' := rdel_clean N q b gs L.hcl ql bl
  have ls : hs.length + 1 = gs.length := rdel_length N q b gs ql
  have pl : p < hs.length := by omega
  have el : e.val < N+p := by have := e.isLt; omega
  have hcl : CleanL N ts := rdel_clean N p e.val hs hcl' pl el
  have lt : ts.length + 2 = gs.length := by
    have del : ts.length + 1 = hs.length := rdel_length N p e.val hs pl
    omega
  have eval_fixed (x : Fin N → Bool) (xe : x e = true) :
      vl ts x (cutWire N p q e.val b o) = f x := by
    have score := or_value_true L.hcl hp hop hip x xe
    have first := rdel_all N q b gs L.hcl ql bl x (and_value_of_true L.hcl hq hoq hiq x score)
    have portEq : vl hs x (N+p) = vl hs x e.val := by
      have eq := first (N+p)
      rw [rd_lt _ _ _ _ (by omega)] at eq
      rw [eq, score,vl_input hs x _ e.isLt,xe]
    exact (rdel_all N p e.val hs hcl' pl el x portEq (rd N q b o)).trans
      ((first o).trans (L.hev x))
  have noE : ∀ j, ¬ Reads ts j e := by
    intro j h
    obtain ⟨g,hg,hr⟩ := h
    obtain ⟨k,old,hk,np,nq,_,rfl⟩ := cut_original L.hcl pq ql bl hg
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hr
    have eq' := (show rd N p e.val (rd N q b w) = e.val from eq)
    by_cases hwq : rd N q b w = N+p
    · have wq := (rd_preceding_iff (w:=w) (by omega : N+p < N+q) bp).mp hwq
      exact nq (onlyQ k ⟨old,hk,wq ▸ hw⟩)
    · have e' : rd N q b w = e.val := by
        rcases lt_or_gt_of_ne hwq with before | after
        · rwa [rd_lt _ _ _ _ before] at eq'
        · rw [rd_gt _ _ _ _ after] at eq'
          have := e.isLt
          omega
      have we := (rd_primary_iff e.isLt be).mp e'
      exact np (onlyP k ⟨old,hk,we ▸ hw⟩)
  have outne : cutWire N p q e.val b o ≠ e.val := by
    intro h
    obtain ⟨x,y,hxy⟩ := hc
    apply hxy
    rw [← eval_fixed _ (Function.update_self e true x),
      ← eval_fixed _ (Function.update_self e true y),h]
    simp [vl_input ts _ _ e.isLt]
  have eval_all (x : Fin N → Bool) :
      vl ts x (cutWire N p q e.val b o) = f (Function.update x e true) := by
    rw [wire_agree_no_input hcl e noE x true _ outne]
    exact eval_fixed _ (Function.update_self e true x)
  refine ⟨⟨hcl,eval_all,?_⟩,lt⟩
  intro us u uh uv
  change ts.length ≤ us.length
  by_contra hm
  have hs : HasCircuitSize N (fun x => f (Function.update x e true)) us.length := by
    have eq : (fun x : Fin N → Bool => vl us x u) = fun x => f (Function.update x e true) :=
      funext uv
    rw [← eq]
    exact has_of_clean N us u uh
  exact noT ⟨us.length,by omega,hs⟩

lemma least_dep_read_false {N : ℕ} {gs : List Gate} {f : (Fin N → Bool) → Bool}
    {o : ℕ} (L : Least N f gs o) (v : Fin N) (hd : Dep f v)
    (hc : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) :
    ∃ r, Reads gs r v := by
  by_contra h
  have noV (j : ℕ) : ¬ Reads gs j v := fun hj => h ⟨j,hj⟩
  have out : o ≠ v.val := by
    rintro rfl
    obtain ⟨x,y,he⟩ := hc
    apply he
    rw [← L.hev,← L.hev]
    simp [vl_input gs _ _ v.isLt]
  obtain ⟨x,hx⟩ := hd
  apply hx
  rw [← L.hev,← L.hev]
  exact (wire_agree_no_input L.hcl v noV x (!x v) o out).symm

lemma cofactor_save_one_false {n : ℕ} {f : (Fin (n+1) → Bool) → Bool}
    (v : Fin (n+1)) (hd : Dep f v)
    (hc : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false))
    {s : ℕ} (hC : HasCircuitSize (n+1) f s) : Drop f v false 1 s := by
  obtain ⟨gs,o,L,sz⟩ := exists_least (n+1) f s (dep_nc hd) hC
  obtain ⟨r,rv⟩ := least_dep_read_false L v hd hc
  have drop := L.save v false hc {r} (by
    intro j hj
    have eq : j = r := Finset.mem_singleton.mp hj
    subst j
    exact rc_input false rv)
  rw [Finset.card_singleton] at drop
  exact drop.mono (le_refl 1) sz

private lemma cut_false_unique_or {n : ℕ} {gs : List Gate} {f : (Fin (n+1) → Bool) → Bool}
    {o : ℕ} (L : Least (n+1) f gs o) (v : Fin (n+1)) (hd : Dep f v)
    (hc : ∃ x y, f (Function.update x v false) ≠ f (Function.update y v false))
    (noF : ¬ Drop f v false 2 gs.length) :
    ∃ r g, gs[r]? = some g ∧ v.val ∈ g.inputs ∧ g.op = GateOp.or ∧
      ∀ j, Reads gs j v → j = r := by
  obtain ⟨r,g,hg,hm⟩ := least_dep_read_false L v hd hc
  have rr : Reads gs r v := ⟨g,hg,hm⟩
  have rl := reads_len rr
  have only (j : ℕ) (jr : Reads gs j v) : j = r := by
    by_contra h
    exact noF (L.save2 v false hc j r h (rc_input false jr) (rc_input false rr))
  have op : g.op = GateOp.or := by
    rcases L.hcl _ _ hg with ⟨hn, _⟩ | ⟨ha | ho, _⟩
    · exfalso
      have c := isC_reader L.hcl v r g hg hm false (Or.inl hn)
      obtain ⟨j,rj,_,jRC⟩ := L.next v false hc r rl c
      exact noF (L.save2 v false hc r j rj.ne (rc_input false rr) jRC)
    · exfalso
      have c := isC_reader L.hcl v r g hg hm false (Or.inr (by simp [fixBit,ha]))
      obtain ⟨j,rj,_,jRC⟩ := L.next v false hc r rl c
      exact noF (L.save2 v false hc r j rj.ne (rc_input false rr) jRC)
    · exact ho
  exact ⟨r,g,hg,hm,op,only⟩

private lemma cut_cannot_read_both {N : ℕ} {gs : List Gate} {f : (Fin N → Bool) → Bool}
    {p q j e o : ℕ} {v : Fin N}
    (hcl : CleanL N gs) (pq : p < q) (ql : q < gs.length)
    (C : Least N f (cutTrue N p q e v.val gs) o)
    (nc : ∃ x y, f x ≠ f y)
    (hv : Reads gs j v) (hq : Reads gs j (N+q)) : False := by
  have qj : q < j := by have := reads_lt hcl hq; omega
  obtain ⟨g,hg,vMem⟩ := hv
  obtain ⟨g',hg',qMem⟩ := hq
  have eq : g' = g := Option.some.inj (hg'.symm.trans hg)
  subst g'
  have vq : v.val ≠ N+q := by have := v.isLt; omega
  have vl : v.val < N+q := by have := v.isLt; omega
  have keep := cut_keep hcl pq ql vl (e:=e) hg (by omega) qj.ne'
  have shape : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [v.val,N+q] ∨ g.inputs = [N+q,v.val]) := by
    rcases hcl j g hg with ⟨_,w,_,ports⟩ | ⟨hop,a,b,_,_,ports⟩
    · rw [ports] at vMem qMem
      exact (vq ((List.mem_singleton.mp vMem).trans (List.mem_singleton.mp qMem).symm)).elim
    · refine ⟨hop,?_⟩
      rw [ports] at vMem qMem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at vMem qMem
      rcases vMem with h | h <;> rcases qMem with h' | h'
      · exact (vq (h.trans h'.symm)).elim
      · left
        rw [ports,← h,← h']
      · right
        rw [ports,← h,← h']
      · exact (vq (h.trans h'.symm)).elim
  have jl := (List.getElem?_eq_some_iff.mp keep).1
  have vj : v.val < N + cutGate p q j := by have := v.isLt; omega
  apply C.no_alias nc (cutGate p q j) jl v.val vj
  intro x
  rw [vl_gate _ C.hcl x _ _ keep]
  rcases shape.1 with op | op <;> rcases shape.2 with h | h <;>
    simp [op,h,cut_primary (v:=v),cut_redirect_consumer (v:=v),GateOp.eval]

lemma leaf_neighbour_reader {n : ℕ} {gs : List Gate} {f : (Fin (n+1) → Bool) → Bool} {o : ℕ}
    (L : Least (n+1) f gs o) (e v : Fin (n+1)) (ev : e ≠ v) {p q a b : ℕ} {gp gq : Gate}
    (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (hop : gp.op = GateOp.or) (hoq : gq.op = GateOp.and)
    (hip : gp.inputs = [e.val,a] ∨ gp.inputs = [a,e.val])
    (hiq : gq.inputs = [n+1+p,b] ∨ gq.inputs = [b,n+1+p])
    (onlyP : ∀ j, Reads gs j e → j = p)
    (onlyQ : ∀ j, Reads gs j (n+1+p) → j = q)
    (noav : a ≠ v.val)
    (dep : Dep (fun x => f (Function.update x e true)) v)
    (hc : ∃ x y, f (Function.update (Function.update x v false) e true) ≠
      f (Function.update (Function.update y v false) e true))
    (noT : ¬ Drop f e true 3 gs.length)
    (noVF : ¬ Drop (fun x => f (Function.update x e true)) v false 4 gs.length) :
    (b = v.val ∧ ∀ j, Reads gs j v → j = q) ∨
      (b ≠ v.val ∧ ∃ r g, gs[r]? = some g ∧ v.val ∈ g.inputs ∧ g.op = GateOp.or ∧
        ∀ j, Reads gs j v → j = r) := by
  let N := n+1
  let F := fun x => f (Function.update x e true)
  have ncF : ∃ x y, F x ≠ F y := by obtain ⟨x,y,h⟩ := hc; exact ⟨_,_,h⟩
  have ncf : ∃ x y, f x ≠ f y := by obtain ⟨x,y,h⟩ := hc; exact ⟨_,_,h⟩
  obtain ⟨C,len⟩ := cut_true_least L e hp hq hop hoq hip hiq onlyP onlyQ ncF noT
  let ts := cutTrue N p q e.val b gs
  have noF : ¬ Drop F v false 2 ts.length := by
    rintro ⟨s,hs,hC⟩
    exact noVF ⟨s,by change ts.length+2 = gs.length at len; omega,hC⟩
  obtain ⟨r,g,hr,hm,op,only⟩ := cut_false_unique_or C v dep hc noF
  have ev' : e.val ≠ v.val := fun h => ev (Fin.ext h)
  have np (j : ℕ) (hj : Reads gs j v) : j ≠ p := by
    rintro rfl
    obtain ⟨g',hg',hv⟩ := hj
    have eq := Option.some.inj (hg'.symm.trans hp)
    subst g'
    rcases hip with h | h <;> simp [h,ev'.symm,noav.symm] at hv
  have ql := (List.getElem?_eq_some_iff.mp hq).1
  have pr : N+p ∈ gq.inputs := by rcases hiq with h | h <;> simp [h,N]
  have br : b ∈ gq.inputs := by rcases hiq with h | h <;> simp [h]
  have pq : p < q := by have := (L.hcl q gq hq).lt (N+p) pr; dsimp [N] at *; omega
  have bl := (L.hcl q gq hq).lt b br
  by_cases bEq : b = v.val
  · left
    refine ⟨bEq,?_⟩
    subst b
    have out : o ≠ N+q := by
      intro he
      obtain ⟨x,y,h⟩ := hc
      apply h
      have eo : cutWire N p q e.val v.val o = v.val := by rw [he,cut_redirect_consumer (v:=v)]
      rw [← C.hev,← C.hev,eo]
      simp [vl_input _ _ _ v.isLt]
    obtain ⟨k,qk,hk⟩ := L.live ncf q ql out
    have hkr := cut_reads (e:=e.val) L.hcl pq ql bl hk (by omega) qk.ne'
    rw [cut_redirect_consumer (v:=v)] at hkr
    intro j hj
    by_contra jq
    have hjr := cut_reads (e:=e.val) L.hcl pq ql bl hj (np j hj) jq
    rw [cut_primary (v:=v)] at hjr
    have eq := cut_gate_injective pq (np j hj) jq (by omega) qk.ne'
      ((only _ hjr).trans (only _ hkr).symm)
    subst j
    exact cut_cannot_read_both (e:=e.val) L.hcl pq ql C ncF hj hk
  · right
    refine ⟨bEq,?_⟩
    have nq (j : ℕ) (hj : Reads gs j v) : j ≠ q := by
      rintro rfl
      obtain ⟨g',hg',hv⟩ := hj
      have eq := Option.some.inj (hg'.symm.trans hq)
      subst g'
      have vlt : v.val ≠ N+p := by have := v.isLt; dsimp [N] at *; omega
      rcases hiq with h | h <;> simp [N,h,vlt,Ne.symm bEq] at hv
    obtain ⟨k,old,hk,kp,kq,idx,eg⟩ := cut_original L.hcl pq ql bl hr
    rw [eg] at hm op
    obtain ⟨w,hw,he⟩ := List.mem_map.mp hm
    have hwe : w = v.val := by
      change rd N p e.val (rd N q b w) = v.val at he
      exact (rd_primary_iff v.isLt bEq).mp ((rd_primary_iff v.isLt ev').mp he)
    have kr : Reads gs k v := ⟨old,hk,hwe ▸ hw⟩
    refine ⟨k,old,hk,hwe ▸ hw,op,?_⟩
    intro j hj
    have hjr := cut_reads (e:=e.val) L.hcl pq ql bl hj (np j hj) (nq j hj)
    rw [cut_primary (v:=v)] at hjr
    exact cut_gate_injective pq (np j hj) (nq j hj) kp kq ((only _ hjr).trans idx.symm)

end C10980

namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers C10980.EdgeFn

private lemma f_nonconstant : ∃ x y : Bits, f x ≠ f y :=
  ⟨fun i => i == 1 || i == 5, fun _ => false, by decide⟩

private lemma no_duplicate_binary {gs : List Gate} {o r w : ℕ} {g : Gate}
    (L : Least 9 f gs o) (hg : gs[r]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.inputs ≠ [w,w] := by
  intro h
  have rl := (List.getElem?_eq_some_iff.mp hg).1
  have wl := (L.hcl r g hg).lt w (by simp [h])
  apply L.no_alias f_nonconstant r rl w wl
  intro x
  rw [vl_gate _ L.hcl x _ _ hg]
  rcases hop with op | op <;> simp [op,h,GateOp.eval]

private lemma leaf_shape_evals {gs : List Gate} {o : ℕ} {e : Fin 9}
    (L : Least 9 f gs o) (T : TightLeaf gs e) :
    T.a < 9+T.p ∧ T.p < T.q ∧ T.a ≠ e.val ∧ T.b ≠ 9+T.p ∧
    (∀ x : Bits, vl gs x (9+T.p) = (x e || vl gs x T.a)) ∧
    (∀ x : Bits, vl gs x (9+T.q) = ((x e || vl gs x T.a) && vl gs x T.b)) := by
  have ap : T.a ∈ T.gp.inputs := by rcases T.hip with h | h <;> simp [h]
  have pq : 9+T.p ∈ T.gq.inputs := by rcases T.hiq with h | h <;> simp [h]
  have al := (L.hcl _ _ T.hp).lt _ ap
  have pl := (L.hcl _ _ T.hq).lt _ pq
  have na : T.a ≠ e.val := by
    intro he
    apply no_duplicate_binary (w:=e.val) L T.hp (Or.inr T.hop)
    rcases T.hip with h | h <;> simp [h,he]
  have nb : T.b ≠ 9+T.p := by
    intro he
    apply no_duplicate_binary (w:=9+T.p) L T.hq (Or.inl T.hoq)
    rcases T.hiq with h | h <;> simp [h,he]
  have orEval (x : Bits) : vl gs x (9+T.p) = (x e || vl gs x T.a) := by
    rw [vl_gate _ L.hcl x _ _ T.hp,T.hop]
    rcases T.hip with h | h <;> simp [h,GateOp.eval,vl_input gs x _ e.isLt,Bool.or_comm]
  have andEval (x : Bits) : vl gs x (9+T.q) = ((x e || vl gs x T.a) && vl gs x T.b) := by
    rw [vl_gate _ L.hcl x _ _ T.hq,T.hoq,← orEval]
    rcases T.hiq with h | h <;> simp [h,GateOp.eval,Bool.and_comm]
  exact ⟨al,by omega,na,nb,orEval,andEval⟩

private lemma direct_on_max_tail {gs : List Gate} {o t : ℕ} {e v : Fin 9}
    (L : Least 9 f gs o) (T : TightLeaf gs e)
    (ev : e ≠ v) (tail : TailGE 9 f gs t)
    (maxTail : ∀ hs out, Least 9 f hs out → ¬ TailGE 9 f hs (t+1))
    (count : gs.countP isNotOp ≤ 1)
    (edge : f (Function.update (single v) e true) = true)
    (edgeCase : ∀ x : Bits, f x = false →
      f (Function.update (Function.update x e true) v false) = false ∧
      f (Function.update (Function.update x e true) v true) = true)
    (dep : Dep (fun x => f (Function.update x e true)) v)
    (nc : ∃ x y, f (Function.update (Function.update x v false) e true) ≠
      f (Function.update (Function.update y v false) e true))
    (noT : ¬ Drop f e true 3 gs.length)
    (noVF : ¬ Drop (fun x => f (Function.update x e true)) v false 4 gs.length) :
    T.b = v.val ∧ onlyReader gs v T.q := by
  obtain ⟨ae,_,nae,nb,orEval,_⟩ := leaf_shape_evals L T
  have av := false_at_neighbour L T.only_input ae nae edge orEval
  have noav : T.a ≠ v.val := by
    intro h
    rw [h,vl_input gs _ _ v.isLt] at av
    simp [single] at av
  rcases leaf_neighbour_reader L e v ev T.hp T.hq T.hop T.hoq T.hip T.hiq
      T.only_input T.only_next noav dep nc noT noVF with direct | ⟨_,r,g,hr,hm,op,only⟩
  · exact direct
  · exfalso
    rcases gate_cases gs L.hcl r g hr v.val hm with ⟨neg,_,_⟩ | ⟨d,ports,⟨ha,_⟩ | ⟨_,_⟩⟩
    · rw [op] at neg
      contradiction
    · rw [op] at ha
      contradiction
    have hvd : d ≠ v.val := by
      intro h
      apply no_duplicate_binary (w:=v.val) L hr (Or.inr op)
      rcases ports with hp | hp <;> simp [hp,h]
    have de : d < 9+r := (L.hcl r g hr).lt _ (by rcases ports with h | h <;> simp [h])
    have gpReads : e.val ∈ T.gp.inputs := by rcases T.hip with h | h <;> simp [h]
    have nopr : o ≠ 9+T.p := pruned_or_not_output L.hcl T.hp T.hop gpReads
      ((L.hev (single e)).trans (single_false e))
    have pivotal : vl gs (single v) o ≠ vl gs (Function.update (single v) e true) o := by
      rw [L.hev,L.hev,single_false,edge]
      decide
    exact saturated_or_contradiction L tail maxTail only hr op ports hvd edgeCase
      (leaf_mono_for_partner L.hcl T.only_input T.only_next only T.hp (by simp [T.hop])
        T.hq T.hoq T.hiq nb count (out_not_primary L e) nopr pivotal de)

private lemma cofactor_absurd {F : Bits → Bool} {s top : ℕ}
    (hC : HasCircuitSize 9 F s) (hle : s ≤ top) (hno : ¬ HasCircuitSize 9 F top) : False := by
  obtain ⟨C,hg,hs,hf⟩ := hC
  exact hno ⟨C,hg,hs.trans hle,hf⟩

private lemma no_leaf_savings {e v : Fin 9} {s : ℕ} (sz : s ≤ 14)
    (dep : Dep (fun x => f (Function.update x e true)) v)
    (nc : ∃ x y, f (Function.update (Function.update x v false) e true) ≠
      f (Function.update (Function.update y v false) e true))
    (hf : ¬ HasCircuitSize 9 (fun x => f (Function.update x e false)) 12)
    (hv : ¬ HasCircuitSize 9 (fun x => f (Function.update (Function.update x v false) e true)) 10) :
    (¬ Drop f e false 2 s) ∧ (¬ Drop f e true 3 s) ∧
      (¬ Drop (fun x => f (Function.update x e true)) v false 4 s) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨u,hu,hC⟩
    exact cofactor_absurd hC (by omega) hf
  · rintro ⟨u,hu,hC⟩
    obtain ⟨r,hr,hD⟩ := cofactor_save_one_false v dep nc hC
    exact cofactor_absurd hD (by omega) hv
  · rintro ⟨u,hu,hC⟩
    exact cofactor_absurd hC (by omega) hv

theorem structural_lower_10981
    (false3 : ¬ HasCircuitSize 9 (fun x => f (Function.update x 3 false)) 12)
    (false4 : ¬ HasCircuitSize 9 (fun x => f (Function.update x 4 false)) 12)
    (true3false7 : ¬ HasCircuitSize 9
      (fun x => f (Function.update (Function.update x 7 false) 3 true)) 10)
    (true4false0 : ¬ HasCircuitSize 9
      (fun x => f (Function.update (Function.update x 0 false) 4 true)) 10)
    (few_not : ∀ gs out, Least 9 f gs out → gs.length ≤ 14 →
      TightLeaf gs (3 : Fin 9) → TightLeaf gs (4 : Fin 9) → gs.countP isNotOp ≤ 1) :
    ¬ HasCircuitSize 9 f 14 := by
  classical
  intro h
  obtain ⟨gs₀,o₀,L₀,sz₀⟩ := exists_least 9 f 14 f_nonconstant h
  let P (k : ℕ) := ∃ gs out, Least 9 f gs out ∧ TailGE 9 f gs k
  let t := Nat.findGreatest P 14
  have zero : P 0 := ⟨gs₀,o₀,L₀,TailGE.zero _ _ _⟩
  obtain ⟨gs,o,L,tail⟩ := Nat.findGreatest_spec (P:=P) (by decide : 0 ≤ 14) zero
  have sz : gs.length ≤ 14 := (L.hmin gs₀ o₀ L₀.hcl L₀.hev).trans sz₀
  have maximal (hs : List Gate) (out : ℕ) (L' : Least 9 f hs out) :
      ¬ TailGE 9 f hs (t+1) := by
    intro tail'
    have le : t+1 ≤ 14 := tail'.le.trans ((L'.hmin gs₀ o₀ L₀.hcl L₀.hev).trans sz₀)
    have eq := Nat.le_findGreatest (P:=P) le ⟨hs,out,L',tail'⟩
    change t+1 ≤ t at eq
    omega
  let z : Bits := fun _ => false
  let x : Bits := fun i => i == 1 || i == 5
  have edge3 : f (Function.update (single 7) 3 true) = true := by decide
  have edge4 : f (Function.update (single 0) 4 true) = true := by decide
  have dep3 : Dep f 3 := ⟨single 7,by decide⟩
  have dep4 : Dep f 4 := ⟨single 0,by decide⟩
  have dep7 : Dep (fun x => f (Function.update x 3 true)) 7 := ⟨z,by decide⟩
  have dep0 : Dep (fun x => f (Function.update x 4 true)) 0 := ⟨z,by decide⟩
  have nc7 : ∃ x y, f (Function.update (Function.update x 7 false) 3 true) ≠
      f (Function.update (Function.update y 7 false) 3 true) := ⟨x,z,by decide⟩
  have nc0 : ∃ x y, f (Function.update (Function.update x 0 false) 4 true) ≠
      f (Function.update (Function.update y 0 false) 4 true) := ⟨x,z,by decide⟩
  have nc3 (c : Bool) : ∃ x y, f (Function.update x 3 c) ≠ f (Function.update y 3 c) := by
    cases c <;> exact ⟨x,z,by decide⟩
  have nc4 (c : Bool) : ∃ x y, f (Function.update x 4 c) ≠ f (Function.update y 4 c) := by
    cases c <;> exact ⟨x,z,by decide⟩
  obtain ⟨noF3,noT3,noV7⟩ := no_leaf_savings sz dep7 nc7 false3 true3false7
  obtain ⟨noF4,noT4,noV0⟩ := no_leaf_savings sz dep0 nc0 false4 true4false0
  obtain ⟨T3⟩ := tight_leaf_shape L 3 dep3 nc3 noF3 noT3
  obtain ⟨T4⟩ := tight_leaf_shape L 4 dep4 nc4 noF4 noT4
  have count := few_not gs o L sz T3 T4
  obtain ⟨b3,r7⟩ := direct_on_max_tail L T3 (v:=7) (by decide) tail maximal count
    edge3 edge_case_three dep7 nc7 noT3 noV7
  obtain ⟨b4,r0⟩ := direct_on_max_tail L T4 (v:=0) (by decide) tail maximal count
    edge4 edge_case_four dep0 nc0 noT4 noV0
  obtain ⟨a3,pq3,na3,_,or3,and3⟩ := leaf_shape_evals L T3
  obtain ⟨a4,_,na4,_,or4,and4⟩ := leaf_shape_evals L T4
  have na37 : T3.a ≠ 7 := by
    intro he
    have hv := false_at_neighbour L T3.only_input a3 na3 edge3 or3
    rw [he] at hv
    have h7 : vl gs (single 7) 7 = true :=
      (vl_input gs _ 7 (by decide : 7 < 9)).trans rfl
    rw [h7] at hv
    cases hv
  have na30 : T3.a ≠ 0 := by
    intro he
    have ha : 0 ∈ T3.gp.inputs := by rcases T3.hip with hp | hp <;> simp [hp,he]
    have eq := r0 T3.p ⟨T3.gp,T3.hp,ha⟩
    have hsame : gs[T3.p]? = some T4.gq := by rw [eq]; exact T4.hq
    have hg : T3.gp = T4.gq := Option.some.inj (T3.hp.symm.trans hsame)
    have opEq := congrArg Gate.op hg
    rw [T3.hop,T4.hoq] at opEq
    cases opEq
  have and3' (x : Bits) : vl gs x (9+T3.q) = ((x 3 || vl gs x T3.a) && x 7) := by
    rw [and3,b3]
    change ((x 3 || vl gs x T3.a) && vl gs x 7) = _
    rw [vl_input gs x 7 (by decide : 7 < 9)]
    rfl
  have and4' (x : Bits) : vl gs x (9+T4.q) = ((x 4 || vl gs x T4.a) && x 0) := by
    rw [and4,b4]
    change ((x 4 || vl gs x T4.a) && vl gs x 0) = _
    rw [vl_input gs x 0 (by decide : 0 < 9)]
    rfl
  exact direct_case_impossible L T3.only_input T4.only_input r0 r7 a3 a4 (by omega)
    na3 na4 na37 na30 or3 or4 and3' and4'

end C10980

namespace C10981.Signed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def thinF (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)

private def thinCut (b : Bool) : Sig := if b then butterfly ||| wireAt 5 else windCut 6

private def thinRaw : List Sig :=
  [wireAt 0,wireAt 1,wireAt 2,wireAt 3,wireAt 4,wireAt 5,zero]

private theorem thin_cut_bound (hbut : Lower true bfInputs butterfly 8) (b : Bool) :
    Lower true (coreRoots 6) (thinCut b) 9 := by
  cases b
  · exact peripheral_lower hbut 6 (by decide)
  · have hp : proper (thinCut true) := by unfold proper; decide +kernel
    have hbutP : proper butterfly := by unfold proper; decide +kernel
    have h := lift_ok (u:=true) (ms:=zeroVar 5) (raw:=coreRoots 6)
      (xs:=[(wireAt 5,0,32)]) (by decide +kernel) hp hbutP hbut
    exact h

theorem signed_size_bound {T : Sig} {roots : List Sig} {n s L : ℕ} {F : (Fin n → Bool) → Bool}
    (low : Lower true roots T L) (raw : List Sig)
    (properT : proper T) (zeroT : bit 0 T = false) (raw_pos : raw.all plainWord = true)
    (raw_sub : ∀ a ∈ raw, a = zero ∨ a ∈ roots) (hraw : raw.length = n)
    (eq : ∀ r : Row, F (fun j => bit r (raw.getD j.val zero)) = bit r T)
    (has : HasCircuitSize n F s) : L ≤ s := by
  obtain ⟨C,legal,sz,hev⟩ := has
  have goalEq : (execute C.gates raw).getD C.output zero = T := by
    apply bit_ext
    intro r
    rw [← b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    have heq : raw.map (bit r) = List.ofFn (fun j : Fin n => bit r (raw.getD j.val zero)) := by
      apply List.ext_getElem
      · simp [hraw]
      · intro i hi hj
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < raw.length by simpa using hi)]
    rw [heq]
    change C.eval (List.ofFn (fun j : Fin n => bit r (raw.getD j.val zero))) = bit r T
    rw [hev]
    exact eq r
  have h := get_rep (u:=true) (execute C.gates raw) C.output
  rw [goalEq] at h
  unfold Repr at h
  rw [nrm_id zeroT] at h
  obtain ⟨k,S,hle,run,sub⟩ := extract (u:=true) C.gates raw legal (by simp) properT
    (h.resolve_right (fun hh => hh properT))
  rw [nrm_map raw_pos] at sub
  let ws := S.toList
  have rf := list_run run ws (Finset.nodup_toList S) (Finset.toList_toFinset S)
  have heq (w : Wire Row) : restrictRows (fun r : Row => r) w = w := rfl
  have covered : supply true (roots.map observe) ((ws.map observe).map (restrictRows fun r : Row => r)) := by
    intro w hw
    obtain ⟨_,hwhat,rfl⟩ := List.mem_map.mp hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hwhat
    rw [heq]
    have ma := Finset.mem_toList.mp ha
    rcases raw_sub a (sub a ma) with z | am
    · exact False.elim ((live_proper run a ma).1 z)
    · exact Or.inl (List.mem_map_of_mem (f:=observe) am)
  have nh : ¬ Constant (restrictRows (fun r : Row => r) (observe T)) := by
    rw [heq]
    exact observe_proper properT
  have bound := projected_bound (fun r : Row => r) rf nh Reach.start covered
    (L:=L) (by simpa only [heq,Lower] using low)
  have count := List.countP_le_length (l:=C.gates) (p:=fun g => !isNot g)
  change C.gates.length ≤ s at sz
  omega

theorem thin_bound (hbut : Lower true bfInputs butterfly 8) (s : ℕ)
    (hc : HasCircuitSize 7 thinF s) : 11 ≤ s := by
  have dep : ∃ x : Fin 7 → Bool, thinF (Function.update x 6 (!x 6)) ≠ thinF x :=
    ⟨fun i => i == 5, by decide⟩
  have nc (b : Bool) : ∃ x y, thinF (Function.update x 6 b) ≠ thinF (Function.update y 6 b) := by
    cases b <;> exact ⟨fun i => i == 1 || i == 2, fun _ => false, by decide⟩
  obtain ⟨b,t,sz,ht⟩ := C10980.Helpers.PermInputs.gate_elim_at 6 thinF 6 s dep nc hc
  have eq : ∀ b (r : Row), thinF (Function.update (fun j => bit r (thinRaw.getD j.val zero)) 6 b) =
      bit r (thinCut b) := by decide +kernel
  have hp : ∀ b, proper (thinCut b) := by unfold proper; decide +kernel
  have hz : ∀ b, bit 0 (thinCut b) = false := by decide +kernel
  have hraw : ∀ w ∈ thinRaw, w = zero ∨ w ∈ coreRoots 6 := by
    intro w hw
    simp only [thinRaw,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have lo := signed_size_bound (thin_cut_bound hbut b) thinRaw (hp b) (hz b)
    (by decide +kernel) hraw rfl (eq b) ht
  omega

end C10981.Signed

namespace C10980
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity C10980.Helpers
open C10980.Helpers.Readers C10980.Helpers.PermInputs

private def windπ : Fin 9 → Fin 7 := ![1,3,5,0,0,4,6,2,0]
private def thinπ3 : Fin 9 → Fin 7 := ![5,1,3,0,6,2,4,0,0]
private def thinπ4 : Fin 9 → Fin 7 := ![0,1,3,6,0,2,4,5,0]

private def thinWind : (Fin 7 → Bool) → Bool := fun x =>
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)

private lemma bound_after_relabel {F : Bits → Bool} {W : (Fin 7 → Bool) → Bool} {s k : ℕ}
    (π : Fin 9 → Fin 7) (eq : ∀ x, F (x ∘ π) = W x)
    (lw : ∀ t, HasCircuitSize 7 W t → k ≤ t)
    (hC : HasCircuitSize 9 F s) : k ≤ s := by
  have h := relabel_size π F s hC
  rw [show (fun x => F (x ∘ π)) = W from funext eq] at h
  exact lw s h

private lemma false_with_leaf (wind_bound : ∀ t, HasCircuitSize 7 C10981.Signed.windF t → 12 ≤ t)
    {e v : Fin 9} (dep : Dep (fun x => f (Function.update x e false)) v)
    (nc : ∃ x y, f (Function.update (Function.update x v false) e false) ≠
      f (Function.update (Function.update y v false) e false))
    (eq : ∀ x : Fin 7 → Bool,
      f (Function.update (Function.update (x ∘ windπ) v false) e false) = C10981.Signed.windF x) :
    ¬ HasCircuitSize 9 (fun x => f (Function.update x e false)) 12 := by
  intro h
  obtain ⟨s,sz,hs⟩ := cofactor_save_one_false v dep nc h
  have b := bound_after_relabel windπ eq wind_bound hs
  omega

private lemma thin_false3 : ¬ HasCircuitSize 9
    (fun x => f (Function.update (Function.update x 7 false) 3 true)) 10 := by
  intro h
  have b := bound_after_relabel (W:=thinWind) thinπ3 (by decide +kernel) (C10981.Signed.thin_bound C10981.Signed.bf_low) h
  omega

private lemma thin_false4 : ¬ HasCircuitSize 9
    (fun x => f (Function.update (Function.update x 0 false) 4 true)) 10 := by
  intro h
  have b := bound_after_relabel (W:=thinWind) thinπ4 (by decide +kernel) (C10981.Signed.thin_bound C10981.Signed.bf_low) h
  omega

theorem proof_of_10981_from_wind (wind_bound : ∀ t, HasCircuitSize 7 C10981.Signed.windF t → 12 ≤ t) :
    ∀ t : ℕ,
      HasCircuitSize 9 (fun x : Fin 9 → Bool =>
        (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) ||
        (x 3 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 2 && x 8) ||
        (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 15 ≤ t := by
  have false3 := false_with_leaf wind_bound (e:=3) (v:=4) ⟨single 0,by decide⟩
    ⟨fun i => i == 1 || i == 5,fun _ => false,by decide⟩ (by decide +kernel)
  have false4 := false_with_leaf wind_bound (e:=4) (v:=3) ⟨single 7,by decide⟩
    ⟨fun i => i == 1 || i == 5,fun _ => false,by decide⟩ (by decide +kernel)
  have no := structural_lower_10981 false3 false4 thin_false3 thin_false4 (fun _ _ L sz T3 T4 =>
    original_not_count L sz T3 T4 C10981.Signed.bf_low)
  intro t hc
  by_contra lt
  exact cofactor_absurd hc (by omega) no

end C10980


namespace C10981.Signed

abbrev StepInfo := Sig × Sig × Bool

inductive Trace (T : Sig) : Finset Sig → List StepInfo → Prop
  | stop : proper T → Trace T {T} []
  | step {U : Finset Sig} {a b : Sig} {d : Bool} {rest : List StepInfo} :
      proper a → proper b → a ≠ b → prime d a b ∉ insert a (insert b U) →
      Trace T (insert (prime d a b) U) rest → Trace T (insert a (insert b U)) ((a,b,d)::rest)

lemma trace_of_live {T k S} (h : Live false T k S) :
    ∃ trace : List StepInfo, trace.length = k ∧ Trace T S trace := by
  induction h using Live.ind with
  | stop hp => exact ⟨[],rfl,.stop hp⟩
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    obtain ⟨tr,ln,ht⟩ := ih
    rcases allowed_four hd with rfl | rfl | ⟨abs,_⟩ | ⟨abs,_⟩
    · exact ⟨(a,b,false)::tr,by simp [ln],Trace.step ha hb hab fresh ht⟩
    · exact ⟨(a,b,true)::tr,by simp [ln],Trace.step ha hb hab fresh ht⟩
    · cases abs
    · cases abs

lemma live_of_trace {T S tr} (h : Trace T S tr) : Live false T tr.length S := by
  induction h with
  | stop hp => exact Live.stop hp
  | @step U a b d rest ha hb hn hf hr ih =>
    cases d
    · apply Live.binary (d:=0) (Or.inl (by decide)) ha hb hn hf ih
    · apply Live.binary (d:=1) (Or.inl (by decide)) ha hb hn hf ih

def zeroAfter (ms : List Move) (a : Sig) : Bool := movedWord ms a == zero

def stepLost (ms : List Move) (s : StepInfo) : Bool := zeroAfter ms s.1 || zeroAfter ms s.2.1

def lost (ms : List Move) (tr : List StepInfo) : Nat := tr.countP (stepLost ms)

lemma moved_obs_prime (ms : List Move) (d : Bool) (a b : Sig) :
    observe (movedWord ms (prime d a b)) = combine d (observe (movedWord ms a)) (observe (movedWord ms b)) := by
  funext r
  cases d <;> simp [observe,bit_moved,bit_prime,combine]

lemma moved_zero_const {ms : List Move} {a : Sig} (hz : zeroAfter ms a = true) :
    Constant (observe (movedWord ms a)) := by
  have h := beq_iff_eq.mp hz
  rw [h]
  exact ⟨false,funext bit_zero⟩

lemma trace_project {T S tr} (run : Trace T S tr) (ms : List Move)
    (roots : List (Wire Row)) {p bank} (reach : Reach true roots p bank)
    (sup : ∀ a ∈ S, Available true bank (observe (movedWord ms a))) :
    ∃ n next, Reach true roots n next ∧ Available true next (observe (movedWord ms T)) ∧
      n + lost ms tr ≤ p + tr.length := by
  induction run generalizing p bank with
  | stop proper => exact ⟨p,bank,reach,sup _ (by simp),by simp [lost]⟩
  | @step U a b d rest ha hb hn hf hr ih =>
    have aAvail := sup a (Finset.mem_insert_self ..)
    have bAvail := sup b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have uz (a : Sig) (hm : a ∈ U) := sup a (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    set w := observe (movedWord ms (prime d a b))
    have eq := moved_obs_prime ms d a b
    by_cases drop : stepLost ms (a,b,d) = true
    · have constant : Constant (observe (movedWord ms a)) ∨ Constant (observe (movedWord ms b)) := by
        rcases Bool.or_eq_true_iff.mp drop with a | b
        · exact Or.inl (moved_zero_const a)
        · exact Or.inr (moved_zero_const b)
      have nw : Available true bank w := by
        rw [show w = _ from eq]
        exact from_constant d constant aAvail bAvail
      obtain ⟨n,next,nr,np,nle⟩ := ih reach (by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | um
        · exact nw
        · exact uz v um)
      refine ⟨n,next,nr,np,?_⟩
      simp only [lost,List.countP_cons_of_pos drop,List.length_cons] at nle ⊢
      omega
    · let next := w :: bank
      have nr : Reach true roots (p+1) next := by
        simp only [next,w,eq]
        exact Reach.two d reach aAvail bAvail
      obtain ⟨n,fin,fn,fv,le⟩ := ih nr (by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | um
        · exact Or.inl (by simp [next,w])
        · exact available_cons w (uz v um))
      refine ⟨n,fin,fn,fv,?_⟩
      simp only [lost,List.countP_cons_of_neg drop,List.length_cons] at le ⊢
      omega

def zeroCount (ms : List Move) (S : Finset Sig) : Nat := (S.filter (fun a => zeroAfter ms a)).card

lemma zeroCount_insert_le (ms : List Move) (S : Finset Sig) (a : Sig) :
    zeroCount ms (insert a S) ≤ zeroCount ms S + (zeroAfter ms a).toNat := by
  unfold zeroCount
  rw [Finset.filter_insert]
  split
  · rename_i hh
    simpa [hh] using (Finset.card_insert_le (a:=a) (s:=S.filter (fun a => zeroAfter ms a)))
  · simp_all

lemma zeroCount_insert (ms : List Move) (S : Finset Sig) (a : Sig) (na : a ∉ S) :
    zeroCount ms (insert a S) = zeroCount ms S + (zeroAfter ms a).toNat := by
  unfold zeroCount
  rw [Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (fun h => na (Finset.mem_filter.mp h).1)]
    simp_all
  · simp_all

lemma trace_has_losses {T S tr} (run : Trace T S tr) (ms : List Move) (tgt : zeroAfter ms T = false) :
    zeroCount ms S ≤ lost ms tr := by
  induction run with
  | stop hp => simp [zeroCount,lost,tgt]
  | @step U a b d rest ha hb hn hf hr ih =>
    have fa := zeroCount_insert_le ms (insert b U) a
    have fb := zeroCount_insert_le ms U b
    have hnew := zeroCount_insert ms U (prime d a b) (fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
    rw [hnew] at ih
    have cha : (zeroAfter ms a).toNat + (zeroAfter ms b).toNat ≤
        (stepLost ms (a,b,d)).toNat + (zeroAfter ms (prime d a b)).toNat := by
      cases aa : zeroAfter ms a <;> cases bb : zeroAfter ms b <;> simp [stepLost,aa,bb]
      have z : zeroAfter ms (prime d a b) = true := by
        have p := beq_iff_eq.mp aa
        have q := beq_iff_eq.mp bb
        apply beq_iff_eq.mpr
        apply bit_ext
        intro r
        have eq := congrFun (moved_obs_prime ms d a b) r
        rw [p,q] at eq
        exact eq.trans (by cases d <;> simp [combine,observe,bit_zero])
      simp [z]
    simp only [lost,List.countP_cons] at ih ⊢
    cases age : stepLost ms (a,b,d) <;> simp [age] at cha ⊢ <;> omega

def projectionRaw (i : Fin 7) : List (Wire Row) := (coreRoots i).map observe

lemma projected_initial (i : Fin 7) (hi : i ≠ 0) :
    wi.all (fun w => freeWord (coreRoots i) (movedWord (zeroVar i) w)) = true := by
  exact (show ∀ i : Fin 7, i ≠ 0 →
    wi.all (fun w => freeWord (coreRoots i) (movedWord (zeroVar i) w)) = true by decide +kernel) i hi

lemma wind_trace_loss_bound (bf : Lower true bfInputs butterfly 8) {tr : List StepInfo}
    (run : Trace wind wi.toFinset tr) (size : tr.length ≤ 11) (i : Fin 7) (hi : i ≠ 0) :
    lost (zeroVar i) tr ≤ 2 := by
  have supply0 : ∀ a ∈ wi.toFinset, Available true (projectionRaw i) (observe (movedWord (zeroVar i) a)) := by
    intro a ha
    exact freeWord_ok ((List.all_eq_true.mp (projected_initial i hi)) a (List.mem_toFinset.mp ha))
  obtain ⟨n,bank,hr,hv,le⟩ := trace_project run (zeroVar i) (projectionRaw i) Reach.start supply0
  have lower := peripheral_lower bf i hi
  have size' := lower n bank hr hv
  omega

end C10981.Signed

namespace C10981.Signed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem wind_upper_trace (bf : Lower true bfInputs butterfly 8) {s : ℕ}
    (small : s ≤ 11) (has : HasCircuitSize 7 windF s) :
    ∃ tr, tr.length ≤ 11 ∧ Trace wind wi.toFinset tr := by
  obtain ⟨C,legal,sz,hev⟩ := has
  have hwi : wi = List.ofFn wireAt := rfl
  have raw_pos : wi.all plainWord = true := by decide +kernel
  have computes (r : Row) : C.eval (wi.map (bit r)) = windF (sampled7 r) := by
    rw [hwi,List.map_ofFn]
    exact hev (sampled7 r)
  have low := signed_windmill_any bf C legal wi raw_pos (fun a h => Or.inr h) computes
  have count : C.gates.countP (fun g => !isNot g) = C.gates.length := by
    unfold binaryCount at low
    have le := List.countP_le_length (l:=C.gates) (p:=fun g => !isNot g)
    change C.gates.length ≤ s at sz
    omega
  have mono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have h := List.countP_eq_length.mp count g hg
    simpa only [Bool.not_eq_true'] using h
  have eval : (execute C.gates wi).getD C.output zero = wind := by
    apply bit_ext
    intro r
    rw [← b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1),wind_table]
    exact computes r
  have hp : proper wind := by unfold proper; decide +kernel
  have h := get_rep (u:=false) (execute C.gates wi) C.output
  rw [eval] at h
  unfold Repr at h
  rw [nrm_id (u:=false) (by decide +kernel : bit 0 wind = false)] at h
  obtain ⟨k,S,hle,run,sub⟩ :=
    extract (u:=false) C.gates wi legal (fun _ => mono) hp
      (h.resolve_right (fun hh => hh hp))
  rw [nrm_map raw_pos] at sub
  have ess : ∀ i : Fin 7, ∃ r s : Fin 128,
    bit (Fin.ofNat 512 r.val) wind ≠ bit (Fin.ofNat 512 s.val) wind ∧
    ∀ j : Fin 7, wireAt j ≠ wireAt i →
      bit (Fin.ofNat 512 r.val) (wireAt j) = bit (Fin.ofNat 512 s.val) (wireAt j) := by decide +kernel
  have eq : S = wi.toFinset := by
    ext a
    constructor
    · intro ha
      exact List.mem_toFinset.mpr (sub a ha)
    · intro ha
      have hw := List.mem_toFinset.mp ha
      rw [hwi] at hw
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      obtain ⟨r,t,hd,agree⟩ := ess i
      refine raw_required run wi (wireAt i) sub (Fin.ofNat 512 r.val) (Fin.ofNat 512 t.val) hd ?_
      intro b hb hn
      rw [hwi] at hb
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
      exact agree j hn
  obtain ⟨tr,len,trace⟩ := trace_of_live run
  change C.gates.length ≤ s at sz
  exact ⟨tr,by omega,eq ▸ trace⟩

theorem wind_bound_of_trace (bf : Lower true bfInputs butterfly 8)
    (excluded : ∀ tr, tr.length ≤ 11 → ¬ Trace wind wi.toFinset tr)
    (s : ℕ) (has : HasCircuitSize 7 windF s) : 12 ≤ s := by
  by_contra h
  obtain ⟨tr,sz,hr⟩ := wind_upper_trace bf (by omega) has
  exact excluded tr sz hr

end C10981.Signed


namespace C10981.Signed

abbrev Cut := Fin 9
abbrev Generator := Fin 5

def profileMask (v : Cut) : Nat :=
  if v.val < 6 then 1 <<< (v.val+1) else 3 <<< (2*(v.val-6)+1)
def profileCut (v : Cut) : List Move := fixRows (profileMask v) 0
def profileLimit (v : Cut) : Nat := if v.val < 6 then 2 else 3
def profileRoots (v : Cut) : List Sig := varsX (127 ^^^ profileMask v)
def profileTarget (v : Cut) : Sig := movedWord (profileCut v) wind

def projectToButter (v : Cut) : List Move :=
  if v.val = 6 then [swapRows 81,swapRows 98] else
  if v.val = 7 then [swapRows 83,swapRows 100] else []

set_option maxRecDepth 32768 in
lemma wind_profile_lower (bf : Lower true bfInputs butterfly 8) (v : Cut) :
    Lower true (profileRoots v) (profileTarget v) (11 - profileLimit v) := by
  by_cases h : v.val < 6
  · let w : Fin 7 := ⟨v.val+1,by omega⟩
    have hw : w ≠ 0 := by intro eq; have := congrArg Fin.val eq; simp [w] at this
    have hs : profileCut v = zeroVar w := by simp [profileCut,profileMask,zeroVar,h,w]
    have hr : profileRoots v = coreRoots w := by simp [profileRoots,profileMask,coreRoots,h,w]
    simp only [profileLimit,if_pos h,profileTarget,hs,hr]
    exact peripheral_lower bf w hw
  · have cert : checkMap (projectToButter v) (profileRoots v) (profileTarget v) bfInputs butterfly = true := by
      exact (show ∀ i : Cut, ¬ i.val < 6 →
        checkMap (projectToButter i) (profileRoots i) (profileTarget i) bfInputs butterfly = true by decide +kernel) v h
    have properV : proper (profileTarget v) :=
      (show ∀ i : Cut, proper (profileTarget i) by unfold proper; decide +kernel) v
    have plainV : plainWord (profileTarget v) = true :=
      (show ∀ i : Cut, plainWord (profileTarget i) = true by decide +kernel) v
    have plainR : (profileRoots v).all plainWord = true :=
      (show ∀ i : Cut, (profileRoots i).all plainWord = true by decide +kernel) v
    have properB : proper butterfly := by unfold proper; decide +kernel
    simpa [profileLimit,h] using lower_map cert properV plainV plainR properB bf

set_option maxRecDepth 32768 in
lemma wind_profile_loss_bound (bf : Lower true bfInputs butterfly 8) {tr : List StepInfo}
    (run : Trace wind wi.toFinset tr) (size : tr.length ≤ 11) (v : Cut) :
    lost (profileCut v) tr ≤ profileLimit v := by
  have initial : wi.all (fun w => freeWord (profileRoots v) (movedWord (profileCut v) w)) = true :=
    (show ∀ i : Cut, wi.all (fun w => freeWord (profileRoots i) (movedWord (profileCut i) w)) = true by decide +kernel) v
  have supply0 : ∀ a ∈ wi.toFinset, Available true ((profileRoots v).map observe) (observe (movedWord (profileCut v) a)) := by
    intro a ha
    exact freeWord_ok ((List.all_eq_true.mp initial) a (List.mem_toFinset.mp ha))
  obtain ⟨n,bank,hr,hv,le⟩ := trace_project run (profileCut v) ((profileRoots v).map observe) Reach.start supply0
  have lower := wind_profile_lower bf v
  have size' := lower n bank hr hv
  have bd : profileLimit v ≤ 11 := by unfold profileLimit; split <;> omega
  omega

def genMoves (g : Generator) : List Move :=
  (![ [swapRows 33], [swapRows 67], [swapRows 101], [swapRows 49,swapRows 66],
    [swapRows 83,swapRows 100]] : Generator → List Move) g

def genIndex (g : Generator) (i : Cut) : Cut :=
  (![ (![1,0,2,3,4,5,6,7,8] : Cut → Cut), ![0,1,3,2,4,5,6,7,8],
    ![0,1,2,3,5,4,6,7,8], ![2,3,0,1,4,5,7,6,8], ![0,1,4,5,2,3,6,8,7]] : Generator → Cut → Cut) g i

def genWord (g : Generator) : Sig → Sig := movedWord (genMoves g)
def genSequence (n : Nat) : List Generator :=
  ([0,1,2] : List Generator).filter (fun g => n.testBit g.val) ++
    ([[],[3],[4],[3,4],[4,3],[3,4,3]] : List (List Generator)).getD (n/8) []

def autoWind (gs : List Generator) (a : Sig) : Sig := gs.foldr genWord a
def relabelCut (gs : List Generator) (i : Cut) : Cut := gs.foldl (fun j g => genIndex g j) i

def rotateStep (f : Sig → Sig) (e : StepInfo) : StepInfo := (f e.1,f e.2.1,e.2.2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma gen_surj (g : Generator) : Function.Surjective (movedRow (genMoves g)) := by
  have idgen : ∀ g : Generator, ∀ r : Row,
      movedRow (genMoves g) (movedRow (genMoves g) r) = r := by decide +kernel
  exact fun r => ⟨movedRow (genMoves g) r,idgen g r⟩

lemma gen_target : ∀ g : Generator, genWord g wind = wind := by decide +kernel

lemma gen_limit : ∀ g : Generator, ∀ i : Cut, profileLimit (genIndex g i) = profileLimit i := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
lemma gen_rows (g : Generator) (i : Cut) (r : Row) :
    movedRow (genMoves g) (movedRow (profileCut i) r) =
      movedRow (profileCut (genIndex g i)) (movedRow (genMoves g) r) := by
  have val : ∀ g : Generator, ∀ i : Cut, ∀ r : Row,
      movedRow (genMoves g) (movedRow (profileCut i) r) =
        movedRow (profileCut (genIndex g i)) (movedRow (genMoves g) r) := by decide +kernel
  exact val g i r

lemma gen_inj (g : Generator) : Function.Injective (genWord g) := by
  intro a b ab
  have eq : rename (movedRow (genMoves g)) a = rename (movedRow (genMoves g)) b := by
    change movedWord (genMoves g) a = movedWord (genMoves g) b at ab
    simpa only [moved_eq_rename] using ab
  exact rename_inj _ (gen_surj g) eq

lemma gen_const (g : Generator) : genWord g zero = zero ∧ genWord g one = one := by
  unfold genWord
  simp only [moved_eq_rename]
  exact rename_constants _

lemma gen_prime (g : Generator) (d : Bool) (a b : Sig) :
    genWord g (prime d a b) = prime d (genWord g a) (genWord g b) := by
  apply bit_ext
  intro r
  simp only [genWord,bit_moved,bit_prime]

lemma gen_zero (g : Generator) (i : Cut) (a : Sig) :
    zeroAfter (profileCut i) (genWord g a) = zeroAfter (profileCut (genIndex g i)) a := by
  have eq : movedWord (profileCut i) (genWord g a) = genWord g (movedWord (profileCut (genIndex g i)) a) := by
    apply bit_ext
    intro r
    simp only [genWord,bit_moved,gen_rows]
  unfold zeroAfter
  rw [eq]
  conv => lhs; rw [← (gen_const g).1]
  by_cases h : movedWord (profileCut (genIndex g i)) a = zero
  · simp [h]
  · have ne : genWord g (movedWord (profileCut (genIndex g i)) a) ≠ genWord g zero := fun e => h (gen_inj g e)
    simp [h,ne]

lemma trace_gen {S tr} (run : Trace wind S tr) (g : Generator) :
    Trace wind (S.image (genWord g)) (tr.map (rotateStep (genWord g))) := by
  have pp (v : Sig) (h : proper v) : proper (genWord g v) :=
    ⟨fun e => h.1 (gen_inj g (e.trans (gen_const g).1.symm)),
     fun e => h.2 (gen_inj g (e.trans (gen_const g).2.symm))⟩
  generalize eT : wind = T at run
  induction run with
  | stop proper => simpa [← eT,gen_target] using Trace.stop (T:=wind) (eT ▸ proper)
  | @step U a b d rest ha hb hn hf hr ih =>
    have fr : genWord g (prime d a b) ∉ (insert a (insert b U)).image (genWord g) := by
      rintro hh
      obtain ⟨x,xm,xe⟩ := Finset.mem_image.mp hh
      exact hf (gen_inj g xe ▸ xm)
    simp only [Finset.image_insert,gen_prime,List.map_cons,rotateStep] at fr ih ⊢
    exact Trace.step (pp _ ha) (pp _ hb) (fun e => hn (gen_inj g e)) fr ih

lemma lost_gen (g : Generator) (i : Cut) (tr : List StepInfo) :
    lost (profileCut i) (tr.map (rotateStep (genWord g))) =
      lost (profileCut (genIndex g i)) tr := by
  unfold lost
  rw [List.countP_map]
  apply List.countP_congr
  intro a ha
  simp only [Function.comp_apply,rotateStep,stepLost,gen_zero]

lemma auto_trace {S tr} (run : Trace wind S tr) (gs : List Generator) :
    Trace wind (S.image (autoWind gs)) (tr.map (rotateStep (autoWind gs))) := by
  induction gs generalizing S tr with
  | nil =>
    have ident : rotateStep (autoWind []) = id := by funext a; rcases a with ⟨x,y,z⟩; rfl
    rw [ident,List.map_id,show autoWind [] = id from rfl,Finset.image_id]
    exact run
  | cons g gs ih =>
    have step := trace_gen (ih run) g
    have eq : rotateStep (genWord g) ∘ rotateStep (autoWind gs) = rotateStep (autoWind (g :: gs)) := rfl
    rw [Finset.image_image,List.map_map,eq] at step
    exact step

lemma lost_auto (gs : List Generator) (i : Cut) (tr : List StepInfo) :
    lost (profileCut i) (tr.map (rotateStep (autoWind gs))) =
      lost (profileCut (relabelCut gs i)) tr := by
  induction gs generalizing i with
  | nil =>
    have ident : rotateStep (autoWind []) = id := by funext a; rcases a with ⟨x,y,z⟩; rfl
    simp [ident,relabelCut]
  | cons g gs ih =>
    have eq : (tr.map (rotateStep (autoWind gs))).map (rotateStep (genWord g)) =
        tr.map (rotateStep (autoWind (g :: gs))) := by rw [List.map_map]; rfl
    rw [← eq,lost_gen,ih]
    rfl

lemma limit_auto (gs : List Generator) (i : Cut) : profileLimit (relabelCut gs i) = profileLimit i := by
  induction gs generalizing i with
  | nil => rfl
  | cons g gs ih => exact (ih (genIndex g i)).trans (gen_limit g i)

end C10981.Signed

namespace C10981.Signed

abbrev WindSample := BitVec 54
abbrev WindPack := Sig × WindSample × WindSample
abbrev WindRow := List Nat × Nat × List Nat
def windPos : List Nat := [3,5,9,6,24,6,24,17,96,33,65,96,33,17,9,65,3,17,9,5,6,6,96,96,24,24,3,5,3,65,6,6,24,24,33,33,9,9,96,96,3,5,5,6,6,17,17,24,24,33,65,65,96,96]
def windNeg : List Nat := [42,84,44,82,52,44,74,82,42,1,76,84,50,1,1,1,1,52,74,1,42,84,44,82,50,76,50,44,74,82,50,74,42,82,42,52,42,76,50,74,82,52,76,52,76,50,84,44,84,44,74,84,52,76]
def windWords : Array (Nat × WindSample × WindSample) := #[(0xaa88aa88aa88aa88aa88aa88aa88aa88,0x13014054005,0x0),(0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8,0x7301c0d4007,0x0),(0xaaaaaaaaaa88aa88aaaaaaaaaa88aa88,0x2013c14055205,0x0),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe673c3c0ff687,0x9e200),(0xc8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8,0x1900d4310029,0x0),(0xcccccccccccccccccccccccccccccccc,0x1900d4310029,0x421d7f59411c9),(0xeaeaeaeaeae0eae0eaeaeaeaeae0eae0,0x21e3cc83c522e,0x0),(0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa,0xe673c3c0ff687,0x40095901de341),(0xeecceecceecceecceecceecceecceecc,0x1930d435402d,0x421d7f59411c9),(0xeeeeeeeeee00ee00eeeeeeeeee00ee00,0x2003c00045204,0x420d5d5141141),(0xeeeeeeeeeeaaeeaaeeeeeeeeeeaaeeaa,0xe673c3c0ff687,0x420d5d51df341),(0xeeeeeeeeeecceecceeeeeeeeeecceecc,0x2193cd435522d,0x421d7f59411c9),(0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,0xe7f3cfc3ff6af,0x421d7f59df3c9),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1e00c838002a,0x3bde280a620c36),(0xfaf0faf0faf0faf0faf0faf0faf0faf0,0x1e30c83c402e,0x3bde280a620c36),(0xfaf8faf8faf8faf8faf8faf8faf8faf8,0x1f30dc3d402f,0x3bde280a620c36),(0xfafafafafaf0faf0fafafafafaf0faf0,0x21e3cc83c522e,0x3bde280a620c36),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1803303044054,0x2694b59a540565),(0xff88ff88ff88ff88ff88ff88ff88ff88,0x1813317054055,0x2694b59a540565),(0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0,0x186330b0c4056,0x2694b59a540565),(0xffaaaa88ffaaaa88ffaaaa88ffaaaa88,0x1e133170760d5,0x0),(0xffaaffaaffaaffaaffaaffaaffaaffaa,0xfe73f3f0ff6d7,0x2694b59a5de765),(0xffccaa88ffccaa88ffccaa88ffccaa88,0x1813317054055,0x214265801088),(0xffccffccaa88aa88ffccffccaa88aa88,0x13014054005,0x2a0554d501125),(0xffccffccffccffccffccffccffccffcc,0x19933d735407d,0x26b5f7ffd415ed),(0xffeeaa88ffeeaa88ffeeaa88ffeeaa88,0x1e133170760d5,0x214265801088),(0xffeeffeeeeeeeeeeffeeffeeeeeeeeee,0xe7f3cfc3ff6af,0x6a1d7fdddf3ed),(0xffeeffeeffccffccffeeffeeffccffcc,0x3993fd735527d,0x26b5f7ffd415ed),(0xffeeffeeffeeffeeffeeffeeffeeffee,0xfff3fff3ff6ff,0x26b5f7ffddf7ed),(0xffff0000ffff0000ffff0000ffff0000,0x1e003030220d0,0x196b4a65a2189a),(0xffff8888ffff8888ffff8888ffff8888,0x1e103170320d1,0x196b4a65a2189a),(0xffffaa88ffffaa88ffffaa88ffffaa88,0x1e133170760d5,0x196b4a65a2189a),(0xffffaaa0ffffaaa0ffffaaa0ffffaaa0,0x1e6330b0e60d6,0x196b4a65a2189a),(0xffffaaaaffff0000ffffaaaaffff0000,0x3e00f030232d0,0x196b4a65a2189a),(0xffffaaaaffff8888ffffaaaaffff8888,0x3e10f170332d1,0x196b4a65a2189a),(0xffffaaaaffffaa00ffffaaaaffffaa00,0x3e03f030672d4,0x196b4a65a2189a),(0xffffaaaaffffaa88ffffaaaaffffaa88,0x3e13f170772d5,0x196b4a65a2189a),(0xffffaaaaffffaaaaffffaaaaffffaaaa,0xfe73f3f0ff6d7,0x196b4a65abfa9a),(0xffffccccffffccccffffccccffffcccc,0x1f903d73320f9,0x1d6bdff5b619db),(0xffffffff00000000ffffffff00000000,0x3200cc00c01b00,0x12aa5d4d521135),(0xffffffff88888888aaaaaaaa88888888,0x3201cc14c11b01,0x0),(0xffffffff88888888ffffffff88888888,0x3201cc14c11b01,0x12aa5d4d521135),(0xffffffffaa00aa00ffffffffaa00aa00,0x3200fc00c45b04,0x12aa5d4d521135),(0xffffffffaa88aa88ffffffffaa88aa88,0x3201fc14c55b05,0x12aa5d4d521135),(0xffffffffaaaa0000ffffffffaaaa0000,0x3260cc00c23b80,0x12aa5d4d521135),(0xffffffffaaaa8888ffffffffaaaa8888,0x3261cc14c33b81,0x12aa5d4d521135),(0xffffffffaaaaaa00ffffffffaaaaaa00,0x3260fc00c67b84,0x12aa5d4d521135),(0xffffffffaaaaaaaaaaaaaaaa88888888,0x3e01cc34c19f01,0x0),(0xffffffffaaaaaaaaaaaaaaaaaa00aa00,0x3e00fc20c4df04,0x0),(0xffffffffaaaaaaaaaaaaaaaaaa88aa88,0x3e01fc34c5df05,0x0),(0xffffffffaaaaaaaaaaaaaaaaaaaa0000,0x3e60cc20c2bf80,0x0),(0xffffffffaaaaaaaaaaaaaaaaaaaaaaaa,0x3e67fc3ccfff87,0x9e200),(0xffffffffaaaaaaaaffffffff88888888,0x3e01cc34c19f01,0x12aa5d4d521135),(0xffffffffaaaaaaaaffffffffaa88aa88,0x3e01fc34c5df05,0x12aa5d4d521135),(0xffffffffaaaaaaaaffffffffaaaa0000,0x3e60cc20c2bf80,0x12aa5d4d521135),(0xffffffffaaaaaaaaffffffffaaaaaaaa,0x3e67fc3ccfff87,0x12aa5d4d5bf335),(0xffffffffccccccccffffffffcccccccc,0x3219ccd4f11b29,0x16abdffdd611fd),(0xffffffffeeeeeeeeffffffffeeeeeeee,0x3e7ffcfcffffaf,0x16abdffddff3fd),(0xffffffffff00aa00ffffffffff00aa00,0x3380ff03c45b54,0x12aa5d4d521135),(0xffffffffff00ff00ffffffffff00ff00,0x3380ff03c45b54,0x36befddf561575),(0xffffffffffaaaa00ffffffffffaaaa00,0x33e0ff03c67bd4,0x12aa5d4d521135),(0xffffffffffaaaa88ffffffffffaaaa88,0x33e1ff17c77bd5,0x12aa5d4d521135),(0xffffffffffaaffaaffffffffffaaffaa,0x3fe7ff3fcfffd7,0x36befddf5ff775),(0xffffffffffccffccffffffffffccffcc,0x3399ffd7f55b7d,0x36bfffffd615fd),(0xffffffffffeeffeeffffffffffeeffee,0x3fffffffffffff,0x36bfffffdff7fd),(0xffffffffffff0000ffffffffffff0000,0x33e0cf03c23bd0,0x1beb5f6df219bf),(0xffffffffffffaa00ffffffffffffaa00,0x33e0ff03c67bd4,0x1beb5f6df219bf),(0xffffffffffffaaaaffffaaaaffff0000,0x3fe0cf23c2bfd0,0x196b4a65a2189a),(0xffffffffffffaaaaffffaaaaffff8888,0x3fe1cf37c3bfd1,0x196b4a65a2189a),(0xffffffffffffaaaaffffaaaaffffaa00,0x3fe0ff23c6ffd4,0x196b4a65a2189a),(0xffffffffffffffff0000000000000000,0x3c00c020c08d00,0x2d55a2b2a40cca),(0xffffffffffffffff8888888888888888,0x3c01c034c18d01,0x2d55a2b2a40cca),(0xffffffffffffffffaa00aa00aa00aa00,0x3c00f020c4cd04,0x2d55a2b2a40cca),(0xffffffffffffffffaa88aa88aa88aa88,0x3c01f034c5cd05,0x2d55a2b2a40cca),(0xffffffffffffffffaaa0aaa0aaa0aaa0,0x3c06f028cccd06,0x2d55a2b2a40cca),(0xffffffffffffffffaaaa8888aaaa8888,0x3c61c034c3ad81,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaa88aaaaaa88,0x3c61f034c7ed85,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaa88888888,0x3e01cc34c19f01,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaaaa00aa00,0x3e00fc20c4df04,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaaaa88aa88,0x3e01fc34c5df05,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaaaaaa0000,0x3e60cc20c2bf80,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaaaaaa8888,0x3e61cc34c3bf81,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaaaaaaaa00,0x3e60fc20c6ff84,0x2d55a2b2a40cca),(0xffffffffffffffffaaaaaaaaaaaaaaaa,0x3e67fc3ccfff87,0x2d55a2b2adeeca),(0xffffffffffffffffcc88cc88cc88cc88,0x3c01c034c18d01,0x2d55b7b2b40dcb),(0xffffffffffffffffcccccccccccccccc,0x3c19c0f4f18d29,0x2d75f7f7b41dcb),(0xffffffffffffffffeecceecceecceecc,0x3c19f0f4f5cd2d,0x2d75f7f7b41dcb),(0xffffffffffffffffeeeeeeeeeeeeeeee,0x3e7ffcfcffffaf,0x2d75f7f7bdffcb),(0xffffffffffffffffff00ff00ff00ff00,0x3d80f323c4cd54,0x2fd5b7baf40def),(0xffffffffffffffffff88ff88ff88ff88,0x3d81f337c5cd55,0x2fd5b7baf40def),(0xffffffffffffffffffaaaa88ffaaaa88,0x3de1f337c7edd5,0x2d55a2b2a40cca),(0xffffffffffffffffffaaaaaaffaaaa00,0x3fe0ff23c6ffd4,0x2d55a2b2a40cca),(0xffffffffffffffffffaaffaaff88ff88,0x3f81ff37c5df55,0x2fd5b7baf40def),(0xffffffffffffffffffaaffaaffaaffaa,0x3fe7ff3fcfffd7,0x2fd5b7bafdefef),(0xffffffffffffffffffccffccffccffcc,0x3d99f3f7f5cd7d,0x2ff5f7fff41def),(0xffffffffffffffffffff0000ffff0000,0x3de0c323c2add0,0x3d7feaf7a61cda),(0xffffffffffffffffffffccccffffcccc,0x3df9c3f7f3adf9,0x3d7ffff7b61ddb),(0xffffffffffffffffffffffffaa88aa88,0x3e01fc34c5df05,0x3ffffffff61dff),(0xffffffffffffffffffffffffcccccccc,0x3e19ccf4f19f29,0x3ffffffff61dff)]
def windRows : Nat → Array WindRow
  | 4 => #[([3,5,13,60,91],989568,[]),([3,5,13,61,90],742788,[]),([5,13,17,51,67],924160,[]),([5,13,17,51,68],874756,[]),([5,13,17,51,69],923968,[])]
  | 5 => #[([3,5,13,17,29,47],808964,[]),([3,5,13,17,29,49],874564,[]),([3,5,13,17,33,50],924160,[]),([3,5,13,17,34,47],874756,[]),([3,5,13,17,35,48],923968,[]),([3,5,13,17,37,50],924160,[]),([3,5,13,17,47,68],874756,[144,64]),([3,5,13,17,48,69],923968,[192,16]),([3,5,13,17,50,67],924160,[96,20]),([5,13,17,29,47,51],808964,[106,200,146,144]),([5,13,17,29,51,52],812036,[])]
  | 6 => #[([0,3,5,13,20,39,70],213380,[122,216,162,160]),([3,4,16,17,29,39,70],361556,[]),([3,5,6,17,29,39,70],361556,[]),([3,5,13,17,25,39,70],147780,[]),([3,5,13,17,29,39,71],548868,[]),([3,5,13,17,29,39,71],614468,[]),([3,5,13,17,29,39,73],611396,[]),([3,5,13,17,29,39,73],614468,[]),([3,5,13,17,29,39,77],611396,[]),([3,5,13,17,29,39,79],611396,[]),([3,5,13,17,29,40,77],808964,[484]),([3,5,13,17,29,41,77],808964,[]),([3,5,13,17,29,43,73],611396,[]),([3,5,13,17,29,43,79],611396,[]),([3,5,13,17,29,43,79],874564,[]),([3,5,13,17,29,47],808964,[250,432,394,344,290,288]),([3,5,13,17,29,47,52],812036,[480]),([3,5,13,17,29,47,55],808964,[]),([3,5,13,17,29,47,56],808964,[]),([3,5,13,17,29,52,77],808964,[0]),([3,5,13,17,29,52,83],812036,[4]),([3,5,13,17,29,53,83],877636,[52]),([3,5,13,17,30,39,75],414212,[]),([3,5,13,17,30,45,75],677380,[]),([3,5,13,17,31,39,73],414020,[]),([3,5,13,17,31,39,76],414020,[]),([3,5,13,17,31,43,73],677188,[]),([3,5,13,17,33,39,80],660992,[]),([3,5,13,17,33,44,70],657920,[]),([3,5,13,17,33,44,80],924160,[]),([3,5,13,17,33,55,70],657920,[]),([3,5,13,17,33,55,80],924160,[96]),([3,5,13,17,34,39,81],611588,[]),([3,5,13,17,34,39,81],677380,[]),([3,5,13,17,34,41,77],874756,[]),([3,5,13,17,34,45,70],411140,[]),([3,5,13,17,34,45,70],674308,[]),([3,5,13,17,34,55,70],608516,[]),([3,5,13,17,34,55,70],674308,[]),([3,5,13,17,34,55,77],874756,[144]),([3,5,13,17,35,39,78],660800,[]),([3,5,13,17,35,39,82],660800,[]),([3,5,13,17,35,42,78],923968,[]),([3,5,13,17,35,46,70],657728,[]),([3,5,13,17,35,55,70],657728,[]),([3,5,13,17,35,55,78],923968,[192]),([3,5,13,17,35,58,70],657728,[]),([3,5,13,17,36,39,79],677188,[]),([3,5,13,17,36,55,70],674116,[]),([3,5,13,17,37,44,80],924160,[]),([3,5,13,17,37,45,75],677380,[]),([3,5,13,17,37,54,83],927232,[244]),([3,5,14,17,32,39,74],430432,[]),([3,5,14,19,29,39,74],430240,[]),([3,5,14,21,29,39,74],430240,[]),([3,5,15,17,31,39,73],430420,[]),([3,5,15,21,29,39,73],430228,[]),([3,5,16,21,29,55,70],673936,[]),([5,13,17,29,52,55,83],812036,[480])]
  | 7 => #[([0,3,5,13,17,29,39,70],345156,[276,416,260,400,340,288]),([0,3,5,13,17,29,39,73],348228,[1066,1160,1058,1152,576]),([0,3,5,13,17,29,43,73],611396,[1114,1256,1106,1248]),([0,3,5,13,17,31,39,70],147780,[1322,1944,544,1156,1152]),([0,3,5,13,17,31,39,73],414020,[2497,2640,1648,1248]),([0,3,5,13,18,29,39,70],147588,[1370,1338,544,1062,1058]),([0,3,5,13,18,29,39,73],413828,[2545,2505,1648,1106]),([0,3,5,13,18,31,39,70],213380,[1418,2040,1650,1648]),([0,3,5,13,21,29,39,70],147588,[1466,2136,980,1794,1792]),([0,3,5,13,21,29,39,73],413828,[2593,2688,1888,2402]),([0,3,5,13,21,31,39,70],213380,[1514,2184,1890,1888,0]),([0,3,5,15,17,31,39,70],164180,[2056,2040,2644,2640]),([0,3,5,15,18,29,39,70],163988,[1434,2040,2509,2505]),([0,3,5,15,21,29,39,70],163988,[2394,2184,2692,2688]),([0,3,8,13,18,29,39,70],163976,[1434,1418,2549,2545]),([0,3,8,13,21,29,39,70],163976,[2394,1514,2597,2593]),([0,3,12,13,21,29,39,70],163976,[2494,2478,2761,2760]),([1,3,5,15,17,29,39,70],98388,[944,2088,1992,1212,1208]),([2,3,5,13,17,29,39,70],345156,[372,464,356,448,340,432]),([2,3,5,13,17,29,39,79],611396,[1594,2264,1586,2256,672]),([2,3,5,13,17,29,43,70],345156,[1690,1570,1682,1554,624]),([2,3,5,13,17,29,43,70],608324,[1738,1618,1730,1602,672]),([2,3,5,13,17,29,55,70],608324,[1834,2312,1826,2304,1012]),([3,5,9,13,17,29,39,70],345156,[372]),([3,5,9,13,17,29,55,70],608324,[1834]),([3,5,10,13,17,29,39,70],345156,[]),([3,5,11,13,17,29,39,78],611396,[]),([3,5,11,13,17,29,42,70],608324,[]),([3,5,11,13,17,29,55,70],608324,[]),([3,5,11,16,17,29,39,70],361556,[]),([3,5,12,13,17,29,39,70],345156,[]),([3,5,12,13,17,29,39,72],614468,[]),([3,5,12,13,17,29,39,78],611396,[]),([3,5,12,16,17,29,39,70],361556,[96]),([3,5,13,17,22,31,39,70],147780,[2248]),([3,5,13,17,23,29,43,70],345156,[]),([3,5,13,17,23,29,43,70],608324,[]),([3,5,13,17,24,29,39,73],614468,[]),([3,5,13,17,24,29,39,79],611396,[]),([3,5,13,17,24,29,43,73],611396,[]),([3,5,13,17,24,31,39,73],414020,[]),([3,5,13,17,24,36,39,70],410948,[]),([3,5,13,17,26,29,39,70],345156,[]),([3,5,13,17,27,29,39,70],345156,[]),([3,5,13,17,28,29,39,73],348228,[]),([3,5,13,17,28,31,39,70],147780,[144]),([3,5,13,17,29,39,63,70],345156,[]),([3,5,13,17,29,39,63,73],611396,[]),([3,5,13,17,29,39,63,77],611396,[]),([3,5,13,17,29,39,63,79],611396,[]),([3,5,13,17,29,39,64,70],345156,[]),([3,5,13,17,29,39,71,83],548868,[]),([3,5,13,17,29,39,71,87],548868,[]),([3,5,13,17,29,39,71,89],614468,[]),([3,5,13,17,29,39,71,93],614468,[]),([3,5,13,17,29,39,71,94],614468,[]),([3,5,13,17,29,39,73],614468,[1856,1840]),([3,5,13,17,29,39,73,83],348228,[72]),([3,5,13,17,29,39,73,83],614468,[]),([3,5,13,17,29,39,73,85],614468,[240]),([3,5,13,17,29,39,73,94],348228,[]),([3,5,13,17,29,39,73,94],614468,[]),([3,5,13,17,29,39,73,97],611396,[]),([3,5,13,17,29,39,77,83],545796,[2788]),([3,5,13,17,29,39,77,92],611396,[]),([3,5,13,17,29,39,77,98],545796,[]),([3,5,13,17,29,39,79],611396,[2336,2320,1012]),([3,5,13,17,29,39,83,84],614468,[240]),([3,5,13,17,29,39,83,85],548868,[192]),([3,5,13,17,29,39,83,86],614468,[336]),([3,5,13,17,29,41,56,77],808964,[]),([3,5,13,17,29,41,77],808964,[2362,964,480]),([3,5,13,17,29,43,73],611396,[2410,2402]),([3,5,13,17,29,52,83],812036,[2458,2784,724,820,768]),([3,5,13,17,29,52,83,85],812036,[868,532]),([3,5,13,17,30,38,39,75],414212,[]),([3,5,13,17,30,39,75],414212,[2600,1796]),([3,5,13,17,31,39,73],414020,[2696,1888]),([3,5,13,17,33,37,55,70],657920,[]),([3,5,13,17,33,39,65,80],660992,[]),([3,5,13,17,33,39,80],660992,[2132,1488]),([3,5,13,17,33,44,65,70],657920,[]),([3,5,13,17,33,44,70],657920,[1462,1440]),([3,5,13,17,33,55,65,70],657920,[1344]),([3,5,13,17,33,55,70],657920,[]),([3,5,13,17,34,55,56,70],608516,[1074]),([3,5,13,17,34,55,70],608516,[2744]),([3,5,13,17,35,39,59,78],660800,[]),([3,5,13,17,35,39,78],660800,[2176,2160]),([3,5,13,17,35,55,59,70],657728,[1314]),([3,5,13,17,35,55,70],657728,[2470]),([3,5,13,17,35,59,66,70],657728,[2208]),([3,5,13,17,37,39,83,96],680452,[1828,1844])]
  | 8 => #[([0,3,5,13,17,24,29,39,73],348228,[3610,1928,3602,1920,1872]),([0,3,5,13,17,24,31,39,70],147780,[3818,4200,3376,1924,1920]),([0,3,5,13,17,28,29,39,70],81988,[2532,2168,2516,2160,2116,2112]),([0,3,5,13,17,29,39,43,70],345156,[1336,1288,1320,1272,1416]),([0,3,5,13,17,29,39,55,70],345156,[1532,1576,1516,1560,2788,1608]),([0,3,5,13,17,29,39,63,70],345156,[2676,2336,2660,2320,2932,2256]),([0,3,5,13,17,29,39,73],348228,[3658,296,3704,200,3650,288,3696,192,3456,1416,96,440,432]),([0,3,5,13,17,31,39,70],147780,[3866,584,4248,528,3424,336,3700,1272,196,3696,1273,192,632,480]),([0,3,5,13,18,24,29,39,70],147588,[3914,3834,3376,3606,3602]),([0,3,5,13,18,29,39,70],147588,[3962,672,3882,576,3424,336,3654,1320,292,3650,1321,288,728,384]),([0,3,5,13,21,24,29,39,70],147588,[4010,4296,3572,4098,4096,240]),([0,3,5,13,21,29,39,70],147588,[4058,720,4344,624,3524,480,4146,1368,436,4144,1369,432,768]),([2,3,5,13,17,24,29,39,70],345156,[2868,1976,2852,0,2064,1968,1780,1824]),([2,3,5,13,17,29,39,63,70],345156,[2964,2384,2948,2368,2932,2352]),([2,3,5,13,17,29,39,70],345156,[2724,1040,3200,944,2708,1024,3184,928,2692,1008,3168,912,1088,1072,1056]),([3,5,7,12,13,17,29,39,70],81988,[]),([3,5,7,13,17,29,39,70],81988,[2040,2041]),([3,5,9,12,13,17,29,39,70],345156,[2820]),([3,5,9,13,17,29,39,59,70],345156,[1812]),([3,5,9,13,17,29,39,70],345156,[32,1200,1168,1152,2724,1760]),([3,5,11,13,17,29,39,59,70],345156,[2964,1104,2208]),([3,5,11,13,17,29,39,70],345156,[2820,864,1440,1360,1344]),([3,5,12,13,17,28,29,39,70],81988,[]),([3,5,12,13,17,29,39,62,70],345156,[1200,2400]),([3,5,12,13,17,29,39,64,70],345156,[]),([3,5,12,13,17,29,39,83,88],614468,[4426,1156,1488]),([3,5,13,17,24,29,39,64,70],345156,[]),([3,5,13,17,24,29,39,73],348228,[4112,4096,48,2112,2256,1684,2880]),([3,5,13,17,24,29,39,83,94],614468,[1776]),([3,5,13,17,24,31,39,70],147780,[4312,3572,144,2160,4408,1632,3136,2320,2322]),([3,5,13,17,28,29,39,57,70],345156,[2016,2400]),([3,5,13,17,28,29,39,63,70],345156,[2064,2400]),([3,5,13,17,28,29,39,64,70],345156,[]),([3,5,13,17,28,29,39,70],81988,[2400,2404]),([3,5,13,17,29,39,63,64,70],345156,[]),([3,5,13,17,29,39,64,70],345156,[]),([3,5,13,17,29,39,71],548868,[4064,1496,1497,258,2448,2544,2546]),([3,5,13,17,29,39,71,83],548868,[3776,402,3320,2592,3321,2594]),([3,5,13,17,29,39,71,83,85],548868,[2496]),([3,5,13,17,29,39,71,85],548868,[4016,3264,258,2496,2640,2642]),([3,5,13,17,29,39,73],348228,[4160,4144,1608,964,2736,2976]),([3,5,13,17,29,39,77],545796,[4352,1544,1545,3508,840,3024,3072,3074]),([3,5,13,17,29,39,83,85,87],548868,[2496]),([3,5,13,17,29,39,83,85,93],614468,[2592,3216]),([3,5,13,17,29,39,83,85,94],614468,[2640,2832]),([3,5,13,17,29,39,83,94],614468,[4426,4418,1060,2688,2928,2784]),([3,5,13,17,37,39,83,95],664064,[803,4416,4417,4036,3988,3748,4052,4004,3764])]
  | 9 => #[([0,3,5,13,17,24,29,39,70],81988,[1908,392,1400,56,1892,384,1392,48,1300,984,4,1296,985,0,488,480,96,240,244]),([0,3,5,13,17,29,39,70],81988,[1764,440,2000,344,1748,432,1984,336,1924,1032,292,144,1920,1033,288,148,536,528,192,196]),([3,5,12,13,17,21,29,39,70],81988,[2238,1236,1238,768,728,720,1584,1064,1056,1112,1116,1220,1222,1104,1108]),([3,5,12,13,17,28,29,39,70],81988,[2108,2109,1440,1444,1152,1156]),([3,5,12,13,17,29,39,59,70],345156,[1220,1204,224,1104,2196,1380,912,864,816,1680,1280,1152]),([3,5,13,17,24,28,29,39,70],81988,[2052,2036,96,1488,1492,1248,1252]),([3,5,13,17,24,29,39,63,70],345156,[2148,2132,240,1488,1348,576,1248]),([3,5,13,17,28,29,39,70],81988,[1128,1129,1680,1536,1684,1540]),([3,5,13,17,29,39,63,70],345156,[2196,2180,2164,672,624,1680,1632]),([3,5,13,17,29,39,83,85],548868,[2218,1208,1209,546,498,2016,2064,2160,2112,2066,2162,2114,1728,1872,1776,1824,2016])]
  | 10 => #[([3,5,12,13,17,29,39,70],16388,[96,98,112,114,468,469,476,477,336,144,338,146,352,160,354,162,192,196,194,198]),([3,5,13,17,24,29,39,70],81988,[468,452,48,0,336,240,216,217,384,288,388,292])]
  | 11 => #[([3,5,13,17,29,39,70],0,[0,1,8,9,24,25,48,50,64,66,49,51,65,67,80,82,81,83])]
  | _ => #[]

end C10981.Signed


namespace C10981.Signed

def wOpen (n : Nat) : Sig := (BitVec.ofNat 512 n) * (BitVec.ofNat 512 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001)

def windRead (i : Nat) : WindPack :=
  let (w,p,n) := windWords[i]?.getD (0,0,0)
  (wOpen w,p,n)

def forceWindN {α : Type} : Nat → (Nat → α) → α
  | 0,f => f 0
  | n+1,f => f (n+1)

def forceWindP {α : Type} (w : WindPack) (f : WindPack → α) : α :=
  forceWindN w.1.toNat fun x => forceWindN w.2.1.toNat fun y => forceWindN w.2.2.toNat fun z =>
    f (BitVec.ofNat _ x,BitVec.ofNat _ y,BitVec.ofNat _ z)

def windState : List Nat → List WindPack
  | [] => []
  | i::is => forceWindP (windRead i) fun w => w :: windState is

def windBase (op : Bool) (a b : WindSample) : WindSample := if op then a ||| b else a &&& b

def windBin (d : Bool) (a b : WindPack) : WindPack :=
  (prime d a.1 b.1,windBase d a.2.1 b.2.1,windBase d a.2.2 b.2.2)

def windChild (ws : List WindPack) (z a b : WindPack) (ka kb : Bool) : List WindPack :=
  z :: kept ka a (kept kb b ((ws.eraseP (fun p => a.1 == p.1)).eraseP (fun p => b.1 == p.1)))

def windCover : List WindPack → WindSample
  | [] => 0
  | w::ws => (w.2.1 &&& ~~~w.2.2) ||| windCover ws

def cutSelection (i : Cut) : Sig := wOpen (([0x33333333333333333333333333333333,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xff00ff00ff00ff00ff00ff00ff00ff,0xffff0000ffff0000ffff0000ffff,0xffffffff00000000ffffffff,0xffffffffffffffff,0x3030303030303030303030303030303,0xff000000ff000000ff000000ff,0xffffffff] : List Nat).getD i.val 0)

def fastZero (i : Cut) (w : Sig) : Bool := (w &&& cutSelection i) == zero

def decodeDebt (n : Nat) (i : Cut) : Nat := (n >>> (2*(i.val+1))) &&& 3

def plusDebt (parent : Cut → Nat) (a b : Sig) (i : Cut) : Nat :=
  parent i + (fastZero i a || fastZero i b).toNat

def admBudget (ws : List WindPack) (p : Cut → Nat) : Bool :=
  (List.finRange 9).all fun i => p i + ws.countP (fun w => fastZero i w.1) ≤ profileLimit i

def windKids (cap : Nat) (ws : List WindPack) (p : Cut → Nat) : List (List WindPack × (Cut → Nat)) :=
  ws.flatMap fun a => ws.flatMap fun b =>
    if a.1.toNat < b.1.toNat then
      [false,true].flatMap fun d =>
        forceWindP (windBin d a b) fun z =>
          if z.1 == 0 || ws.any (fun w => w.1 == z.1) then [] else
          [false,true].flatMap fun ka => [false,true].filterMap fun kb =>
            let next := windChild ws z a b ka kb
            let inc := plusDebt p a.1 b.1
            if next.length ≤ cap && windCover next == BitVec.allOnes 54 && admBudget next inc then some (next,inc) else none
    else []

def windLink (cap : Nat) (node : List WindPack × (Cut → Nat)) (h : Nat) : Bool :=
  match (windRows cap)[h/48]? with
  | none => false
  | some dst =>
    let gs := genSequence (h % 48)
    let source := (node.1.map Prod.fst).map (autoWind gs)
    let into := (windState dst.1).map Prod.fst
    source.all into.contains && into.all source.contains &&
      (List.finRange 9).all fun i => node.2 (relabelCut gs i) == decodeDebt dst.2.1 i

def windLinks (cap : Nat) : List (List WindPack × (Cut → Nat)) → List Nat → Bool
  | [],[] => true
  | q::qs,h::hs => windLink cap q h && windLinks cap qs hs
  | _,_ => false

def windNode (cap : Nat) (row : WindRow) : Bool :=
  let ws := windState row.1
  decide (ws.map Prod.fst).Nodup && !(ws.any fun a => a.1 == wind) &&
  (if cap = 0 then true else windLinks (cap-1) (windKids cap ws (decodeDebt row.2.1)) row.2.2)

def windBlock (cap start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => windNode cap ((windRows cap)[start]?.getD ([],0,[])) && windBlock cap (start+1) n

end C10981.Signed


namespace C10981.Signed

set_option maxRecDepth 32768 in
lemma cut_selection : ∀ i : Cut, ∀ r : Row,
    bit r (cutSelection i) = decide (movedRow (profileCut i) r = r) := by decide +kernel

set_option maxRecDepth 32768 in
lemma cut_idem : ∀ i : Cut, ∀ r : Row,
    movedRow (profileCut i) (movedRow (profileCut i) r) = movedRow (profileCut i) r := by decide +kernel

lemma fastZero_correct (i : Cut) (a : Sig) : fastZero i a = zeroAfter (profileCut i) a := by
  have iff_zero : a &&& cutSelection i = zero ↔ movedWord (profileCut i) a = zero := by
    constructor
    · intro h
      apply bit_ext
      intro r
      let s := movedRow (profileCut i) r
      have same : bit s (cutSelection i) = true := by
        change bit (movedRow (profileCut i) r) (cutSelection i) = true
        rw [cut_selection,cut_idem]; exact decide_eq_true rfl
      have hx := congrArg (bit s) h
      rw [bit_and,same,bit_zero] at hx
      rw [bit_moved,bit_zero]
      simpa only [Bool.and_true] using hx
    · intro h
      apply bit_ext
      intro r
      rw [bit_and,bit_zero,cut_selection]
      by_cases eq : movedRow (profileCut i) r = r
      · have hx := congrArg (bit r) h
        rw [bit_moved,eq,bit_zero] at hx
        simp [eq,hx]
      · simp [eq]
  unfold fastZero zeroAfter
  by_cases h : a &&& cutSelection i = zero
  · simp [h, iff_zero.mp h]
  · have n : movedWord (profileCut i) a ≠ zero := fun x => h (iff_zero.mpr x)
    simp [h,n]

end C10981.Signed

namespace C10981.Signed

def windPosRow (i : Fin 54) : Row := Fin.ofNat 512 (windPos.getD i.val 0)
def windNegRow (i : Fin 54) : Row := Fin.ofNat 512 (windNeg.getD i.val 0)

abbrev WindFaith (w : WindPack) : Prop := ∀ i : Fin 54,
  w.2.1.getLsbD i.val = bit (windPosRow i) w.1 ∧
  w.2.2.getLsbD i.val = bit (windNegRow i) w.1

lemma forceWindN_eval {α : Type} (n : Nat) (f : Nat → α) : forceWindN n f = f n := by
  cases n <;> rfl

lemma forceWindP_eval {α : Type} (w : WindPack) (f : WindPack → α) : forceWindP w f = f w := by
  rcases w with ⟨a,b,c⟩
  simp [forceWindP,forceWindN_eval]

lemma windState_map (xs : List Nat) : windState xs = xs.map windRead := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [windState,forceWindP_eval,ih]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma windRead_faith (i : Nat) : WindFaith (windRead i) := by
  by_cases h : i < windWords.size
  · exact (show ∀ j : Fin windWords.size, WindFaith (windRead j.val) by decide +kernel) ⟨i,h⟩
  · have none : windWords[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt h)
    unfold windRead
    rw [none]
    exact (show WindFaith (wOpen 0,0,0) by decide +kernel)

lemma wind_state_faith (xs : List Nat) : ∀ w ∈ windState xs, WindFaith w := by
  intro w hw
  rw [windState_map] at hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact windRead_faith i

lemma wind_bin_faith (d : Bool) {a b : WindPack} (ha : WindFaith a) (hb : WindFaith b) :
    WindFaith (windBin d a b) := by
  intro i
  obtain ⟨ap,an⟩ := ha i
  obtain ⟨bp,bn⟩ := hb i
  cases d <;>
    simp only [windBin,windBase,bit_prime,Bool.false_eq_true,ite_false,ite_true,
      BitVec.getLsbD_and,BitVec.getLsbD_or,ap,an,bp,bn,and_self]

private lemma wind_cover_bit (ws : List WindPack) {w : WindPack} (hw : w ∈ ws) (i : Fin 54)
    (hv : (w.2.1 &&& ~~~w.2.2).getLsbD i.val = true) :
    (windCover ws).getLsbD i.val = true := by
  induction ws with
  | nil => simp at hw
  | cons a ws ih =>
    rcases List.mem_cons.mp hw with rfl | wh
    · simp only [windCover,BitVec.getLsbD_or,hv,Bool.true_or]
    · simp only [windCover,BitVec.getLsbD_or,ih wh,Bool.or_true]

private lemma wind_pair_good : ∀ i : Fin 54,
    bit (windPosRow i) wind = true ∧ bit (windNegRow i) wind = false := by decide +kernel

lemma wind_full_cover {ws : List WindPack} {k : ℕ}
    (fp : ∀ w ∈ ws, WindFaith w) (h : Live false wind k (ws.map Prod.fst).toFinset) :
    windCover ws = BitVec.allOnes 54 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i il
  let j : Fin 54 := ⟨i,il⟩
  obtain ⟨a,am,ap,an⟩ := mono_row_difference h rfl (wind_pair_good j).1 (wind_pair_good j).2
  obtain ⟨w,wm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp am)
  have wf := fp w wm j
  simp only [BitVec.getLsbD_allOnes,il,decide_true]
  apply wind_cover_bit ws wm j
  rw [BitVec.getLsbD_and,BitVec.getLsbD_not,wf.1,wf.2,ap,an]
  simp [j.isLt]

lemma wind_prime_bin (d : Bool) (a b : Sig) : prime d a b = bin d.toNat a b := by
  cases d <;> rfl

lemma wind_packed_child (ws : List WindPack) (a b : WindPack) (d ka kb : Bool) :
    (windChild ws (windBin d a b) a b ka kb).map Prod.fst =
    childTwo (ws.map Prod.fst) a.1 b.1 d.toNat ka kb := by
  cases ka <;> cases kb <;>
    simp [windChild,windBin,wind_prime_bin,kept,childTwo,List.erase_eq_eraseP,
      List.eraseP_map,Function.comp_def]

lemma wind_inherits_faith {ws : List WindPack} (fp : ∀ w ∈ ws, WindFaith w)
    {a b : WindPack} (am : a ∈ ws) (bm : b ∈ ws) (d ka kb : Bool) :
    ∀ w ∈ windChild ws (windBin d a b) a b ka kb, WindFaith w := by
  intro w hw
  unfold windChild at hw
  have rest (h : w ∈ (ws.eraseP fun p => a.1 == p.1).eraseP (fun p => b.1 == p.1)) : WindFaith w :=
    fp w (List.mem_of_mem_eraseP (List.mem_of_mem_eraseP h))
  have a' := fp a am
  have b' := fp b bm
  have z := wind_bin_faith d a' b'
  cases ka <;> cases kb <;> simp only [kept,List.mem_cons,Bool.false_eq_true,ite_false,ite_true] at hw
  · rcases hw with rfl | h
    · exact z
    · exact rest h
  · rcases hw with rfl | rfl | h
    · exact z
    · exact b'
    · exact rest h
  · rcases hw with rfl | rfl | h
    · exact z
    · exact a'
    · exact rest h
  · rcases hw with rfl | rfl | rfl | h
    · exact z
    · exact a'
    · exact b'
    · exact rest h

end C10981.Signed


namespace C10981.Signed

def WindImpossible (cap : Nat) (S : Finset Sig) (p : Cut → Nat) : Prop :=
  ∀ tr, Trace wind S tr → tr.length ≤ cap → (∀ i, p i + lost (profileCut i) tr ≤ profileLimit i) → False

def windCert (cap : Nat) (row : WindRow) : Prop :=
  WindImpossible cap ((windState row.1).map Prod.fst).toFinset (decodeDebt row.2.1)

lemma wind_link_sound {cap : Nat}
    (prior : ∀ (j : Nat) (r : WindRow), (windRows cap)[j]? = some r → windCert cap r)
    (qs : List WindPack) (p : Cut → Nat) (hint : Nat)
    (chk : windLink cap (qs,p) hint = true) : WindImpossible cap (qs.map Prod.fst).toFinset p := by
  unfold windLink at chk
  split at chk
  · contradiction
  · rename_i row rr
    simp only [Bool.and_eq_true] at chk
    obtain ⟨⟨src,dst⟩,budget⟩ := chk
    let gs := genSequence (hint % 48)
    have same : ((qs.map Prod.fst).toFinset).image (autoWind gs) =
        ((windState row.1).map Prod.fst).toFinset := by
      ext w
      constructor
      · intro hm
        obtain ⟨x,xm,rfl⟩ := Finset.mem_image.mp hm
        have m : autoWind gs x ∈ (qs.map Prod.fst).map (autoWind gs) :=
          List.mem_map.mpr ⟨x,List.mem_toFinset.mp xm,rfl⟩
        exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (List.all_eq_true.mp src _ m))
      · intro hm
        have m : w ∈ (qs.map Prod.fst).map (autoWind gs) :=
          List.contains_iff_mem.mp (List.all_eq_true.mp dst _ (List.mem_toFinset.mp hm))
        obtain ⟨x,xm,hx⟩ := List.mem_map.mp m
        exact Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr xm,hx⟩
    intro tr run le capok
    have moved := auto_trace run gs
    rw [same] at moved
    refine prior _ _ rr _ moved (by simpa using le) ?_
    intro i
    have e : p (relabelCut gs i) = decodeDebt row.2.1 i :=
      beq_iff_eq.mp (List.all_eq_true.mp budget i (List.mem_finRange i))
    rw [← e,lost_auto,← limit_auto gs i]
    exact capok (relabelCut gs i)

lemma wind_links_mem {cap : Nat} {nodes : List (List WindPack × (Cut → Nat))} {hints : List Nat}
    (chk : windLinks cap nodes hints = true) {node : List WindPack × (Cut → Nat)} (m : node ∈ nodes) :
    ∃ i, windLink cap node i = true := by
  induction nodes generalizing hints with
  | nil => simp at m
  | cons x xs ih =>
    cases hints with
    | nil => cases chk
    | cons y ys =>
      simp only [windLinks,Bool.and_eq_true] at chk
      rcases List.mem_cons.mp m with rfl | hm
      · exact ⟨y,chk.1⟩
      · exact ih chk.2 hm

lemma wind_zeros_eq (ws : List WindPack) (d : (ws.map Prod.fst).Nodup) (i : Cut) :
    ws.countP (fun w => fastZero i w.1) = zeroCount (profileCut i) (ws.map Prod.fst).toFinset := by
  unfold zeroCount
  rw [← List.toFinset_filter]
  rw [List.toFinset_card_of_nodup (d.filter _),← List.countP_eq_length_filter,List.countP_map]
  apply List.countP_congr
  intro a ha
  simp only [Function.comp_apply,fastZero_correct]

lemma wind_child_budget {ws : List WindPack} (nd : (ws.map Prod.fst).Nodup)
    (p : Cut → Nat) (s : Sig) (t : Sig) (op : Bool) {tr : List StepInfo}
    (run : Trace wind (ws.map Prod.fst).toFinset tr)
    (valid : ∀ i, p i + lost (profileCut i) ((s,t,op)::tr) ≤ profileLimit i) :
    admBudget ws (plusDebt p s t) = true ∧
      ∀ i, plusDebt p s t i + lost (profileCut i) tr ≤ profileLimit i := by
  have hbound (i : Cut) : plusDebt p s t i + lost (profileCut i) tr ≤ profileLimit i := by
    unfold plusDebt
    rw [fastZero_correct,fastZero_correct]
    have v := valid i
    unfold lost at v ⊢
    rw [List.countP_cons] at v
    cases q : stepLost (profileCut i) (s,t,op)
    · have e : (zeroAfter (profileCut i) s || zeroAfter (profileCut i) t) = false := q
      simp [q,e] at v ⊢
      exact v
    · have e : (zeroAfter (profileCut i) s || zeroAfter (profileCut i) t) = true := q
      simp [q,e] at v ⊢
      omega
  refine ⟨List.all_eq_true.mpr (fun i hi => ?_),hbound⟩
  have nz : ∀ i : Cut, zeroAfter (profileCut i) wind = false := by decide +kernel
  have cnt := trace_has_losses run (profileCut i) (nz i)
  have le := hbound i
  change decide (plusDebt p s t i + ws.countP (fun w => fastZero i w.1) ≤ profileLimit i) = true
  apply decide_eq_true_eq.mpr
  rw [wind_zeros_eq ws nd i]
  omega

lemma wind_child_member (cap : Nat) (ws : List WindPack) (p : Cut → Nat)
    {a b : WindPack} {d ka kb : Bool}
    (am : a ∈ ws) (bm : b ∈ ws) (h : a.1.toNat < b.1.toNat)
    (fresh : (windBin d a b).1 ∉ ws.map Prod.fst) (proper : (windBin d a b).1 ≠ zero)
    (sz : (windChild ws (windBin d a b) a b ka kb).length ≤ cap)
    (budget : admBudget (windChild ws (windBin d a b) a b ka kb) (plusDebt p a.1 b.1) = true)
    (cover : windCover (windChild ws (windBin d a b) a b ka kb) = BitVec.allOnes 54) :
    (windChild ws (windBin d a b) a b ka kb,plusDebt p a.1 b.1) ∈ windKids cap ws p := by
  unfold windKids
  refine List.mem_flatMap.mpr ⟨a,am,List.mem_flatMap.mpr ⟨b,bm,?_⟩⟩
  rw [if_pos h]
  refine List.mem_flatMap.mpr ⟨d,by cases d <;> simp,?_⟩
  rw [forceWindP_eval]
  have no : (ws.any fun v => v.1 == (windBin d a b).1) = false := by
    cases e : (ws.any fun v => v.1 == (windBin d a b).1)
    · rfl
    · obtain ⟨w,wm,wz⟩ := List.any_eq_true.mp e
      exact False.elim (fresh (List.mem_map.mpr ⟨w,wm,beq_iff_eq.mp wz⟩))
  have no0 : ((windBin d a b).1 == (0 : Sig)) = false := by
    cases eq : ((windBin d a b).1 == (0 : Sig))
    · rfl
    · exact False.elim (proper (beq_iff_eq.mp eq))
  simp only [no0,no,Bool.false_or,Bool.false_eq_true,if_false]
  refine List.mem_flatMap.mpr ⟨ka,by cases ka <;> simp,List.mem_filterMap.mpr ⟨kb,by cases kb <;> simp,?_⟩⟩
  simp [sz,budget,cover]

end C10981.Signed

namespace C10981.Signed

lemma wind_kept_exact (ws : List Sig) (nd : ws.Nodup) {a b : Sig} {U : Finset Sig}
    (roots : ws.toFinset = insert a (insert b U)) (neq : a ≠ b) :
    (kept (decide (a ∈ U)) a (kept (decide (b ∈ U)) b ((ws.erase a).erase b))).toFinset = U := by
  rw [kept_fin,kept_fin,erase_fin (nd.erase _) b,erase_fin nd a,roots]
  ext j
  by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
    by_cases jb : j=b <;> simp_all

set_option maxRecDepth 32768 in
lemma wind_node_sound (cap : Nat) (row : WindRow)
    (prev : ∀ (i : Nat) (r : WindRow), (windRows (cap-1))[i]? = some r → windCert (cap-1) r)
    (chk : windNode cap row = true) : windCert cap row := by
  classical
  let ws := windState row.1
  let p := decodeDebt row.2.1
  have fp := wind_state_faith row.1
  simp only [windNode,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at chk
  obtain ⟨⟨nd,notWind⟩,checked⟩ := chk
  have nd : (ws.map Prod.fst).Nodup := nd
  have hout : wind ∉ (ws.map Prod.fst).toFinset := by
    intro h
    obtain ⟨x,xm,xe⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    have y : (ws.any fun a => a.1 == wind) = true := List.any_eq_true.mpr ⟨x,xm,beq_iff_eq.mpr xe⟩
    rw [y] at notWind
    contradiction
  intro tr run le profile
  generalize eqS : (ws.map Prod.fst).toFinset = S at run
  generalize ew : wind = target' at run
  cases run with
  | stop good => exact hout (by simp [eqS,← ew])
  | @step U s t d rest hs ht st fr remain =>
    subst target'
    have capNZ : cap ≠ 0 := by simp at le; omega
    have checks : windLinks (cap-1) (windKids cap ws p) row.2.2 = true := by simpa [capNZ] using checked
    have order_case (a b : Sig) (neq : a ≠ b) (order : a.toNat < b.toNat)
        (roots : (ws.map Prod.fst).toFinset = insert a (insert b U))
        (fresh : prime d a b ∉ insert a (insert b U))
        (run' : Trace wind (insert (prime d a b) U) rest)
        (bound : ∀ i, p i + lost (profileCut i) ((a,b,d)::rest) ≤ profileLimit i) : False := by
      have am' : a ∈ ws.map Prod.fst := List.mem_toFinset.mp (roots.symm ▸ Finset.mem_insert_self _ _)
      have bm' : b ∈ ws.map Prod.fst := List.mem_toFinset.mp (roots.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      obtain ⟨x,xm,rfl⟩ := List.mem_map.mp am'
      obtain ⟨y,ym,rfl⟩ := List.mem_map.mp bm'
      have bm : bin d.toNat x.1 y.1 = prime d x.1 y.1 := by cases d <;> rfl
      have fresh' : bin d.toNat x.1 y.1 ∉ ws.map Prod.fst := by
        intro h
        apply fresh
        rw [← roots,← bm]
        exact List.mem_toFinset.mpr h
      let ka := decide (x.1 ∈ U)
      let kb := decide (y.1 ∈ U)
      let restWs := ((ws.map Prod.fst).erase x.1).erase y.1
      have kee : (kept ka x.1 (kept kb y.1 restWs)).toFinset = U :=
        wind_kept_exact (ws.map Prod.fst) nd roots neq
      let next := windChild ws (windBin d x y) x y ka kb
      have em := wind_packed_child ws x y d ka kb
      have childEq : (next.map Prod.fst).toFinset = insert (prime d x.1 y.1) U := by
        change (windChild ws (windBin d x y) x y ka kb |>.map Prod.fst).toFinset = _
        rw [em,childTwo,List.toFinset_cons,show (((ws.map Prod.fst).erase x.1).erase y.1) = restWs by rfl,kee,bm]
      have nodupNext : (next.map Prod.fst).Nodup := by
        change ((windChild ws (windBin d x y) x y ka kb).map Prod.fst).Nodup
        rw [em]
        exact childTwo_nodup_bf' nd _ _ am' bm' neq _ _ _ fresh'
      have trNext : Trace wind (next.map Prod.fst).toFinset rest := childEq.symm ▸ run'
      have nextLe : next.length ≤ cap := by
        rw [←List.length_map (f:=Prod.fst),←List.toFinset_card_of_nodup nodupNext,childEq]
        have sc := live_size (live_of_trace run')
        simp at le
        omega
      have zNot : (windBin d x y).1 ≠ zero :=
        (live_proper (live_of_trace run') _ (Finset.mem_insert_self _ _)).1
      have zFresh : (windBin d x y).1 ∉ (ws.map Prod.fst) := by
        rw [show (windBin d x y).1 = prime d x.1 y.1 by rfl,← bm]
        exact fresh'
      obtain ⟨budget,losses⟩ := wind_child_budget nodupNext p x.1 y.1 d trNext bound
      have cover := wind_full_cover (wind_inherits_faith fp xm ym d ka kb) (live_of_trace trNext)
      obtain ⟨j,hj⟩ := wind_links_mem checks (wind_child_member cap ws p xm ym order zFresh zNot nextLe budget cover)
      exact wind_link_sound prev next (plusDebt p x.1 y.1) j hj rest trNext (by simp at le; omega) losses
    have hne : s.toNat ≠ t.toNat := fun eq => st (BitVec.eq_of_toNat_eq eq)
    rcases lt_or_gt_of_ne hne with lt | lt
    · exact order_case s t st lt eqS fr remain profile
    · have same : prime d t s = prime d s t := by cases d <;> simp [prime,BitVec.and_comm,BitVec.or_comm]
      have equal : insert t (insert s U) = insert s (insert t U) := by ext w; simp [or_left_comm]
      apply order_case t s st.symm lt (eqS.trans equal.symm)
      · rwa [same,equal]
      · rwa [same]
      · intro i
        have flip : stepLost (profileCut i) (t,s,d) = stepLost (profileCut i) (s,t,d) :=
          Bool.or_comm _ _
        have hswap : lost (profileCut i) ((t,s,d)::rest) = lost (profileCut i) ((s,t,d)::rest) := by
          simp only [lost,List.countP_cons,flip]
        change decodeDebt row.2.1 i + lost (profileCut i) ((t,s,d)::rest) ≤ profileLimit i
        rw [hswap]
        exact profile i

lemma wind_block_at (cap start count : Nat) (ok : windBlock cap start count = true)
    (i : Nat) (lo : start ≤ i) (hi : i < start+count) :
    windNode cap ((windRows cap)[i]?.getD ([],0,[])) = true := by
  induction count generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [windBlock,Bool.and_eq_true] at ok
    obtain ⟨a,b⟩ := ok
    by_cases eq : i = start
    · simpa only [eq] using a
    · exact ih (start+1) b (by omega) (by omega)

lemma wind_block_join (cap start a b : Nat) (p : windBlock cap start a = true)
    (q : windBlock cap (start+a) b = true) : windBlock cap start (a+b) = true := by
  induction a generalizing start with
  | zero => simpa using q
  | succ n ih =>
    simp only [windBlock,Bool.and_eq_true] at p
    obtain ⟨a,b'⟩ := p
    have q' : windBlock cap (start+1+n) b = true := by convert q using 2 <;> omega
    have eq : n+1+b = (n+b)+1 := by omega
    rw [eq]
    simp only [windBlock,Bool.and_eq_true]
    exact ⟨a,ih (start+1) b' q'⟩

theorem wind_rows_sound (top : Nat) (all : ∀ k ≤ top, windBlock k 0 (windRows k).size = true) :
    ∀ k ≤ top, ∀ (i : Nat) (row : WindRow), (windRows k)[i]? = some row → windCert k row := by
  intro k
  induction k with
  | zero =>
    intro hk i row h
    simp [windRows] at h
  | succ k ih =>
    intro hk i row h
    refine wind_node_sound (k+1) row (ih (by omega)) ?_
    have bd : i < (windRows (k+1)).size := (Array.getElem?_eq_some_iff.mp h).1
    simpa [h] using wind_block_at (k+1) 0 _ (all (k+1) hk) i (Nat.zero_le _) (by simpa using bd)

end C10981.Signed


namespace C10981.Signed
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell4_0 : windBlock 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell5_0 : windBlock 5 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell5_6 : windBlock 5 6 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_0 : windBlock 6 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_6 : windBlock 6 6 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_12 : windBlock 6 12 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_18 : windBlock 6 18 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_24 : windBlock 6 24 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_30 : windBlock 6 30 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_36 : windBlock 6 36 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_42 : windBlock 6 42 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_48 : windBlock 6 48 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell6_54 : windBlock 6 54 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_0 : windBlock 7 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_6 : windBlock 7 6 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_12 : windBlock 7 12 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_18 : windBlock 7 18 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_24 : windBlock 7 24 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_30 : windBlock 7 30 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_36 : windBlock 7 36 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_42 : windBlock 7 42 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_48 : windBlock 7 48 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_54 : windBlock 7 54 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_60 : windBlock 7 60 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_66 : windBlock 7 66 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_72 : windBlock 7 72 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_78 : windBlock 7 78 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_84 : windBlock 7 84 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell7_90 : windBlock 7 90 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_0 : windBlock 8 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_6 : windBlock 8 6 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_12 : windBlock 8 12 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_18 : windBlock 8 18 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_24 : windBlock 8 24 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_30 : windBlock 8 30 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_36 : windBlock 8 36 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell8_42 : windBlock 8 42 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell9_0 : windBlock 9 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell9_6 : windBlock 9 6 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell10_0 : windBlock 10 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wind_cell11_0 : windBlock 11 0 1 = true := by decide +kernel
theorem wind_level0 : windBlock 0 0 (windRows 0).size = true := rfl
theorem wind_level1 : windBlock 1 0 (windRows 1).size = true := rfl
theorem wind_level2 : windBlock 2 0 (windRows 2).size = true := rfl
theorem wind_level3 : windBlock 3 0 (windRows 3).size = true := rfl
theorem wind_level4 : windBlock 4 0 (windRows 4).size = true := wind_cell4_0
theorem wind_level5 : windBlock 5 0 (windRows 5).size = true := wind_block_join 5 0 6 5 (wind_cell5_0) wind_cell5_6
theorem wind_level6 : windBlock 6 0 (windRows 6).size = true := wind_block_join 6 0 54 5 (wind_block_join 6 0 48 6 (wind_block_join 6 0 42 6 (wind_block_join 6 0 36 6 (wind_block_join 6 0 30 6 (wind_block_join 6 0 24 6 (wind_block_join 6 0 18 6 (wind_block_join 6 0 12 6 (wind_block_join 6 0 6 6 (wind_cell6_0) wind_cell6_6) wind_cell6_12) wind_cell6_18) wind_cell6_24) wind_cell6_30) wind_cell6_36) wind_cell6_42) wind_cell6_48) wind_cell6_54
theorem wind_level7 : windBlock 7 0 (windRows 7).size = true := wind_block_join 7 0 90 3 (wind_block_join 7 0 84 6 (wind_block_join 7 0 78 6 (wind_block_join 7 0 72 6 (wind_block_join 7 0 66 6 (wind_block_join 7 0 60 6 (wind_block_join 7 0 54 6 (wind_block_join 7 0 48 6 (wind_block_join 7 0 42 6 (wind_block_join 7 0 36 6 (wind_block_join 7 0 30 6 (wind_block_join 7 0 24 6 (wind_block_join 7 0 18 6 (wind_block_join 7 0 12 6 (wind_block_join 7 0 6 6 (wind_cell7_0) wind_cell7_6) wind_cell7_12) wind_cell7_18) wind_cell7_24) wind_cell7_30) wind_cell7_36) wind_cell7_42) wind_cell7_48) wind_cell7_54) wind_cell7_60) wind_cell7_66) wind_cell7_72) wind_cell7_78) wind_cell7_84) wind_cell7_90
theorem wind_level8 : windBlock 8 0 (windRows 8).size = true := wind_block_join 8 0 42 5 (wind_block_join 8 0 36 6 (wind_block_join 8 0 30 6 (wind_block_join 8 0 24 6 (wind_block_join 8 0 18 6 (wind_block_join 8 0 12 6 (wind_block_join 8 0 6 6 (wind_cell8_0) wind_cell8_6) wind_cell8_12) wind_cell8_18) wind_cell8_24) wind_cell8_30) wind_cell8_36) wind_cell8_42
theorem wind_level9 : windBlock 9 0 (windRows 9).size = true := wind_block_join 9 0 6 4 (wind_cell9_0) wind_cell9_6
theorem wind_level10 : windBlock 10 0 (windRows 10).size = true := wind_cell10_0
theorem wind_level11 : windBlock 11 0 (windRows 11).size = true := wind_cell11_0

set_option maxRecDepth 32768 in
theorem allWind : ∀ k ≤ 11, windBlock k 0 (windRows k).size = true := by
  intro k le
  interval_cases k
  · exact wind_level0
  · exact wind_level1
  · exact wind_level2
  · exact wind_level3
  · exact wind_level4
  · exact wind_level5
  · exact wind_level6
  · exact wind_level7
  · exact wind_level8
  · exact wind_level9
  · exact wind_level10
  · exact wind_level11

end C10981.Signed


namespace C10981.Signed

set_option maxRecDepth 32768 in
lemma wind_no_trace : ∀ tr, tr.length ≤ 11 → ¬ Trace wind wi.toFinset tr := by
  intro tr le h
  let raw : List Nat := [3,5,13,17,29,39,70]
  let hints : List Nat := [0,1,8,9,24,25,48,50,64,66,49,51,65,67,80,82,81,83]
  have root : (windRows 11)[0]? = some (raw,0,hints) := rfl
  have checked := wind_rows_sound 11 allWind 11 (by decide) 0 _ root
  have good : (windState raw).map Prod.fst = wi := by decide +kernel
  have hi : Trace wind ((windState raw).map Prod.fst).toFinset tr := good.symm ▸ h
  refine checked tr hi le ?_
  intro i
  have p := wind_profile_loss_bound bf_low h le i
  simpa [decodeDebt] using p

end C10981.Signed

end PEqualNP.Outside.L_meta_10980

theorem PEqualNP.Outside.L_meta_10980 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 1 && x 8) || (x 2 && x 8) || (x 5 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 15 ≤ t := by
  exact PEqualNP.Outside.L_meta_10980.C10980.proof_of_10981_from_wind
    (PEqualNP.Outside.L_meta_10980.C10981.Signed.wind_bound_of_trace
      PEqualNP.Outside.L_meta_10980.C10981.Signed.bf_low
      PEqualNP.Outside.L_meta_10980.C10981.Signed.wind_no_trace)
