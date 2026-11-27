import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2565_aux

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

def sval (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def svalid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) : Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
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

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
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
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, svalid w.length s) :
    svalid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    sval (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (sval w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, svalid, sval, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, svalid, sval, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, svalid, sval, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, svalid, sval, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, svalid, sval, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, svalid, sval, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
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

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

def hits (g : Gate) : Bool := g.inputs.any fun k => k == 4 || k == 9

theorem elim_count (n : ℕ) (gs : List Gate) : ∀ acc : List (Bool ⊕ ℕ) × List Gate,
    (∀ g ∈ gs, NOk g) → 10 ≤ acc.1.length →
    acc.1.getD 4 (Sum.inl false) = Sum.inl false →
    acc.1.getD 9 (Sum.inl false) = Sum.inl false →
    (elim n gs acc).2.length + gs.countP hits ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hlen h4 h9
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have hl : (elimStep n acc g).1.length = acc.1.length + 1 := by simp [elimStep]
    have h4' : (elimStep n acc g).1.getD 4 (Sum.inl false) = Sum.inl false := by
      simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact h4
    have h9' : (elimStep n acc g).1.getD 9 (Sum.inl false) = Sum.inl false := by
      simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact h9
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by omega) h4' h9'
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hg : hits g = true
    · have hnok := hok g List.mem_cons_self
      obtain ⟨k, hk, hk49⟩ := List.any_eq_true.1 hg
      have hconst : acc.1.getD k (Sum.inl false) = Sum.inl false := by
        rcases Bool.or_eq_true_iff.1 hk49 with e | e
        · rw [beq_iff_eq.1 e]; exact h4
        · rw [beq_iff_eq.1 e]; exact h9
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨false, List.mem_map.2 ⟨k, hk, hconst⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hg, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hg]
      simp only [Bool.false_eq_true, ite_false]
      omega

theorem svalid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Bool ⊕ ℕ, svalid m s → svalid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem sval_append (w t : List Bool) : ∀ s : Bool ⊕ ℕ, svalid w.length s →
    sval (w ++ t) s = sval w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    svalid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    sval (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (sval w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show svalid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      sval (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨svalid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, sval_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem agree_off4 (gs : List Gate) : ∀ w w' : List Bool, w.length = w'.length →
    10 ≤ w.length → w.getD 9 false = false → w'.getD 9 false = false →
    (∀ i, i ≠ 4 → w.getD i false = w'.getD i false) →
    (∀ g ∈ gs, 4 ∉ g.inputs ∨ (g.op = GateOp.and ∧ 9 ∈ g.inputs)) →
    ∀ i, i ≠ 4 → (wiresFrom gs w).getD i false = (wiresFrom gs w').getD i false := by
  induction gs with
  | nil => intro w w' _ _ _ _ h _ i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hl hlen h9 h9' hag hgs
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      rcases hgs g List.mem_cons_self with h4 | ⟨hop, hin⟩
      · congr 1
        apply List.map_congr_left
        intro a ha
        exact hag a (fun e => h4 (e ▸ ha))
      · have e1 : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
          rw [hop]
          simp only [GateOp.eval, List.all_eq_false]
          exact ⟨false, List.mem_map.2 ⟨9, hin, h9⟩, by simp⟩
        have e2 : g.op.eval (g.inputs.map fun i => w'.getD i false) = false := by
          rw [hop]
          simp only [GateOp.eval, List.all_eq_false]
          exact ⟨false, List.mem_map.2 ⟨9, hin, h9'⟩, by simp⟩
        rw [e1, e2]
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (by simp [hl]) (by simp; omega)
      (by rw [getD_snoc_ne _ _ _ _ (by omega)]; exact h9)
      (by rw [getD_snoc_ne _ _ _ _ (by omega)]; exact h9')
      _ (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    by_cases hil : i = w.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq, hv]
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      exact hag i hi

theorem two_le_countP {α : Type} (p : α → Bool) : ∀ (l : List α) (a b : α), a ∈ l → b ∈ l →
    a ≠ b → p a = true → p b = true → 2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro a b ha; simp at ha
  | cons c l ih =>
    intro a b ha hb hab hpa hpb
    rw [List.countP_cons]
    classical
    by_cases hca : c = a
    · subst hca
      have hb' : b ∈ l := by
        rcases List.mem_cons.1 hb with e | e
        · exact absurd e.symm hab
        · exact e
      have := List.countP_pos_iff.2 ⟨b, hb', hpb⟩
      simp only [hpa, ite_true]
      omega
    · by_cases hcb : c = b
      · subst hcb
        have ha' : a ∈ l := by
          rcases List.mem_cons.1 ha with e | e
          · exact absurd e.symm hca
          · exact e
        have := List.countP_pos_iff.2 ⟨a, ha', hpa⟩
        simp only [hpb, ite_true]
        omega
      · have ha' : a ∈ l := by
          rcases List.mem_cons.1 ha with e | e
          · exact absurd e.symm hca
          · exact e
        have hb' : b ∈ l := by
          rcases List.mem_cons.1 hb with e | e
          · exact absurd e.symm hcb
          · exact e
        have := ih a b ha' hb' hab hpa hpb
        split <;> omega


def F9 (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def G8 (x : Fin 8 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 ||
    x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4

def xa : Fin 9 → Bool := fun i => decide (i = 3) || decide (i = 4)

def xb : Fin 9 → Bool := fun i => decide (i = 3)

def x4only : Fin 9 → Bool := fun i => decide (i = 4)

def lift (y : Fin 8 → Bool) : Fin 9 → Bool := ![y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7]

def acc0 : List (Bool ⊕ ℕ) × List Gate :=
  ([Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false, Sum.inr 4, Sum.inr 5,
    Sum.inr 6, Sum.inr 7, Sum.inl false], [])

theorem F9_lift (y : Fin 8 → Bool) : F9 (lift y) = G8 y := by
  simp [F9, G8, lift]

theorem inv_acc0 (y : Fin 8 → Bool) :
    Inv 8 (List.ofFn y) (List.ofFn (lift y) ++ [lift y 4 && lift y 6]) acc0 := by
  refine ⟨by simp [acc0], ?_⟩
  intro i
  rcases Nat.lt_or_ge i 10 with hlt | hge
  · interval_cases i <;> simp [acc0, svalid, sval, wiresFrom, lift]
  · rw [List.getD_eq_default _ _ (by simp [acc0]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem main (C : Circuit) (hfan : FanInTwo C)
    (hex : ∃ g ∈ C.gates, g.op = GateOp.and ∧ 9 ∈ g.inputs)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) = F9 x) :
    HasCircuitSize 8 G8 (C.size - 2) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hfan g0 hg0)
  have hev : ∀ x : Fin 9 → Bool,
      (wiresFrom gs (List.ofFn x ++ [x 4 && x 6])).getD C.output false = F9 x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hcomp x]
    rfl
  have hout4 : C.output ≠ 4 := by
    intro h
    have e := hev x4only
    rw [h, getD_wiresFrom _ _ _ (by simp)] at e
    exact absurd e (by decide)
  have hread : ∃ h ∈ gs, 4 ∈ h.inputs ∧ ¬ (h.op = GateOp.and ∧ 9 ∈ h.inputs) := by
    by_contra hno
    push Not at hno
    have e := agree_off4 gs (List.ofFn xa ++ [xa 4 && xa 6]) (List.ofFn xb ++ [xb 4 && xb 6])
      (by simp) (by simp) (by decide) (by decide)
      (by
        intro i hi
        rcases Nat.lt_or_ge i 10 with hlt | hge
        · interval_cases i <;> first | exact absurd rfl hi | decide
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg
        by_cases h4 : 4 ∈ g.inputs
        · exact Or.inr (hno g hg h4)
        · exact Or.inl h4)
      C.output hout4
    rw [hev, hev] at e
    exact absurd e (by decide)
  obtain ⟨h, hh, h4, hnot⟩ := hread
  obtain ⟨g, hg, hand, h9⟩ := hex
  have hgg : normGate g = g := by
    obtain ⟨op, inputs⟩ := g
    simp only at hand
    subst hand
    rfl
  have hg' : g ∈ gs := by
    rw [hgs, ← hgg]
    exact List.mem_map_of_mem hg
  have hne : g ≠ h := by
    rintro rfl
    exact hnot ⟨hand, h9⟩
  have htwo : 2 ≤ gs.countP hits :=
    two_le_countP hits gs g h hg' hh hne
      (List.any_eq_true.2 ⟨9, h9, by simp⟩) (List.any_eq_true.2 ⟨4, h4, by simp⟩)
  have hinv : ∀ y : Fin 8 → Bool,
      Inv 8 (List.ofFn y) (wiresFrom gs (List.ofFn (lift y) ++ [lift y 4 && lift y 6]))
        (elim 8 gs acc0) := fun y =>
    inv_elim 8 (List.ofFn y) (by simp) gs _ acc0 (fun g hg => (hnok g hg).1) (inv_acc0 y)
  set acc := elim 8 gs acc0 with hacc
  have hval : ∀ y : Fin 8 → Bool,
      sval (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = G8 y := by
    intro y
    rw [((hinv y).2 C.output).2, hev, F9_lift]
  have hcount := elim_count 8 gs acc0 hnok (by simp [acc0]) rfl rfl
  rw [← hacc] at hcount
  have hlen : gs.length = C.size := by
    rw [hgs, List.length_map]; rfl
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    have e1 := hval (fun _ => false)
    have e2 := hval (fun _ => true)
    rw [hs] at e1 e2
    simp only [sval] at e1 e2
    rw [e1] at e2
    exact absurd e2 (by decide)
  | inr j =>
    refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
    · intro g hg
      exact elim_ok 8 gs acc0 (by simp [acc0]) g hg
    · show acc.2.length ≤ C.size - 2
      simp [acc0] at hcount
      omega
    · intro y
      have e := hval y
      rw [hs] at e
      exact e

end PEqualNP.Outside.L_meta_2565_aux

theorem PEqualNP.Outside.L_meta_2565 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (9 : ℕ) ∈ x3.inputs) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) (x1.size - (2 : ℕ)) :=
  fun C hfan hex hcomp => PEqualNP.Outside.L_meta_2565_aux.main C hfan hex hcomp
