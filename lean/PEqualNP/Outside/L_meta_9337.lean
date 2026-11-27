import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9337.Elim

-- Gate restriction adapted from the project proof of L-meta-726.
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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  all_goals simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl
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

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_count (n k : ℕ) (b : Bool) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → k < acc.1.length → acc.1.getD k (Sum.inl false) = Sum.inl b →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by simp only [elimStep]; rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1
        · simpa using hnok.2
        · exact ⟨b, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, if_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false]
      simp
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

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
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
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
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (v : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = v then Sum.inl b else Sum.inr i)

theorem inv_init (n : ℕ) (v : Fin n) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Function.update y v b)) (initStats n v b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · by_cases hv : (⟨i, hlt⟩ : Fin n) = v
    · subst hv
      simp [initStats, hlt, Stat.Valid, Stat.val]
    · simp [initStats, hlt, hv, Stat.Valid, Stat.val, wiresFrom, Function.update_of_ne hv]
  · rw [List.getD_eq_default _ _ (by simp [initStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem sum_eq_countP (l : List Gate) (k : ℕ) :
    (∑ i : Fin l.length, if k ∈ (l.get i).inputs then 1 else 0)
      = l.countP (fun g => decide (k ∈ g.inputs)) := by
  induction l with
  | nil => simp
  | cons g l ih =>
    show (∑ i : Fin (l.length + 1), if k ∈ ((g :: l).get i).inputs then 1 else 0) = _
    rw [Fin.sum_univ_succ, List.countP_cons]
    simp at ih
    by_cases h : k ∈ g.inputs <;> simp [h] <;> omega

theorem countP_eq_card (l : List Gate) (k : ℕ) :
    (Finset.univ.filter (fun j : Fin l.length => k ∈ (l.get j).inputs)).card
      = l.countP (fun g => decide (k ∈ g.inputs)) := by
  rw [Finset.card_filter]
  exact sum_eq_countP l k

theorem eliminate : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool), PEqualNP.MetaComplexity.Monotone2 C → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro n C v b hmono hy
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    simpa using h1
  set acc := elim n C.gates (initStats n v b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Function.update y v b))) acc := by
    intro y
    exact inv_elim n _ (by simp) C.gates _ _ hok (inv_init n v b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = C.eval (List.ofFn (Function.update y v b)) := by
    intro y
    exact ((hinv y).2 C.output).2
  have hcnt := elim_count n v.val b C.gates (initStats n v b, []) hok (by simp [initStats])
    (by simp [initStats])
  rw [← hacc] at hcnt
  simp only [List.length_nil, zero_add] at hcnt
  have hmD : ∀ out : ℕ, PEqualNP.MetaComplexity.Monotone2 ⟨acc.2, out⟩ := by
    intro out g hg
    obtain ⟨h1, h2⟩ := elim_ok n C.gates _ (by simp) g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h <;> simp [h]
  have hsz : ∀ out : ℕ, (⟨acc.2, out⟩ : PEqualNP.CircuitLowerBounds.Circuit).size
      + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card
      ≤ C.size := by
    intro out
    rw [countP_eq_card]
    exact hcnt
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    cases c with
    | true =>
      exfalso
      obtain ⟨y, hy⟩ := hy
      have := hval y
      rw [hst] at this
      rw [← this] at hy
      exact absurd hy (by simp [Stat.val])
    | false =>
      refine ⟨⟨acc.2, n + acc.2.length⟩, hmD _, hsz _, ?_⟩
      intro x
      rw [← hval x, hst]
      show (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = false
      rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp)]
  | inr j =>
    refine ⟨⟨acc.2, j⟩, hmD _, hsz _, ?_⟩
    intro x
    have := hval x
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_9337.Elim

namespace PEqualNP.Outside.L_meta_9337.Restricted

-- The four-by-four lower bound is the project proof of L-meta-6298.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x80000000001fffff8102040810204081, 0x7ffe00000060c183060c18306, 0x1fff800000000183060c183060c18, 0x7ffe00000000000060c183060c183060, 0x80fe03f80000007f0204081020408102, 0x7f0000000fe000008912244891224489, 0x1fc0000003f802448912244891224, 0x7f01fc00050a142850a142850]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (13741 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 2), (0, 3), (1, 1), (1, 3), (2, 0), (2, 2), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2), (3, 3)]

def pairIx (p : ℕ) : ℕ := if p < 63 then p else 0

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (pairIx k.val % 7) (0, 0) else posL.getD (pairIx (k.val - 64) / 7) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem all_front : inputs.sublists.all
    (fun l => decide (9 < l.length) || decide (l = inputs) || !(optimized 8 (9 - l.length) l)) = true := by
  decide +kernel

def pairOK (p : W × W × List W) : Bool := !(dispatch 1 (optimized 7) p.1 p.2.1 p.2.2)

theorem all_of_chunks {β : Type} (F : β → Bool) (n : ℕ) : ∀ (m : ℕ) (L : List β), L.length ≤ n * m →
    (∀ j < m, ((L.drop (n * j)).take n).all F = true) → L.all F = true := by
  intro m
  induction m with
  | zero =>
    intro L hl _
    have h0 : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [h0]
  | succ m ih =>
    intro L hl h
    rw [← List.take_append_drop n L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ih (L.drop n) ?_ ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      generalize n * m = t at *
      omega
    · intro j hj
      have e : List.drop (n * j) (List.drop n L) = List.drop (n * (j + 1)) L := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [e]
      exact h (j + 1) (by omega)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_0 : (((pairs inputs).drop (1 * 0)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_1 : (((pairs inputs).drop (1 * 1)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_2 : (((pairs inputs).drop (1 * 2)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_3 : (((pairs inputs).drop (1 * 3)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_4 : (((pairs inputs).drop (1 * 4)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_5 : (((pairs inputs).drop (1 * 5)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_6 : (((pairs inputs).drop (1 * 6)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_7 : (((pairs inputs).drop (1 * 7)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_8 : (((pairs inputs).drop (1 * 8)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_9 : (((pairs inputs).drop (1 * 9)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_10 : (((pairs inputs).drop (1 * 10)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_11 : (((pairs inputs).drop (1 * 11)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_12 : (((pairs inputs).drop (1 * 12)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_13 : (((pairs inputs).drop (1 * 13)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_14 : (((pairs inputs).drop (1 * 14)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_15 : (((pairs inputs).drop (1 * 15)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_16 : (((pairs inputs).drop (1 * 16)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_17 : (((pairs inputs).drop (1 * 17)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_18 : (((pairs inputs).drop (1 * 18)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_19 : (((pairs inputs).drop (1 * 19)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_20 : (((pairs inputs).drop (1 * 20)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_21 : (((pairs inputs).drop (1 * 21)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_22 : (((pairs inputs).drop (1 * 22)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_23 : (((pairs inputs).drop (1 * 23)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_24 : (((pairs inputs).drop (1 * 24)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_25 : (((pairs inputs).drop (1 * 25)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_26 : (((pairs inputs).drop (1 * 26)).take 1).all pairOK = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_27 : (((pairs inputs).drop (1 * 27)).take 1).all pairOK = true := by
  decide +kernel

theorem pairs_ok : (pairs inputs).all pairOK = true :=
  all_of_chunks pairOK 1 28 (pairs inputs) (by decide +kernel) (fun j hj => by
    interval_cases j
    exacts [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27])

theorem full_search : optimized 8 1 inputs = false := by
  have hp := List.all_eq_true.mp pairs_ok
  show (inputs == [goal] || (pairs inputs).any (fun (a, b, r) => dispatch 1 (optimized 7) a b r)) = false
  rw [Bool.or_eq_false_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hm
  have hx := hp _ hm
  simpa [pairOK] using hx

theorem len_one : 9 - inputs.length = 1 := by decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 8)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 8 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 8 l (9 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (9 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  have hli : l = inputs := by simpa using hrow
  rw [hli, len_one, full_search] at hsearch
  exact Bool.noConfusion hsearch

end PEqualNP.Outside.L_meta_9337.Restricted

namespace PEqualNP.Outside.L_meta_9337

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_9337.Elim

def off (k : ℕ) (x y : List Bool) : Prop :=
  ∀ i, i ≠ k → x.getD i false = true → y.getD i false = true

theorem step_order (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool)
    (le : ∀ i ∈ g.inputs, x.getD i false = true → y.getD i false = true) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
    g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases hop with h | h
  · simp only [h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
    intro hx i hi
    exact le i hi (hx i hi)
  · simp only [h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_def, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, le i hi hx⟩

theorem propagate (k : ℕ) (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (avoid : ∀ g ∈ gs, k ∉ g.inputs)
    (x y : List Bool) (len : x.length = y.length) (rel : off k x y) :
    off k (wiresFrom gs x) (wiresFrom gs y) := by
  induction gs generalizing x y with
  | nil => exact rel
  | cons g gs ih =>
    apply ih (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => avoid g' (List.mem_cons_of_mem _ hg'))
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [len])
    intro i hne
    by_cases last : i = x.length
    · rw [last, getD_snoc_eq, len, getD_snoc_eq]
      exact step_order _ (ops g List.mem_cons_self) _ _
        (fun j hj => rel j (fun eq => avoid g List.mem_cons_self (eq ▸ hj)))
    · rw [getD_snoc_ne _ _ _ _ last, getD_snoc_ne _ _ _ _ (by omega)]
      exact rel i hne

theorem drop_input {n : ℕ} (C : Circuit) (hm : Monotone2 C) (v : Fin n)
    (x y z : Fin n → Bool) (xy : ∀ i, i ≠ v → x i = true → y i = true)
    (vy : Function.update y v false = y) (vz : z v = false)
    (hx : C.eval (List.ofFn x) = true) (hy : C.eval (List.ofFn y) = false)
    (hz : C.eval (List.ofFn z) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
      ∀ a : Fin n → Bool, D.eval (List.ofFn a) = C.eval (List.ofFn (Function.update a v false)) := by
  obtain ⟨D, dm, ds, de⟩ := Elim.eliminate n C v false hm ⟨y, by rw [vy]; exact hy⟩
  refine ⟨D, dm, ?_, de⟩
  suffices 0 < (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card by omega
  by_contra! no
  have avoid : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
    intro g hg hv
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    have pos := Finset.card_pos.mpr (show (Finset.univ.filter
      (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).Nonempty from
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)
    omega
  have ne : C.output ≠ v.val := by
    intro eq
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix C.gates (List.ofFn z)
    change (wiresFrom C.gates (List.ofFn z)).getD C.output false = true at hz
    rw [eq, ht, List.getD_append _ _ _ _ (by simp)] at hz
    simp [List.getD_eq_getElem?_getD, vz] at hz
  have rel : off v.val (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases hn : i < n
    · simpa [List.getD_eq_getElem?_getD,hn] using xy ⟨i,hn⟩ (fun eq => hi (congrArg Fin.val eq))
    · simp [List.getD_eq_getElem?_getD,hn]
  have h := propagate v.val C.gates (fun g hg => by simpa using (hm g hg).1)
    avoid _ _ (by simp) rel C.output ne hx
  change C.eval (List.ofFn y) = true at h
  simp [hy] at h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def renameGate (ρ : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map ρ }

def renameCircuit (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (renameGate ρ), output := ρ C.output }

def wireRel (ρ : ℕ → ℕ) (w v : List Bool) : Prop :=
  ∀ i, v.getD (ρ i) false = w.getD i false

theorem size_rename (ρ : ℕ → ℕ) (C : Circuit) :
    (renameCircuit ρ C).size = C.size := by
  change (C.gates.map (renameGate ρ)).length = C.gates.length
  simp only [List.length_map]


theorem input_get {n : Nat} (v : Fin n → Bool) (i : Fin n) :
    (List.ofFn v).getD i.val false=v i := by simp [List.getD_eq_getElem?_getD]

def resize {n m : Nat} (σ : Fin n → Fin m) (i : Nat) :=
  if h : i<n then (σ ⟨i,h⟩).val else m+(i-n)

theorem resize_rel_append {n m : Nat} (σ : Fin n → Fin m)
    (v w : List Bool) (k : Nat) (hl : v.length=n+k) (hr : w.length=m+k)
    (rel : wireRel (resize σ) v w) (b : Bool) : wireRel (resize σ) (v++[b]) (w++[b]) := by
  intro i
  by_cases hi : i<v.length
  · have small : resize σ i<w.length := by
      by_cases raw : i<n
      · simp [resize,raw,hr]; have h := (σ ⟨i,raw⟩).isLt; omega
      · simp [resize,raw,hr]; omega
    simpa only [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ small] using rel i
  · have nonraw : ¬i<n := by omega
    have off : resize σ i-w.length=i-v.length := by simp [resize,nonraw,hr,hl]; omega
    have big : w.length≤resize σ i := by simp [resize,nonraw,hr]; omega
    rw [List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (by omega),off]

theorem resize_gates {n m : Nat} (σ : Fin n → Fin m) (gs : List Gate) (v w : List Bool)
    (k : Nat) (hl : v.length=n+k) (hr : w.length=m+k) (rel : wireRel (resize σ) v w) :
    wireRel (resize σ)
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) v)
      ((gs.map (renameGate (resize σ))).foldl
        (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w) := by
  induction gs generalizing k v w with
  | nil => exact rel
  | cons g gs ih =>
    simp only [List.foldl_cons,List.map_cons]
    have eq : (renameGate (resize σ) g).op.eval
        ((renameGate (resize σ) g).inputs.map fun i => w.getD i false)=
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      simp only [renameGate,List.map_map]
      congr 2
      exact funext rel
    rw [eq]
    exact ih _ _ (k+1) (by simp [hl,Nat.add_assoc]) (by simp [hr,Nat.add_assoc])
      (resize_rel_append σ v w k hl hr rel _)

theorem resize_eval {n m : Nat} (σ : Fin n → Fin m) (C : Circuit) (z : Fin m → Bool) :
    (renameCircuit (resize σ) C).eval (List.ofFn z) = C.eval (List.ofFn fun i => z (σ i)) := by
  apply resize_gates σ C.gates _ _ 0 (by simp) (by simp) _ C.output
  intro i
  by_cases h : i<n
  · rw [show resize σ i = (σ ⟨i,h⟩).val by simp [resize,h],input_get]
    exact (input_get (fun j => z (σ j)) ⟨i,h⟩).symm
  · have large : m≤resize σ i := by simp [resize,h]
    simp [List.getD_eq_getElem?_getD,h,Nat.not_lt.mpr large]


theorem rename_mono (ρ : ℕ → ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (renameCircuit ρ C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact ⟨(h g' hg').1, by simpa [renameGate] using (h g' hg').2⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def raw (n : ℕ) (u v : Fin n) (i : Fin (n + n)) : Bool :=
  decide (i.val = u.val ∨ i.val = n + v.val)

def rr : Fin 4 → Fin 5 := ![1,0,2,4]
def cc : Fin 4 → Fin 5 := ![0,1,2,4]
def dest : Fin 10 → Fin 8 := ![1,0,2,0,3,4,5,6,0,7]

theorem raw5_ok : ∀ (u v : Fin 5), List.ofFn (raw 5 u v) = oneEach u v := by decide +kernel
theorem raw4_ok : ∀ (u v : Fin 4), List.ofFn (raw 4 u v) = oneEach u v := by decide +kernel
theorem restrict_bits : ∀ (u v : Fin 4) (i : Fin 10),
    Function.update (Function.update (fun j => raw 4 u v (dest j)) 8 false) 3 false i =
      raw 5 (rr u) (cc v) i := by decide +kernel
theorem restrict_mask : ∀ (u v : Fin 4), (3315386 : ℕ).testBit (5 * (rr u).val + (cc v).val) =
    (13741 : ℕ).testBit (4 * u.val + v.val) := by decide +kernel

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 5 => (3315386 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hc⟩
  have evalC (u v : Fin 5) : C.eval (List.ofFn (raw 5 u v)) =
      (3315386 : ℕ).testBit (5 * u.val + v.val) := by rw [raw5_ok]; exact hc u v
  obtain ⟨D, dm, ds, de⟩ := drop_input C hm (3 : Fin 10) (raw 5 3 0) (raw 5 0 0) (raw 5 1 0)
    (by decide +kernel) (by funext i; exact (by decide +kernel : ∀ j : Fin 10,
      Function.update (raw 5 0 0) 3 false j = raw 5 0 0 j) i) (by decide +kernel)
    ((evalC 3 0).trans (by decide +kernel)) ((evalC 0 0).trans (by decide +kernel))
    ((evalC 1 0).trans (by decide +kernel))
  have fixed3 : ∀ (u v : Fin 5) (j : Fin 10), u ≠ 3 →
      Function.update (raw 5 u v) 3 false j = raw 5 u v j := by decide +kernel
  have evalD (u v : Fin 5) (h : u ≠ 3) : D.eval (List.ofFn (raw 5 u v)) =
      (3315386 : ℕ).testBit (5 * u.val + v.val) := by
    rw [de, show Function.update (raw 5 u v) 3 false = raw 5 u v from funext (fun j => fixed3 u v j h)]
    exact evalC u v
  obtain ⟨E, em, es, ee⟩ := drop_input D dm (8 : Fin 10) (raw 5 0 3) (raw 5 0 0) (raw 5 1 0)
    (by decide +kernel) (by funext i; exact (by decide +kernel : ∀ j : Fin 10,
      Function.update (raw 5 0 0) 8 false j = raw 5 0 0 j) i) (by decide +kernel)
    ((evalD 0 3 (by decide)).trans (by decide +kernel)) ((evalD 0 0 (by decide)).trans (by decide +kernel))
    ((evalD 1 0 (by decide)).trans (by decide +kernel))
  apply Restricted.no_small (renameCircuit (resize dest) E)
    (rename_mono _ _ em) (by rw [size_rename]; omega)
  intro u v
  rw [← raw4_ok, resize_eval, ee, de, funext (restrict_bits u v)]
  exact (evalC (rr u) (cc v)).trans (restrict_mask u v)
end PEqualNP.Outside.L_meta_9337

theorem PEqualNP.Outside.L_meta_9337 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3315386 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact PEqualNP.Outside.L_meta_9337.lower
