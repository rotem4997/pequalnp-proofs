import Mathlib
import PEqualNP.Defs

-- The absorbing-wire elimination lemma is from jerry22717, PR 77, with the original credits below.
namespace PEqualNP.Outside.L_meta_8257
namespace Absorb193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire semantics and constant propagation below reuse the project’s
-- Shannon, Support and Elim helpers within the allowed dependency set.

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


abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

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
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

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


def reader (n h : ℕ) (p : Gate × ℕ) : Bool :=
  decide (h < n + p.2) && (normGate p.1).inputs.contains h

-- Every counted reader sees the fixed false wire and emits no gate.
theorem savings (n m h : ℕ) (gs : List Gate) (j : ℕ) (acc : List Stat × List Gate)
    (ok : ∀ g ∈ gs, Ok g) (hh : h < acc.1.length)
    (fixed : acc.1.getD h (.inl false) = .inl false) :
    (elim m (gs.map normGate) acc).2.length + (gs.zipIdx j).countP (reader n h)
      ≤ acc.2.length + gs.length := by
  induction gs generalizing acc j with
  | nil => simp [elim]
  | cons g gs ih =>
    let a := elimStep m acc (normGate g)
    have tail := ih (j+1) a (fun g hg => ok g (by simp [hg]))
      (by simp [a, elimStep]; omega)
      (by change (acc.1 ++ [_]).getD h _ = _; rw [List.getD_append _ _ _ _ hh, fixed])
    change (elim m (gs.map normGate) a).2.length + _ ≤ _
    rw [List.zipIdx_cons, List.countP_cons, List.length_cons]
    let r := simplify (normGate g).op (m + acc.2.length)
      ((normGate g).inputs.map fun i => acc.1.getD i (.inl false))
    have ha : a.2.length = acc.2.length + r.1.toList.length := List.length_append
    by_cases hit : reader n h (g,j) = true
    · have mem : h ∈ (normGate g).inputs := by simpa [reader] using (Bool.and_eq_true_iff.mp hit).2
      have ng := normGate_nok g (ok g (by simp))
      have zero : r.1 = none := simplify_count _ _ _ ng.1.1
        (by simpa using ng.1.2) (fun e => by simpa using ng.2 e)
        ⟨false, List.mem_map.mpr ⟨h, mem, fixed⟩⟩
      simp [zero] at ha
      simp [hit]; omega
    · have := toList_length_le r.1
      simp [hit]; omega

def seed (m h : ℕ) : List Stat :=
  List.ofFn fun i : Fin m => if i.val = h then .inl false else .inr i.val

theorem seed_inv (w : List Bool) (m h : ℕ) (hw : w.length = m)
    (hz : w.getD h false = false) : Inv m w w (seed m h, []) := by
  refine ⟨by simp [seed, hw], fun i => ?_⟩
  by_cases hi : i < m
  · by_cases e : i = h
    · subst i; simpa [seed, hi, Stat.Valid, Stat.val] using hz
    · simp [seed, hi, e, Stat.Valid, Stat.val, wiresFrom]
  · have : m ≤ i := by omega
    simpa [seed, hi, Stat.Valid, Stat.val] using (List.getD_eq_default w false (by omega : w.length ≤ i))

-- Reattach h to the residual output using a single final gate.
def finish (h : ℕ) : Stat → Gate
  | .inl true => ⟨.and, []⟩
  | .inl false => ⟨.or, [h]⟩
  | .inr j => ⟨.or, [h,j]⟩

theorem finish_ok (h : ℕ) (s : Stat) : Ok (finish h s) := by
  cases s with
  | inl b => cases b <;> simp [finish, Ok]
  | inr j => simp [finish, Ok]

theorem finish_eval (w : List Bool) (h : ℕ) (s : Stat) :
    (wiresFrom [finish h s] w).getD w.length false = (w.getD h false || s.val w) := by
  cases s with
  | inl b => cases b <;> simp [finish, wiresFrom, GateOp.eval, Stat.val]
  | inr j => simp [finish, wiresFrom, GateOp.eval, Stat.val]

end Absorb193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Absorb193

theorem absorbing : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), PEqualNP.MetaComplexity.FanInTwo C → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains h) ≤ C.size + 1 := by
  intro n C h ok absorbs
  have form (g : Gate) : (GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs
      (g.inputs.take 1) (fun _ => g.inputs) g.inputs) = (normGate g).inputs := by
    cases g with | mk op ins => cases op <;> rfl
  simp_rw [form]
  change ∃ D, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
    D.size + C.gates.zipIdx.countP (reader n h) ≤ C.size + 1
  by_cases existsH : h < n + C.gates.length
  swap
  · refine ⟨C, ok, rfl, ?_⟩
    have z : C.gates.zipIdx.countP (reader n h) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have := List.snd_lt_of_mem_zipIdx hp
      simp [reader, show ¬h < n + p.2 by omega]
    omega
  let pre := C.gates.take (h+1-n)
  let rest := C.gates.drop (h+1-n)
  have splitG : pre ++ rest = C.gates := List.take_append_drop ..
  let m := n + pre.length
  have hpLen : pre.length = min (h+1-n) C.gates.length := List.length_take ..
  have hm : h < m := by dsimp [m]; omega
  let init : List Stat × List Gate := (seed m h, [])
  let pass := elim m (rest.map normGate) init
  let s := pass.1.getD C.output (.inl false)
  let D : Circuit := ⟨(pre ++ pass.2) ++ [finish h s], m + pass.2.length⟩
  have preOk (g) (hg : g ∈ pre) : Ok g := ok g (splitG ▸ List.mem_append_left _ hg)
  have restOk (g) (hg : g ∈ rest) : Ok g := ok g (splitG ▸ List.mem_append_right _ hg)
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ (pre ++ pass.2) ++ [finish h s] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hp | hr) | rfl)
    · exact preOk g hp
    · exact elim_ok m _ init (by simp [init]) g hr
    · exact finish_ok h s
  · funext x
    let y := List.ofFn x
    let w := wiresFrom pre y
    let v := wiresFrom pass.2 w
    have lw : w.length = m := by simp [w, y, length_wiresFrom, m]
    have lv : v.length = m + pass.2.length := by simp [v, length_wiresFrom, lw]
    have hh : h < w.length := lw ▸ hm
    have old : C.wires y = wiresFrom rest w := by rw [wires_eq, ← splitG, wiresFrom_append]
    have origH : (C.wires y).getD h false = w.getD h false := by rw [old, getD_wiresFrom _ _ _ hh]
    have out : circuitFun n D x = (w.getD h false || s.val v) := by
      change (wiresFrom ((pre ++ pass.2) ++ [finish h s]) y).getD (m + pass.2.length) false = _
      rw [wiresFrom_append, wiresFrom_append]
      change (wiresFrom [finish h s] v).getD _ false = _
      rw [← lv, finish_eval, getD_wiresFrom _ _ _ hh]
    rw [out]
    cases hc : w.getD h false with
    | true => simpa using (absorbs x (origH.trans hc)).symm
    | false =>
      have hi := inv_elim m w lw (rest.map normGate) w init
        (by intro g hg; obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
            exact (normGate_nok _ (restOk _ hg')).1)
        (seed_inv w m h lw hc)
      have eq := (hi.2 C.output).2
      rw [wiresFrom_norm, ← old] at eq
      simpa [s, v, pass, circuitFun, Circuit.eval, y] using eq
  · have zero : pre.zipIdx.countP (reader n h) = 0 := by
      apply List.countP_eq_zero.mpr
      intro p hp
      have := List.snd_lt_of_mem_zipIdx hp
      simp [reader, show ¬ h < n + p.2 by omega]
    have save := savings n m h rest pre.length init restOk
      (by simpa [init, seed] using hm) (by simp [init, seed, hm])
    change pass.2.length + _ ≤ [].length + rest.length at save
    change ((pre ++ pass.2) ++ [finish h s]).length + _ ≤ C.gates.length + 1
    rw [← splitG, List.zipIdx_append, List.countP_append, zero]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at *
    omega
namespace Sole
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def pins (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def reads (v : Nat) (g : Gate) := (pins g).contains v
def mark {n : Nat} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def atBank (g : Gate) (z : List Bool) := g.op.eval (g.inputs.map fun k => z.getD k false)

lemma read_only {v : Nat} {gs : List Gate} {a b : Gate}
    (le : (gs.filter (reads v)).length ≤ 1) (ha : a ∈ gs.filter (reads v))
    (hb : b ∈ gs) (read : v ∈ pins b) : b = a := by
  have both : b ∈ gs.filter (reads v) := List.mem_filter.mpr ⟨hb,List.contains_iff_mem.mpr read⟩
  generalize gs.filter (reads v) = ls at le ha both
  cases ls with
  | nil => simp at ha
  | cons c t =>
    have e : t = [] := by simpa using le
    subst t
    simpa using (List.mem_singleton.mp both).trans (List.mem_singleton.mp ha).symm

lemma raw {n} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    (List.ofFn x ++ tail).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append,i.isLt]

lemma same_pin {n} (x y : Fin n → Bool) (tail : List Bool) (i : Nat)
    (h : ∀ j : Fin n, i=j.val → x j=y j) :
    (List.ofFn x ++ tail).getD i false = (List.ofFn y ++ tail).getD i false := by
  by_cases b : i<n
  · let j : Fin n := ⟨i,b⟩
    exact (raw x tail j).trans ((h j rfl).trans (raw y tail j).symm)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append,b]

lemma eval_from_pins (g : Gate) (z w : List Bool)
    (fan : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (agree : ∀ i ∈ pins g, z.getD i false = w.getD i false) : atBank g z = atBank g w := by
  obtain ⟨op,ins⟩ := g
  rcases fan with ⟨opok,arity⟩
  change op = .and ∨ op = .or ∨ op = .not at opok
  change ins.length ≤ 2 at arity
  rcases opok with rfl|rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢ <;> simp [ha]
    | cons b t =>
      have empty : t=[] := by simpa using arity
      subst t
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢
      rw [ha]
      all_goals
        have hb := agree b (by simp [pins,GateOp.eval])
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

lemma parallel_wires {n} (x y : Fin n → Bool) (gs : List Gate)
    (step : ∀ g ∈ gs, ∀ rest, atBank g (List.ofFn x ++ rest) = atBank g (List.ofFn y ++ rest))
    (t : List Bool) : ∃ suffix, (Circuit.mk gs 0).wires (List.ofFn x ++ t) = List.ofFn x ++ suffix ∧
      (Circuit.mk gs 0).wires (List.ofFn y ++ t) = List.ofFn y ++ suffix := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    have eq := step g (by simp) t
    obtain ⟨s,hx,hy⟩ := ih (fun a ha => step a (List.mem_cons_of_mem _ ha)) (t++[atBank g (List.ofFn x ++ t)])
    refine ⟨s,?_,?_⟩
    · change (Circuit.mk gs 0).wires ((List.ofFn x ++ t) ++ [atBank g _]) = _
      simpa only [List.append_assoc] using hx
    · change (Circuit.mk gs 0).wires ((List.ofFn y ++ t) ++ [atBank g _]) = _
      rw [←eq]
      simpa only [List.append_assoc] using hy

lemma lockstep {n} (C : Circuit) (fan : FanInTwo C) (g : Gate) (x y : Fin n → Bool)
    (out : n ≤ C.output)
    (reader : ∀ i : Fin n, x i ≠ y i → ∀ q ∈ C.gates, i.val ∈ pins q → q = g)
    (agree : ∀ tail, atBank g (List.ofFn x ++ tail) = atBank g (List.ofFn y ++ tail)) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  have step (q) (mem : q ∈ C.gates) (tail) :
      atBank q (List.ofFn x ++ tail)=atBank q (List.ofFn y ++ tail) := by
    by_cases eq : q=g
    · exact eq ▸ agree tail
    apply eval_from_pins _ _ _ (fan _ mem)
    intro i hi
    apply same_pin
    rintro j rfl
    by_contra different
    exact eq (reader j different q mem hi)
  obtain ⟨s,hx,hy⟩ := parallel_wires x y _ step []
  simp only [List.append_nil] at hx hy
  change ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD _ false =
    ((Circuit.mk C.gates 0).wires (List.ofFn y)).getD _ false
  rw [hx,hy]
  exact same_pin x y s C.output (fun j h => by have := j.isLt; omega)

section Geometry
open SimpleGraph
variable {n : ℕ} {G : SimpleGraph (Fin n)}
def girthFive (G : SimpleGraph (Fin n)) := ∀ u (p : G.Walk u u), p.IsCycle → 5 ≤ p.length

lemma triangle (h : girthFive G) {u v w : Fin n} (uv : G.Adj u v) (vw : G.Adj v w)
    (wu : G.Adj w u) : False := by
  let p := Walk.cons uv (Walk.cons vw (Walk.cons wu Walk.nil))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have a := uv.ne
    have b := vw.ne
    have c := wu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,a,b,c,Ne.symm a,Ne.symm b,Ne.symm c]
  have bound := h u p hp
  simp [p] at bound

lemma square (h : girthFive G) {u a w b : Fin n} (ua : G.Adj u a) (aw : G.Adj a w)
    (wb : G.Adj w b) (bu : G.Adj b u) (uw : u ≠ w) (ab : a ≠ b) : False := by
  let p := Walk.cons ua (Walk.cons aw (Walk.cons wb (Walk.cons bu Walk.nil)))
  have hp : p.IsCycle := by
    unfold p
    rw [Walk.cons_isCycle_iff]
    have h1 := ua.ne
    have h2 := aw.ne
    have h3 := wb.ne
    have h4 := bu.ne
    constructor <;> simp [Walk.cons_isPath_iff,Sym2.eq_iff,h1,h2,h3,h4,uw,ab,
      Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm uw,Ne.symm ab]
  have bound := h u p hp
  simp [p] at bound

lemma private_neighbor (h : girthFive G) {u w a b : Fin n} (uw : u ≠ w)
    (ua : G.Adj u a) (ub : G.Adj u b) (ab : a ≠ b) :
    ∃ r, G.Adj u r ∧ r ≠ w ∧ ¬ G.Adj w r := by
  by_cases aw : a = w
  · subst w
    exact ⟨b,ub,ab.symm,fun e => triangle h ua e ub.symm⟩
  by_cases bw : b = w
  · subst w
    exact ⟨a,ua,aw,fun e => triangle h ub e ua.symm⟩
  by_cases wa : G.Adj w a
  · exact ⟨b,ub,bw,fun e => square h ua wa.symm e ub.symm uw ab⟩
  · exact ⟨a,ua,aw,wa⟩
end Geometry
open SimpleGraph
variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))

lemma mark_true (S : Finset (Fin n)) :
    graphFun G A (mark S) = true ↔
      (∃ i ∈ A, i ∈ S) ∨ (∃ i j, G.Adj i j ∧ i ∈ S ∧ j ∈ S) := by
  simp [graphFun,mark]

lemma off_pair (a b : Fin n) (ao : a ∉ A) (bo : b ∉ A) (ab : ¬G.Adj a b) :
    graphFun G A (mark {a,b}) = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  rcases (mark_true G A _).mp yes with ⟨i,hi,mem⟩|⟨i,j,adj,hi,hj⟩
  · rcases Finset.mem_insert.mp mem with rfl|e
    · exact ao hi
    · exact bo (Finset.mem_singleton.mp e ▸ hi)
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;>
      first | exact adj.ne rfl | exact ab adj | exact ab adj.symm

lemma off_one (a : Fin n) (ao : a ∉ A) : graphFun G A (mark {a}) = false := by
  simpa using off_pair G A a a ao ao (G.loopless.irrefl a)

lemma on_edge {a b : Fin n} (ab : G.Adj a b) (S : Finset (Fin n)) (aS : a∈S) (bS : b∈S) :
    graphFun G A (mark S) = true :=
  (mark_true G A S).mpr (Or.inr ⟨a,b,ab,aS,bS⟩)

lemma inserts_differ (S : Finset (Fin n)) (u i : Fin n)
    (diff : mark S i ≠ mark (insert u S) i) : i = u := by
  by_contra ne
  exact diff (by simp [mark,ne])

lemma not_raw_output (C : Circuit) (out : circuitFun n C = graphFun G A)
    (apart : ∀ i j, G.Adj i j → i ∉ A) (edge : ∃ i j, G.Adj i j) :
    n ≤ C.output := by
  by_contra! small
  let k : Fin n := ⟨C.output,small⟩
  have projected (x : Fin n → Bool) : graphFun G A x = x k := by
    rw [←out]
    change ((Absorb193.wiresFrom C.gates (List.ofFn x)).getD k.val false) = _
    rw [Absorb193.getD_wiresFrom _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  by_cases hk : k ∈ A
  · obtain ⟨a,b,adj⟩ := edge
    have ak : k ≠ a := fun e => apart a b adj (e ▸ hk)
    have bk : k ≠ b := fun e => apart b a adj.symm (e ▸ hk)
    have yes := on_edge G A adj {a,b} (by simp) (by simp)
    rw [projected] at yes
    simp [mark,ak,bk] at yes
  · have no := off_one G A k hk
    rw [projected] at no
    simp [mark] at no

lemma two_neighbors (u : Fin n) (degree : (G.neighborSet u).ncard = 3) :
    ∃ a b, G.Adj u a ∧ G.Adj u b ∧ a ≠ b := by
  have more : 1 < (G.neighborFinset u).card := by
    change 1 < (G.neighborSet u).toFinset.card
    rw [← Set.ncard_eq_toFinset_card']
    omega
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp more
  exact ⟨a,b,(G.mem_neighborFinset _ _).mp ha,(G.mem_neighborFinset _ _).mp hb,ab⟩


lemma count_read {n} (i : Fin n) (gs : List Gate) (fan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (k : Nat) :
    (gs.zipIdx k).countP (Absorb193.reader n i.val) = (gs.filter (reads i.val)).length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨op,len⟩ := fan g (by simp)
    have same : Absorb193.reader n i.val (g,k) = reads i.val g := by
      have lt : i.val < n+k := by have := i.isLt; omega
      obtain ⟨o,l⟩ := g
      change o = .and ∨ o = .or ∨ o = .not at op
      change l.length ≤ 2 at len
      rcases op with rfl|rfl|rfl <;> simp [Absorb193.reader,Absorb193.normGate,reads,pins,GateOp.eval,lt,List.take_of_length_le len]
    rw [List.zipIdx_cons,List.countP_cons, same]
    have tail := ih (fun z hz => fan z (List.mem_cons_of_mem _ hz)) (k+1)
    rw [tail]
    by_cases on : reads i.val g = true <;> simp [on,List.filter_cons]

lemma absorbing_reads (C : Circuit) (minimal : IsMinimalCircuit n C)
    (correct : circuitFun n C = graphFun G A) (v : Fin n) (mem : v ∈ A) :
    (C.gates.filter (reads v.val)).length ≤ 1 := by
  have fixed (x : Fin n → Bool) (on : (C.wires (List.ofFn x)).getD v.val false = true) :
      circuitFun n C x = true := by
    change (Absorb193.wiresFrom C.gates (List.ofFn x)).getD v.val false = true at on
    rw [Absorb193.getD_wiresFrom _ _ _ (by simp)] at on
    have xv : x v = true := by simpa [List.getD_eq_getElem?_getD] using on
    rw [correct]
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inl ⟨v,mem,xv⟩
  obtain ⟨D,fan,eq,bound⟩ := absorbing n C v.val minimal.1 fixed
  have smaller := minimal.2 D fan eq
  have count : (C.gates.zipIdx.countP (Absorb193.reader n v.val)) =
      (C.gates.filter (reads v.val)).length := count_read v _ minimal.1 0
  have equal_reader (p : Gate × Nat) :
      (decide (v.val < n+p.2) && (GateOp.casesOn (motive := fun _ => List Nat) p.1.op
        p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains v.val)
        = Absorb193.reader n v.val p := by
    rcases p with ⟨⟨o,ins⟩,j⟩
    cases o <;> rfl
  simp_rw [equal_reader] at bound
  change D.size + C.gates.zipIdx.countP (Absorb193.reader n v.val) ≤ C.size + 1 at bound
  rw [count] at bound
  omega


lemma pair_eval (u v : Fin n) (g : Gate) (ord : g.inputs.Perm [u.val,v.val]) (join : Bool)
    (op : g.op = if join then .or else .and) (x : Fin n → Bool) (t : List Bool) :
    atBank g (List.ofFn x ++ t) = if join then x u || x v else x u && x v := by
  rcases List.perm_pair.mp ord with e|e <;> cases join <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] at op ⊢ <;>
    simp only [atBank,e,op,List.map_cons,List.map_nil,raw,GateOp.eval] <;>
    simp [Bool.and_comm,Bool.or_comm]

lemma main (C : Circuit) (u : Fin n) (uout : u ∉ A)
    (degree : (G.neighborSet u).ncard = 3)
    (girth : ∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length)
    (apart : ∀ i j, G.Adj i j → i ∉ A) (edge : ∃ i j, G.Adj i j)
    (small : IsMinimalCircuit n C) (correct : circuitFun n C = graphFun G A)
    (few : (C.gates.filter (reads u.val)).length ≤ 1) (g : Gate)
    (mem : g ∈ C.gates.filter (reads u.val)) (v : Fin n) (vu : v≠u)
    (ord : g.inputs.Perm [u.val,v.val]) : g.op ≠ .and ∧ g.op ≠ .or := by
  have out := not_raw_output G A C correct apart edge
  obtain ⟨a,b,ua,ub,ab⟩ := two_neighbors G u degree
  have short : girthFive G := fun i p hp => le_trans (by decide : 5 ≤ 7) (girth i p hp)
  obtain ⟨r,ur,rv,vr⟩ := private_neighbor short vu.symm ua ub ab
  have ur' := ur.ne
  have rout : r ∉ A := apart _ _ ur.symm
  have deny (x y : Fin n → Bool) (readers :
      ∀ i : Fin n, x i ≠ y i → ∀ q ∈ C.gates, i.val ∈ pins q → q=g)
      (same : ∀ t, atBank g (List.ofFn x ++ t) = atBank g (List.ofFn y ++ t))
      (changeVal : graphFun G A x ≠ graphFun G A y) : False := by
    have eq := lockstep C small.1 g x y out readers same
    change circuitFun n C x = circuitFun n C y at eq
    rw [correct] at eq
    exact changeVal eq
  have only_u (S : Finset (Fin n)) (i : Fin n) (diff : mark S i ≠ mark (insert u S) i) :
      ∀ q ∈ C.gates, i.val ∈ pins q → q=g := by
    obtain rfl := inserts_differ S u i diff
    exact fun q h r => read_only few mem h r
  constructor
  · intro op
    refine deny (mark {r}) (mark (insert u {r})) (only_u _) ?_ ?_
    · intro t
      rw [pair_eval u v g ord false op, pair_eval u v g ord false op]
      simp [mark,rv.symm,vu]
    · rw [off_one G A r rout,on_edge G A ur _ (by simp) (by simp)]
      decide
  · intro op
    by_cases va : v∈A
    · have vg : v.val ∈ pins g := by
        rcases List.perm_pair.mp ord with e|e <;> simp [pins,op,e,GateOp.eval]
      have vm : g ∈ C.gates.filter (reads v.val) :=
        List.mem_filter.mpr ⟨(List.mem_filter.mp mem).1,List.contains_iff_mem.mpr vg⟩
      have vf := absorbing_reads G A C small correct v va
      refine deny (mark {u}) (mark {v}) ?_ ?_ ?_
      · intro i diff q h r
        by_cases iu : i=u
        · subst i; exact read_only few mem h r
        by_cases iv : i=v
        · subst i; exact read_only vf vm h r
        exact False.elim (diff (by simp [mark,iu,iv]))
      · intro t
        rw [pair_eval u v g ord true op,pair_eval u v g ord true op]
        simp [mark]
      · have on := (mark_true G A {v}).mpr (Or.inl ⟨v,va,by simp⟩)
        rw [off_one G A u uout,on]; decide
    · refine deny (mark {v,r}) (mark (insert u {v,r})) (only_u _) ?_ ?_
      · intro t
        rw [pair_eval u v g ord true op,pair_eval u v g ord true op]
        simp [mark]
      · rw [off_pair G A v r va rout vr,on_edge G A ur _ (by simp) (by simp)]
        decide


lemma main2 (C : Circuit) (u : Fin n) (uout : u ∉ A)
    (deg : 1 < (G.neighborSet u).ncard)
    (girth : ∀ i (p : G.Walk i i), p.IsCycle → 7 ≤ p.length)
    (apart : ∀ i j, G.Adj i j → i ∉ A)
    (fan : FanInTwo C) (correct : circuitFun n C = graphFun G A)
    (one : (C.gates.filter (reads u.val)).length = 1) (g : Gate) (hg : g ∈ C.gates)
    (v : Fin n) (vu : v ≠ u)
    (ord0 : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val]) :
    g.op ≠ .and ∧ (g.op = .or → v ∈ A) := by
  have few : (C.gates.filter (reads u.val)).length ≤ 1 := by omega
  have ord : g.inputs.Perm [u.val, v.val] := by
    rcases ord0 with e|e
    · rw [e]
    · rw [e]; exact List.Perm.swap u.val v.val []
  obtain ⟨a, b, ha, hb, ab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp deg
  have ua : G.Adj u a := ha
  have ub : G.Adj u b := hb
  have edge : ∃ i j, G.Adj i j := ⟨u, a, ua⟩
  have out := not_raw_output G A C correct apart edge
  have short : girthFive G := fun i p hp => le_trans (by decide : 5 ≤ 7) (girth i p hp)
  obtain ⟨r,ur,rv,vr⟩ := private_neighbor short vu.symm ua ub ab
  have ur' := ur.ne
  have rout : r ∉ A := apart _ _ ur.symm
  have deny (x y : Fin n → Bool) (readers :
      ∀ i : Fin n, x i ≠ y i → ∀ q ∈ C.gates, i.val ∈ pins q → q=g)
      (same : ∀ t, atBank g (List.ofFn x ++ t) = atBank g (List.ofFn y ++ t))
      (changeVal : graphFun G A x ≠ graphFun G A y) : False := by
    have eq := lockstep C fan g x y out readers same
    change circuitFun n C x = circuitFun n C y at eq
    rw [correct] at eq
    exact changeVal eq
  have memOf (hop : g.op = .and ∨ g.op = .or) : g ∈ C.gates.filter (reads u.val) := by
    refine List.mem_filter.mpr ⟨hg, ?_⟩
    rcases ord0 with e|e <;> rcases hop with h|h <;> simp [reads, pins, e, h, GateOp.eval]
  constructor
  · intro op
    have mem := memOf (Or.inl op)
    refine deny (mark {r}) (mark (insert u {r})) ?_ ?_ ?_
    · intro i diff
      obtain rfl := inserts_differ {r} u i diff
      exact fun q h rd => read_only few mem h rd
    · intro t
      rw [pair_eval u v g ord false op, pair_eval u v g ord false op]
      simp [mark,rv.symm,vu]
    · rw [off_one G A r rout,on_edge G A ur _ (by simp) (by simp)]
      decide
  · intro op
    by_contra va
    have mem := memOf (Or.inr op)
    refine deny (mark {v,r}) (mark (insert u {v,r})) ?_ ?_ ?_
    · intro i diff
      obtain rfl := inserts_differ {v,r} u i diff
      exact fun q h rd => read_only few mem h rd
    · intro t
      rw [pair_eval u v g ord true op,pair_eval u v g ord true op]
      simp [mark]
    · rw [off_pair G A v r va rout vr,on_edge G A ur _ (by simp) (by simp)]
      decide

end Sole
end PEqualNP.Outside.L_meta_8257

theorem PEqualNP.Outside.L_meta_8257 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x6 ∉ x3, (1 : ℕ) < (x2.neighborSet x6).ncard → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x3) → (∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → (∀ (x11 : Fin x1 → Bool), x4 x11 = Bool.true ↔ (∃ x12 ∈ x3, x11 x12 = Bool.true) ∨ ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 → (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x6) x5.gates).length = (1 : ℕ) → ∀ x15 ∈ x5.gates, ∀ (x17 : Fin x1), x17 ≠ x6 → x15.inputs = [↑x6, ↑x17] ∨ x15.inputs = [↑x17, ↑x6] → x15.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x15.op = PEqualNP.CircuitLowerBounds.GateOp.or → x17 ∈ x3) := by
  intro n G A f C u uA deg apart girth hf fan hC one g hg v vu ord
  classical
  have hfG : f = PEqualNP.MetaComplexity.NestedCover.graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [hf x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rw [hfG] at hC
  exact PEqualNP.Outside.L_meta_8257.Sole.main2 G A C u uA deg girth apart fan hC one g hg v vu ord
