import PEqualNP.Defs

-- The circuit argument adapts our two-leaf argument for L-meta-10422.
-- Seven-vertex certificates come from L-meta-982.
-- The wire bypass construction is adapted from the checked L-meta-2668 and L-meta-1499.
-- The two pendant vertices force distinct OR and AND gates; the adjacent centers cannot both be masked.
namespace PEqualNP.Outside.L_meta_10938_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
namespace PinBase


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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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


end PinBase

section
open PinBase

def ProperNot (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1

def pinRow (n p : ℕ) (b : Bool) (x : List Bool) : List Bool :=
  List.ofFn (fun j : Fin n => if j.val=p then b else x.getD j false)

def pinStart (n p : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun j : Fin n => if j.val=p then .const b else .wire j)

theorem pin_inv (n p : ℕ) (b : Bool) (x : List Bool) (hx : x.length=n) :
    Inv n x (pinRow n p b x) (pinStart n p b,[]) := by
  refine ⟨by simp [pinRow,pinStart],?_⟩
  intro i
  change ((pinStart n p b).getD i (.const false)).Valid (n+0) ∧
    ((pinStart n p b).getD i (.const false)).val x =
      (pinRow n p b x).getD i false
  by_cases hi : i<n
  · by_cases he : i=p
    · subst i
      simp [pinRow,pinStart,List.getD_eq_getElem?_getD,hi,Stat.Valid,Stat.val]
    · simp [pinRow,pinStart,List.getD_eq_getElem?_getD,hi,he,Stat.Valid,Stat.val]
  · simp [pinRow,pinStart,List.getD_eq_getElem?_getD,hi,Stat.Valid,Stat.val]
end

namespace Bypass


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
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
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

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

end Bypass
open Bypass

section
open PinBase
open Bypass (gateAt_eq)

def atGate (n : ℕ) (C : Circuit) (a : List Stat × List Gate) (j : ℕ) :=
  elim n (C.gates.take j) a

def outcome (n : ℕ) (C : Circuit) (a : List Stat × List Gate) (j : ℕ) : Option Gate × Stat :=
  let z := atGate n C a j
  let g := gateAt C j
  simplify g.op (n+z.2.length) (g.inputs.map fun i => z.1.getD i (.const false))

private theorem elim_join (n : ℕ) (l r : List Gate) (a : List Stat × List Gate) :
    elim n (l++r) a = elim n r (elim n l a) := by
  simp [elim,List.foldl_append]

theorem next_stage {n : ℕ} {C : Circuit} (a : List Stat × List Gate) {j : ℕ}
    (jl : j<C.gates.length) :
    atGate n C a (j+1) = ((atGate n C a j).1 ++ [(outcome n C a j).2],
      (atGate n C a j).2 ++ (outcome n C a j).1.toList) := by
  unfold atGate
  rw [List.take_succ_eq_append_getElem jl,elim_join,←gateAt_eq jl]
  rfl

private theorem stat_length (n : ℕ) (gs : List Gate) (a : List Stat × List Gate) :
    (elim n gs a).1.length = a.1.length+gs.length := by
  induction gs generalizing a with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n a g)).1.length = a.1.length+(g::gs).length
    rw [ih]
    simp [elimStep]
    omega

theorem first_size {n : ℕ} {C : Circuit} (a : List Stat × List Gate)
    {j : ℕ} (jl : j≤C.gates.length) :
    (atGate n C a j).1.length = a.1.length+j := by
  simp [atGate,stat_length,Nat.min_eq_left jl]

theorem keep_status {n : ℕ} {C : Circuit} (a : List Stat × List Gate) {j k i : ℕ}
    (le : j≤k) (inTable : i<(atGate n C a j).1.length) :
    (atGate n C a k).1.getD i (.const false) = (atGate n C a j).1.getD i (.const false) := by
  have split : C.gates.take k = C.gates.take j ++ (C.gates.take k).drop j := by
    conv_lhs => rw [← List.take_append_drop j (C.gates.take k)]
    rw [List.take_take,Nat.min_eq_left le]
  show (elim n (C.gates.take k) a).1.getD i _ = _
  rw [split,elim_join]
  exact elim_getD _ _ _ _ _ inTable

theorem born_status {n : ℕ} {C : Circuit} (a : List Stat × List Gate) (alen : a.1.length=n)
    {j : ℕ} (jl : j<C.gates.length) :
    (atGate n C a (j+1)).1.getD (n+j) (.const false) = (outcome n C a j).2 := by
  rw [next_stage a jl]
  have hlen := first_size (n := n) (C := C) a jl.le
  rw [alen] at hlen
  exact getD_snoc_len _ _ _ _ hlen

theorem cost_selected {n : ℕ} {C : Circuit} (a : List Stat × List Gate) (S : Finset ℕ)
    (valid : S ⊆ Finset.range C.gates.length)
    (noemit : ∀ j ∈ S, (outcome n C a j).1 = none) :
    (elim n C.gates a).2.length+S.card ≤ a.2.length+C.gates.length := by
  have h : ∀ m ≤ C.gates.length, (atGate n C a m).2.length+
      (S.filter (fun j => j<m)).card ≤ a.2.length+m := by
    intro m
    induction m with
    | zero => simp [atGate,elim]
    | succ m ih =>
      intro hm
      have jl : m < C.gates.length := by omega
      have prev := ih jl.le
      rw [next_stage a jl]
      simp only [List.length_append]
      have le := toList_length_le (outcome n C a m).1
      by_cases mm : m∈S
      · have ss : S.filter (fun j => j<m+1) =
            insert m (S.filter (fun j => j<m)) := by
          ext k
          simp only [Finset.mem_filter,Finset.mem_insert]
          constructor
          · rintro ⟨ks,klt⟩
            by_cases e : k=m
            · exact Or.inl e
            · exact Or.inr ⟨ks,by omega⟩
          · rintro (rfl|⟨ks,klt⟩)
            · exact ⟨mm,by omega⟩
            · exact ⟨ks,by omega⟩
        rw [ss,Finset.card_insert_of_notMem (by simp),noemit m mm]
        simp
        omega
      · have ss : S.filter (fun j => j<m+1) = S.filter (fun j => j<m) := by
          ext k
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ks,klt⟩
            have ne : k≠m := fun e => mm (e ▸ ks)
            exact ⟨ks,by omega⟩
          · exact fun ⟨ks,klt⟩ => ⟨ks,by omega⟩
        rw [ss]
        omega
  have ss : S.filter (fun j => j<C.gates.length)=S := by
    exact Finset.filter_true_of_mem (fun j hj => Finset.mem_range.mp (valid hj))
  have hh := h C.gates.length le_rfl
  simpa [atGate,ss] using hh

theorem no_emit_if_constant {n : ℕ} {C : Circuit} (a : List Stat × List Gate)
    {j i : ℕ} (jl : j<C.gates.length) (read : i∈(gateAt C j).inputs)
    (fan : FanInTwo C) (norm : ProperNot C) {b : Bool}
    (known : (atGate n C a j).1.getD i (.const false)=.const b) :
    (outcome n C a j).1 = none := by
  have member : gateAt C j ∈ C.gates := by rw [gateAt_eq jl]; exact List.getElem_mem jl
  obtain ⟨op,le⟩ := fan _ member
  exact simplify_count _ _ _ op (by simpa using le) (by simpa using norm _ member)
    ⟨b,List.mem_map.mpr ⟨i,read,known⟩⟩

theorem controlling_constant (op : GateOp) (m : ℕ) (ins : List Stat) {b : Bool}
    (small : ins.length≤2) (short : op=GateOp.not → ins.length≤1)
    (controls : (op=GateOp.and ∧ b=false) ∨ (op=GateOp.or ∧ b=true) ∨ op=GateOp.not)
    (known : Stat.const b∈ins) :
    ∃ c : Bool, simplify op m ins = (none,.const c) := by
  rcases controls with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | rfl
  · rcases ins with _ | ⟨p, _ | ⟨q, _ | ⟨r,rs⟩⟩⟩
    · simp at known
    · have e : p=Stat.const false := (List.mem_singleton.mp known).symm
      subst p
      exact ⟨false,rfl⟩
    · have kn : Stat.const false=p ∨ Stat.const false=q := by simpa using known
      rcases kn with h|h
      · subst p; exact ⟨false, by cases q <;> simp [simplify,simpAnd]⟩
      · subst q; exact ⟨false, by cases p <;> simp [simplify,simpAnd]⟩
    · simp at small
  · rcases ins with _ | ⟨p, _ | ⟨q, _ | ⟨r,rs⟩⟩⟩
    · simp at known
    · have e : p=Stat.const true := (List.mem_singleton.mp known).symm
      subst p
      exact ⟨true,rfl⟩
    · have kn : Stat.const true=p ∨ Stat.const true=q := by simpa using known
      rcases kn with h|h
      · subst p; exact ⟨true, by cases q <;> simp [simplify,simpOr]⟩
      · subst q; exact ⟨true, by cases p <;> simp [simplify,simpOr]⟩
    · simp at small
  · rcases ins with _ | ⟨p, _ | ⟨q,l⟩⟩
    · simp at known
    · have e : p=Stat.const b := (List.mem_singleton.mp known).symm
      subst p
      exact ⟨!b,rfl⟩
    · have h := short rfl; simp at h

end

section
open PinBase
open Bypass (gateAt_mem)

def pinAcc (n p : ℕ) (b : Bool) : List Stat × List Gate :=
  (pinStart n p b,[])

theorem raw_frozen {n p : ℕ} (hp : p<n) (b : Bool) (C : Circuit) (j : ℕ) :
    (atGate n C (pinAcc n p b) j).1.getD p (.const false)=.const b := by
  have pl : p<(atGate n C (pinAcc n p b) 0).1.length := by
    simp [atGate,elim,pinAcc,pinStart,hp]
  rw [keep_status (pinAcc n p b) (Nat.zero_le j) pl]
  simp [atGate,elim,pinAcc,pinStart,List.getD_eq_getElem?_getD,hp]

theorem read_frozen_skips {n p : ℕ} (hp : p<n) (b : Bool) {C : Circuit}
    (fan : FanInTwo C) (norm : ProperNot C) {j : ℕ} (jl : j<C.gates.length)
    (read : p∈(gateAt C j).inputs) :
    (outcome n C (pinAcc n p b) j).1=none :=
  no_emit_if_constant _ jl read fan norm (raw_frozen hp b C j)

theorem freezes_if_controlled {n : ℕ} {C : Circuit} (fan : FanInTwo C)
    (norm : ProperNot C) (a : List Stat × List Gate) {i j : ℕ}
    (jl : j<C.gates.length) (read : i∈(gateAt C j).inputs) {b : Bool}
    (known : (atGate n C a j).1.getD i (.const false)=.const b)
    (controls : ((gateAt C j).op=.and ∧ b=false) ∨
      ((gateAt C j).op=.or ∧ b=true) ∨ (gateAt C j).op=.not) :
    ∃ c : Bool, outcome n C a j = (none,.const c) := by
  exact controlling_constant _ _ _ (by simpa using (fan _ (gateAt_mem jl)).2)
    (by simpa using norm _ (gateAt_mem jl)) controls (List.mem_map.mpr ⟨i,read,known⟩)

theorem frozen_status_later {n : ℕ} {C : Circuit} (a : List Stat × List Gate)
    (alen : a.1.length=n) {j k : ℕ} (jl : j<C.gates.length) (jk : j<k) {c : Bool}
    (born : outcome n C a j=(none,.const c)) :
    (atGate n C a k).1.getD (n+j) (.const false)=.const c := by
  have len := first_size (n := n) (C := C) a (show j+1≤C.gates.length by omega)
  rw [alen] at len
  have good : n+j<(atGate n C a (j+1)).1.length := by omega
  rw [keep_status a (by omega : j+1≤k) good,born_status a alen jl,born]

theorem pin_selected {n p : ℕ} {C : Circuit} (fan : FanInTwo C) (b : Bool)
    (S : Finset ℕ) (valid : S ⊆ Finset.range C.gates.length)
    (noemit : ∀ j∈S, (outcome n C (pinAcc n p b) j).1=none)
    (nonconstant : ∃ x z : List Bool, x.length=n ∧ z.length=n ∧
      C.eval (pinRow n p b x) ≠ C.eval (pinRow n p b z)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size+S.card ≤ C.size ∧
      ∀ x : List Bool, x.length=n → D.eval x = C.eval (pinRow n p b x) := by
  let a := pinAcc n p b
  let packed := elim n C.gates a
  have inv (x : List Bool) (hx : x.length=n) :
      Inv n x (wiresFrom C.gates (pinRow n p b x)) packed :=
    inv_elim n x hx C.gates _ _ fan (pin_inv n p b x hx)
  cases e : packed.1.getD C.output (.const false) with
  | const c =>
    exfalso
    obtain ⟨x,z,hx,hz,ne⟩ := nonconstant
    apply ne
    have xx := ((inv x hx).2 C.output).2
    have zz := ((inv z hz).2 C.output).2
    rw [e] at xx zz
    exact xx.symm.trans zz
  | wire q =>
    refine ⟨⟨packed.2,q⟩,elim_ok _ _ _ (by simp [a,pinAcc]),?_,?_⟩
    · simpa [Circuit.size,packed,a,pinAcc] using cost_selected (n := n) (C := C) a S valid noemit
    · intro x hx
      have hh := ((inv x hx).2 C.output).2
      rw [e] at hh
      exact hh

end

section
open PinBase

def PinFloor (n p : ℕ) (b : Bool) (C : Circuit) (k : ℕ) : Prop :=
  ∀ D : Circuit, FanInTwo D → (∀ x : List Bool, x.length=n →
    D.eval x = C.eval (pinRow n p b x)) → k ≤ D.size

def PinVaries (n p : ℕ) (b : Bool) (C : Circuit) : Prop :=
  ∃ x z : List Bool, x.length=n ∧ z.length=n ∧
    C.eval (pinRow n p b x) ≠ C.eval (pinRow n p b z)

def skipped (n p : ℕ) (b : Bool) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => (outcome n C (pinAcc n p b) j).1.isNone

theorem mem_skipped {n p j : ℕ} {b : Bool} {C : Circuit} :
    j ∈ skipped n p b C ↔ j<C.gates.length ∧ (outcome n C (pinAcc n p b) j).1=none := by
  simp only [skipped,Finset.mem_filter,Finset.mem_range]
  cases (outcome n C (pinAcc n p b) j).1 <;> simp

theorem skipped_budget {n p k : ℕ} {b : Bool} {C : Circuit} (fan : FanInTwo C)
    (lower : PinFloor n p b C k) (varies : PinVaries n p b C) :
    k+(skipped n p b C).card ≤ C.size := by
  obtain ⟨D,fd,sz,correct⟩ := pin_selected fan b (skipped n p b C)
    (fun _ h => Finset.mem_range.mpr (mem_skipped.mp h).1)
    (fun _ h => (mem_skipped.mp h).2) varies
  exact (Nat.add_le_add_right (lower D fd correct) _).trans sz

theorem reader_skips {n p j : ℕ} {b : Bool} {C : Circuit} (hp : p<n) (fan : FanInTwo C)
    (norm : ProperNot C) (jl : j<C.gates.length) (read : p∈(gateAt C j).inputs) :
    j∈skipped n p b C :=
  mem_skipped.mpr ⟨jl,read_frozen_skips hp b fan norm jl read⟩

theorem frozen_reader_skips {n p r j : ℕ} {b c : Bool} {C : Circuit}
    (fan : FanInTwo C) (norm : ProperNot C) (jl : j<C.gates.length)
    (rj : r<j) (control : outcome n C (pinAcc n p b) r=(none,.const c))
    (read : n+r∈(gateAt C j).inputs) : j ∈ skipped n p b C :=
  mem_skipped.mpr ⟨jl,no_emit_if_constant _ jl read fan norm
    (frozen_status_later _ (by simp [pinAcc,pinStart]) (rj.trans jl) rj control)⟩

theorem sole_raw_reader {n p j k : ℕ} {b : Bool} {C : Circuit}
    (hp : p<n) (fan : FanInTwo C) (norm : ProperNot C)
    (budget : (skipped n p b C).card≤1)
    (jl : j<C.gates.length) (kl : k<C.gates.length)
    (rdj : p∈(gateAt C j).inputs) (rdk : p∈(gateAt C k).inputs) :
    j=k :=
  (Finset.card_le_one.mp budget) _ (reader_skips hp fan norm jl rdj)
    _ (reader_skips hp fan norm kl rdk)

theorem sole_frozen_reader {n p r j k : ℕ} {b c : Bool} {C : Circuit}
    (fan : FanInTwo C) (norm : ProperNot C) (budget : (skipped n p b C).card≤2)
    (rl : r<C.gates.length) (rj : r<j) (rk : r<k)
    (jl : j<C.gates.length) (kl : k<C.gates.length)
    (control : outcome n C (pinAcc n p b) r=(none,.const c))
    (rdj : n+r∈(gateAt C j).inputs) (rdk : n+r∈(gateAt C k).inputs) :
    j=k := by
  by_contra ne
  let S : Finset ℕ := {r,j,k}
  have s : S ⊆ skipped n p b C := by
    intro i h
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl
    · exact mem_skipped.mpr ⟨rl,by rw [control]⟩
    · exact frozen_reader_skips fan norm jl rj control rdj
    · exact frozen_reader_skips fan norm kl rk control rdk
  have card : S.card=3 := by
    unfold S
    rw [Finset.card_insert_of_notMem (by simp [show r≠j by omega,show r≠k by omega])]
    simp [ne]
  have b := Finset.card_le_card s
  omega

end

section

theorem bypass_value_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n+r)
    (agree : val C x (n+r) = val C x i) :
    ∀ u, val (bypass n C r i) x (aliasWire (n+r) i u) = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hit : u = n+r
    · rw [hit, aliasWire_self, bypass_val_lt hx hr i hi, agree]
    by_cases hlt : u < n+r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]
    rw [aliasWire_gt_self (by omega)]
    by_cases hge : n + C.gates.length ≤ u
    · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]
    obtain ⟨k,rfl⟩ : ∃ k, u = n+(k+1) := ⟨u-n-1,by omega⟩
    have hk : k+1 < C.gates.length := by omega
    have kr : ¬ k < r := by omega
    have eq : n+(k+1)-1 = n+k := by omega
    have hd : k < (bypass n C r i).gates.length := by rw [bypass_length]; omega
    rw [eq, val_gate hx hd, val_gate hx hk, gateAt_bypass (by omega), if_neg kr]
    simp only [aliasGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply]
    by_cases early : a < n+(k+1)
    · have mappedEarly := aliasWire_lt hi (by omega : n+r ≤ n+k) (by omega : a < n+k+1)
      rw [if_pos early, if_pos mappedEarly]
      exact ih a early
    · have later : n+r < a := by omega
      rw [if_neg early, aliasWire_gt_self later, if_neg (by omega)]

theorem bypass_eval_eq_any {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n+r)
    (agree : val C x (n+r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  bypass_value_eq hx hr hi agree C.output

def appendOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [a,b]⟩], n+C.gates.length⟩

private theorem oldGate_appendOr (n : ℕ) (C : Circuit) (a b j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendOr n C a b) j = gateAt C j := by
  unfold gateAt appendOr
  simpa using List.getD_append C.gates [⟨GateOp.or,[a,b]⟩] ⟨GateOp.or,[]⟩ j hj

private theorem tailGate_appendOr (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendOr n C a b) C.gates.length = ⟨.or,[a,b]⟩ := by
  simp [gateAt,appendOr]

theorem appendOr_eval {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length=n)
    {a b : ℕ} (ha : a<n+C.gates.length) (hb : b<n+C.gates.length) :
    (appendOr n C a b).eval x = (val C x a || val C x b) := by
  change val (appendOr n C a b) x (n+C.gates.length) = _
  rw [val_gate hx (by simp [appendOr]), tailGate_appendOr]
  have H (j : ℕ) (hj : j < n+C.gates.length) :
      val (appendOr n C a b) x j = val C x j :=
    val_prefix hx (m := C.gates.length) (by omega) (by simp [appendOr])
      (oldGate_appendOr n C a b) j hj
  simp [GateOp.eval, ha, hb, H a ha, H b hb]

theorem appendOr_fan {n : ℕ} {C : Circuit} (fan : FanInTwo C) (a b : ℕ) :
    FanInTwo (appendOr n C a b) := by
  intro g hg
  simp only [appendOr, List.mem_append, List.mem_singleton] at hg
  rcases hg with h | rfl
  · exact fan _ h
  · simp

theorem appendOr_back {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {a b : ℕ} (ha : a < n+C.gates.length) (hb : b < n+C.gates.length) :
    ReadsBack n (appendOr n C a b) := by
  intro j hj u hu
  by_cases hj0 : j < C.gates.length
  · rw [oldGate_appendOr _ _ _ _ _ hj0] at hu
    exact back j hj0 u hu
  · have hj1 : j = C.gates.length := by simp [appendOr] at hj; omega
    subst j
    rw [tailGate_appendOr] at hu
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl | rfl <;> assumption

def moveOr (n : ℕ) (C : Circuit) (r y d : ℕ) : Circuit :=
  let D := bypass n C r y
  appendOr n D d D.output


theorem moveOr_sound {n : ℕ} {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C)
    (out : C.output < n+C.gates.length)
    {r y d : ℕ} (hr : r < C.gates.length) (hy : y < n+r) (hd : d < n+r)
    (gate : gateAt C r = ⟨.or,[y,d]⟩ ∨ gateAt C r = ⟨.or,[d,y]⟩)
    (absorbs : ∀ x : List Bool, x.length = n → val C x d = true → C.eval x = true) :
    FanInTwo (moveOr n C r y d) ∧ ReadsBack n (moveOr n C r y d) ∧
      (moveOr n C r y d).size = C.size ∧
      ∀ x : List Bool, x.length = n → (moveOr n C r y d).eval x = C.eval x := by
  let D := bypass n C r y
  have len : D.gates.length = C.gates.length-1 := bypass_length _ _ _ _
  have hDout : D.output < n+D.gates.length := by
    change aliasWire (n+r) y C.output < n+D.gates.length
    rw [len]
    exact aliasWire_lt hy (by omega) (by omega)
  have hDd : d < n+D.gates.length := by omega
  have fanD : FanInTwo D := by
    intro g hg
    obtain ⟨g', hm, op, inputs⟩ := bypass_mem g hg
    rw [op,inputs]
    exact fan g' hm
  refine ⟨appendOr_fan fanD _ _, appendOr_back (bypass_readsBack hy back) hDd hDout, ?_, ?_⟩
  · change (D.gates ++ [(⟨GateOp.or,[d,D.output]⟩ : Gate)]).length = C.gates.length
    simp [len]
    omega
  · intro x hx
    change (appendOr n D d D.output).eval x = C.eval x
    rw [appendOr_eval hx hDd hDout, bypass_val_lt hx hr d hd]
    cases e : val C x d with
    | true => simp [absorbs x hx e]
    | false =>
      simp only [Bool.false_or]
      have agree : val C x (n+r) = val C x y := by
        rcases gate with gate | gate <;>
          rw [val_gate hx hr, gate] <;> simp [GateOp.eval,hy,hd,e]
      exact bypass_eval_eq_any hx hr hy agree


theorem mask_raw {n : ℕ} {C : Circuit} (back : ReadsBack n C)
    {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    {r y d : ℕ} (hr : r < C.gates.length) (hd : d < n+r) (hne : d ≠ y)
    (gate : gateAt C r = ⟨.or,[y,d]⟩ ∨ gateAt C r = ⟨.or,[d,y]⟩)
    (sole : ∀ j < C.gates.length, y ∈ (gateAt C j).inputs → j = r)
    (same : ∀ i < n, i ≠ y → x.getD i false = z.getD i false)
    (companion : val C x d = true) :
    ∀ w, w ≠ y → val C x w = val C z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases raw : w<n
    · rw [val_input hx raw, val_input hz raw, same w raw hw]
    by_cases gone : n+C.gates.length ≤ w
    · rw [val_ge hx gone,val_ge hz gone]
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have jl : j < C.gates.length := by omega
    rw [val_gate hx jl,val_gate hz jl]
    by_cases hit : j=r
    · subst j
      have t : val C z d = true := (ih d hd hne).symm.trans companion
      have ylt : y < n+r := back r hr y (by rcases gate with g | g <;> rw [g] <;> simp)
      rcases gate with g | g <;> rw [g] <;> simp [GateOp.eval,hd,ylt,companion,t]
    · congr 1
      apply List.map_congr_left
      intro a ha
      have le := back j jl a ha
      rw [if_pos le,if_pos le]
      exact ih a le (fun e => hit (sole j jl (e ▸ ha)))

end

section
inductive Reach (n : ℕ) (C : Circuit) (y : ℕ) : ℕ → Prop where
  | start : Reach n C y y
  | step {i j : ℕ} : j < C.gates.length → i ∈ (gateAt C j).inputs →
      Reach n C y i → Reach n C y (n+j)

theorem reach_after {n y r : ℕ} {C : Circuit} (back : ReadsBack n C)
    (sole : ∀ j < C.gates.length, y ∈ (gateAt C j).inputs → j = r) {w : ℕ}
    (h : Reach n C y w) : w = y ∨ n+r ≤ w := by
  induction h with
  | start => exact Or.inl rfl
  | @step i j jl read _ ih =>
    rcases ih with rfl | h
    · exact Or.inr (by rw [sole j jl read])
    · exact Or.inr (h.trans (back j jl i read).le)

theorem reach_bypass {n y r : ℕ} {C : Circuit} (hy : y < n) (hr : r < C.gates.length)
    (back : ReadsBack n C) {w : ℕ} (h : Reach n C y w) :
    Reach n (bypass n C r y) y (aliasWire (n+r) y w) := by
  induction h with
  | start =>
    rw [aliasWire_lt_self (by omega : y < n+r)]
    exact Reach.start
  | @step i j jl read _ ih =>
    by_cases eq : j=r
    · subst j
      rw [aliasWire_self]
      exact Reach.start
    by_cases before : j < r
    · have ij := back j jl i read
      rw [aliasWire_lt_self (by omega : i < n+r)] at ih
      rw [aliasWire_lt_self (by omega : n+j < n+r)]
      have jlen : j < (bypass n C r y).gates.length := by rw [bypass_length]; omega
      apply Reach.step jlen _ ih
      rw [gateAt_bypass (by omega),if_pos before]
      exact read
    · have shift : aliasWire (n+r) y (n+j) = n+(j-1) := by
        rw [aliasWire_gt_self (by omega)]
        omega
      rw [shift]
      have jlen : j-1 < (bypass n C r y).gates.length := by rw [bypass_length]; omega
      apply Reach.step jlen _ ih
      rw [gateAt_bypass (by omega),if_neg (by omega),show j-1+1=j by omega]
      exact List.mem_map.mpr ⟨i,read,rfl⟩

private theorem append_old_gate (n : ℕ) (C : Circuit) (a b j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendOr n C a b) j = gateAt C j := by
  unfold gateAt appendOr
  simpa using List.getD_append C.gates [⟨GateOp.or,[a,b]⟩] ⟨GateOp.or,[]⟩ j hj

theorem reach_appendOr {n y w : ℕ} {C : Circuit} (a b : ℕ) (h : Reach n C y w) :
    Reach n (appendOr n C a b) y w := by
  induction h with
  | start => exact Reach.start
  | @step i j jl read _ ih =>
    have js : j < (appendOr n C a b).gates.length := by simp [appendOr]; omega
    exact Reach.step js (by rw [append_old_gate _ _ _ _ _ jl]; exact read) ih

theorem moved_nonor {n y d r j : ℕ} {C : Circuit} (hy : y<n) (hr : r<C.gates.length)
    (back : ReadsBack n C) (jl : j<C.gates.length) (rj : r<j)
    (bad : (gateAt C j).op ≠ GateOp.or) (h : Reach n C y (n+j)) :
    ∃ k < j, k < (moveOr n C r y d).gates.length ∧
      (gateAt (moveOr n C r y d) k).op ≠ GateOp.or ∧
      Reach n (moveOr n C r y d) y (n+k) := by
  let D := bypass n C r y
  have lenD : D.gates.length = C.gates.length-1 := bypass_length _ _ _ _
  have hk : j-1 < D.gates.length := by omega
  have e : (gateAt (moveOr n C r y d) (j-1)).op = (gateAt C j).op := by
    change (gateAt (appendOr n D d D.output) (j-1)).op = _
    rw [append_old_gate _ _ _ _ _ hk, gateAt_bypass (by omega),
      if_neg (by omega),show j-1+1=j by omega]
    rfl
  have V := reach_bypass hy hr back h
  rw [aliasWire_gt_self (by omega : n+r < n+j),show n+j-1=n+(j-1) by omega] at V
  refine ⟨j-1, by omega, ?_,fun eq => bad (e.symm.trans eq),reach_appendOr d D.output V⟩
  change j-1 < (appendOr n D d D.output).gates.length
  simp [appendOr]
  omega

theorem reachable_true {n y w : ℕ} {C : Circuit} {x : List Bool}
    (hy : y<n) (hx : x.length=n) (truth : x.getD y false = true)
    (back : ReadsBack n C)
    (ops : ∀ j < C.gates.length, Reach n C y (n+j) → (gateAt C j).op = GateOp.or)
    (h : Reach n C y w) : val C x w = true := by
  induction h with
  | start => rw [val_input hx hy, truth]
  | @step i j jl read h ih =>
    exact (val_or hx jl (ops j jl (Reach.step jl read h))).mpr
      ⟨i,read,back j jl i read,ih⟩
end

section
def Fits (n s : ℕ) (F : List Bool → Bool) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack n C ∧ C.output < n+C.gates.length ∧ C.size ≤ s ∧ ProperNot C ∧
    ∀ x : List Bool, x.length=n → C.eval x = F x

structure SoleOr (n : ℕ) (C : Circuit) (y : ℕ) where
  gate : ℕ
  other : ℕ
  valid : gate < C.gates.length
  early : other < n+gate
  different : other ≠ y
  op : gateAt C gate = ⟨.or,[y,other]⟩ ∨ gateAt C gate = ⟨.or,[other,y]⟩
  unique : ∀ j < C.gates.length, y ∈ (gateAt C j).inputs → j=gate
  notOutput : C.output ≠ y

private def on (n p : ℕ) (x : List Bool) : List Bool :=
  List.ofFn (fun j : Fin n => if j.val = p then true else x.getD j false)

private theorem on_read (n p : ℕ) (x : List Bool) {i : ℕ} (hi : i<n) :
    (on n p x).getD i false = if i=p then true else x.getD i false := by
  simp [on,List.getD_eq_getElem?_getD,hi]


theorem sufficient_move {n s y : ℕ} {C : Circuit} {F : List Bool → Bool} (hy : y<n)
    (fits : Fits n s F C) (r : SoleOr n C y)
    (sufficient : ∀ x, x.length=n → x.getD y false = true → F x = true) :
    Fits n s F (moveOr n C r.gate y r.other) := by
  obtain ⟨fan,back,out,sz,norm,correct⟩ := fits
  have absorb : ∀ x : List Bool, x.length=n → val C x r.other = true → C.eval x = true := by
    intro x hx companion
    let z := on n y x
    have hz : z.length=n := by simp [z,on]
    have zy : z.getD y false=true := by rw [on_read n y x hy,if_pos rfl]
    have same : ∀ i<n, i≠y → x.getD i false = z.getD i false := by
      intro i hi ne
      rw [on_read n y x hi,if_neg ne]
    have equal := mask_raw back hx hz r.valid r.early r.different r.op r.unique same companion
      C.output r.notOutput
    change C.eval x = C.eval z at equal
    rw [equal,correct z hz,sufficient z hz zy]
  obtain ⟨fanD,backD,eqSize,eqEval⟩ := moveOr_sound fan back out
    r.valid (by omega : y<n+r.gate) r.early r.op absorb
  refine ⟨fanD,backD,?_,eqSize.le.trans sz,?_,fun x hx => (eqEval x hx).trans (correct x hx)⟩
  · simp [moveOr,appendOr]
  · intro g hg hn
    simp only [moveOr,appendOr,List.mem_append,List.mem_singleton] at hg
    rcases hg with mem | rfl
    · obtain ⟨old,oldMem,o,l⟩ := bypass_mem g mem
      rw [l]
      exact norm old oldMem (o.symm.trans hn)
    · cases hn


theorem sufficient_or_descendants {n s y : ℕ} {F : List Bool → Bool} (hy : y<n)
    (sufficient : ∀ x, x.length=n → x.getD y false = true → F x = true)
    (shape : ∀ C, Fits n s F C → Nonempty (SoleOr n C y))
    {C : Circuit} (fits : Fits n s F C) :
    ∀ j<C.gates.length, Reach n C y (n+j) → (gateAt C j).op = GateOp.or := by
  classical
  intro j jl reachable
  by_contra bad
  let P (k : ℕ) : Prop := ∃ A : Circuit, Fits n s F A ∧ k<A.gates.length ∧
    (gateAt A k).op ≠ GateOp.or ∧ Reach n A y (n+k)
  have ex : ∃ k, P k := ⟨j,C,fits,jl,bad,reachable⟩
  let k := Nat.find ex
  obtain ⟨A,fA,kA,notOr,path⟩ : P k := Nat.find_spec ex
  obtain ⟨r⟩ := shape A fA
  have back := fA.2.1
  have rk : r.gate < k := by
    rcases reach_after back r.unique path with ty | tk
    · omega
    · by_contra! ng
      have h : r.gate=k := by omega
      rcases r.op with eq | eq
      · exact notOr (by rw [←h,eq])
      · exact notOr (by rw [←h,eq])
  have fD := sufficient_move hy fA r sufficient
  obtain ⟨j',small,jD,badD,pathD⟩ := moved_nonor (d := r.other) hy r.valid back kA rk notOr path
  have found : P j' := ⟨moveOr n A r.gate y r.other,fD,jD,badD,pathD⟩
  exact (Nat.not_lt_of_ge (Nat.find_min' ex found)) small
end

section
open PinBase

def MinEval (n : ℕ) (C : Circuit) : Prop :=
  ∀ D : Circuit, FanInTwo D →
    (∀ x : List Bool, x.length=n → D.eval x=C.eval x) → C.size≤D.size

def GateLive (n : ℕ) (C : Circuit) : Prop :=
  ∀ j<C.gates.length, C.output ≠ n+j →
    ∃ k, j<k ∧ k<C.gates.length ∧ n+j∈(gateAt C k).inputs

theorem gate_eq_parts {g h : Gate} (op : g.op=h.op) (ins : g.inputs=h.inputs) : g=h := by
  cases g
  cases h
  cases op
  cases ins
  rfl

theorem binary_reader {inputs : List ℕ} {p : ℕ}
    (bound : inputs.length≤2) (read : p∈inputs) :
    (inputs=[p] ∨ inputs=[p,p]) ∨
      ∃ d≠p, inputs=[p,d] ∨ inputs=[d,p] := by
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  · simp at read
  · left
    exact Or.inl (by simpa using (List.mem_singleton.mp read).symm)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at read
    rcases read with e|e
    · subst a
      by_cases eq : b=p
      · exact Or.inl (Or.inr (by rw [eq]))
      · exact Or.inr ⟨b,eq,Or.inl rfl⟩
    · subst b
      by_cases eq : a=p
      · exact Or.inl (Or.inr (by rw [eq]))
      · exact Or.inr ⟨a,eq,Or.inr rfl⟩
  · simp at bound

theorem no_copy {n : ℕ} {C : Circuit} (fan : FanInTwo C) (minimum : MinEval n C)
    {j i : ℕ} (jl : j<C.gates.length) (early : i<n+j)
    (op : (gateAt C j).op=.or ∨ (gateAt C j).op=.and)
    (copy : (gateAt C j).inputs=[i] ∨ (gateAt C j).inputs=[i,i]) : False := by
  have fanD : FanInTwo (bypass n C j i) := by
    intro g hg
    obtain ⟨g',h',eq,le⟩ := bypass_mem g hg
    rw [eq,le]
    exact fan g' h'
  have eq (x : List Bool) (hx : x.length=n) : (bypass n C j i).eval x=C.eval x := by
    apply bypass_eval_eq_any hx jl early
    rw [val_gate hx jl]
    rcases op with hor|hand
    · rcases copy with e|e <;> simp [hor,e,GateOp.eval,early]
    · rcases copy with e|e <;> simp [hand,e,GateOp.eval,early]
  have cc := minimum _ fanD eq
  change C.gates.length≤(bypass n C j i).gates.length at cc
  rw [bypass_length] at cc
  omega

theorem constant_output_impossible {n p j : ℕ} {C : Circuit} {b c : Bool}
    (fan : FanInTwo C) (vary : PinVaries n p b C)
    (jl : j<C.gates.length) (atOutput : C.output=n+j)
    (ctrl : outcome n C (pinAcc n p b) j=(none,.const c)) : False := by
  have freeze := frozen_status_later (pinAcc n p b) (by simp [pinAcc,pinStart]) jl jl ctrl
  have state : (elim n C.gates (pinAcc n p b)).1.getD C.output (.const false)=.const c := by
    rw [atOutput]
    simpa [atGate] using freeze
  have equal (x : List Bool) (hx : x.length=n) : C.eval (pinRow n p b x)=c := by
    have inv := inv_elim n x hx C.gates _ _ fan (pin_inv n p b x hx)
    have out := (inv.2 C.output).2
    change ((elim n C.gates (pinAcc n p b)).1.getD C.output (.const false)).val
        (wiresFrom (elim n C.gates (pinAcc n p b)).2 x) = C.eval (pinRow n p b x) at out
    rw [state] at out
    exact out.symm
  obtain ⟨x,z,hx,hz,ne⟩ := vary
  exact ne ((equal x hx).trans (equal z hz).symm)

theorem raw_zero_sole_or {n p floor : ℕ} {C : Circuit} (hp : p<n)
    (fan : FanInTwo C) (back : ReadsBack n C) (norm : ProperNot C)
    (minimum : MinEval n C) (live : GateLive n C) (out : C.output≠p)
    (small : C.size≤floor+1) (cofactor : PinFloor n p false C floor) (varies : PinVaries n p false C)
    (used : ∃ j<C.gates.length, p∈(gateAt C j).inputs) :
    Nonempty (SoleOr n C p) := by
  obtain ⟨j,jl,read⟩ := used
  have budget : (skipped n p false C).card≤1 := by
    have := skipped_budget fan cofactor varies
    omega
  have unique (k : ℕ) (kl : k<C.gates.length) (rd : p∈(gateAt C k).inputs) :
      k=j := sole_raw_reader hp fan norm budget kl jl rd read
  have hor : (gateAt C j).op=.or := by
    rcases (fan _ (gateAt_mem jl)).1 with hand|hor|hnot
    · exfalso
      obtain ⟨c,born⟩ := freezes_if_controlled fan norm (pinAcc n p false) jl read
        (raw_frozen hp false C j) (Or.inl ⟨hand,rfl⟩)
      by_cases output : C.output=n+j
      · exact constant_output_impossible fan varies jl output born
      · obtain ⟨k,jk,kl,readk⟩ := live j jl output
        have hj : j∈skipped n p false C := reader_skips hp fan norm jl read
        have hk : k∈skipped n p false C := frozen_reader_skips fan norm kl jk born readk
        exact (Nat.ne_of_lt jk) (Finset.card_le_one.mp budget j hj k hk)
    · exact hor
    · exfalso
      obtain ⟨c,born⟩ := freezes_if_controlled fan norm (pinAcc n p false) jl read
        (raw_frozen hp false C j) (Or.inr (Or.inr hnot))
      by_cases output : C.output=n+j
      · exact constant_output_impossible fan varies jl output born
      · obtain ⟨k,jk,kl,readk⟩ := live j jl output
        have hj : j∈skipped n p false C := reader_skips hp fan norm jl read
        have hk : k∈skipped n p false C := frozen_reader_skips fan norm kl jk born readk
        exact (Nat.ne_of_lt jk) (Finset.card_le_one.mp budget j hj k hk)
  rcases binary_reader (fan _ (gateAt_mem jl)).2 read with copying|⟨d,ne,shape⟩
  · exact False.elim (no_copy fan minimum jl (back j jl p read) (Or.inl hor) copying)
  · have dmem : d∈(gateAt C j).inputs := by rcases shape with e|e <;> rw [e] <;> simp
    have gate : gateAt C j=⟨.or,[p,d]⟩ ∨ gateAt C j=⟨.or,[d,p]⟩ := by
      rcases shape with e|e
      · left; exact gate_eq_parts hor e
      · right; exact gate_eq_parts hor e
    exact ⟨⟨j,d,jl,back j jl d dmem,ne,gate,unique,out⟩⟩
end

section
open PinBase

structure LeafPair (n : ℕ) (C : Circuit) (p : ℕ) where
  first : SoleOr n C p
  gate : ℕ
  other : ℕ
  valid : gate<C.gates.length
  afterFirst : first.gate<gate
  early : other<n+gate
  different : other≠n+first.gate
  op : gateAt C gate=⟨.and,[n+first.gate,other]⟩ ∨
       gateAt C gate=⟨.and,[other,n+first.gate]⟩
  unique : ∀ j<C.gates.length, n+first.gate∈(gateAt C j).inputs → j=gate

private theorem first_born_true {n p : ℕ} {C : Circuit} (hp : p<n) (r : SoleOr n C p) :
    outcome n C (pinAcc n p true) r.gate=(none,.const true) := by
  let acc := atGate n C (pinAcc n p true) r.gate
  have pp : acc.1.getD p (.const false)=.const true := raw_frozen hp true C _
  rcases r.op with e|e
  · unfold outcome
    rw [e]
    change simplify .or (n+acc.2.length) [acc.1.getD p (.const false),acc.1.getD r.other (.const false)] = _
    rw [pp]
    cases acc.1.getD r.other (.const false) <;> simp [simplify,simpOr]
  · unfold outcome
    rw [e]
    change simplify .or (n+acc.2.length) [acc.1.getD r.other (.const false),acc.1.getD p (.const false)] = _
    rw [pp]
    cases acc.1.getD r.other (.const false) <;> simp [simplify,simpOr]

theorem leaf_pair_of_reader {n p floor : ℕ} {C : Circuit} (hp : p<n)
    (fan : FanInTwo C) (back : ReadsBack n C) (norm : ProperNot C) (min : MinEval n C)
    (live : GateLive n C) (small : C.size≤floor+2)
    (r : SoleOr n C p) (truthFloor : PinFloor n p true C floor)
    (truthVar : PinVaries n p true C)
    (singleReject : ∃ x : List Bool, x.length=n ∧ x.getD p false=true ∧ C.eval x=false) :
    Nonempty (LeafPair n C p) := by
  classical
  have budget : (skipped n p true C).card≤2 := by
    have := skipped_budget fan truthFloor truthVar
    omega
  have gop : (gateAt C r.gate).op=.or := by rcases r.op with e|e <;> rw [e]
  have gmem : p∈(gateAt C r.gate).inputs := by rcases r.op with e|e <;> rw [e] <;> simp
  have gout : C.output≠n+r.gate := by
    intro out
    obtain ⟨x,hx,px,fx⟩ := singleReject
    have trueGate : val C x (n+r.gate)=true :=
      (val_or hx r.valid gop).mpr ⟨p,gmem,by omega,by rw [val_input hx hp,px]⟩
    rw [eval_eq_val,out,trueGate] at fx
    contradiction
  obtain ⟨j,gj,jl,jread⟩ := live r.gate r.valid gout
  have born := first_born_true hp r
  have unique (k : ℕ) (kl : k<C.gates.length) (km : n+r.gate∈(gateAt C k).inputs) :
      k=j := by
    have rk : r.gate<k := by have := back k kl (n+r.gate) km; omega
    exact sole_frozen_reader fan norm budget r.valid rk gj kl jl born km jread
  have jOp : (gateAt C j).op=.and := by
    by_contra na
    have ctl : ((gateAt C j).op=.and ∧ true=false) ∨
        ((gateAt C j).op=.or ∧ true=true) ∨ (gateAt C j).op=.not := by
      rcases (fan _ (gateAt_mem jl)).1 with ha|ho|hn
      · exact False.elim (na ha)
      · exact Or.inr (Or.inl ⟨ho,rfl⟩)
      · exact Or.inr (Or.inr hn)
    have len : (pinAcc n p true).1.length=n := by simp [pinAcc,pinStart]
    obtain ⟨c,second⟩ := freezes_if_controlled fan norm _ jl jread
      (frozen_status_later _ len r.valid gj born) ctl
    by_cases jout : C.output=n+j
    · exact constant_output_impossible fan truthVar jl jout second
    obtain ⟨k,jk,kl,kread⟩ := live j jl jout
    let S : Finset ℕ := {r.gate,j,k}
    have hs : S ⊆ skipped n p true C := by
      intro i hi
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl
      · exact mem_skipped.mpr ⟨r.valid,by rw [born]⟩
      · exact mem_skipped.mpr ⟨jl,by rw [second]⟩
      · exact frozen_reader_skips fan norm kl jk second kread
    have cS : S.card=3 := by
      unfold S
      rw [Finset.card_insert_of_notMem (by simp [show r.gate≠j by omega,show r.gate≠k by omega])]
      simp [show j≠k by omega]
    have count := Finset.card_le_card hs
    omega
  rcases binary_reader (fan _ (gateAt_mem jl)).2 jread with copy|⟨d,diff,ins⟩
  · exact False.elim (no_copy fan min jl (by omega) (Or.inr jOp) copy)
  · have dmem : d∈(gateAt C j).inputs := by rcases ins with e|e <;> rw [e] <;> simp
    have gate : gateAt C j=⟨.and,[n+r.gate,d]⟩ ∨ gateAt C j=⟨.and,[d,n+r.gate]⟩ := by
      rcases ins with e|e
      · exact Or.inl (gate_eq_parts jOp e)
      · exact Or.inr (gate_eq_parts jOp e)
    exact ⟨⟨r,j,d,jl,gj,back j jl d dmem,diff,gate,unique⟩⟩
end

section
def origin (r j : ℕ) : ℕ := if j<r then j else j+1

theorem alias_raw {n p r i u : ℕ} (hp : p<n) :
    aliasWire (n+r) i u=p ↔ u=p ∨ (u=n+r ∧ i=p) := by
  unfold aliasWire
  split_ifs with eq gt
  · simp [eq,show n+r≠p by omega]
  · have ne : u≠p := by omega
    simp [ne,eq,show u-1≠p by omega]
  · simp [eq]

theorem bypass_raw_imp {n p r i j : ℕ} {C : Circuit} (hp : p<n)
    (jl : j<(bypass n C r i).gates.length)
    (read : p∈(gateAt (bypass n C r i) j).inputs) :
    p∈(gateAt C (origin r j)).inputs ∨ (i=p ∧ n+r∈(gateAt C (origin r j)).inputs) := by
  have jj : j<C.gates.length-1 := by rwa [bypass_length] at jl
  rw [gateAt_bypass jj] at read
  unfold origin
  by_cases before : j<r
  · rw [if_pos before] at read ⊢
    exact Or.inl read
  · rw [if_neg before] at read ⊢
    obtain ⟨u,mem,eq⟩ := List.mem_map.mp read
    rcases (alias_raw hp).mp eq with e|⟨e,pin⟩
    · exact Or.inl (e ▸ mem)
    · exact Or.inr ⟨pin,e ▸ mem⟩

theorem out_unchanged_when_raw_unread {n p : ℕ} {C : Circuit} (back : ReadsBack n C)
    (out : C.output≠p) (unread : ∀ j<C.gates.length, p∉(gateAt C j).inputs)
    {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    (same : ∀ i<n, i≠p → x.getD i false=z.getD i false) :
    C.eval x=C.eval z := by
  suffices ∀ w, w≠p → val C x w=val C z w from this C.output out
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro ne
    by_cases raw : w<n
    · rw [val_input hx raw,val_input hz raw,same w raw ne]
    by_cases wide : n+C.gates.length≤w
    · rw [val_ge hx wide,val_ge hz wide]
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have kl : k<C.gates.length := by omega
    rw [val_gate hx kl,val_gate hz kl]
    congr 1
    apply List.map_congr_left
    intro u um
    have ul := back k kl u um
    rw [if_pos ul,if_pos ul]
    exact ih u ul (fun e => unread k kl (e ▸ um))

end

section
theorem bypass_fan_not {n r i : ℕ} {C : Circuit} (fan : FanInTwo C) (norm : ProperNot C) :
    FanInTwo (bypass n C r i) ∧ ProperNot (bypass n C r i) := by
  constructor
  · intro g hg
    obtain ⟨g',mem,op,len⟩ := bypass_mem g hg
    rw [op,len]
    exact fan g' mem
  · intro g hg h
    obtain ⟨g',mem,op,len⟩ := bypass_mem g hg
    rw [len]
    exact norm g' mem (op.symm.trans h)

theorem origin_ne (r j : ℕ) : origin r j≠r := by
  unfold origin
  split <;> omega

def cutLeaf {n : ℕ} {C : Circuit} {p : ℕ} (L : LeafPair n C p) : Circuit :=
  bypass n (bypass n C L.first.gate p) (L.gate-1) (aliasWire (n+L.first.gate) p L.other)

theorem cut_leaf_true {n p : ℕ} {C : Circuit} (hp : p<n)
    (fan : FanInTwo C) (back : ReadsBack n C) (norm : ProperNot C)
    (L : LeafPair n C p) (outFirst : C.output≠n+L.first.gate) :
    FanInTwo (cutLeaf L) ∧ ReadsBack n (cutLeaf L) ∧ ProperNot (cutLeaf L) ∧
      (cutLeaf L).size+2=C.size ∧
      (∀ x : List Bool, x.length=n → (cutLeaf L).eval x=C.eval (pinRow n p true x)) := by
  let r := L.first.gate
  let h := L.gate
  let b := L.other
  let D := bypass n C r p
  let h' := h-1
  let b' := aliasWire (n+r) p b
  let E := bypass n D h' b'
  have rh : r<h := L.afterFirst
  have hl : h<C.gates.length := L.valid
  have rl : r<C.gates.length := L.first.valid
  have hb : b<n+h := L.early
  have pr : p<n+r := by omega
  have dl : D.gates.length=C.gates.length-1 := bypass_length _ _ _ _
  have hl' : h'<D.gates.length := by dsimp [h']; omega
  have eb : b'<n+h' := by
    unfold b' h'
    exact aliasWire_lt pr (by omega) (by omega)
  have rb : b≠n+r := L.different
  have bm : b∈(gateAt C h).inputs := by rcases L.op with e|e <;> rw [e] <;> simp [b]
  have bp : b≠p := by
    intro eq
    have e := L.first.unique h hl (eq ▸ bm)
    omega
  have bp' : b'≠p := by simp [b',alias_raw hp,bp,rb]
  have shape : gateAt D h'=⟨.and,[p,b']⟩ ∨ gateAt D h'=⟨.and,[b',p]⟩ := by
    unfold D h'
    rw [gateAt_bypass (by omega),if_neg (by omega),show h-1+1=h by omega]
    rcases L.op with e|e
    · left
      rw [e]
      simp [aliasGate,aliasWire_self,b',r,b]
    · right
      rw [e]
      simp [aliasGate,aliasWire_self,b',r,b]
  have soleD (j : ℕ) (jl : j<D.gates.length) (rd : p∈(gateAt D j).inputs) : j=h' := by
    have os : origin r j<C.gates.length := by unfold origin; split <;> omega
    rcases bypass_raw_imp hp jl rd with old|⟨_,old⟩
    · exact False.elim (origin_ne r j (L.first.unique _ os old))
    · have ht : origin r j=h := L.unique _ os old
      unfold origin at ht
      unfold h'
      split at ht <;> omega
  have outD : D.output≠p := by
    rw [bypass_output]
    simp [alias_raw hp,L.first.notOutput,outFirst,r]
  have outE : E.output≠p := by
    rw [bypass_output]
    simp [alias_raw hp,outD,bp']
  have unread (j : ℕ) (jl : j<E.gates.length) : p∉(gateAt E j).inputs := by
    intro rd
    have el : E.gates.length=D.gates.length-1 := bypass_length _ _ _ _
    have os : origin h' j<D.gates.length := by unfold origin; split <;> omega
    rcases bypass_raw_imp hp jl rd with old|⟨e,_⟩
    · exact origin_ne _ _ (soleD _ os old)
    · exact bp' e
  obtain ⟨fanD,normD⟩ := bypass_fan_not (n := n) (r := r) (i := p) fan norm
  obtain ⟨fanE,normE⟩ := bypass_fan_not (n := n) (r := h') (i := b') fanD normD
  have backD : ReadsBack n D := bypass_readsBack pr back
  have backE : ReadsBack n E := bypass_readsBack eb backD
  refine ⟨fanE,backE,normE,?_,?_⟩
  · change E.gates.length+2=C.gates.length
    have eh : E.gates.length=D.gates.length-1 := bypass_length _ _ _ _
    omega
  · intro x hx
    let z := pinRow n p true x
    have hz : z.length=n := by simp [z,pinRow]
    have zp : z.getD p false=true := by simp [z,pinRow,List.getD_eq_getElem?_getD,hp]
    have same : ∀ i<n, i≠p → x.getD i false=z.getD i false := by
      intro i hi ip
      simp [z,pinRow,List.getD_eq_getElem?_getD,hi,ip]
    have gop : (gateAt C r).op=.or := by rcases L.first.op with e|e <;> rw [e]
    have gmem : p∈(gateAt C r).inputs := by rcases L.first.op with e|e <;> rw [e] <;> simp
    have rawTrue : val C z p=true := by rw [val_input hz hp,zp]
    have t : val C z (n+r)=val C z p := by
      rw [rawTrue]
      exact (val_or hz rl gop).mpr ⟨p,gmem,pr,rawTrue⟩
    have one : D.eval z=C.eval z := bypass_eval_eq_any hz rl pr t
    have rawD : val D z p=true := by rw [val_input hz hp,zp]
    have core : val D z (n+h')=val D z b' := by
      rw [val_gate hz hl']
      have early : p<n+h' := by omega
      rcases shape with eq|eq <;> rw [eq] <;> simp [GateOp.eval,eb,early,rawD]
    have two : E.eval z=D.eval z := bypass_eval_eq_any hz hl' eb core
    exact (out_unchanged_when_raw_unread backE outE unread hx hz same).trans (two.trans one)
end

section
def shift (r j : ℕ) : ℕ := if j<r then j else j-1

theorem origin_shift {r j : ℕ} (ne : j≠r) : origin r (shift r j)=j := by
  unfold origin shift
  split_ifs <;> omega

theorem shift_inj {r i j : ℕ} (hi : i≠r) (hj : j≠r) (eq : shift r i=shift r j) : i=j := by
  calc
    i = origin r (shift r i) := (origin_shift hi).symm
    _ = origin r (shift r j) := congrArg _ eq
    _ = j := origin_shift hj

theorem gate_after_bypass {n r i j : ℕ} {C : Circuit} (back : ReadsBack n C)
    (rl : r<C.gates.length) (jl : j<C.gates.length) (ne : j≠r) :
    shift r j<(bypass n C r i).gates.length ∧
      gateAt (bypass n C r i) (shift r j)=aliasGate (n+r) i (gateAt C j) := by
  have sh : shift r j<C.gates.length-1 := by unfold shift; split <;> omega
  refine ⟨by rwa [bypass_length],?_⟩
  rw [gateAt_bypass sh]
  by_cases before : j<r
  · rw [show shift r j=j by simp [shift,before],if_pos before]
    apply gate_eq_parts (g := gateAt C j) (h := aliasGate (n+r) i (gateAt C j)) rfl
    change (gateAt C j).inputs = (gateAt C j).inputs.map (aliasWire (n+r) i)
    calc
      _ = (gateAt C j).inputs.map id := (List.map_id _).symm
      _ = _ := by
        apply List.map_congr_left
        intro u um
        exact (aliasWire_lt_self (w := n+r) (i := i) (u := u) (by have := back j jl u um; omega)).symm
  · rw [show shift r j=j-1 by simp [shift,before],if_neg (by omega),show j-1+1=j by omega]

def cutShift {n : ℕ} {C : Circuit} {p : ℕ} (L : LeafPair n C p) (j : ℕ) :=
  shift (L.gate-1) (shift L.first.gate j)

def cutWire {n : ℕ} {C : Circuit} {p : ℕ} (L : LeafPair n C p) (w : ℕ) :=
  aliasWire (n+(L.gate-1)) (aliasWire (n+L.first.gate) p L.other)
    (aliasWire (n+L.first.gate) p w)
end


section
theorem cut_shift_inj {n : ℕ} {C : Circuit} {p i j : ℕ} (L : LeafPair n C p)
    (ir : i≠L.first.gate) (jr : j≠L.first.gate) (ih : i≠L.gate) (jh : j≠L.gate)
    (eq : cutShift L i=cutShift L j) : i=j := by
  have after := L.afterFirst
  have step : shift L.first.gate L.gate = L.gate-1 := by unfold shift; rw [if_neg (by omega)]
  have ni : shift L.first.gate i≠L.gate-1 :=
    fun e => ih (shift_inj ir (by omega) (e.trans step.symm))
  have nj : shift L.first.gate j≠L.gate-1 :=
    fun e => jh (shift_inj jr (by omega) (e.trans step.symm))
  exact shift_inj ir jr (shift_inj ni nj eq)

theorem cut_gate_shape {n : ℕ} {C : Circuit} {p j : ℕ} (L : LeafPair n C p)
    (back : ReadsBack n C) (hp : p<n) (jl : j<C.gates.length)
    (r : j≠L.first.gate) (h : j≠L.gate) :
    cutShift L j<(cutLeaf L).gates.length ∧
      gateAt (cutLeaf L) (cutShift L j) =
        ⟨(gateAt C j).op, (gateAt C j).inputs.map (cutWire L)⟩ := by
  have first := gate_after_bypass (i := p) back L.first.valid jl r
  have position := L.afterFirst
  have tail := L.valid
  have hD : L.gate-1<(bypass n C L.first.gate p).gates.length := by rw [bypass_length]; omega
  have hne : shift L.first.gate j≠L.gate-1 := by
    intro eq
    have e : shift L.first.gate L.gate = L.gate-1 := by unfold shift; rw [if_neg (by omega)]
    exact h (shift_inj r (by omega) (eq.trans e.symm))
  have backD := bypass_readsBack (by omega : p<n+L.first.gate) back
  have second := gate_after_bypass (i := aliasWire (n+L.first.gate) p L.other)
    backD hD first.1 hne
  refine ⟨second.1,?_⟩
  have eq := second.2
  change gateAt (cutLeaf L) (cutShift L j)=_ at eq
  rw [eq,first.2]
  simp [aliasGate,List.map_map,cutWire,Function.comp_def]

theorem cut_raw_id {n : ℕ} {C : Circuit} {p y : ℕ} (L : LeafPair n C p) (hy : y<n) :
    cutWire L y=y := by
  unfold cutWire
  rw [aliasWire_lt_self (by omega : y<n+L.first.gate),
      aliasWire_lt_self (by omega : y<n+(L.gate-1))]

theorem cut_owned_alias {n : ℕ} {C : Circuit} {p y : ℕ} (L : LeafPair n C p)
    (hy : y<n) (same : L.other=y) : cutWire L (n+L.gate)=y := by
  unfold cutWire
  have after := L.afterFirst
  rw [aliasWire_gt_self (by omega : n+L.first.gate<n+L.gate),
    show n+L.gate-1=n+(L.gate-1) by omega,aliasWire_self,same,
    aliasWire_lt_self (by omega : y<n+L.first.gate)]
end

section
private theorem member_image {n p j v : ℕ} {C : Circuit} (L : LeafPair n C p)
    (hp : p<n) (back : ReadsBack n C) (jl : j<C.gates.length)
    (gr : j≠L.first.gate) (hr : j≠L.gate) (reads : v∈(gateAt C j).inputs) :
    cutShift L j<(cutLeaf L).gates.length ∧
      cutWire L v∈(gateAt (cutLeaf L) (cutShift L j)).inputs := by
  have keep := cut_gate_shape L back hp jl gr hr
  refine ⟨keep.1,?_⟩
  rw [keep.2]
  exact List.mem_map.mpr ⟨v,reads,rfl⟩

private theorem map_two_equal {xs : List ℕ} {a b : ℕ} (sz : xs.length≤2)
    (am : a∈xs) (bm : b∈xs) (neq : b≠a) {f : ℕ→ℕ} (equal : f b=f a) :
    xs.map f=[f a,f a] := by
  rcases binary_reader sz am with copies|⟨d,diff,shape⟩
  · rcases copies with e|e <;> simp [e,neq] at bm
  · rcases shape with e|e
    · have bd : b=d := by simpa [e,neq] using bm
      simp [e,←bd,equal]
    · have bd : b=d := by simpa [e,neq] using bm
      simp [e,←bd,equal]

theorem center_cut_case {n p y : ℕ} {C : Circuit} (hp : p<n) (hy : y<n)
    (fan : FanInTwo C) (back : ReadsBack n C) (minimum : MinEval n C)
    (live : GateLive n C) (L : LeafPair n C p)
    (notFirst : y∉(gateAt C L.first.gate).inputs) (notOut : C.output≠y)
    (use : ∃ j<C.gates.length, y∈(gateAt C j).inputs)
    (cof : SoleOr n (cutLeaf L) y) :
    (L.other=y ∧ ∀ j<C.gates.length, y∈(gateAt C j).inputs → j=L.gate) ∨
      ∃ s : SoleOr n C y, s.gate≠L.first.gate ∧ s.gate≠L.gate := by
  have shift_other (j : ℕ) (jl : j<C.gates.length) (rj : j≠L.first.gate) (hj : j≠L.gate)
      (read : y∈(gateAt C j).inputs) : cutShift L j=cof.gate := by
    have im := member_image L hp back jl rj hj read
    exact cof.unique _ im.1 (by simpa only [cut_raw_id L hy] using im.2)
  by_cases match_ : L.other=y
  · refine Or.inl ⟨match_,?_⟩
    have uout : C.output≠n+L.gate := by
      intro e
      apply cof.notOutput
      change cutWire L C.output=y
      rw [e,cut_owned_alias L hy match_]
    obtain ⟨k,hk,kl,kr⟩ := live L.gate L.valid uout
    have rg : k≠L.first.gate := by have := L.afterFirst; omega
    have kg : k≠L.gate := by omega
    have im := member_image L hp back kl rg kg kr
    have ek : cutShift L k=cof.gate :=
      cof.unique _ im.1 (by simpa only [cut_owned_alias L hy match_] using im.2)
    intro j jl yr
    by_contra hj
    have rj : j≠L.first.gate := fun e => notFirst (e ▸ yr)
    have ej := shift_other j jl rj hj yr
    have e : j=k := cut_shift_inj L rj rg hj kg (ej.trans ek.symm)
    subst j
    have keep := cut_gate_shape L back hp kl rg kg
    have duplicate : (gateAt (cutLeaf L) cof.gate).inputs=[y,y] := by
      rw [←ek,keep.2]
      change ((gateAt C k).inputs.map (cutWire L)) = [y,y]
      have member : gateAt C k ∈ C.gates := Bypass.gateAt_mem kl
      have map := map_two_equal (fan _ member).2 yr kr (by omega)
        ((cut_owned_alias L hy match_).trans (cut_raw_id L hy).symm)
      simpa only [cut_raw_id L hy] using map
    rcases cof.op with e|e <;> rw [e] at duplicate <;> simpa [cof.different] using duplicate

  · have hv : y∉(gateAt C L.gate).inputs := by
      have raw : y≠n+L.first.gate := by omega
      rcases L.op with e|e <;> rw [e] <;> simp [raw,Ne.symm match_]
    obtain ⟨j,jl,yr⟩ := use
    have rg : j≠L.first.gate := fun e => notFirst (e ▸ yr)
    have hg : j≠L.gate := fun e => hv (e ▸ yr)
    have keep := cut_gate_shape L back hp jl rg hg
    have ec := shift_other j jl rg hg yr
    have oldOr : (gateAt C j).op=.or := by
      have op := congrArg Gate.op keep.2
      change (gateAt (cutLeaf L) (cutShift L j)).op=(gateAt C j).op at op
      rw [ec] at op
      rcases cof.op with e|e <;> rw [e] at op <;> exact op.symm
    have unique (k : ℕ) (kl : k<C.gates.length) (usek : y∈(gateAt C k).inputs) : k=j := by
      have a : k≠L.first.gate := fun e => notFirst (e ▸ usek)
      have b : k≠L.gate := fun e => hv (e ▸ usek)
      exact cut_shift_inj L a rg b hg ((shift_other k kl a b usek).trans ec.symm)
    have memb := Bypass.gateAt_mem jl
    rcases binary_reader (fan _ memb).2 yr with e|⟨d,ne,shape⟩
    · exact False.elim (no_copy fan minimum jl (back j jl y yr) (Or.inl oldOr) e)
    · have dm : d∈(gateAt C j).inputs := by rcases shape with e|e <;> rw [e] <;> simp
      have ors : gateAt C j=⟨.or,[y,d]⟩ ∨ gateAt C j=⟨.or,[d,y]⟩ := by
        rcases shape with e|e
        · exact Or.inl (gate_eq_parts oldOr e)
        · exact Or.inr (gate_eq_parts oldOr e)
      exact Or.inr ⟨⟨j,d,jl,back j jl d dm,ne,ors,unique,notOut⟩,rg,hg⟩
end

section
theorem cut_wire_late {n p j : ℕ} {C : Circuit} (L : LeafPair n C p) (late : L.gate<j) :
    cutWire L (n+j)=n+cutShift L j := by
  have rh := L.afterFirst
  have s1 : shift L.first.gate j = j-1 := by unfold shift; rw [if_neg (by omega)]
  have s2 : shift (L.gate-1) (j-1)=j-2 := by unfold shift; rw [if_neg (by omega)]; omega
  unfold cutWire cutShift
  rw [s1,s2,aliasWire_gt_self (by omega : n+L.first.gate<n+j)]
  rw [aliasWire_gt_self (by omega : n+(L.gate-1)<n+j-1)]
  omega

theorem cut_reach_late {n p y w : ℕ} {C : Circuit} (L : LeafPair n C p)
    (hp : p<n) (hy : y<n) (back : ReadsBack n C) (r : SoleOr n C y) (late : L.gate<r.gate)
    (reach : Reach n C y w) : Reach n (cutLeaf L) y (cutWire L w) := by
  induction reach with
  | start => rw [cut_raw_id L hy]; exact Reach.start
  | @step i j jl read prev ih =>
    have here := Reach.step jl read prev
    have jlate : L.gate<j := by
      rcases reach_after back r.unique here with e|e <;> omega
    have older := L.afterFirst
    have im := cut_gate_shape L back hp jl (by omega) (by omega)
    rw [cut_wire_late L jlate]
    exact Reach.step im.1 (by rw [im.2]; exact List.mem_map.mpr ⟨i,read,rfl⟩) ih

theorem no_late_center {n p y : ℕ} {C : Circuit} (hp : p<n) (hy : y<n)
    (back : ReadsBack n C) (L : LeafPair n C p) (r : SoleOr n C y) (late : L.gate<r.gate)
    (cofOr : ∀ j<(cutLeaf L).gates.length,
      Reach n (cutLeaf L) y (n+j) → (gateAt (cutLeaf L) j).op=.or)
    (essential : Reach n C y C.output)
    {x : List Bool} (hx : x.length=n) (yx : x.getD y false=true) (reject : C.eval x=false) : False := by
  have ops (j : ℕ) (jl : j<C.gates.length) (reachable : Reach n C y (n+j)) :
      (gateAt C j).op=.or := by
    have jlate : L.gate<j := by
      rcases reach_after back r.unique reachable with e|e <;> omega
    have older := L.afterFirst
    have im := cut_gate_shape L back hp jl (by omega) (by omega)
    have got := cut_reach_late L hp hy back r late reachable
    rw [cut_wire_late L jlate] at got
    have yes := cofOr _ im.1 got
    simpa [im.2] using yes
  have accept := reachable_true hy hx yx back ops essential
  change C.eval x=true at accept
  rw [reject] at accept
  contradiction

theorem difference_implies_reach {n y : ℕ} {C : Circuit} (back : ReadsBack n C)
    {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    (same : ∀ i<n, i≠y → x.getD i false=z.getD i false)
    (diff : C.eval x≠C.eval z) : Reach n C y C.output := by
  classical
  by_contra no
  apply diff
  suffices ∀ w, ¬Reach n C y w → val C x w=val C z w from this C.output no
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro nw
    by_cases raw : w<n
    · have d : w≠y := fun e => nw (e ▸ Reach.start)
      rw [val_input hx raw,val_input hz raw,same w raw d]
    by_cases gone : n+C.gates.length≤w
    · rw [val_ge hx gone,val_ge hz gone]
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have jl : j<C.gates.length := by omega
    rw [val_gate hx jl,val_gate hz jl]
    congr 1
    apply List.map_congr_left
    intro i mi
    have early := back j jl i mi
    rw [if_pos early,if_pos early]
    exact ih i early (fun hi => nw (Reach.step jl mi hi))
end

section
theorem cut_leaf_valid {n p : ℕ} {C : Circuit} (L : LeafPair n C p)
    (hp : p<n) (out : C.output<n+C.gates.length) :
    (cutLeaf L).output<n+(cutLeaf L).gates.length := by
  let r := L.first.gate
  let j := L.gate
  let D := bypass n C r p
  let e := aliasWire (n+r) p L.other
  have rj : r<j := L.afterFirst
  have jl : j<C.gates.length := L.valid
  have el : L.other<n+j := L.early
  have dLen : D.gates.length=C.gates.length-1 := bypass_length _ _ _ _
  have dOut : D.output<n+D.gates.length := by
    change aliasWire (n+r) p C.output < n+D.gates.length
    rw [dLen]
    exact aliasWire_lt (by omega) (by omega) (by omega)
  have ep : e<n+(j-1) := by
    unfold e
    exact aliasWire_lt (by omega) (by omega) (by omega)
  change (bypass n D (j-1) e).output<n+(bypass n D (j-1) e).gates.length
  rw [bypass_output,bypass_length]
  exact aliasWire_lt ep (by omega) (by omega)
end

namespace AnchorMove


def shifted (r j : ℕ) : ℕ := if j<r then j else j-1

theorem shifted_le (r j : ℕ) : shifted r j≤j := by
  unfold shifted
  split <;> omega

theorem shifted_lt_of_after {r j : ℕ} (after : r<j) : shifted r j<j := by
  unfold shifted
  split <;> omega

theorem shifted_order {r a b : ℕ} (aSaved : a≠r) (bSaved : b≠r) (h : a<b) :
    shifted r a<shifted r b := by
  unfold shifted
  split_ifs <;> omega

theorem shifted_bound {r j len : ℕ} (hr : r<len) (hj : j<len) (saved : j≠r) :
    shifted r j<len-1 := by
  unfold shifted
  split <;> omega

theorem wire_shifted (n r y j : ℕ) (saved : j≠r) :
    aliasWire (n+r) y (n+j) = n+shifted r j := by
  by_cases early : j<r
  · rw [aliasWire_lt_self (by omega), shifted, ite_eq_left early]
  · rw [aliasWire_gt_self (by omega), shifted, ite_eq_right early]
    omega

theorem alias_eq {cut replacement wire kept : ℕ} (saved : kept≠cut)
    (notReplacement : replacement≠aliasWire cut replacement kept) :
    aliasWire cut replacement wire = aliasWire cut replacement kept ↔ wire=kept := by
  constructor
  · intro equal
    have wireSaved : wire≠cut := by
      intro e
      rw [e,aliasWire_self] at equal
      exact notReplacement equal
    unfold aliasWire at equal
    rw [ite_eq_right wireSaved,ite_eq_right saved] at equal
    split_ifs at equal <;> omega
  · rintro rfl
    rfl

theorem moveOr_length {n r y d : ℕ} {C : Circuit} (hr : r<C.gates.length) :
    (moveOr n C r y d).gates.length=C.gates.length := by
  simp only [moveOr,appendOr,List.length_append,List.length_singleton,bypass_length]
  omega

theorem moveOr_output (n : ℕ) (C : Circuit) (r y d : ℕ) :
    (moveOr n C r y d).output = n+(C.gates.length-1) := by
  change n+(bypass n C r y).gates.length = _
  rw [bypass_length]

theorem moveOr_valid {n r y d : ℕ} {C : Circuit} (hr : r<C.gates.length) :
    (moveOr n C r y d).output < n+(moveOr n C r y d).gates.length := by
  rw [moveOr_length hr, moveOr_output]
  omega

theorem moveOr_proper (n : ℕ) (C : Circuit) (r y d : ℕ) (ok : ProperNot C) :
    ProperNot (moveOr n C r y d) := by
  intro g hg op
  simp only [moveOr,appendOr,List.mem_append,List.mem_singleton] at hg
  rcases hg with old | rfl
  · obtain ⟨g',mem,eq,len⟩ := bypass_mem g old
    rw [len]
    exact ok _ mem (eq.symm.trans op)
  · cases op

theorem moveAt_bypass {n r y d k : ℕ} {C : Circuit} (hk : k<C.gates.length-1) :
    gateAt (moveOr n C r y d) k = gateAt (bypass n C r y) k := by
  let D := bypass n C r y
  have valid : k<D.gates.length := by rwa [bypass_length]
  exact List.getD_append D.gates [⟨GateOp.or,[d,D.output]⟩] ⟨GateOp.or,[]⟩ k valid

theorem moveAt_tail (n : ℕ) (C : Circuit) (r y d : ℕ) :
    gateAt (moveOr n C r y d) (C.gates.length-1) =
      ⟨.or,[d,aliasWire (n+r) y C.output]⟩ := by
  have len := bypass_length n C r y
  rw [← len]
  simp [gateAt,moveOr,appendOr,bypass_output]

theorem moveAt_shifted {n r y d j : ℕ} {C : Circuit}
    (back : ReadsBack n C) (hr : r<C.gates.length) (hj : j<C.gates.length) (save : j≠r) :
    gateAt (moveOr n C r y d) (shifted r j) = aliasGate (n+r) y (gateAt C j) := by
  have valid := shifted_bound hr hj save
  rw [moveAt_bypass valid,gateAt_bypass valid]
  by_cases early : j<r
  · rw [shifted,ite_eq_left early,ite_eq_left early]
    have mapEq : (gateAt C j).inputs.map (aliasWire (n+r) y) = (gateAt C j).inputs := by
      calc
        _ = (gateAt C j).inputs.map id := by
          apply List.map_congr_left
          intro u hu
          exact aliasWire_lt_self ((back j hj u hu).trans (by omega))
        _ = _ := List.map_id _
    cases g : gateAt C j with
    | mk op ins =>
      change (⟨op,ins⟩ : Gate) = ⟨op,ins.map (aliasWire (n+r) y)⟩
      rw [g] at mapEq
      exact congrArg (fun xs => (⟨op,xs⟩ : Gate)) mapEq.symm
  · have after : r<j := by omega
    have e : shifted r j=j-1 := ite_eq_right early
    rw [e,ite_eq_right (by omega : ¬j-1<r)]
    have eq : j-1+1=j := by omega
    rw [eq]

theorem move_reader {n r y d j u : ℕ} {C : Circuit}
    (back : ReadsBack n C) (hr : r<C.gates.length)
    (hd : d<n+r) (hGate : gateAt C r = ⟨.or,[y,d]⟩ ∨ gateAt C r = ⟨.or,[d,y]⟩)
    (saved : u≠n+r) (replace : y≠aliasWire (n+r) y u) (jSaved : j≠r)
    (out : C.output≠u)
    (unique : ∀ k<C.gates.length, u∈(gateAt C k).inputs → k=j) :
    ∀ k<(moveOr n C r y d).gates.length,
      aliasWire (n+r) y u∈(gateAt (moveOr n C r y d) k).inputs → k=shifted r j := by
  intro k hk mem
  rw [moveOr_length hr] at hk
  by_cases old : k<C.gates.length-1
  · let a := if k<r then k else k+1
    have aValid : a<C.gates.length := by dsimp [a]; split <;> omega
    have aSaved : a≠r := by dsimp [a]; split <;> omega
    have index : shifted r a=k := by
      by_cases h : k<r
      · simp [a,shifted,h]
      · have h₂ : ¬k+1<r := by omega
        simp [a,shifted,h,h₂]
    rw [← index,moveAt_shifted back hr aValid aSaved] at mem
    change aliasWire (n+r) y u ∈ (gateAt C a).inputs.map (aliasWire (n+r) y) at mem
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
    have ws : w=u := (alias_eq saved replace).mp eq
    have aj : a=j := unique _ aValid (ws ▸ hw)
    rw [← index,aj]
  · have tail : k=C.gates.length-1 := by omega
    rw [tail,moveAt_tail] at mem
    change aliasWire (n+r) y u ∈ [d,aliasWire (n+r) y C.output] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with hit | hit
    · have ed : aliasWire (n+r) y d = aliasWire (n+r) y u := by
        rw [aliasWire_lt_self hd,hit]
      have du : d=u := (alias_eq saved replace).mp ed
      have hread : d∈(gateAt C r).inputs := by
        rcases hGate with e | e <;> simp [e]
      exact (jSaved (unique _ hr (du ▸ hread)).symm).elim
    · exact (out ((alias_eq saved replace).mp hit.symm)).elim

theorem move_leaf {n r y d p : ℕ} {C : Circuit}
    (oldBack : ReadsBack n C) (newBack : ReadsBack n (moveOr n C r y d))
    (hr : r<C.gates.length) (hy : y<n) (hp : p<n) (neq : y≠p) (hd : d<n+r)
    (hGate : gateAt C r = ⟨.or,[y,d]⟩ ∨ gateAt C r = ⟨.or,[d,y]⟩)
    (A : LeafPair n C p) (savedFirst : A.first.gate≠r) (savedAnd : A.gate≠r)
    (notOutputFirst : C.output≠n+A.first.gate) :
    ∃ B : LeafPair n (moveOr n C r y d) p,
      B.gate=shifted r A.gate ∧ B.first.gate=shifted r A.first.gate := by
  let D := moveOr n C r y d
  let s := shifted r A.first.gate
  let t := shifted r A.gate
  let w := aliasWire (n+r) y
  have raw : aliasWire (n+r) y p=p := aliasWire_lt_self (by omega)
  have firstWire : aliasWire (n+r) y (n+A.first.gate)=n+s := wire_shifted _ _ _ _ savedFirst
  have sv : s<D.gates.length := by rw [moveOr_length hr]; have h := shifted_bound hr A.first.valid savedFirst; omega
  have tv : t<D.gates.length := by rw [moveOr_length hr]; have h := shifted_bound hr A.valid savedAnd; omega
  have savedRaw : p≠n+r := by omega
  have aliasRaw : y≠aliasWire (n+r) y p := by rwa [raw]
  have aliasFirst : y≠aliasWire (n+r) y (n+A.first.gate) := by rw [firstWire]; omega
  have savedWire : n+A.first.gate≠n+r := by omega
  have firstOp : gateAt D s = ⟨.or,[p,w A.first.other]⟩ ∨
      gateAt D s = ⟨.or,[w A.first.other,p]⟩ := by
    rw [moveAt_shifted oldBack hr A.first.valid savedFirst]
    rcases A.first.op with e | e
    · exact Or.inl (by simp [e,aliasGate,raw,w])
    · exact Or.inr (by simp [e,aliasGate,raw,w])
  have secondOp : gateAt D t = ⟨.and,[n+s,w A.other]⟩ ∨
      gateAt D t = ⟨.and,[w A.other,n+s]⟩ := by
    rw [moveAt_shifted oldBack hr A.valid savedAnd]
    rcases A.op with e | e
    · exact Or.inl (by simp [e,aliasGate,firstWire,w])
    · exact Or.inr (by simp [e,aliasGate,firstWire,w])
  have firstMember : w A.first.other ∈ (gateAt D s).inputs := by
    rcases firstOp with e | e <;> rw [e] <;> simp
  have secondMember : w A.other ∈ (gateAt D t).inputs := by
    rcases secondOp with e | e <;> rw [e] <;> simp
  let newFirst : SoleOr n D p :=
    { gate := s
      other := w A.first.other
      valid := sv
      early := newBack _ sv _ firstMember
      different := fun e => A.first.different ((alias_eq savedRaw aliasRaw).mp (e.trans raw.symm))
      op := firstOp
      unique := by
        simpa only [raw] using move_reader oldBack hr hd hGate savedRaw aliasRaw savedFirst
          A.first.notOutput A.first.unique
      notOutput := by rw [moveOr_output]; omega }
  refine ⟨{
    first := newFirst
    gate := t
    other := w A.other
    valid := tv
    afterFirst := shifted_order savedFirst savedAnd A.afterFirst
    early := newBack _ tv _ secondMember
    different := fun e => A.different ((alias_eq savedWire aliasFirst).mp (e.trans firstWire.symm))
    op := secondOp
    unique := by
      simpa only [firstWire] using move_reader oldBack hr hd hGate savedWire aliasFirst savedAnd
        notOutputFirst A.unique
  },rfl,rfl⟩

end AnchorMove

namespace AnchorMove


structure Representative (n budget : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop where
  fan : FanInTwo C
  back : ReadsBack n C
  proper : ProperNot C
  small : C.size≤budget
  validOutput : C.output<n+C.gates.length
  computes : ∀ x : Fin n → Bool, C.eval (List.ofFn x)=F x

def LeastAnchorSum {n budget p q : ℕ} {F : (Fin n → Bool) → Bool}
    {C : Circuit} (A : LeafPair n C p) (B : LeafPair n C q) : Prop :=
  ∀ (D : Circuit) (A' : LeafPair n D p) (B' : LeafPair n D q),
    Representative n budget F D → A.gate+B.gate≤A'.gate+B'.gate

theorem exists_least_anchors {n budget p q : ℕ} {F : (Fin n → Bool) → Bool}
    (has : ∃ (C : Circuit), Nonempty (LeafPair n C p) ∧ Nonempty (LeafPair n C q) ∧
      Representative n budget F C) :
    ∃ (C : Circuit) (A : LeafPair n C p) (B : LeafPair n C q),
      Representative n budget F C ∧ LeastAnchorSum (budget := budget) (F := F) A B := by
  classical
  let hasSum (k : ℕ) : Prop := ∃ (C : Circuit) (A : LeafPair n C p) (B : LeafPair n C q),
      Representative n budget F C ∧ k=A.gate+B.gate
  have someSum : ∃ k, hasSum k := by
    obtain ⟨C,⟨A⟩,⟨B⟩,h⟩ := has
    exact ⟨_,C,A,B,h,rfl⟩
  obtain ⟨C,A,B,good,eq⟩ := Nat.find_spec someSum
  refine ⟨C,A,B,good,?_⟩
  intro D A' B' h
  rw [←eq]
  exact Nat.find_min' someSum ⟨D,A',B',h,rfl⟩

theorem and_ne_or {n p y : ℕ} {C : Circuit} (A : LeafPair n C p) (R : SoleOr n C y) :
    A.gate≠R.gate := by
  intro eq
  have a : (gateAt C A.gate).op=.and := by
    rcases A.op with h | h <;> rw [h]
  have b : (gateAt C R.gate).op=.or := by
    rcases R.op with h | h <;> rw [h]
  rw [eq,b] at a
  cases a

theorem least_forbids_move {n budget p q y : ℕ} {F : (Fin n → Bool) → Bool}
    {C : Circuit} (good : Representative n budget F C)
    (A : LeafPair n C p) (B : LeafPair n C q)
    (least : LeastAnchorSum (budget := budget) (F := F) A B) (R : SoleOr n C y)
    (hy : y<n) (hp : p<n) (hq : q<n) (yp : y≠p) (yq : y≠q)
    (saveA : A.first.gate≠R.gate) (saveB : B.first.gate≠R.gate)
    (outA : C.output≠n+A.first.gate) (outB : C.output≠n+B.first.gate)
    (early : R.gate<A.gate ∨ R.gate<B.gate)
    (absorbs : ∀ x : List Bool, x.length=n → val C x R.other=true → C.eval x=true) :
    False := by
  let D := moveOr n C R.gate y R.other
  obtain ⟨fan,back,size,compute⟩ :=
    moveOr_sound good.fan good.back good.validOutput R.valid (by omega : y<n+R.gate) R.early R.op absorbs
  have new : Representative n budget F D := by
    refine ⟨fan,back,moveOr_proper _ _ _ _ _ good.proper,size.le.trans good.small,moveOr_valid R.valid,?_⟩
    intro x
    exact (compute _ (by simp)).trans (good.computes x)
  obtain ⟨A',ag,_⟩ := move_leaf good.back back R.valid hy hp yp R.early R.op A
    saveA (and_ne_or A R) outA
  obtain ⟨B',bg,_⟩ := move_leaf good.back back R.valid hy hq yq R.early R.op B
    saveB (and_ne_or B R) outB
  have bound := least D A' B' new
  rw [ag,bg] at bound
  have an := shifted_le R.gate A.gate
  have bn := shifted_le R.gate B.gate
  rcases early with a | b
  · have h := shifted_lt_of_after a
    omega
  · have h := shifted_lt_of_after b
    omega

end AnchorMove

namespace Basis
lemma bFT:(false=true)=False:=Bool.false_eq_true
lemma bTA {b:Bool}:(true&&b)=b:=Bool.true_and b
lemma bOT {a b:Bool}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma bAT {a b:Bool}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma bNF:(!false)=true:=Bool.not_false
lemma bNT {b:Bool}:((!b)=true)=(b=false):=Bool.not_eq_true' b
lemma lAA {α:Type _} (l1 l2 l3:List α):(l1++l2)++l3=l1++(l2++l3):=List.append_assoc l1 l2 l3
lemma lMC {α β:Type _} {f : α->β} {a : α} {l:List α}:(a::l).map f=f a::l.map f:=List.map_cons
lemma lMM {α:Type _} {a b : α} {l:List α}:a ∈ b::l ↔ a=b\/a ∈ l:=List.mem_cons
lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma lRC {α:Type _} {a : α} {l:List α}:(a::l).reverse=l.reverse++[a]:=List.reverse_cons
lemma lFC {α β:Type _} {f : α->β->β} {b : β} {a : α} {l:List α}:(a::l).foldr f b=f a (l.foldr f b):=List.foldr_cons
lemma lAL {α:Type _} {p : α->Bool} {l:List α}:l.all p=true ↔ ∀ x ∈ l,p x=true:=List.all_eq_true
lemma lAN {α:Type _} {p : α->Bool} {l:List α}:l.any p=true ↔ ∃ x ∈ l,p x=true:=List.any_eq_true
lemma nTB {n i:Nat}:(2 ^ n - 1).testBit i=decide (i < n):=by simp [Nat.testBit_two_pow_sub_one]
lemma nEQ {x y:Nat} (h:∀ i,x.testBit i=y.testBit i):x=y:=Nat.eq_of_testBit_eq h
lemma nTO {x y i:Nat}:(x|||y).testBit i=(x.testBit i||y.testBit i):=by simp [Nat.testBit_or]
lemma nTA {x y i:Nat}:(x&&&y).testBit i=(x.testBit i&&y.testBit i):=by simp [Nat.testBit_and]
lemma nTX {x y i:Nat}:(x^^^y).testBit i=(x.testBit i ^^ y.testBit i):=by simp [Nat.testBit_xor]
lemma nTS {x k i:Nat}:(x >>> k).testBit i=x.testBit (k+i):=by simp [Nat.testBit_shiftRight]
lemma nLO {x y:Nat}:Nat.lor x y=x|||y:=Nat.lor_eq
lemma nLA {x y:Nat}:Nat.land x y=x&&&y:=Nat.land_eq
lemma nXO {x y:Nat}:Nat.xor x y=x^^^y:=Nat.xor_eq
lemma nZT {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma lMA {α β:Type _} {f : α->β} {l1 l2:List α}:(l1++l2).map f=l1.map f++l2.map f:=List.map_append
lemma lLM {α β:Type _} (f : α->β) {l:List α}:(l.map f).length=l.length:=List.length_map f
lemma lRR {α:Type _} {l:List α}:l.reverse.reverse=l:=List.reverse_reverse l
lemma lANil {α:Type _} {l:List α}:l++[]=l:=List.append_nil l
lemma lCA {α:Type _} {a : α} {l1 l2:List α}:(a::l1)++l2=a::(l1++l2):=List.cons_append
lemma lPM {α:Type _} {a : α} {l₁ l₂:List α}:(l₁++a::l₂).Perm (a::(l₁++l₂)):=List.perm_middle
lemma nAC (a b:Nat):a+b=b+a:=Nat.add_comm a b
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma nAZ {a:Nat}:a+0=a:=Nat.add_zero a
lemma nZL (a:Nat) : 0<=a:=Nat.zero_le a
lemma bOS {a:Bool}:(a||a)=a:=Bool.or_self a
lemma bOTR {a:Bool}:(a||true)=true:=Bool.or_true a
lemma bTOR {a:Bool}:(true||a)=true:=Bool.true_or a
lemma bATR {a:Bool}:(a&&true)=a:=Bool.and_true a
lemma bBT {a:Bool}:(a ^^ true)=!a:=Bool.bne_true a
lemma n2P (n:Nat) : 0 < 2 ^ n:=Nat.two_pow_pos n
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma fCD {α β γ:Type _} (f : β->γ) (g : α->β):f ∘ g=fun x => f (g x):=Function.comp_def f g
lemma lPR {α:Type _} (l:List α):l.Perm l:=List.Perm.refl l
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
lemma lPC {α:Type _} (x : α) {l1 l2:List α} (h:l1.Perm l2):(x::l1).Perm (x::l2):=List.Perm.cons x h
abbrev BFn (n : ℕ):=(Fin n->Bool)->Bool
def q3 (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma zd (gs gs':List Gate) (w:List Bool) :
   q3 (gs++gs') w=q3 gs' (q3 gs w):=by
 simp [q3,List.foldl_append]
lemma y1 (gs:List Gate):∀ w:List Bool,
   ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   have:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht];simp
lemma qu (gs:List Gate) (w:List Bool) :
   (q3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=y1 gs w
 rw [ht];simp [hl]
lemma ve (gs:List Gate) (w:List Bool) (i : ℕ) (h:i < w.length) :
   (q3 gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=y1 gs w
 rw [ht,List.getD_append _ _ _ _ h]
def Ok (g:Gate):Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
   (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 . exact List.getD_append _ _ _ _ hj
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
 simp
lemma z2 {α:Type} (L:List α) (S d : α) (k : ℕ) (h:L.length=k) :
   (L++[S]).getD k d=S:=by
 subst h;simp
def yb {n : ℕ} (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
 (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n : ℕ} (l:List ℕ) (F : ℕ->Finset (Fin n)) (i:Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]
lemma kf {n : ℕ} (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
   i ∈ yb L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 q71 _ _ _
def zb {n : ℕ} (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
 gs.foldl (fun L g => L++[yb L g]) L
def qr (n : ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n => {i}
def q207 {n : ℕ} (x y:Fin n->Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
 L.length=w.length/\w.length=w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n : ℕ} (x y:Fin n->Bool) (gs:List Gate) :
   ∀ (L:List (Finset (Fin n))) (w w':List Bool),q207 x y L w w' ->
     q207 x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil => intro L w w' h;exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[yb L g])
     (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w'++[g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0] at hj
     rw [h1,z0,h2,z0]
     congr 1
     apply List.map_congr_left
     intro a ha
     exact h3 a (fun i hi => hj i ((kf L g i).2 ⟨a,ha,hi⟩))
   . rw [q8 _ _ _ _ hjl] at hj
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact h3 j hj
lemma j4 {n : ℕ} (x y:Fin n->Bool) :
   q207 x y (qr n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 . have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [qr,hjn])
   simp [hjn,hx]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
def Cnt {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))):Prop :=
 ∀ W:Finset ℕ,(W.biUnion fun j => L.getD j ∅).card<=t+W.card
lemma q166 {n : ℕ}:Cnt 0 (qr n):=by
 intro W
 refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _
 by_cases hjn:j < n
 . simp [qr,hjn]
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q194 {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))) (g:Gate) (hg:g.inputs.length<=2)
   (h:Cnt t L):Cnt (t+1) (L++[yb L g]):=by
 intro W
 by_cases hW:L.length ∈ W
 . have hsub:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅):=by
     intro i hi
     rw [Finset.mem_biUnion] at hi ⊢
     obtain ⟨j,hjW,hij⟩:=hi
     by_cases hjl:j=L.length
     . subst hjl
       rw [z0] at hij
       obtain ⟨a,ha,hia⟩:=(kf L g i).1 hij
       exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
     . rw [q8 _ _ _ _ hjl] at hij
       exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
   have hc1:(W.erase L.length ∪ g.inputs.toFinset).card<=(W.card - 1)+2:=by
     refine le_trans (Finset.card_union_le _ _) ?_
     rw [Finset.card_erase_of_mem hW]
     exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
   have hWpos : 1<=W.card:=Finset.card_pos.2 ⟨_,hW⟩
   have:=h (W.erase L.length ∪ g.inputs.toFinset)
   have:=Finset.card_le_card hsub
   omega
 . have heq:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       = (W.biUnion fun j => L.getD j ∅):=by
     apply Finset.biUnion_congr rfl
     intro j hj
     exact q8 _ _ _ _ (fun e => hW (e ▸ hj))
   rw [heq]
   have:=h W
   omega
lemma q118 {n : ℕ} (gs:List Gate):∀ (t : ℕ) (L:List (Finset (Fin n))),
   (∀ g ∈ gs,Ok g)->Cnt t L->Cnt (t+gs.length) (zb gs L):=by
 induction gs with
 | nil => intro t L _ h;exact h
 | cons g gs ih =>
   intro t L hok h
   have:=ih (t+1) (L++[yb L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
     (q194 t L g (hok g List.mem_cons_self).2 h)
   rw [lLC,show t+(gs.length+1)=t+1+gs.length by omega]
   exact this
lemma q117 (n : ℕ) (f:(Fin n->Bool)->Bool) (T:Finset (Fin n))
   (hdep:∀ i ∈ T,∃ x:Fin n->Bool,f (Function.update x i (!x i))≠f x)
   (s : ℕ) (h:HasCircuitSize n f s):T.card<=s+1:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set S:=(zb C.gates (qr n)).getD C.output ∅ with hS
 have hall:T ⊆ S:=by
   intro i hiT
   by_contra hi
   obtain ⟨x,hx⟩:=hdep i hiT
   apply hx
   have hag:=(k6 (Function.update x i (!x i)) x C.gates _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠i:=fun e => hi (e ▸ hk)
       simp [fUN this])
   rw [← hev,← hev]
   exact hag
 have hc:=q118 C.gates 0 (qr n) ok q166 {C.output}
 simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc
 rw [← hS] at hc
 have:=Finset.card_le_card hall
 omega
def vg (g:Gate):Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g
lemma q107 (g:Gate) (F : ℕ->Bool) :
   (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g
 cases op <;> simp only [vg]
 cases inputs <;> simp [GateOp.eval]
def NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma q45 (g:Gate) (h:Ok g):NOk (vg g):=by
 obtain ⟨op,inputs⟩:=g
 obtain ⟨hop,hlen⟩:=h
 rcases hop with h | h | h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg] <;> omega
lemma jd (gs:List Gate):∀ w:List Bool,
   q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil => intro w;rfl
 | cons g gs ih =>
   intro w
   have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
       (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
   have s2:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [s1,s2,q107,ih]
abbrev Stat:=Sum Bool ℕ
def ze (w:List Bool):Stat->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false
def qn (m : ℕ):Stat->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m
def wr (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | Sum.inl c::_ => (none,Sum.inl (!c))
 | Sum.inr j::_ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def ko (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def ji (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
 match op with
 | GateOp.and => ko m ins
 | GateOp.or => ji m ins
 | GateOp.not => wr m ins
 | _ => (none,Sum.inl false)
def q161 (m : ℕ) (g:Gate):Prop :=
 (g.op=GateOp.not/\∃ j,j < m/\g.inputs=[j]) \/
 ((g.op=GateOp.and\/g.op=GateOp.or)/\∃ j k,j < m/\k < m/\g.inputs=[j,k])
lemma j2 {m : ℕ} {g:Gate} (h:q161 m g):∀ a ∈ g.inputs,a < m:=by
 rcases h with ⟨_,j,hj,hin⟩ | ⟨_,j,k,hj,hk,hin⟩
 . intro a ha;simp [hin] at ha;omega
 . intro a ha;simp [hin] at ha;rcases ha with rfl | rfl <;> omega
def yq (n : ℕ) (gs:List Gate):Prop :=
 ∀ p g,gs[p]?=some g->q161 (n+p) g
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp [wr] at hg <;> (subst hg;simp [Ok])
 . simp at hg
 . simp at hg
lemma q80 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hv:∀ s ∈ ins,qn m s) :
   ∀ g ∈ (qg op m ins).1,q161 m g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg
   subst hg
   exact Or.inr ⟨Or.inl rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg
   subst hg
   exact Or.inr ⟨Or.inr rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [wr] at hg
   subst hg
   exact Or.inl ⟨rfl,_,hv (Sum.inr _) (by simp),rfl⟩
 . simp at hg
 . simp at hg
lemma jh (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
   (qg op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ko]
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
   (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
   (hv:∀ s ∈ ins,qn w.length s) :
   qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
   ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
     = op.eval (ins.map (ze w)):=by
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
 (acc.1++[(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2++(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
 gs.foldl (qa n) acc
lemma k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
   elim n (g::gs) acc=elim n gs (qa n acc g):=rfl
lemma jz (n : ℕ) (pre post:List Gate) (acc:List Stat × List Gate) :
   elim n (pre++post) acc=elim n post (elim n pre acc):=by
 simp [elim,List.foldl_append]
lemma q50 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
   intro acc
   rw [k4,ih]
   simp only [qa,lLA,lLC,List.length_nil]
   omega
lemma wy (n k : ℕ) (d:Stat) (gs:List Gate):∀ acc:List Stat × List Gate,
   k < acc.1.length->(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
   intro acc hk
   rw [k4,ih (qa n acc g) (by simp [qa];omega)]
   exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by
 cases o <;> simp
lemma q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil => intro acc h;exact h
 | cons g gs ih =>
   intro acc h
   apply ih (qa n acc g)
   intro g' hg'
   rcases List.mem_append.1 hg' with h1 | h1
   . exact h g' h1
   . exact q151 _ _ _ g' (by simpa using h1)
lemma q29 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).2.length<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (qa n acc g)
   have h2:(qa n acc g).2.length<=acc.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   rw [k4,lLC];omega
lemma zt (n k : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->k < acc.1.length->(∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) ->
   (∃ g ∈ gs,k ∈ g.inputs)->(elim n gs acc).2.length+1<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
   intro acc hok hk hc hex
   rw [k4,lLC]
   by_cases hkg:k ∈ g.inputs
   . obtain ⟨c,hc⟩:=hc
     have hnok:=hok g List.mem_cons_self
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hnok.1.1
       . simpa using hnok.1.2
       . intro h;simpa using hnok.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
     have h2:(qa n acc g).2.length=acc.2.length:=by
       show (acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
       rw [hnone];simp
     have:=q29 n gs (qa n acc g)
     omega
   . have hex':∃ g' ∈ gs,k ∈ g'.inputs:=by
       obtain ⟨g',hg',hk'⟩:=hex
       rcases List.mem_cons.1 hg' with rfl | h
       . exact absurd hk' hkg
       . exact ⟨g',h,hk'⟩
     have h1:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       (by simp [qa];omega)
       (by
         obtain ⟨c,hc⟩:=hc
         refine ⟨c,?_⟩
         simp only [qa]
         rw [q8 _ _ _ _ (by omega)];exact hc)
       hex'
     have h2:(qa n acc g).2.length<=acc.2.length+1:=by
       simp only [qa,lLA]
       have:=y2 (qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
       omega
     omega
lemma km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma jg (w t:List Bool):∀ s:Stat,qn w.length s ->
   ze (w++t) s=ze w s
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length/\∀ i : ℕ,
   qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
   ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
lemma j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=q3 acc.2 y with hw'
   have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw'];exact (hi a).1)
   rw [lw'] at hs
   set r:=qg g.op (n+acc.2.length) ins with hr
   have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,lMMp]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
     rw [zd]
   obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
   refine ⟨by simp [qa,hl],?_⟩
   intro i
   show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
     ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
   rw [hnew,lLA,← nAA]
   by_cases hil:i=acc.1.length
   . subst hil
     rw [z0,hl,z0]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
     refine ⟨km (by omega) _ (hi i).1,?_⟩
     rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
     exact (hi i).2
lemma q100 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,Ok g)->(∀ i,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) ->
   yq n acc.2->yq n (elim n gs acc).2:=by
 induction gs with
 | nil => intro acc _ _ hc;exact hc
 | cons g gs ih =>
   intro acc hok hv hc
   have hstep:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   apply hstep
   . intro i
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 (List.replicate (n+acc.2.length) false) ins
       (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         simpa using hv a)
     simp only [List.length_replicate] at hs
     show qn (n+(acc.2++_).length) ((acc.1++[_]).getD i (Sum.inl false))
     rw [lLA,← nAA]
     by_cases hil:i=acc.1.length
     . subst hil;rw [z0];exact hs.1
     . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
   . intro p g' hp
     simp only [qa] at hp
     by_cases hlt:p < acc.2.length
     . rw [List.getElem?_append_left hlt] at hp
       exact hc p g' hp
     . rw [List.getElem?_append_right (by omega)] at hp
       set r:=qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
       cases ho:r.1 with
       | none => simp [ho] at hp
       | some g0 =>
         rw [ho] at hp
         have hp0:p - acc.2.length=0:=by
           have:=(List.getElem?_eq_some_iff.1 hp).1
           simp at this;omega
         have hpeq:p=acc.2.length:=by omega
         rw [hp0] at hp
         simp at hp
         subst hp
         rw [hpeq]
         exact q80 g.op (n+acc.2.length) _ (by
           intro s hs
           obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
           exact hv a) g0 (by rw [← hr,ho];rfl)
def qd (n : ℕ) (b:Bool):List Stat :=
 List.ofFn (fun i:Fin n => Sum.inr (i : ℕ))++[Sum.inl b]
lemma kp (n : ℕ) (b:Bool) :
   (qd n b).getD n (Sum.inl false)=Sum.inl b :=
 z2 _ _ _ _ (by simp)
lemma q159 (n : ℕ) (b:Bool) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i
 have l1:(List.ofFn (fun i:Fin n => (Sum.inr (i : ℕ):Stat))).length=n:=by simp
 have l2:(List.ofFn y).length=n:=by simp
 by_cases hin:i=n
 . subst hin
   simp only [qd]
   rw [z2 _ _ _ _ l1,z2 _ _ _ _ l2]
   exact ⟨trivial,rfl⟩
 . simp only [qd]
   rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases hlt:i < n
   . simp [hlt,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
     exact ⟨trivial,rfl⟩
lemma q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
   List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
 rw [List.ofFn_succ']
 simp
lemma jr (n : ℕ) (gs:List Gate):∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,n ∉ g.inputs)->(∀ j : ℕ,j≠n->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q74 (m j : ℕ) (h:j < m) :
   (qr m).getD j ∅={⟨j,h⟩}:=by
 simp [qr,h]
lemma yi (n : ℕ):∀ j : ℕ,j≠n ->
   Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j hj
 by_cases hlt:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,hlt⟩}:=q74 (n+1) j hlt
   rw [e,Finset.mem_singleton]
   intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q115 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s',s'+1<=s/\HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 set acc:=elim n gs (qd n b,[]) with hacc
 have hinv:∀ y:Fin n->Bool,
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool))) acc:=by
   intro y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ y:Fin n->Bool,
     ze (q3 acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
       = f (Fin.snoc y b):=by
   intro y
   rw [((hinv y).2 C.output).2,hevg]
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst];rfl
 | inr j =>
   have hlen:acc.2.length+1<=s:=by
     by_cases hread:∃ g ∈ gs,n ∈ g.inputs
     . have:=zt n n gs (qd n b,[]) hnok (by simp [qd])
         ⟨b,z2 _ _ _ _ (by simp)⟩ hread
       rw [← hacc] at this
       have hl:gs.length=C.gates.length:=by simp [hgs]
       simp only [List.length_nil,zero_add] at this
       omega
     . exfalso
       push Not at hread
       have hout:C.output≠n:=by
         intro e
         rw [e,hacc,wy n n _ gs _ (by simp [qd])] at hst
         have hb:(qd n b).getD n (Sum.inl false)=Sum.inl b :=
           z2 _ _ _ _ (by simp)
         rw [show ((qd n b,([]:List Gate))).1=qd n b from rfl,hb] at hst
         cases hst
       obtain ⟨x,hx⟩:=hdep
       apply hx
       have hns:=jr n gs (qr (n+1)) hread (yi n) C.output hout
       have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
         (j4 _ _)).2.2 C.output (by
           intro k hk
           have:k≠Fin.last n:=fun e => hns (e ▸ hk)
           simp [fUN this])
       rw [← hevg,← hevg]
       exact hag
   refine ⟨acc.2.length,hlen,⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval y
   rw [hst] at this
   exact this
lemma q79 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (b:Bool)
   (hand:op=GateOp.and->b=false) (hor:op=GateOp.or->b=true)
   (hc:Sum.inl b ∈ ins):∃ c,(qg op m ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 . have:=hand rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ko]
 . have:=hor rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma vs (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (c:Bool) (hc:acc.1.getD k (Sum.inl false)=Sum.inl c) :
   (qa n acc g).2.length=acc.2.length:=by
 have hnone:(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
   apply jh
   . exact hg.1.1
   . simpa using hg.1.2
   . intro h;simpa using hg.2 h
   . exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
 show (acc.2++(qg g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
 rw [hnone];simp
def wl (g:Gate):Bool :=
 match g.op with
 | GateOp.or => true
 | _ => false
lemma q90 (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (hc:acc.1.getD k (Sum.inl false)=Sum.inl (wl g)) :
   ∃ c,(qa n acc g).1.getD acc.1.length (Sum.inl false)=Sum.inl c:=by
 have e:(qa n acc g).1.getD acc.1.length (Sum.inl false)
     = (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2:=z0 _ _ _
 rw [e]
 apply q79 _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
   (wl g)
 . intro h;simp [wl,h]
 . intro h;simp [wl,h]
 . exact List.mem_map.2 ⟨k,hk,hc⟩
lemma q53 {n : ℕ} (pre post:List Gate) (L:List (Finset (Fin n))) :
   zb (pre++post) L=zb post (zb pre L):=by
 simp [zb,List.foldl_append]
lemma q54 {n : ℕ} (gs:List Gate):∀ L:List (Finset (Fin n)),
   (zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil => intro L;rfl
 | cons g gs ih =>
   intro L
   have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl
   rw [h,ih]
   simp only [lLA,lLC,List.length_nil]
   omega
lemma q124 (n : ℕ) (D : ℕ->Prop) (gs:List Gate) :
   ∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,∀ a ∈ g.inputs,¬ D a)->(∀ j : ℕ,¬ D j->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,¬ D j->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (hno g List.mem_cons_self a ha) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q173 (n : ℕ) (gs:List Gate) (hnok:∀ g ∈ gs,NOk g) (o : ℕ)
   (hdep:Fin.last n ∈ (zb gs (qr (n+1))).getD o ∅)
   (hout:∀ b c,(elim n gs (qd n b,[])).1.getD o (Sum.inl false)≠Sum.inl c) :
   ∃ b,(elim n gs (qd n b,[])).2.length+2<=gs.length:=by
 have hon:o≠n:=by
   intro e
   apply hout false false
   rw [e,wy n n _ gs _ (by simp [qd])]
   exact kp n false
 by_cases hread:∃ g ∈ gs,n ∈ g.inputs
 swap
 . exfalso
   push Not at hread
   exact jr n gs (qr (n+1)) hread (yi n) o hon hdep
 obtain ⟨g,hg,hng⟩:=hread
 obtain ⟨pre,post,rfl⟩:=List.append_of_mem hg
 have hgn:NOk g:=hnok g hg
 have hpren:∀ g' ∈ pre,NOk g':=fun g' h => hnok g' (List.mem_append_left _ h)
 have hpostn:∀ g' ∈ post,NOk g' :=
   fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have hsplit:∀ b,elim n (pre++g::post) (qd n b,[])
     = elim n post (qa n (elim n pre (qd n b,[])) g) :=
   fun b => by rw [jz,k4]
 have hAn:∀ b,(elim n pre (qd n b,[])).1.getD n (Sum.inl false)=Sum.inl b:=by
   intro b
   rw [wy n n _ pre _ (by simp [qd])]
   exact kp n b
 have hAl:∀ b,(elim n pre (qd n b,[])).1.length=n+1+pre.length:=by
   intro b
   rw [q50]
   simp [qd]
 have hA2:∀ b,(elim n pre (qd n b,[])).2.length<=0+pre.length :=
   fun b => q29 n pre (qd n b,[])
 have hB2:=fun b => vs n (elim n pre (qd n b,[])) g hgn n hng b (hAn b)
 have hBl:∀ b,(qa n (elim n pre (qd n b,[])) g).1.length
     = n+1+pre.length+1:=by
   intro b
   simp [qa,hAl b]
 have hBn:∀ b,(qa n (elim n pre (qd n b,[])) g).1.getD n (Sum.inl false)
     = Sum.inl b:=by
   intro b
   show ((elim n pre (qd n b,[])).1++[_]).getD n _=_
   rw [q8 _ _ _ _ (by rw [hAl b];omega)]
   exact hAn b
 have hF:=fun b => q29 n post (qa n (elim n pre (qd n b,[])) g)
 have hlen:(pre++g::post).length=pre.length+post.length+1:=by
   simp only [lLA,lLC];omega
 by_cases h1:∃ g' ∈ pre,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:(elim n pre (qd n false,[])).2.length+1<=0+pre.length :=
     zt n n pre (qd n false,[]) hpren (by simp [qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 by_cases h2:∃ g' ∈ post,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:=zt n n post (qa n (elim n pre (qd n false,[])) g) hpostn
     (by rw [hBl];omega) ⟨false,hBn false⟩ h2
   have:=hA2 false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 obtain ⟨c,hc⟩:=q90 n (elim n pre (qd n (wl g),[])) g hgn n hng
   (hAn (wl g))
 rw [hAl (wl g)] at hc
 refine ⟨wl g,?_⟩
 by_cases h3:∃ g' ∈ post,(n+1+pre.length) ∈ g'.inputs
 . have a1:=zt n (n+1+pre.length) post
     (qa n (elim n pre (qd n (wl g),[])) g) hpostn
     (by rw [hBl];omega) ⟨c,hc⟩ h3
   have:=hA2 (wl g)
   have:=hB2 (wl g)
   rw [hsplit,hlen]
   omega
 . exfalso
   have hom:o≠n+1+pre.length:=by
     intro e
     apply hout (wl g) c
     rw [hsplit,e,wy n _ _ post _ (by rw [hBl];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (pre++g::post) (qr (n+1))
       = zb post (zb pre (qr (n+1))
         ++ [yb (zb pre (qr (n+1))) g]):=by
     rw [q53];rfl
   rw [hs] at hdep
   have hL:=jr n pre (qr (n+1)) h1 (yi n)
   have hLl:(zb pre (qr (n+1))).length=n+1+pre.length:=by
     rw [q54]
     simp [qr]
   refine q124 n (fun j => j=n\/j=n+1+pre.length) post _ ?_ ?_ o
     (by simp [hon,hom]) hdep
   . intro g' hg' a ha hD
     rcases hD with rfl | rfl
     . exact h2 g' hg' ha
     . exact h3 g' hg' ha
   . intro j hj
     have hj':j≠n/\j≠n+1+pre.length:=by
       constructor
       . exact fun e => hj (Or.inl e)
       . exact fun e => hj (Or.inr e)
     rw [q8 _ _ _ _ (by rw [hLl];exact hj'.2)]
     exact hL j hj'.1
lemma q114 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∀ b:Bool,∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hl:gs.length=C.gates.length:=by simp [hgs]
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 have hinv:∀ (b:Bool) (y:Fin n->Bool),
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)))
       (elim n gs (qd n b,[])):=by
   intro b y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ (b:Bool) (y:Fin n->Bool),
     ze (q3 (elim n gs (qd n b,[])).2 (List.ofFn y))
       ((elim n gs (qd n b,[])).1.getD C.output (Sum.inl false))=f (Fin.snoc y b):=by
   intro b y
   rw [((hinv b y).2 C.output).2,hevg]
 have hout:∀ b c,
     (elim n gs (qd n b,[])).1.getD C.output (Sum.inl false)≠Sum.inl c:=by
   intro b c hst
   obtain ⟨y,y',hne⟩:=hnc b
   apply hne
   rw [← hval b y,← hval b y',hst];rfl
 have hsupp:Fin.last n ∈ (zb gs (qr (n+1))).getD C.output ∅:=by
   by_contra hns
   obtain ⟨x,hx⟩:=hdep
   apply hx
   have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠Fin.last n:=fun e => hns (e ▸ hk)
       simp [fUN this])
   rw [← hevg,← hevg]
   exact hag
 obtain ⟨b,hb⟩:=q173 n gs hnok C.output hsupp hout
 cases hst:(elim n gs (qd n b,[])).1.getD C.output (Sum.inl false) with
 | inl c => exact absurd hst (hout b c)
 | inr j =>
   refine ⟨b,(elim n gs (qd n b,[])).2.length,by omega,
     ⟨(elim n gs (qd n b,[])).2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval b y
   rw [hst] at this
   exact this
def wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
 if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
def jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
 ⟨C.gates.map (jt n m π),wmap n m π C.output⟩
def step (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
 n<=W.length/\W'.length+n=W.length+m /\
   ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
lemma q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
   (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv:(jt n m π g).op.eval
     ((jt n m π g).inputs.map fun i => W'.getD i false)
     = g.op.eval (g.inputs.map fun i => W.getD i false):=by
   simp only [jt,lMMp]
   congr 1
   apply List.map_congr_left
   intro a _
   exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w
 simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 . have hlt:wmap n m π w < W'.length:=by
     unfold wmap
     split
     . have:=(π ⟨w,by assumption⟩).2;omega
     . omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
   exact h3 w
 . have he:wmap n m π w=W'.length:=by
     unfold wmap
     split
     . omega
     . omega
   rw [he,hw,z0,z0]
 . have hge:W'.length+1<=wmap n m π w:=by
     unfold wmap
     split
     . omega
     . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
lemma q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
   ∀ W W':List Bool,Rel n m π W W' ->
     Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   exact ih _ _ (q182 n m π W W' g h)
lemma q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
   Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w
 unfold wmap
 split
 . rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 . rename_i hw
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
lemma yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
   (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨q174 n m π C,?_,?_,?_⟩
 . intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
 . simpa [q174,Circuit.size] using hsz
 . intro x
   show _=h (x ∘ π)
   rw [← hev (x ∘ π)]
   have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
   exact this
lemma ks (n : ℕ) (p:Fin (n+1)) (x:Fin (n+1)->Bool) (b:Bool) :
   (Fin.snoc (fun j:Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
       Fin (n+1)->Bool) ∘ (Equiv.swap p (Fin.last n))
     = Function.update x p b:=by
 funext j
 simp only [Function.comp_apply]
 by_cases hj:j=p
 . subst hj
   rw [Equiv.swap_apply_left,Fin.snoc_last,fUS]
 . have hl:Equiv.swap p (Fin.last n) j≠Fin.last n:=by
     intro e
     apply hj
     have:=congrArg (Equiv.swap p (Fin.last n)) e
     rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain ⟨t,ht⟩:=Fin.exists_castSucc_eq.2 hl
   rw [← ht,Fin.snoc_castSucc,ht,Equiv.swap_apply_self,fUN hj]
lemma q70 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s' : ℕ,s'+1<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   obtain ⟨x,y,hxy⟩:=hnc
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨s',hs,h'⟩:=q115 n _ b s hdep' hnc' hg
 refine ⟨s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
lemma q141 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∀ b:Bool,∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∀ b:Bool,∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   intro b
   obtain ⟨x,y,hxy⟩:=hnc b
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨b,s',hs,h'⟩:=q114 n _ s hdep' hnc' hg
 refine ⟨b,s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
def val (gs:List Gate) (n : ℕ) (a : ℕ):BFn n :=
 fun x => (q3 gs (List.ofFn x)).getD a false
lemma q172 (gs:List Gate) (n : ℕ) (i:Fin n):val gs n i=fun x => x i:=by
 funext x
 unfold val
 rw [ve _ _ _ (by simp)]
 simp
lemma q60 {α:Type} (gs:List α) (p : ℕ) (g : α) (hp:gs[p]?=some g) :
   ∃ pre post,gs=pre++g::post/\pre.length=p:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hp).1
 have hget:gs[p]=g:=(List.getElem?_eq_some_iff.1 hp).2
 refine ⟨gs.take p,gs.drop (p+1),?_,by simp;omega⟩
 have h1:gs=gs.take p++gs.drop p:=(List.take_append_drop p gs).symm
 have h2:gs.drop p=gs[p]::gs.drop (p+1):=List.drop_eq_getElem_cons hlt
 exact h1.trans (by rw [h2,hget])
lemma q103 (n : ℕ) (gs:List Gate) (p : ℕ) (g:Gate) (hp:gs[p]?=some g)
   (hlt:∀ a ∈ g.inputs,a < n+p) (x:Fin n->Bool) :
   val gs n (n+p) x=g.op.eval (g.inputs.map fun a => val gs n a x):=by
 obtain ⟨pre,post,rfl,hlen⟩:=q60 gs p g hp
 unfold val
 have h1:q3 (pre++g::post) (List.ofFn x)=q3 post
     (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]):=by
   rw [zd];rfl
 have hl:(q3 pre (List.ofFn x)).length=n+p:=by
   rw [qu];simp [hlen]
 rw [h1,ve _ _ _ (by simp [hl]),z2 _ _ _ _ hl]
 congr 1
 apply List.map_congr_left
 intro a ha
 have hal:=hlt a ha
 have e1:=ve post (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]) a
       (by simp [hl];omega)
 rw [e1,List.getD_append _ _ _ _ (by omega)]
def vi (n : ℕ):List Stat:=List.ofFn fun i:Fin n => Sum.inr (i : ℕ)
lemma q165 (n : ℕ) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y) (vi n,[]):=by
 refine ⟨by simp [vi],?_⟩
 intro i
 by_cases hlt:i < n
 . simp [vi,hlt,qn,ze,q3]
 . rw [lGD _ _ (by simp [vi];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma q48 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,yq n gs/\gs.length<=s/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set acc:=elim n C.gates (vi n,[]) with hacc
 have hinv:∀ y:Fin n->Bool,Inv n (List.ofFn y) (q3 C.gates (List.ofFn y)) acc :=
   fun y => j7 n _ (by simp) C.gates _ _ ok (q165 n y)
 have hcl:yq n acc.2:=by
   apply q100 n C.gates (vi n,[]) ok
   . intro i
     by_cases hlt:i < n
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
   . intro p g hp;simp at hp
 have hlen:acc.2.length<=s:=by
   have:=q29 n C.gates (vi n,[])
   rw [← hacc] at this
   simp only [List.length_nil,zero_add] at this
   omega
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=((hinv y).2 C.output).2
   have e2:=((hinv y').2 C.output).2
   rw [hst] at e1 e2
   have h1:(q3 C.gates (List.ofFn y)).getD C.output false=f y:=hev y
   have h2:(q3 C.gates (List.ofFn y')).getD C.output false=f y':=hev y'
   rw [← h1,← h2,← e1,← e2];rfl
 | inr j =>
   have hj:j < n+acc.2.length:=by
     obtain ⟨y,_,_⟩:=hnc
     have:=((hinv y).2 C.output).1
     rw [hst] at this
     exact this
   refine ⟨acc.2,j,hcl,hlen,hj,?_⟩
   intro x
   have e1:=((hinv x).2 C.output).2
   rw [hst] at e1
   exact e1.trans (hev x)
def qk {α:Type} (b:Bool) (x : α) (xs:List α):List α :=
 if b then x::xs else xs
def Run {α:Type} (inv : α->α) (meet join : α->α->α) (y : α) (t : ℕ) (ws:List α):Prop :=
 ∀ P : ℕ->List α->Prop,P 0 [y] ->
   (∀ {s xs zs},List.Perm xs zs->P s xs->P s zs) ->
   (∀ {s a r} (neg save:Bool),P s ((if neg then inv a else a)::qk save a r) ->
     P (s+1) (a::r)) ->
   (∀ {s a b r} (c ka kb:Bool),
     P s ((if c then meet a b else join a b)::qk ka a (qk kb b r)) ->
     P (s+1) (a::b::r))->P t ws
lemma Run.done {α inv meet join y} : @Run α inv meet join y 0 [y]:=fun _ d _ _ _ => d
lemma Run.perm {α inv meet join y s xs zs} (p:List.Perm xs zs)
   (h : @Run α inv meet join y s xs):Run inv meet join y s zs :=
 fun P d q u b => q p (h P d q u b)
lemma Run.one {α inv meet join y s a r} (neg save:Bool)
   (h : @Run α inv meet join y s ((if neg then inv a else a)::qk save a r)) :
   Run inv meet join y (s+1) (a::r):=fun P d q u b => u neg save (h P d q u b)
lemma Run.two {α inv meet join y s a b r} (c ka kb:Bool)
   (h : @Run α inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))) :
   Run inv meet join y (s+1) (a::b::r):=fun P d q u v => v c ka kb (h P d q u v)
lemma Run.fold {α inv meet join y} {P:∀ t ws,@Run α inv meet join y t ws->Prop}
   (done:P 0 [y] Run.done)
   (perm:∀ {s xs zs} (hp:List.Perm xs zs) (h:Run inv meet join y s xs),
     P s xs h->P s zs (Run.perm hp h))
   (one:∀ {s a r} (neg save:Bool)
     (h:Run inv meet join y s ((if neg then inv a else a)::qk save a r)),
     P _ _ h->P _ _ (Run.one neg save h))
   (two:∀ {s a b r} (c ka kb:Bool)
     (h:Run inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))),
     P _ _ h->P _ _ (Run.two c ka kb h))
   {t ws} (h:Run inv meet join y t ws):P t ws h:=by
 have hex:=h (fun s xs => ∃ h':Run inv meet join y s xs,P s xs h')
   ⟨Run.done,done⟩
   (fun hp ⟨h',ih⟩ => ⟨Run.perm hp h',perm hp h' ih⟩)
   (fun n k ⟨h',ih⟩ => ⟨Run.one n k h',one n k h' ih⟩)
   (fun c a b ⟨h',ih⟩ => ⟨Run.two c a b h',two c a b h' ih⟩)
 exact hex.elim fun _ hp => hp
lemma wd {α β:Type} (e : α->β) (b:Bool) (x : α) (xs:List α) :
   (qk b x xs).map e=qk b (e x) (xs.map e):=by cases b <;> simp [qk]
lemma wa {α:Type} (b:Bool) (x a : α) (xs:List α) :
   a ∈ qk b x xs ↔ (b=true/\a=x)\/a ∈ xs:=by cases b <;> simp [qk]
lemma q36 {α:Type} (b:Bool) (x : α) (xs:List α) (h:xs.Nodup) (hx:x ∉ xs) :
   (qk b x xs).Nodup:=by
 cases b
 . simpa [qk] using h
 . simpa [qk] using And.intro hx h
lemma Run.map {α β:Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
   {inv' : β->β} {meet' join' : β->β->β}
   (hi:∀ a,e (inv a)=inv' (e a)) (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {y : α} {s : ℕ} {ws:List α} (h:Run inv meet join y s ws) :
   Run inv' meet' join' (e y) s (ws.map e):=by
 induction h using Run.fold with
 | done => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map e) ih
 | @one s a rest neg save _ ih =>
   have e1:((if neg then inv a else a)::qk save a rest).map e
       = (if neg then inv' (e a) else e a)::qk save (e a) (rest.map e):=by
     cases neg <;> simp [wd,hi]
   rw [e1] at ih
   exact Run.one neg save ih
 | @two s a b rest conj ka kb _ ih =>
   have e1:((if conj then meet a b else join a b)::qk ka a (qk kb b rest)).map e
       = (if conj then meet' (e a) (e b) else join' (e a) (e b))
           :: qk ka (e a) (qk kb (e b) (rest.map e)):=by
     cases conj <;> simp [wd,hm,hj]
   rw [e1] at ih
   exact Run.two conj ka kb ih
def wn (n : ℕ) (gs:List Gate) (o a : ℕ):Prop :=
 ∀ P : ℕ->Prop,P o ->
   (∀ q g,gs[q]?=some g->P (n+q)->∀ u ∈ g.inputs,P u)->P a
lemma q34 (n : ℕ) (gs:List Gate) (o : ℕ):wn n gs o o :=
 fun _ ho _ => ho
lemma q33 {n : ℕ} {gs:List Gate} {o q u : ℕ} {g:Gate}
   (hq:gs[q]?=some g) (hr:wn n gs o (n+q)) (hu:u ∈ g.inputs) :
   wn n gs o u :=
 fun P ho hs => hs q g hq (hr P ho hs) u hu
lemma q66 {n : ℕ} {gs:List Gate} {o a : ℕ} (h:wn n gs o a) :
   a=o\/∃ q g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q):=by
 apply h (fun x => x=o\/∃ q g,gs[q]?=some g/\x ∈ g.inputs/\wn n gs o (n+q))
 . exact Or.inl rfl
 . intro q g hq hP u hu
   refine Or.inr ⟨q,g,hq,hu,?_⟩
   rcases hP with rfl | ⟨q',g',hq',hin',hr'⟩
   . exact q34 n gs (n+q)
   . exact q33 hq' hr' hin'
def q11 (n : ℕ) (gs:List Gate) (o p a : ℕ):Prop :=
 a=o\/∃ q,p<=q/\∃ g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q)
open Classical in
noncomputable def liveList (gs:List Gate) (n o p : ℕ):List ℕ :=
 (List.range (n+p)).filter (fun a => decide (q11 n gs o p a))
lemma qw (gs:List Gate) (n o p a : ℕ) :
   a ∈ liveList gs n o p ↔ a < n+p/\q11 n gs o p a:=by
 simp [liveList]
lemma vy (gs:List Gate) (n o p : ℕ):(liveList gs n o p).Nodup :=
 List.Nodup.filter _ List.nodup_range
abbrev invF {n : ℕ}:BFn n->BFn n:=fun a x => !a x
abbrev meetF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x&&b x
abbrev joinF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x||b x
lemma q73 (n : ℕ) (gs:List Gate) (o : ℕ) (hcl:yq n gs)
   (p : ℕ) (g:Gate) (hg:gs[p]?=some g) (hr:wn n gs o (n+p)) (a : ℕ) :
   a ∈ liveList gs n o (p+1) ↔
     a=n+p\/(a ∈ liveList gs n o p/\(a ∈ g.inputs->q11 n gs o (p+1) a)):=by
 rw [qw,qw]
 constructor
 . rintro ⟨hlt,hl⟩
   by_cases ha:a=n+p
   . exact Or.inl ha
   . refine Or.inr ⟨⟨by omega,?_⟩,fun _ => hl⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
 . rintro (rfl | ⟨⟨hlt,hl⟩,himp⟩)
   . refine ⟨by omega,?_⟩
     rcases q66 hr with h | ⟨q,g',hg',hin,hrq⟩
     . exact Or.inl h
     . refine Or.inr ⟨q,?_,g',hg',hin,hrq⟩
       have:=j2 (hcl q g' hg') _ hin
       omega
   . refine ⟨by omega,?_⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . by_cases hqp:q=p
       . subst hqp
         rw [hg] at hg'
         cases hg'
         exact himp hin
       . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
def gfn {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)):BFn n :=
 fun x => A.any (fun a => x a)||E.any (fun e => x e.1&&x e.2)
def j9 {α:Type} [BEq α]:List α->List α->List α
 | [],acc => acc.reverse
 | a::t,acc => if acc.contains a then j9 t acc else j9 t (a::acc)
def q206 {α:Type} [BEq α] (l:List α):List α:=j9 l []
lemma ww {α:Type} [DecidableEq α]:∀ (l acc:List α) (x : α),
   x ∈ j9 l acc ↔ x ∈ l\/x ∈ acc
 | [],acc,x => by simp [j9]
 | a::t,acc,x => by
   simp only [j9]
   by_cases h:acc.contains a=true
   . simp only [h,↓reduceIte,ww,lMM]
     have ha:a ∈ acc:=by simpa using h
     constructor
     . rintro (ht | hacc)
       . exact Or.inl (Or.inr ht)
       . exact Or.inr hacc
     . rintro ((rfl | ht) | hacc)
       . exact Or.inr ha
       . exact Or.inl ht
       . exact Or.inr hacc
   . simp only [h,bFT,↓reduceIte,ww,lMM]
     tauto
lemma q23 {α:Type} [DecidableEq α] (l:List α) (x : α) :
   x ∈ q206 l ↔ x ∈ l:=by
 simpa [q206] using ww l [] x
def fix0A {n : ℕ} (A:List (Fin n)) (p:Fin n):List (Fin n) :=
 A.filter (·!=p)
def fix0E {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 E.filter (fun e => e.1!=p&&e.2!=p)
def nbrs {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 E.filterMap (fun e => if e.1==p then some e.2 else if e.2==p then some e.1 else none)
def fix1A {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 q206 (A++nbrs E p)
def fix1E {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 let A1:=fix1A A E p
 E.filter (fun e => e.1!=p&&e.2!=p&&!A1.contains e.1&&!A1.contains e.2)
def depCheck {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):Bool :=
 A.contains p ||
   (E.all (fun e => e.1!=e.2) &&
     E.any (fun e => (e.1==p&&!A.contains e.2)||(e.2==p&&!A.contains e.1)))
def isoCheck {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k)) (π:Fin n->Fin k):Bool :=
 E.all (fun e => Eb.any (fun e' => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1))) &&
 Eb.all (fun e' => E.any (fun e => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1)))
lemma q176 {n : ℕ} (A:List (Fin n)) (hnd:A.Nodup) :
   ∀ s : ℕ,HasCircuitSize n (gfn A []) s->A.length - 1<=s:=by
 intro s h
 have hd:=q117 n (gfn A []) A.toFinset (by
   intro i hi
   have hiA:i ∈ A:=List.mem_toFinset.1 hi
   refine ⟨fun _ => false,?_⟩
   have h0:gfn A [] (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A [] (Function.update (fun _ => false) i true)=true:=by
     simp only [gfn,List.any_nil,Bool.or_false,lAN]
     exact ⟨i,hiA,by simp⟩
   simpa [h0,h1]) s h
 rw [List.toFinset_card_of_nodup hnd] at hd
 omega
lemma q99 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n))
   (h:(!A.isEmpty||!E.isEmpty)=true) :
   ∃ x y:Fin n->Bool,gfn A E x≠gfn A E y:=by
 refine ⟨fun _ => false,fun _ => true,?_⟩
 have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
 have h1:gfn A E (fun _ => true)=true:=by
   cases A with
   | cons a t => simp [gfn]
   | nil =>
     cases E with
     | nil => simp at h
     | cons e t => simp [gfn]
 rw [h0,h1];decide
lemma q154 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (h:depCheck A E p=true) :
   ∃ x:Fin n->Bool,gfn A E (Function.update x p (!x p))≠gfn A E x:=by
 simp only [depCheck,bOT,bAT,List.contains_eq_mem,decide_eq_true_eq,
   lAL,lAN,bne_iff_ne,beq_iff_eq,bNT,
   decide_eq_false_iff_not] at h
 rcases h with hpA | ⟨hloop,⟨e,heE,⟨rfl,hqA⟩ | ⟨rfl,hqA⟩⟩⟩
 . refine ⟨fun _ => false,?_⟩
   have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A E (Function.update (fun _ => false) p true)=true:=by
     simp only [gfn,bOT,lAN]
     exact Or.inl ⟨p,hpA,by simp⟩
   simpa [h0,h1]
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.2),?_⟩
   have h0:gfn A E (fun i => decide (i=e.2))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.2)) e.1 (!decide (e.1=e.2)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [hne]
     . simp [fUN (Ne.symm hne)]
   rw [h0,h1];decide
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.1),?_⟩
   have h0:gfn A E (fun i => decide (i=e.1))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.1)) e.2 (!decide (e.2=e.1)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [fUN hne]
     . simp [Ne.symm hne]
   rw [h0,h1];decide
lemma zo {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n) :
   (fun x => gfn A E (Function.update x p false))=gfn (fix0A A p) (fix0E E p):=by
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix0A,fix0E,bOT,lAN,List.mem_filter,
   bAT,bne_iff_ne]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . by_cases hap:a=p
     . subst hap;simp at hxa
     . exact Or.inl ⟨a,⟨ha,hap⟩,by simpa [fUN hap] using hxa⟩
   . by_cases h1p:e.1=p
     . rw [h1p,fUS] at h1;cases h1
     . by_cases h2p:e.2=p
       . rw [h2p,fUS] at h2;cases h2
       . exact Or.inr ⟨e,⟨he,h1p,h2p⟩,
           by simpa [fUN h1p] using h1,
           by simpa [fUN h2p] using h2⟩
 . rintro (⟨a,⟨ha,hap⟩,hxa⟩ | ⟨e,⟨he,h1p,h2p⟩,h1,h2⟩)
   . exact Or.inl ⟨a,ha,by simpa [fUN hap] using hxa⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using h1,
       by simpa [fUN h2p] using h2⟩
lemma q109 {n : ℕ} (E:List (Fin n × Fin n)) (p q:Fin n) :
   q ∈ nbrs E p ↔ ∃ e ∈ E,(e.1=p/\e.2=q)\/(e.1≠p/\e.2=p/\e.1=q):=by
 simp only [nbrs,List.mem_filterMap,beq_iff_eq]
 constructor
 . rintro ⟨e,he,h⟩
   split_ifs at h with h1 h2
   . cases h;exact ⟨e,he,Or.inl ⟨h1,rfl⟩⟩
   . cases h;exact ⟨e,he,Or.inr ⟨h1,h2,rfl⟩⟩
 . rintro ⟨e,he,⟨h1,h2⟩ | ⟨h1,h2,h3⟩⟩
   . exact ⟨e,he,by rw [if_pos h1,h2]⟩
   . exact ⟨e,he,by rw [if_neg h1,if_pos h2,h3]⟩
lemma kx {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true) :
   (fun x => gfn A E (Function.update x p true))=gfn (fix1A A E p) (fix1E A E p):=by
 have hpnot:p ∉ A:=by simpa [List.contains_eq_mem] using hpA
 have hne:∀ e ∈ E,e.1≠e.2:=by simpa [lAL,bne_iff_ne] using hloop
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix1E,bOT,lAN,bAT,List.mem_filter,
   bne_iff_ne,bNT,List.contains_eq_mem,decide_eq_false_iff_not]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . have hap:a≠p:=fun h => hpnot (h ▸ ha)
     refine Or.inl ⟨a,?_,by simpa [fUN hap] using hxa⟩
     rw [fix1A,q23];exact List.mem_append_left _ ha
   . by_cases h1p:e.1=p
     . have h2p:e.2≠p:=fun h => hne e he (h1p.trans h.symm)
       refine Or.inl ⟨e.2,?_,by simpa [fUN h2p] using h2⟩
       rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.2).2 ⟨e,he,Or.inl ⟨h1p,rfl⟩⟩)
     . by_cases h2p:e.2=p
       . refine Or.inl ⟨e.1,?_,by simpa [fUN h1p] using h1⟩
         rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.1).2 ⟨e,he,Or.inr ⟨h1p,h2p,rfl⟩⟩)
       . have hx1:x e.1=true:=by simpa [fUN h1p] using h1
         have hx2:x e.2=true:=by simpa [fUN h2p] using h2
         by_cases m1:e.1 ∈ fix1A A E p
         . exact Or.inl ⟨e.1,m1,hx1⟩
         . by_cases m2:e.2 ∈ fix1A A E p
           . exact Or.inl ⟨e.2,m2,hx2⟩
           . exact Or.inr ⟨e,⟨he,⟨⟨h1p,h2p⟩,m1⟩,m2⟩,hx1,hx2⟩
 . rintro (⟨a,ha,hxa⟩ | ⟨e,⟨he,⟨⟨h1p,h2p⟩,_⟩,_⟩,hx1,hx2⟩)
   . rw [fix1A,q23,List.mem_append] at ha
     rcases ha with haA | han
     . have hap:a≠p:=fun h => hpnot (h ▸ haA)
       exact Or.inl ⟨a,haA,by simpa [fUN hap] using hxa⟩
     . obtain ⟨e,he,⟨h1,rfl⟩ | ⟨h1,h2,rfl⟩⟩:=(q109 E p a).1 han
       . have h2p:e.2≠p:=fun h => hne e he (h1.trans h.symm)
         exact Or.inr ⟨e,he,by simp [h1],by simpa [fUN h2p] using hxa⟩
       . exact Or.inr ⟨e,he,by simpa [fUN h1] using hxa,by simp [h2]⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using hx1,
       by simpa [fUN h2p] using hx2⟩
lemma q190 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hA:A'=fix0A A p) (hE:E'=fix0E E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p false))=gfn A' E':=by
   rw [hA,hE];exact zo A E p
 have hnc':∃ x y,gfn A E (Function.update x p false)≠gfn A E (Function.update y p false):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p false s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega
lemma q189 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA:A'=fix1A A E p) (hE:E'=fix1E A E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p true))=gfn A' E':=by
   rw [hA,hE];exact kx A E p hpA hloop
 have hnc':∃ x y,gfn A E (Function.update x p true)≠gfn A E (Function.update y p true):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p true s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega
lemma q155 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1))
   (A0:List (Fin (n+1))) (E0:List (Fin (n+1) × Fin (n+1)))
   (A1:List (Fin (n+1))) (E1:List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA0:A0=fix0A A p) (hE0:E0=fix0E E p)
   (hA1:A1=fix1A A E p) (hE1:E1=fix1E A E p)
   (hnc0:(!A0.isEmpty||!E0.isEmpty)=true)
   (hnc1:(!A1.isEmpty||!E1.isEmpty)=true)
   (ih0:∀ s,HasCircuitSize (n+1) (gfn A0 E0) s->k<=s)
   (ih1:∀ s,HasCircuitSize (n+1) (gfn A1 E1) s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+2<=s:=by
 intro s h
 have hres0:(fun x => gfn A E (Function.update x p false))=gfn A0 E0:=by
   rw [hA0,hE0];exact zo A E p
 have hres1:(fun x => gfn A E (Function.update x p true))=gfn A1 E1:=by
   rw [hA1,hE1];exact kx A E p hpA hloop
 have hnc:∀ b:Bool,∃ x y,gfn A E (Function.update x p b)≠gfn A E (Function.update y p b):=by
   intro b
   cases b with
   | false =>
     obtain ⟨x,y,hxy⟩:=q99 A0 E0 hnc0
     exact ⟨x,y,by simpa [congrFun hres0] using hxy⟩
   | true =>
     obtain ⟨x,y,hxy⟩:=q99 A1 E1 hnc1
     exact ⟨x,y,by simpa [congrFun hres1] using hxy⟩
 obtain ⟨b,s',hs',h'⟩:=q141 n (gfn A E) p s (q154 A E p hdep) hnc h
 cases b with
 | false => rw [hres0] at h';have:=ih0 s' h';omega
 | true => rw [hres1] at h';have:=ih1 s' h';omega
lemma q204 {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true) :
   (fun y:Fin k->Bool => gfn [] E (y ∘ π))=gfn [] Eb:=by
 simp only [isoCheck,bAT,lAL,lAN,
   bOT,beq_iff_eq] at hiso
 obtain ⟨h1,h2⟩:=hiso
 funext y
 apply Bool.eq_iff_iff.2
 simp only [gfn,List.any_nil,Bool.false_or,lAN,bAT,Function.comp_apply]
 constructor
 . rintro ⟨e,he,hy1,hy2⟩
   obtain ⟨e',he',⟨a,b⟩ | ⟨a,b⟩⟩:=h1 e he
   . exact ⟨e',he',a ▸ hy1,b ▸ hy2⟩
   . exact ⟨e',he',b ▸ hy2,a ▸ hy1⟩
 . rintro ⟨e',he',hy1,hy2⟩
   obtain ⟨e,he,⟨a,b⟩ | ⟨a,b⟩⟩:=h2 e' he'
   . exact ⟨e,he,a.symm ▸ hy1,b.symm ▸ hy2⟩
   . exact ⟨e,he,a.symm ▸ hy2,b.symm ▸ hy1⟩
lemma q191 {n k val : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true)
   (hb:∀ s : ℕ,HasCircuitSize k (gfn [] Eb) s->val<=s) :
   ∀ s : ℕ,HasCircuitSize n (gfn [] E) s->val<=s:=by
 intro s h
 have h':=yn π (gfn [] E) s h
 rw [q204 E Eb π hiso] at h'
 exact hb s h'
lemma q202 {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
   xs.length<=s+1:=by
 induction h using Run.fold with
 | done => simp
 | perm hp _ ih => rwa [← hp.length_eq]
 | one neg save h ih => cases save <;> simp_all [qk] <;> omega
 | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [qk] <;> omega
lemma q101 {m : ℕ} {g:Gate} (h:q161 m g):NOk g:=by
 rcases h with ⟨hop,j,_,hin⟩ | ⟨hop,j,k,_,_,hin⟩
 . exact ⟨⟨by simp [hop],by simp [hin]⟩,fun _ => by simp [hin]⟩
 . refine ⟨⟨?_,by simp [hin]⟩,fun hnot => ?_⟩
   . rcases hop with h1 | h1 <;> simp [h1]
   . rcases hop with h1 | h1 <;> rw [h1] at hnot <;> cases hnot
lemma ja {n : ℕ} {gs:List Gate} (h:yq n gs):∀ g ∈ gs,NOk g:=by
 intro g hg
 obtain ⟨p,hp,rfl⟩:=List.getElem_of_mem hg
 exact q101 (h p gs[p] (List.getElem?_eq_getElem hp))
lemma q157 {n : ℕ} {gs:List Gate} (h:yq n gs) (p : ℕ):yq n (gs.take p):=by
 intro q g hq
 have hlt:q < (gs.take p).length:=(List.getElem?_eq_some_iff.1 hq).1
 have hqp:q < p:=by simp at hlt;omega
 rw [List.getElem?_take_of_lt hqp] at hq
 exact h q g hq
def InvR (R : ℕ->Prop) (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length /\
 (∀ i : ℕ,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) /\
 (∀ i : ℕ,R i->ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false)
lemma q175 (R : ℕ->Prop) (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g) ->
     (∀ q g,gs[q]?=some g->R (acc.1.length+q)->∀ a ∈ g.inputs,R a) ->
     InvR R n y w acc ->
     InvR R n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ _ h;exact h
 | cons g gs ih =>
   intro w acc hok hR h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   . intro q g' hq hRq a ha
     have hlen:(qa n acc g).1.length=acc.1.length+1:=by simp [qa]
     rw [hlen] at hRq
     exact hR (q+1) g' (by simpa using hq) (by simpa [nAA,nAC 1 q] using hRq) a ha
   . obtain ⟨hl,hv,he⟩:=h
     set w':=q3 acc.2 y with hw'
     have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         rw [lw'];exact hv a)
     rw [lw'] at hs
     set r:=qg g.op (n+acc.2.length) ins with hr
     have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
       rw [zd]
     obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
     refine ⟨by simp [qa,hl],?_,?_⟩
     . intro i
       show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false))
       rw [lLA,← nAA]
       by_cases hil:i=acc.1.length
       . subst hil;rw [z0];exact hs.1
       . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
     . intro i hi
       show ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
       rw [hnew]
       by_cases hil:i=acc.1.length
       . subst hil
         rw [z0,hl,z0,hs.2]
         congr 1
         rw [hins,lMMp]
         apply List.map_congr_left
         intro a ha
         exact he a (hR 0 g rfl (by simpa using hi) a ha)
       . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
         rw [ht,jg _ _ _ (by rw [lw'];exact hv i)]
         exact he i hi
lemma y7 (n : ℕ) (f:BFn n) (pre post:List Gate) (g:Gate) (o : ℕ)
   (hcl:yq n (pre++g::post)) (ho:o < n+(pre++g::post).length)
   (hev:∀ x,val (pre++g::post) n o x=f x)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (st:Stat) (hstV:qn (n+pre.length) st)
   (hcond:(∀ x,ze (q3 pre (List.ofFn x)) st=val (pre++g::post) n (n+pre.length) x) \/
            ¬ wn n (pre++g::post) o (n+pre.length)) :
   ∃ gs' o',yq n gs'/\gs'.length<=pre.length+post.length /\
     o' < n+gs'.length/\∀ x,val gs' n o' x=f x:=by
 set gs:=pre++g::post with hgs
 set p:=pre.length with hp
 set acc0:List Stat × List Gate:=(vi (n+p)++[st],pre) with hacc0
 set acc:=elim n post acc0 with hacc
 have hok_post:∀ g' ∈ post,Ok g':=fun g' hg' =>
   (ja hcl g' (List.mem_append_right _ (List.mem_cons_of_mem _ hg'))).1
 have hcl_pre:yq n pre:=by
   have:pre=gs.take p:=by simp [hgs,hp]
   rw [this];exact q157 hcl p
 have hv0:∀ i,qn (n+acc0.2.length) (acc0.1.getD i (Sum.inl false)):=by
   intro i
   simp only [hacc0,hp]
   by_cases hip:i=n+pre.length
   . subst hip;rw [z2 _ _ _ _ (by simp [vi])];exact hstV
   . rw [q8 _ _ _ _ (by simp [vi];omega)]
     by_cases hlt:i < n+pre.length
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
 have hcl':yq n acc.2:=q100 n post acc0 hok_post hv0 hcl_pre
 have hlen':acc.2.length<=pre.length+post.length:=by
   simpa [hacc,hacc0] using q29 n post acc0
 have hinv_all:∀ x:Fin n->Bool,
     qn (n+acc.2.length) (acc.1.getD o (Sum.inl false)) /\
     ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))=f x:=by
   intro x
   have hsplit:q3 gs (List.ofFn x)=q3 post (q3 (pre++[g]) (List.ofFn x)):=by
     have:gs=(pre++[g])++post:=by simp [hgs]
     rw [this,zd]
   have hl1:(q3 (pre++[g]) (List.ofFn x)).length=n+p+1:=by
     rw [qu];simp [hp];omega
   have hval_lt:∀ i < n+p,(q3 (pre++[g]) (List.ofFn x)).getD i false =
       (q3 pre (List.ofFn x)).getD i false:=by
     intro i hi
     rw [zd,ve _ _ _ (by rw [qu];simp;omega)]
   rcases hcond with hval_eq | hdead
   . have hinv0:Inv n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],?_⟩
       intro i
       refine ⟨hv0 i,?_⟩
       simp only [hacc0]
       by_cases hip:i=n+p
       . subst hip
         rw [z2 _ _ _ _ (by simp [vi])]
         have h1:=hval_eq x
         unfold val at h1
         rw [hsplit,ve _ _ _ (by omega)] at h1
         exact h1
       . rw [q8 _ _ _ _ (by simp [vi];omega)]
         by_cases hlt:i < n+p
         . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
             Option.getD_some,ze]
           exact (hval_lt i hlt).symm
         . rw [lGD _ _ (by simp [vi];omega),
               lGD _ _ (by omega)];rfl
     have hres:=j7 n (List.ofFn x) (by simp) post _ acc0 hok_post hinv0
     rw [← hsplit] at hres
     have h1:=hres.2 o
     exact ⟨h1.1,h1.2.trans (hev x)⟩
   . have hinv0:InvR (wn n gs o) n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],hv0,?_⟩
       intro i hi
       simp only [hacc0]
       have hne:i≠n+p:=fun e => hdead (e ▸ hi)
       rw [q8 _ _ _ _ (by simp [vi];omega)]
       by_cases hlt:i < n+p
       . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
           Option.getD_some,ze]
         exact (hval_lt i hlt).symm
       . rw [lGD _ _ (by simp [vi];omega),
             lGD _ _ (by omega)];rfl
     have hR:∀ q g',post[q]?=some g'->wn n gs o (acc0.1.length+q)->∀ a ∈ g'.inputs,wn n gs o a:=by
       intro q g' hq hRq a ha
       have hidx:gs[p+1+q]?=some g':=by
         have:gs=(pre++[g])++post:=by simp [hgs]
         rw [this,List.getElem?_append_right (by simp [hp])]
         simpa [hp,Nat.add_sub_cancel_left] using hq
       have hlen0:acc0.1.length=n+p+1:=by simp [hacc0,vi]
       rw [hlen0] at hRq
       exact q33 hidx (by simpa [nAA] using hRq) ha
     have hres:=q175 (wn n gs o) n (List.ofFn x) (by simp) post _ acc0 hok_post hR hinv0
     rw [← hsplit] at hres
     exact ⟨hres.2.1 o,(hres.2.2 o (q34 n gs o)).trans (hev x)⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=(hinv_all y).2
   have e2:=(hinv_all y').2
   rw [hst] at e1 e2
   exact e1.symm.trans e2
 | inr j =>
   obtain ⟨y,_,_⟩:=hnc
   have hj:=(hinv_all y).1
   rw [hst] at hj
   refine ⟨acc.2,j,hcl',hlen',hj,?_⟩
   intro x
   have e:=(hinv_all x).2
   rw [hst] at e
   exact e
structure MinClean (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ):Prop where
 hcl:yq n gs
 ho:o < n+gs.length
 hev:∀ x,val gs n o x=f x
 hreach:∀ p < gs.length,wn n gs o (n+p)
 hncG:∀ p < gs.length,∀ c:Bool,val gs n (n+p)≠fun _ => c
 hndup:∀ p < gs.length,∀ u < n+p,val gs n (n+p)≠val gs n u
open Classical in
lemma q56 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,MinClean n f gs o/\gs.length<=s:=by
 have hex:∃ k,∃ gs o,yq n gs/\gs.length=k/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
   obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=q48 n f s hnc h
   exact ⟨gs.length,gs,o,hcl,rfl,ho,hev⟩
 set k:=Nat.find hex with hk
 obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=Nat.find_spec hex
 have hle:k<=s:=by
   obtain ⟨gs0,o0,hcl0,hlen0,ho0,hev0⟩:=q48 n f s hnc h
   exact le_trans (Nat.find_min' hex ⟨gs0,o0,hcl0,rfl,ho0,hev0⟩) hlen0
 have hmin:∀ gs' o',yq n gs'->o' < n+gs'.length->(∀ x,val gs' n o' x=f x)->gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev'
   rw [hlen]
   exact Nat.find_min' hex ⟨gs',o',hcl',rfl,ho',hev'⟩
 refine ⟨gs,o,⟨hcl,ho,hev,?_,?_,?_⟩,by omega⟩
 . intro p hp
   by_contra hnr
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl false) trivial (Or.inr hnr)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp c heqc
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl c) trivial
       (Or.inl fun x => by rw [heqc];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp u hu hequ
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inr u) hu
       (Or.inl fun x => by
         rw [hequ];unfold val
         rw [zd,ve _ _ _ (by rw [qu];simp;omega)];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
def wf (n : ℕ) (v:Fin n):List Stat :=
 List.ofFn fun i:Fin n => if i=v then Sum.inl false else Sum.inr (i : ℕ)
lemma q139 (n : ℕ) (v:Fin n) (x:Fin n->Bool) :
   Inv n (List.ofFn x) (List.ofFn (Function.update x v false)) (wf n v,[]):=by
 refine ⟨by simp [wf],?_⟩
 intro i
 by_cases hlt:i < n
 . by_cases hiv:(⟨i,hlt⟩:Fin n)=v
   . subst hiv;simp [wf,hlt,qn,ze]
   . simp [wf,hlt,hiv,qn,ze,q3,fUN hiv]
 . rw [lGD _ _ (by simp [wf];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma wz (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (v:Fin n) (B : ℕ)
   (hcl:yq n gs) (hev:∀ x,val gs n o x=f x)
   (hnc0:∃ x y:Fin n->Bool,f (Function.update x v false)≠f (Function.update y v false))
   (hlb:∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->B<=s') :
   (∀ c,(elim n gs (wf n v,[])).1.getD o (Sum.inl false)≠Sum.inl c) /\
   B<=(elim n gs (wf n v,[])).2.length:=by
 set acc:=elim n gs (wf n v,[]) with hacc
 have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) acc :=
   fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hcl g hg).1) (q139 n v x)
 have hval:∀ x,ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))
     = f (Function.update x v false):=fun x => ((hinv x).2 o).2.trans (hev _)
 have hno:∀ c,acc.1.getD o (Sum.inl false)≠Sum.inl c:=by
   intro c hc
   obtain ⟨x,y,hne⟩:=hnc0
   apply hne
   rw [← hval x,← hval y,hc];rfl
 refine ⟨hno,?_⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c => exact absurd hst (hno c)
 | inr j =>
   apply hlb acc.2.length
   refine ⟨⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro x;have:=hval x;rw [hst] at this;exact this
lemma k3 (n u w : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->u < acc.1.length->w < acc.1.length ->
   (∃ cu,acc.1.getD u (Sum.inl false)=Sum.inl cu) ->
   (∃ cw,acc.1.getD w (Sum.inl false)=Sum.inl cw) ->
   (∃ g₁ ∈ gs,u ∈ g₁.inputs) ->
   (∃ g₂ ∈ gs,w ∈ g₂.inputs) ->
   (∀ g ∈ gs,¬ (u ∈ g.inputs/\w ∈ g.inputs)) ->
   (elim n gs acc).2.length+2<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ _ _ h1 _ _;obtain ⟨g,hg,_⟩:=h1;simp at hg
 | cons g gs ih =>
   intro acc hok hu hw hcu hcw hg1 hg2 hdisj
   rw [k4,lLC]
   have hgn:NOk g:=hok g List.mem_cons_self
   have hgsn:∀ g' ∈ gs,NOk g':=fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
   by_cases hug:u ∈ g.inputs
   . have hwg:w ∉ g.inputs:=fun h => hdisj g List.mem_cons_self ⟨hug,h⟩
     obtain ⟨cu,hcu⟩:=hcu
     have h0:=vs n acc g hgn u hug cu hcu
     have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
       obtain ⟨g',hg',hw'⟩:=hg2
       rcases List.mem_cons.1 hg' with rfl | hmem
       . exact absurd hw' hwg
       . exact ⟨g',hmem,hw'⟩
     have h1:=zt n w gs (qa n acc g) hgsn (by simp [qa];omega)
       (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
       hg2'
     omega
   . by_cases hwg:w ∈ g.inputs
     . obtain ⟨cw,hcw⟩:=hcw
       have h0:=vs n acc g hgn w hwg cw hcw
       have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have h1:=zt n u gs (qa n acc g) hgsn (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         hg1'
       omega
     . have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
         obtain ⟨g',hg',hw'⟩:=hg2
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hw' hwg
         . exact ⟨g',hmem,hw'⟩
       have h1:=ih (qa n acc g) hgsn (by simp [qa];omega) (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
         hg1' hg2' (fun g' hg' => hdisj g' (List.mem_cons_of_mem _ hg'))
       have h2:(qa n acc g).2.length<=acc.2.length+1:=by
         simp only [qa,lLA]
         have:=y2 (qg g.op (n+acc.2.length)
           (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
         omega
       omega
inductive TagRun {α:Type} (inv : α->α) (meet join : α->α->α) (zero one goal : α) :
   ℕ->List (α × ℕ)->Prop where
 | done (tg : ℕ):TagRun inv meet join zero one goal 0 [(goal,tg)]
 | perm {s xs zs}:List.Perm xs zs ->
     TagRun inv meet join zero one goal s xs ->
     TagRun inv meet join zero one goal s zs
 | uNot {s a ta r} (save:Bool) :
     ta≠1->ta≠2->(ta=3->save=false) ->
     inv a≠zero->inv a≠one->inv a≠a->(∀ x ∈ r,x.1≠inv a) ->
     TagRun inv meet join zero one goal s
       ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Bool) :
     ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
     join a b≠zero->join a b≠one ->
     join a b≠a->join a b≠b->(∀ x ∈ r,x.1≠join a b) ->
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Bool) :
     ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
     meet a b≠zero->meet a b≠one ->
     meet a b≠a->meet a b≠b->(∀ x ∈ r,x.1≠meet a b) ->
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
lemma TagRun.toRun {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   Run inv meet join goal s (ws.map Prod.fst):=by
 induction h with
 | done _ => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map Prod.fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   have e:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst)
       = (if true then inv a else a)::qk save a (r.map Prod.fst):=by
     cases save <;> simp [qk]
   rw [e] at ih
   exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst)
       = (if false then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map Prod.fst)
       = (if true then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two true ka kb ih
lemma TagRun.len_le {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   ws.length<=s+1:=by
 have:=q202 h.toRun
 simpa using this
lemma TagRun.map {α β:Type} (e : α->β) (hinj:Function.Injective e)
   {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {inv' : β->β} {meet' join' : β->β->β} {zero' one' goal' : β}
   (h0:e zero=zero') (h1:e one=one') (hg:e goal=goal')
   (hi:∀ a,e (inv a)=inv' (e a))
   (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   TagRun inv' meet' join' zero' one' goal' s (ws.map fun p => (e p.1,p.2)):=by
 induction h with
 | done tg => rw [← hg];exact TagRun.done tg
 | perm hp _ ih => exact TagRun.perm (hp.map _) ih
 | @uNot s a ta r save h1t h2t h3t hnz hno hna hnr _ ih =>
   have e1:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fun p => (e p.1,p.2))
       = (inv' (e a),if ta=3 then 2 else 0)::qk save (e a,0) (r.map fun p => (e p.1,p.2)):=by
     cases save <;> simp [qk,hi]
   rw [e1] at ih
   refine TagRun.uNot save h1t h2t h3t ?_ ?_ ?_ ?_ ih
   . rw [← hi,← h0];exact fun h => hnz (hinj h)
   . rw [← hi,← h1];exact fun h => hno (hinj h)
   . rw [← hi];exact fun h => hna (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hi];exact fun h => hnr y hy (hinj h)
 | @bOr s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fun p => (e p.1,p.2))
       = (join' (e a) (e b),0)::qk ka (e a,if ta=3 then 1 else 0) (qk kb (e b,if tb=3 then 1 else 0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hj]
   rw [e1] at ih
   refine TagRun.bOr ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hj,← h0];exact fun h => hnz (hinj h)
   . rw [← hj,← h1];exact fun h => hno (hinj h)
   . rw [← hj];exact fun h => hna (hinj h)
   . rw [← hj];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hj];exact fun h => hnr y hy (hinj h)
 | @bAnd s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fun p => (e p.1,p.2))
       = (meet' (e a) (e b),if ta=3\/tb=3 then 1 else 0)::qk ka (e a,0) (qk kb (e b,0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hm]
   rw [e1] at ih
   refine TagRun.bAnd ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hm,← h0];exact fun h => hnz (hinj h)
   . rw [← hm,← h1];exact fun h => hno (hinj h)
   . rw [← hm];exact fun h => hna (hinj h)
   . rw [← hm];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hm];exact fun h => hnr y hy (hinj h)
def v3 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ):List Stat × List Gate :=
 elim n (gs.take p) (wf n v,[])
lemma vb (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (hp:p<=gs.length) :
   (v3 n gs v p).1.length=n+p:=by
 unfold v3
 rw [q50]
 simp [wf,List.length_take,Nat.min_eq_left hp]
lemma q30 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (g:Gate) (hg:gs[p]?=some g) :
   v3 n gs v (p+1)=qa n (v3 n gs v p) g:=by
 unfold v3
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 rw [List.take_succ_eq_append_getElem hlt,hge,jz,k4]
 rfl
lemma zj (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) :
   elim n (gs.drop p) (v3 n gs v p)=elim n gs (wf n v,[]):=by
 unfold v3
 rw [← jz,List.take_append_drop]
def yf (n : ℕ) (gs:List Gate) (f:BFn n) (p a tg : ℕ):Prop :=
 match tg with
 | 0 => True
 | 1 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 2 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl true /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 3 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+2
 | _ => False
lemma q12 {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ}
   (h:yf n gs f p a tg):tg<=3:=by
 match tg with
 | 0 | 1 | 2 | 3 => omega
 | _+4 => exact False.elim h
lemma vv {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ} {g:Gate}
   (hg:gs[p]?=some g) (ha:a < n+p) (h:yf n gs f p a tg) :
   yf n gs f (p+1) a tg:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 have hdrop:gs.drop p=g::gs.drop (p+1):=by rw [List.drop_eq_getElem_cons hlt,hge]
 have step_aux:∀ v c B,
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl c ->
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
     (v3 n gs v (p+1)).1.getD a (Sum.inl false)=Sum.inl c /\
     (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length <=
       (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
   intro v c B hget hbd
   have hsucc:=q30 n gs v p g hg
   have hfl:=vb n gs v p (by omega)
   constructor
   . rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
   . have heq:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
       rw [zj,zj]
     have hlen2:(v3 n gs v (p+1)).2.length<=(v3 n gs v p).2.length+1:=by
       rw [hsucc];simp only [qa,lLA]
       have:=y2 (qg g.op (n+(v3 n gs v p).2.length)
         (g.inputs.map fun i => (v3 n gs v p).1.getD i (Sum.inl false))).1
       omega
     have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
     rw [heq];omega
 match tg with
 | 0 => trivial
 | 1 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 1 hget hbd⟩
 | 2 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v true 1 hget hbd⟩
 | 3 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 2 hget hbd⟩
 | _+4 => exact False.elim h
lemma zr {n : ℕ} {gs:List Gate} {o p u : ℕ} {f:BFn n} {v:Fin n} {c:Bool}
   (hm:MinClean n f gs o) (hp:p<=gs.length)
   (hlive:u ∈ liveList gs n o p)
   (hnc:∃ x y,f (Function.update x v false)≠f (Function.update y v false))
   (hconst:(v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c) :
   ∃ g' ∈ gs.drop p,u ∈ g'.inputs:=by
 have ⟨hlt,hl⟩:=(qw gs n o p u).1 hlive
 rcases hl with rfl | ⟨q,hq,g',hg',hin,_⟩
 . exfalso
   have hfl:=vb n gs v p hp
   have heq:(elim n gs (wf n v,[])).1.getD u (Sum.inl false)=Sum.inl c:=by
     rw [← zj n gs v p,wy n u _ _ _ (by omega)];exact hconst
   have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) (elim n gs (wf n v,[])) :=
     fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hm.hcl g hg).1) (q139 n v x)
   obtain ⟨x,y,hne⟩:=hnc
   apply hne
   have e1:=((hinv x).2 u).2.trans (hm.hev _)
   have e2:=((hinv y).2 u).2.trans (hm.hev _)
   rw [heq] at e1 e2
   exact e1.symm.trans e2
 . have hqlt:q < gs.length:=(List.getElem?_eq_some_iff.1 hg').1
   have hqeq:gs[q]=g':=(List.getElem?_eq_some_iff.1 hg').2
   refine ⟨g',?_,hin⟩
   have:g'=(gs.drop p)[q - p]'(by simp;omega):=by
     rw [List.getElem_drop];simp [show p+(q - p)=q by omega,hqeq]
   rw [this]
   exact List.getElem_mem _
lemma q21 {n : ℕ} {gs:List Gate} {o p j : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length)
   (hval:∀ x,val gs n (n+p) x=!(val gs n j x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by
   intro e;have h0:=hval (fun _ => false);rw [e] at h0
   cases hv:val gs n (n+p) (fun _ => false) <;> rw [hv] at h0 <;> cases h0
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;exact hne (hj.trans hnp.symm)
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hncG q hrlt false
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hncG q hrlt true
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
lemma q22 {n : ℕ} {gs:List Gate} {o p j k : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length) (hjlt:j < n+p)
   (hval:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by omega
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;omega
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hndup q hrlt (n+p) (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hndup q hrlt j (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
lemma q193 {n : ℕ} {gs:List Gate} (hcl:yq n gs) (p : ℕ) :
   ∀ g ∈ gs.drop p,NOk g:=fun g hg => ja hcl g (List.mem_of_mem_drop hg)
open Classical in
lemma q123 (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (hm:MinClean n f gs o) :
   ∀ d p,p+d=gs.length ->
     ∀ tg : ℕ->ℕ,(∀ a ∈ liveList gs n o p,yf n gs f p a (tg a)) ->
       TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f d
         ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
 intro d
 induction d with
 | zero =>
   intro p hp tg _
   have hperm : [o].Perm (liveList gs n o p):=by
     refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
     intro a
     rw [qw,List.mem_singleton]
     constructor
     . rintro rfl;exact ⟨by have:=hm.ho;omega,Or.inl rfl⟩
     . rintro ⟨_,h | ⟨q,hq,g',hg',_,_⟩⟩
       . exact h
       . have:=(List.getElem?_eq_some_iff.1 hg').1;omega
   have hf:val gs n o=f:=funext hm.hev
   have h1:([(f,tg o)]).Perm ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
     rw [← hf];exact hperm.map (fun a => (val gs n a,tg a))
   exact TagRun.perm h1 (TagRun.done (tg o))
 | succ d ih =>
   intro p hp tg hok
   have hplt:p < gs.length:=by omega
   obtain ⟨g,hg⟩:∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hplt⟩
   have hr:wn n gs o (n+p):=hm.hreach p hplt
   have hstep:=q73 n gs o hm.hcl p g hg hr
   have hin:∀ a ∈ g.inputs,a ∈ liveList gs n o p:=fun a ha =>
     (qw _ _ _ _ _).2 ⟨j2 (hm.hcl p g hg) a ha,Or.inr ⟨p,le_rfl,g,hg,ha,hr⟩⟩
   have hnew:∀ a ∈ liveList gs n o p,a≠n+p:=fun a ha =>
     Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
   have hvg:=q103 n gs p g hg (j2 (hm.hcl p g hg))
   have hnd0:=vy gs n o p
   have hdrop:gs.drop p=g::gs.drop (p+1):=by
     rw [List.drop_eq_getElem_cons hplt];have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2;rw [hge]
   have hgn:NOk g:=q101 (hm.hcl p g hg)
   have hdrop_nok:=q193 hm.hcl (p+1)
   have hnz:val gs n (n+p)≠fun _ => false:=hm.hncG p hplt false
   have hno:val gs n (n+p)≠fun _ => true:=hm.hncG p hplt true
   have hnd:∀ a ∈ liveList gs n o p,val gs n a≠val gs n (n+p):=fun a ha e =>
     hm.hndup p hplt a ((qw _ _ _ _ _).1 ha).1 e.symm
   rcases hm.hcl p g hg with ⟨hop,j,hj,hinp⟩ | ⟨hop,j,k,hj,hk,hinp⟩
   ·
     have hjm:j ∈ liveList gs n o p:=hin j (by simp [hinp])
     have hval:val gs n (n+p)=invF (val gs n j):=by
       funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
     have hsave_not:∀ v c B,
         (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
         (v3 n gs v p).1.getD j (Sum.inl false)=Sum.inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
         2<=B /\
         (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c) /\
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (q11 n gs o (p+1) j->3<=B):=by
       intro v c B hncv hget hbd
       have hsucc:=q30 n gs v p g hg
       have hfl:=vb n gs v p (by omega)
       have hfl1:=vb n gs v (p+1) (by omega)
       have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
         rw [hsucc];exact vs n _ g hgn j (by simp [hinp]) c hget
       have hout_c:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c):=by
         rw [hsucc];simp only [qa]
         rw [z2 _ _ _ _ hfl,hop,hinp]
         simp only [lMC,List.map_nil,hget,qg,wr]
       have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
         rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
       have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw [heq_e,h0];omega
       have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
       have hread_np:=zr hm (by omega) hnp_live hncv hout_c
       have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
         (by omega) ⟨!c,hout_c⟩ hread_np
       refine ⟨by omega,hout_c,hbd1,?_⟩
       intro hjlive
       have hj_live1:j ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hjlive⟩
       have hj_c1:(v3 n gs v (p+1)).1.getD j (Sum.inl false)=Sum.inl c:=by
         rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
       have hread_j:=zr hm (by omega) hj_live1 hncv hj_c1
       have hdisj:=q21 hm hplt (fun x => congrFun hval x)
       have hkill2:=k3 n j (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
         hdrop_nok (by omega) (by omega) ⟨c,hj_c1⟩ ⟨!c,hout_c⟩ hread_j hread_np hdisj
       omega
     have ht1:tg j≠1:=by
       intro h1;have hw:=hok j hjm;rw [h1] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 1 hncv hget hbd).1;omega
     have ht2:tg j≠2:=by
       intro h2;have hw:=hok j hjm;rw [h2] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v true 1 hncv hget hbd).1;omega
     have ht3:tg j=3->decide (q11 n gs o (p+1) j)=false:=by
       intro h3;simp only [decide_eq_false_iff_not];intro hjlive
       have hw:=hok j hjm;rw [h3] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 2 hncv hget hbd).2.2.2 hjlive;omega
     set tg' : ℕ->ℕ:=fun a =>
       if a=n+p then (if tg j=3 then 2 else 0)
       else if a=j then 0
       else tg a
     have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
       intro a ha
       simp only [tg']
       by_cases hanp:a=n+p
       . subst hanp;simp only [↓reduceIte]
         by_cases h3:tg j=3
         . simp only [h3,↓reduceIte]
           have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           obtain ⟨_,hout_c,hbd1,_⟩:=hsave_not v false 2 hncv hget hbd
           exact ⟨v,hncv,hout_c,by omega⟩
         . simp only [h3,↓reduceIte];trivial
       . simp only [hanp,↓reduceIte]
         by_cases haj:a=j
         . simp only [haj,↓reduceIte];trivial
         . simp only [haj,↓reduceIte]
           have ha0:a ∈ liveList gs n o p:=by
             rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
             . exact absurd rfl hanp
             . exact h1
           exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
     have IH:=ih (p+1) (by omega) tg' hok'
     have hp1:(liveList gs n o p).Perm (j::(liveList gs n o p).erase j):=List.perm_cons_erase hjm
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
         rw [wa];rintro (⟨_,h⟩ | h)
         . exact hnew j hjm h.symm
         . exact hnew _ (List.mem_of_mem_erase h) rfl
       . intro a
         rw [hstep a,lMM,wa,hnd0.mem_erase_iff,hinp,List.mem_singleton]
         simp only [decide_eq_true_eq]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 haj,haj⟩)
             . exact Or.inr (Or.inr ⟨haj,h1⟩)
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,h2⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨h2,fun h => absurd h h1⟩
     have hmap_rest:((liveList gs n o p).erase j).map (fun a => (val gs n a,tg' a)) =
         ((liveList gs n o p).erase j).map (fun a => (val gs n a,tg a)):=by
       apply List.map_congr_left
       intro a ha
       have h1:a≠j:=(hnd0.mem_erase_iff.1 ha).1
       have h2:a≠n+p:=hnew a (List.mem_of_mem_erase ha)
       simp [tg',h1,h2]
     have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)).map (fun a => (val gs n a,tg' a)) =
         qk (decide (q11 n gs o (p+1) j)) (val gs n j,0) (((liveList gs n o p).erase j).map fun a => (val gs n a,tg a)):=by
       rw [wd,hmap_rest]
       have hjne:j≠n+p:=by omega
       simp [tg',hjne]
     have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
     rw [lMC,hmap_kept,hval] at IH'
     have htgnp:tg' (n+p)=(if tg j=3 then 2 else 0):=by simp [tg']
     rw [htgnp] at IH'
     refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
     refine TagRun.uNot (decide (q11 n gs o (p+1) j)) ht1 ht2 ht3
       (hval ▸ hnz) (hval ▸ hno) (fun e => hnd j hjm (hval ▸ e.symm)) ?_ IH'
     intro x hx
     obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
     exact hval ▸ hnd a (List.mem_of_mem_erase ha)
   ·
     have hjk:j≠k:=by
       intro e;subst e
       apply hm.hndup p hplt j hj
       funext x;rw [hvg x,hinp]
       rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
     have hjm:=hin j (by simp [hinp])
     have hkm:=hin k (by simp [hinp])
     have hke:k ∈ (liveList gs n o p).erase j:=(hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm,hkm⟩
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hnr2:(((liveList gs n o p).erase j).erase k).Nodup:=hnr.erase k
     have hp1:(liveList gs n o p).Perm (j::k::((liveList gs n o p).erase j).erase k) :=
       (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
     have hmr:∀ a,a ∈ ((liveList gs n o p).erase j).erase k ↔ a≠k/\a≠j/\a ∈ liveList gs n o p:=by
       intro a;rw [hnr.mem_erase_iff,hnd0.mem_erase_iff]
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k
             (((liveList gs n o p).erase j).erase k))):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ (q36 _ _ _ hnr2 ?_) ?_⟩
         . rw [wa,wa]
           rintro (⟨_,h⟩ | ⟨_,h⟩ | h)
           . exact hnew j hjm h.symm
           . exact hnew k hkm h.symm
           . exact hnew _ ((hmr _).1 h).2.2 rfl
         . rw [hmr];simp
         . rw [wa,hmr]
           rintro (⟨_,h⟩ | h)
           . exact hjk h
           . exact h.2.1 rfl
       . intro a
         rw [hstep a,lMM,wa,wa,hmr a]
         simp only [decide_eq_true_eq,hinp,lMM,List.not_mem_nil,or_false]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj),haj⟩)
             . by_cases hak:a=k
               . exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak),hak⟩))
               . exact Or.inr (Or.inr (Or.inr ⟨hak,haj,h1⟩))
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,rfl⟩ | ⟨h1,h2,h3⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨hkm,fun _ => h1⟩
           . exact Or.inr ⟨h3,fun h => by rcases h with h | h <;> contradiction⟩
     rcases hop with hop | hop
     ·
       have hval:val gs n (n+p)=meetF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hand_const:∀ (u w_other : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (hval_u:∀ x,val gs n (n+p) x=(val gs n u x&&val gs n w_other x))
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=false ->
             2<=B /\
             (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false /\
             (q11 n gs o (p+1) u->3<=B)) /\
           (c=true->q11 n gs o (p+1) u->2<=B):=by
         intro u wo hu hult hvalu v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hbd1,?_,?_⟩
         . intro hcf;subst hcf
           have hout_f:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ko]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ko]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_f
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hout_f⟩ hread_np
           refine ⟨by omega,hout_f,?_⟩
           intro hulive
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hdisj:=q22 hm hplt hult hvalu
           have hkill2:=k3 n u (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
             hdrop_nok (by omega) (by omega) ⟨false,hu_c1⟩ ⟨false,hout_f⟩ hread_u hread_np hdisj
           omega
         . intro hct hulive;subst hct
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hu_c1⟩ hread_u
           omega
       have hval_j:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x):=fun x => congrFun hval x
       have hval_k:∀ x,val gs n (n+p) x=(val gs n k x&&val gs n j x):=fun x => by
         rw [hval_j x,Bool.and_comm]
       have hta1:tg j≠1:=by
         intro h1;have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const j k (by simp [hinp]) hj hval_j v false 1 hncv hget hbd).2.1 rfl
         omega
       have htb1:tg k≠1:=by
         intro h1;have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const k j (by simp [hinp]) hk hval_k v false 1 hncv hget hbd).2.1 rfl
         omega
       have hta_save:tg j=1\/tg j=2\/tg j=3->decide (q11 n gs o (p+1) j)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hjlive
         rcases h123 with h1 | h2 | h3
         . exact hta1 h1
         . have hw:=hok j hjm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const j k (by simp [hinp]) hj hval_j v true 1 hncv hget hbd).2.2 rfl hjlive;omega
         . have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd).2.1 rfl).2.2 hjlive;omega
       have htb_save:tg k=1\/tg k=2\/tg k=3->decide (q11 n gs o (p+1) k)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hklive
         rcases h123 with h1 | h2 | h3
         . exact htb1 h1
         . have hw:=hok k hkm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const k j (by simp [hinp]) hk hval_k v true 1 hncv hget hbd).2.2 rfl hklive;omega
         . have hw:=hok k hkm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd).2.1 rfl).2.2 hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then (if tg j=3\/tg k=3 then 1 else 0)
         else if a=j\/a=k then 0
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . subst hanp;simp only [↓reduceIte]
           by_cases h3:tg j=3\/tg k=3
           . simp only [h3,↓reduceIte]
             rcases h3 with hj3 | hk3
             . have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
             . have hw:=hok k hkm;rw [hk3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
           . simp only [h3,↓reduceIte];trivial
         . simp only [hanp,↓reduceIte]
           by_cases hajk:a=j\/a=k
           . simp only [hajk,↓reduceIte];trivial
           . simp only [hajk,↓reduceIte]
             have ha0:a ∈ liveList gs n o p:=by
               rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
               . exact absurd rfl hanp
               . exact h1
             exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         simp [tg',hjne,hkne]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=(if tg j=3\/tg k=3 then 1 else 0):=by simp [tg']
       rw [htgnp] at IH'
       have hjle3:=q12 (hok j hjm)
       have hkle3:=q12 (hok k hkm)
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bAnd (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta1 htb1 (fun h => hta_save (by omega)) (fun h => htb_save (by omega))
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
     ·
       have hval:val gs n (n+p)=joinF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hor_const:∀ (u : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c /\
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=true->2<=B) /\
           (c=false->q11 n gs o (p+1) u->2<=B):=by
         intro u hu hult v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hu_c1,hbd1,?_,?_⟩
         . intro hct;subst hct
           have hout_t:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl true:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ji]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ji]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_t
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hout_t⟩ hread_np
           omega
         . intro hcf hulive;subst hcf
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hu_c1⟩ hread_u
           omega
       have hta2:tg j≠2:=by
         intro h2;have hw:=hok j hjm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v true 1 hncv hget hbd).2.2.1 rfl;omega
       have htb2:tg k≠2:=by
         intro h2;have hw:=hok k hkm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v true 1 hncv hget hbd).2.2.1 rfl;omega
       have hta1:tg j=1->decide (q11 n gs o (p+1) j)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hjlive
         have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v false 1 hncv hget hbd).2.2.2 rfl hjlive;omega
       have htb1:tg k=1->decide (q11 n gs o (p+1) k)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hklive
         have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v false 1 hncv hget hbd).2.2.2 rfl hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then 0
         else if a=j then (if tg j=3 then 1 else 0)
         else if a=k then (if tg k=3 then 1 else 0)
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . simp [hanp,yf]
         . simp only [hanp,↓reduceIte]
           by_cases haj:a=j
           . rw [haj];simp only [↓reduceIte]
             by_cases hj3:tg j=3
             . simp only [hj3,↓reduceIte]
               have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hor_const j (by simp [hinp]) hj v false 2 hncv hget hbd
               exact ⟨v,hncv,hh.1,by omega⟩
             . simp only [hj3,↓reduceIte];trivial
           . simp only [haj,↓reduceIte]
             by_cases hak:a=k
             . rw [hak];simp only [↓reduceIte]
               by_cases hk3:tg k=3
               . simp only [hk3,↓reduceIte]
                 have hw:=hok k hkm;rw [hk3] at hw
                 obtain ⟨v,hncv,hget,hbd⟩:=hw
                 have hh:=hor_const k (by simp [hinp]) hk v false 2 hncv hget hbd
                 exact ⟨v,hncv,hh.1,by omega⟩
               . simp only [hk3,↓reduceIte];trivial
             . simp only [hak,↓reduceIte]
               have ha0:a ∈ liveList gs n o p:=by
                 rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
                 . exact absurd rfl hanp
                 . exact h1
               exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,if tg j=3 then 1 else 0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,if tg k=3 then 1 else 0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         have hkj:k≠j:=fun e => hjk e.symm
         simp [tg',hjne,hkne,hkj]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=0:=by simp [tg']
       rw [htgnp] at IH'
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bOr (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta2 htb2 hta1 htb1
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
lemma q133 {n : ℕ} {gs:List Gate} {o : ℕ} {f:BFn n}
   (hev:∀ x,val gs n o x=f x) (v:Fin n)
   (hdep:∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x) :
   (v : ℕ) ∈ liveList gs n o 0:=by
 rw [qw]
 refine ⟨by omega,?_⟩
 by_contra hnl
 have hnr : ¬ wn n gs o (v : ℕ):=by
   intro hr
   rcases q66 hr with heq | ⟨q,g,hg,hin,hrq⟩
   . exact hnl (Or.inl heq)
   . exact hnl (Or.inr ⟨q,nZL q,g,hg,hin,hrq⟩)
 obtain ⟨x,hx⟩:=hdep
 apply hx
 rw [← hev,← hev]
 have hagree:∀ (p : ℕ),∀ i < n+p,wn n gs o i ->
     (q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).getD i false =
     (q3 (gs.take p) (List.ofFn x)).getD i false:=by
   intro p
   induction p with
   | zero =>
     intro i hi hr
     simp only [List.take_zero,q3,List.foldl_nil]
     have hlt:i < n:=by omega
     have hne:(⟨i,hlt⟩:Fin n)≠v:=fun e => hnr (by simpa [← e] using hr)
     simp [hlt,fUN hne]
   | succ p ih =>
     intro i hi hr
     by_cases hp:p < gs.length
     . have htake:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem hp
       rw [htake,zd,zd]
       have hlen1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       have hlen2:(q3 (gs.take p) (List.ofFn x)).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       by_cases hip:i=n+p
       . subst hip
         show (q3 (gs.take p) _++[_]).getD (n+p) false=(q3 (gs.take p) _++[_]).getD (n+p) false
         rw [z2 _ _ _ _ hlen1,z2 _ _ _ _ hlen2]
         congr 1
         apply List.map_congr_left
         intro a ha
         have hra:wn n gs o a:=q33 (List.getElem?_eq_getElem hp) hr ha
         by_cases halt:a < n+p
         . exact ih a halt hra
         . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
       . show (q3 (gs.take p) _++[_]).getD i false=(q3 (gs.take p) _++[_]).getD i false
         rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
         exact ih i (by omega) hr
     . have htake:gs.take (p+1)=gs.take p:=by
         rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
       rw [htake]
       by_cases hlt:i < n+p
       . exact ih i hlt hr
       . have hl1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         have hl2:(q3 (gs.take p) (List.ofFn x)).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         rw [lGD _ _ (by omega),lGD _ _ (by omega)]
 have ho_lt:o < n+gs.length:=by
   by_contra hge
   have hfalse:∀ y:Fin n->Bool,val gs n o y=false:=fun y =>
     lGD _ _ (by rw [qu];simp;omega)
   exact hx (by rw [← hev,← hev,hfalse,hfalse])
 have h:=hagree gs.length o ho_lt (q34 n gs o)
 rw [List.take_length] at h
 exact h
open Classical in
lemma q88 {n : ℕ} (f:BFn n) (cap : ℕ) (initTags:Fin n->ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (hdep:∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s'))
   (s : ℕ) (hs:s<=cap) (hc:HasCircuitSize n f s) :
   ∃ s',s'<=cap /\
     TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s'
       (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)):=by
 obtain ⟨gs,o,hm,hlen⟩:=q56 n f s hnc hc
 have hlive0:liveList gs n o 0=List.range n:=by
   have hsub:=(List.filter_sublist (l:=List.range (n+0)) (p:=fun a => decide (q11 n gs o 0 a)))
   simp only [nAZ] at hsub
   refine List.Sublist.eq_of_length hsub ?_
   have hperm:(List.range n).Perm (liveList gs n o 0):=by
     refine (List.perm_ext_iff_of_nodup List.nodup_range (vy gs n o 0)).2 ?_
     intro a
     rw [List.mem_range]
     constructor
     . intro ha;exact q133 hm.hev ⟨a,ha⟩ (hdep ⟨a,ha⟩)
     . intro ha;exact by simpa using ((qw gs n o 0 a).1 ha).1
   exact hperm.length_eq.symm
 set tg : ℕ->ℕ:=fun a => if h:a < n then initTags ⟨a,h⟩ else 0
 have hok0:∀ a ∈ liveList gs n o 0,yf n gs f 0 a (tg a):=by
   intro a ha
   rw [hlive0,List.mem_range] at ha
   have hta:tg a=initTags ⟨a,ha⟩:=by simp [tg,ha]
   rw [hta]
   rcases htag ⟨a,ha⟩ with h0 | ⟨h1,hnc0,hlb⟩ | ⟨h3,hnc0,hlb⟩
   . rw [h0];trivial
   . rw [h1]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 1) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
   . rw [h3]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 2) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
 have htr:=q123 n f gs o hm gs.length 0 (by omega) tg hok0
 refine ⟨gs.length,by omega,?_⟩
 have heq:(liveList gs n o 0).map (fun a => (val gs n a,tg a)) =
     List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i):=by
   rw [hlive0]
   apply List.ext_getElem
   . simp
   . intro i h1 h2
     have hi:i < n:=by simpa using h2
     simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
     exact Prod.ext (q172 gs n ⟨i,hi⟩) (by simp [tg,hi])
 rw [← heq]
 exact htr
def zm {α:Type} (x:Nat) (f:Nat->α) : α :=
 match x with
 | 0 => f 0
 | n+1 => f (Nat.succ n)
lemma v5 {α:Type} (x:Nat) (f:Nat->α):zm x f=f x:=by
 cases x <;> rfl
structure Cfg where
 k:Nat
 sh0:Nat
 sh1:Nat
 shTT:Nat
 all1v:Nat
 goalv:Nat
 lok:Nat
 m0all:Nat
 m0:Nat
 a29_0:Nat
 b5_0:Nat
 m1:Nat
 m12:Nat
 a29_1:Nat
 b5_1:Nat
def q76 (sw:Nat × Nat × Nat × Nat) (w:Nat):Nat :=
 let (d,m01,m10,mEq):=sw
 Nat.lor (Nat.lor (Nat.land w mEq) (Nat.shiftRight (Nat.land w m01) d))
         (Nat.shiftLeft (Nat.land w m10) d)
def ym:List (Nat × Nat × Nat × Nat)->Nat->Nat
 | [],w => w
 | sw::rest,w => ym rest (q76 sw w)
def q72 (sh:Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (Nat.shiftRight w sh) fun v => (v,tg)::q72 sh rest
def wx (g:List (Nat × Nat × Nat × Nat)):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (ym g w) fun v => (v,tg)::wx g rest
def M128:Nat:=0x9e3779b97f4a7c15f39cc0605cedc835
def q211:Nat:=0x517cc1b727220a95b3650d1e9a87c3f1
def q210:Nat:=0xbf58476d1ce4e5b994d049bb133111eb
def q209:Nat:=0x2545f4914f6cdd1d6c62272e07bb0142
def q208 (salt w tg:Nat):Nat :=
 let s:=match tg with
   | 0 => salt
   | 1 => Nat.xor salt q211
   | 2 => Nat.xor salt q210
   | _ => Nat.xor salt q209
 zm (Nat.xor (Nat.xor w (Nat.shiftRight w 61)) s) fun x =>
 Nat.shiftRight (Nat.mul x (Nat.xor x M128)) 104
def q199 (salt:Nat):Nat->List (Nat × Nat)->Nat
 | acc,[] => acc
 | acc,(w,tg)::rest => zm (Nat.add acc (q208 salt w tg)) fun acc' => q199 salt acc' rest
def q75 (salt:Nat) (ws:List (Nat × Nat)):Nat:=Nat.land (q199 salt 0 ws) 0xFFFFFF
def q205 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 24 i)) 0xFFFFFF
def q192 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 32 i)) 0xFFFFFFFF
def q167 (T h:Nat):Nat->Nat->Nat->Nat
 | 0,lo,_ => lo
 | fuel+1,lo,hi =>
   if Nat.ble (Nat.add lo 2) hi then
     zm (Nat.div (Nat.add lo hi) 2) fun mid =>
     if Nat.ble (q205 T mid) h then q167 T h fuel mid hi else q167 T h fuel lo mid
   else lo
def q85 (NN FL HT:Nat->Nat) (s h:Nat):Nat :=
 let n:=NN s
 if Nat.beq n 0 then 999999
 else
   let ht:=HT s
   zm (q167 ht h (FL s) 0 n) fun j =>
   if Nat.beq (q205 ht j) h then j else 999999
def twEq (a b:Nat × Nat):Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
def jy (x:Nat × Nat):List (Nat × Nat)->Option (List (Nat × Nat))
 | [] => none
 | a::rest =>
   if twEq x a then some rest
   else match jy x rest with
     | none => none
     | some r => some (a::r)
def jk:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],[] => true
 | a::as,bs => match jy a bs with
   | none => false
   | some bs' => jk as bs'
 | _,_ => false
def twLt (a b:Nat × Nat):Bool :=
 if Nat.beq a.1 b.1 then Nat.blt a.2 b.2 else Nat.blt a.1 b.1
def q62 (x:Nat × Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => [x]
 | a::rest => if twLt x a then x::a::rest else a::q62 x rest
def q125:List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | a::rest => q62 a (q125 rest)
def q158:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],_ => false
 | _,[] => false
 | a::as,b::bs =>
   if twEq a b then q158 as bs else twLt a b
def q69 (g:List (Nat × Nat × Nat × Nat)) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let ws':=q125 (wx g ws)
 if q158 ws' ws then ws' else ws
def q35:List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->List (Nat × Nat)
 | [],ws => ws
 | g::rest,ws => q35 rest (q69 g ws)
def q186 (gens:List (List (Nat × Nat × Nat × Nat))) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let s0:=q125 ws
 match gens with
 | [] => s0
 | [g] => q69 g s0
 | _ => q35 gens (q35 gens s0)
def qi (m0 w0:Nat):Nat :=
 zm (Nat.land w0 m0) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m0) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m0) fun c =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 3) m0)) fun nd =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 4) m0)) fun ne =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 5) m0)) fun nf =>
 Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
         (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
def yg (sh1 m1 m12 w:Nat):Nat :=
 zm (Nat.shiftRight w sh1) fun w0 =>
 zm (Nat.land w0 m1) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m1) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m1) fun c =>
 zm (Nat.land (Nat.shiftRight w0 3) m1) fun d =>
 zm (Nat.land (Nat.shiftRight w0 4) m1) fun e =>
 zm (Nat.land (Nat.shiftRight w0 5) m1) fun f =>
 zm (Nat.xor m1 d) fun nd =>
 zm (Nat.xor m1 e) fun ne =>
 zm (Nat.xor m1 f) fun nf =>
 zm (Nat.xor m1 a) fun na =>
 zm (Nat.xor m1 b) fun nb =>
 zm (Nat.xor m1 c) fun nc =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))) fun v1 =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))) fun v2 =>
 zm (Nat.lor v1 v2) fun u =>
 zm (Nat.land u m12) fun hi =>
 Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                     (Nat.land (Nat.land u m1) (Nat.xor m1 (Nat.shiftRight hi 1))))
inductive PList where
 | nil:PList
 | cons (w tg alo ahi nahi cw uw a0 v0w v1w postC postU postV0 postV1:Nat) (tail:PList):PList
def kt (c:Cfg):List (Nat × Nat)->Nat × Nat × Nat × Nat × PList
 | [] => (0,0,0,0,PList.nil)
 | (w,tg)::rest =>
   let (pC,pU,pV0,pV1,tl):=kt c rest
   let alo:=Nat.land w c.lok
   let ahi:=Nat.land (Nat.shiftRight w c.k) c.lok
   let nahi:=Nat.xor c.lok ahi
   let cw:=Nat.xor alo ahi
   let uw:=Nat.land cw ahi
   let a0:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
   let v0w:=qi c.m0 a0
   let v1w:=yg c.sh1 c.m1 c.m12 w
   (Nat.lor cw pC,Nat.lor uw pU,Nat.add v0w pV0,Nat.add v1w pV1,
    PList.cons w tg alo ahi nahi cw uw a0 v0w v1w pC pU pV0 pV1 tl)
def q164:List (Nat × Nat)->Nat
 | [] => 0
 | _::rest => Nat.add 1 (q164 rest)
def yz (x:Nat):List (Nat × Nat)->Bool
 | [] => false
 | (a,_)::rest => if Nat.beq x a then true else yz x rest
def qx:List (Nat × Nat)->List (Nat × Nat)->List (Nat × Nat)
 | [],ys => ys
 | a::xs,ys => qx xs (a::ys)
def pToList:PList->List (Nat × Nat)
 | PList.nil => []
 | PList.cons w tg _ _ _ _ _ _ _ _ _ _ _ _ tl => (w,tg)::pToList tl
def qj (all1v:Nat) (ws:List (Nat × Nat)) (w:Nat):Bool :=
 !(Nat.beq w 0)&&!(Nat.beq w all1v)&&!(yz w ws)
def qb (c:Cfg) (v0Acc v0w:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add (Nat.add v0Acc v0w) c.a29_0) c.b5_0) c.b5_0
def z3 (c:Cfg) (v1Tot:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add v1Tot c.a29_1) c.b5_1) c.b5_1
def ke (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     Nat.beq (Nat.land missU (Nat.lor alo blo)) 0 &&
     qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.lor a0 b0)) &&
     (let w:=Nat.lor a b;qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       Nat.beq (Nat.land missU (Nat.lor nahi nbhi)) 0 &&
       qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.land a0 b0)) &&
       (let w:=Nat.land a b;let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0;
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))))
     if andHit then true
     else ke c ws onSurv a ta alo nahi a0 pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post
def q98 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if ke c ws onSurv a ta alo nahi a0 pre preU preV0 [] suf then true
   else q98 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def vx (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0 v0a:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if okOrB&&qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else if okOrB&&!(Nat.beq tb 1) then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w &&
         onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if okAndB&&qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else if okAndB&&Nat.beq tb 0 then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w &&
           onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else false
     if andHit then true
     else vx c ws onSurv a ta alo nahi a0 v0a pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post
def js (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if vx c ws onSurv a ta alo nahi a0 v0a pre preU preV0 [] suf then true
   else js c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def we (c:Cfg) (ws:List (Nat × Nat))
   (a ta alo nahi a0 v0a:Nat):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | pmU,pmV0,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         (okOrB&&qj c.all1v ws w) ||
         (!(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
         (!(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
       else if okOrB&&!(Nat.beq tb 1) then
         qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws (Nat.lor a b)
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           (okAndB&&qj c.all1v ws w) ||
           (Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
           (Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
         else if okAndB&&Nat.beq tb 0 then
           qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws (Nat.land a b)
         else false
     if andHit then true
     else we c ws a ta alo nahi a0 v0a (Nat.lor pmU ub) (Nat.add pmV0 v0b) post
def q26 (c:Cfg) (ws:List (Nat × Nat)):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | preU,preV0,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if we c ws a ta alo nahi a0 v0a preU preV0 suf then true
   else q26 c ws (Nat.lor preU ua) (Nat.add preV0 v0a) suf
def w7 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ _ cw ua a0 v0a _ _ postU postV0 _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let uw:=Nat.land cw alo;
      Nat.beq (Nat.lor (Nat.lor preU postU) uw) c.lok &&
      qb c (Nat.add preV0 postV0) (qi c.m0 (Nat.xor a0 c.m0all)) &&
      (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
       qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))))
   if hit then true
   else w7 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def kd (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi a0 v0a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | pmC,pmU,pmV0,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
            qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else
         Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
         qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post)))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
              qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else
           Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
           qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post)))
     if andHit then true
     else kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV0 v0b) (Nat.add pmV1 v1b) ((b,tb)::mid) post
def q96 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 v0a v1a _ _ _ _ suf =>
   if kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre preC preU preV0 preV1 [] suf then true
   else q96 c ws hasUp onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def w6 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo _ _ ca ua a0 v0a v1a postC postU postV0 postV1 suf =>
   let hit :=
     if Nat.beq ta 1||Nat.beq ta 2 then false
     else
       let w:=Nat.xor a c.all1v
       let wt:=if Nat.beq ta 3 then 2 else 0
       let uw:=Nat.land ca alo
       let rC:=Nat.lor preC postC
       let rU:=Nat.lor preU postU
       let rV0:=Nat.add preV0 postV0
       let rV1:=Nat.add preV1 postV1
       (Nat.beq (Nat.lor rC ca) c.lok &&
        (Nat.beq (Nat.lor rU uw) c.lok||z3 c (Nat.add rV1 v1a)) &&
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&Nat.beq (Nat.lor rU ca) c.lok &&
        qb c (Nat.add rV0 v0a) (qi c.m0 (Nat.xor a0 c.m0all)) &&
        qj c.all1v ws w&&onSurv ((w,0)::(a,0)::qx pre (pToList suf)))
   if hit then true
   else w6 c ws onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def kc (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi ca a0 v1a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | pmC,pmU,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 _ v1b postC postU _ postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       let v1w:=yg c.sh1 c.m1 c.m12 w
       let ta':=if Nat.beq ta 3 then 1 else 0
       let tb':=if Nat.beq tb 3 then 1 else 0
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest)) ||
         (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&qb c totV0 (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))
       else
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         let v1w:=yg c.sh1 c.m1 c.m12 w
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest)) ||
           (Nat.beq ta 0&&Nat.beq tb 0&&qb c totV0 (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::ws))
         else
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest))
     if andHit then true
     else kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV1 v1b) ((b,tb)::mid) post
def q94 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | preC,preU,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 _ v1a _ _ _ _ suf =>
   if kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre preC preU preV1 [] suf then true
   else q94 c ws hasUp totV0 onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def w5 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta _ _ _ ca _ _ _ _ postC _ _ _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor (Nat.lor preC postC) ca) c.lok&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&onSurv ((w,0)::ws))))
   if hit then true
   else w5 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf
def k9 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi ca:Nat) (pre:List (Nat × Nat)):Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | pmC,mid,PList.cons b tb blo bhi _ cb _ _ _ _ postC _ _ _ post =>
   let rC:=Nat.lor pmC postC
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     (let w:=Nat.lor a b
      let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
      let ta':=if Nat.beq ta 3 then 1 else 0
      let tb':=if Nat.beq tb 3 then 1 else 0
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,0)::rest)) ||
       (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,0)::(a,ta')::rest)) ||
       (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,0)::(b,tb')::rest)) ||
       (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       (let w:=Nat.land a b
        let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
        let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
        qj c.all1v ws w &&
        ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,wt)::rest)) ||
         (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,wt)::(a,0)::rest)) ||
         (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,wt)::(b,0)::rest)) ||
         (Nat.beq ta 0&&Nat.beq tb 0&&onSurv ((w,0)::ws))))
     if andHit then true
     else k9 c ws onSurv a ta alo ahi ca pre (Nat.lor pmC cb) ((b,tb)::mid) post
def q92 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta alo ahi _ ca _ _ _ _ _ _ _ _ suf =>
   if k9 c ws onSurv a ta alo ahi ca pre preC [] suf then true
   else q92 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf
def j6 (c:Cfg) (ws:List (Nat × Nat)):Bool :=
 match ws with
 | [(a,_)] => Nat.beq (Nat.xor a c.all1v) c.goalv
 | [(a,_),(b,_)] => Nat.beq (Nat.lor a b) c.goalv||Nat.beq (Nat.land a b) c.goalv
 | _ => false
def scanAll (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws onSurv 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws onSurv 0 0 [] pl||q96 c ws hasUp onSurv 0 0 0 0 [] pl
     else hasUp&&js c ws onSurv 0 0 [] pl
   | 2 => w6 c ws onSurv 0 0 0 0 [] pl||q94 c ws hasUp totV0 onSurv 0 0 0 [] pl
   | _ => w5 c ws onSurv 0 [] pl||q92 c ws onSurv 0 [] pl
def scanInline (c:Cfg) (s:Nat) (ws:List (Nat × Nat)):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws (fun _ => true) 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws (fun _ => true) 0 0 [] pl||q96 c ws hasUp (fun _ => true) 0 0 0 0 [] pl
     else hasUp&&q26 c ws 0 0 pl
   | 2 => w6 c ws (fun _ => true) 0 0 0 0 [] pl||q94 c ws hasUp totV0 (fun _ => true) 0 0 0 [] pl
   | _ => w5 c ws (fun _ => true) 0 [] pl||q92 c ws (fun _ => true) 0 [] pl
def q42 (pid:Nat):Nat->Nat->Nat × Nat
 | 0,j => (0,j)
 | fuel+1,j =>
   let t:=Nat.div (Nat.mul (Nat.add j 1) j) 2
   if Nat.ble t pid then q42 pid fuel (Nat.add j 1)
   else (Nat.sub pid (Nat.div (Nat.mul j (Nat.sub j 1)) 2),j)
def jw:Nat->List (Nat × Nat)->Nat × Nat
 | _,[] => (0,0)
 | 0,a::_ => a
 | k+1,_::rest => jw k rest
def q38:Nat->List (Nat × Nat)->List (Nat × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::q38 k rest
def q203 (all1v code:Nat) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 if Nat.ble code 32 then
   zm (Nat.sub code 1) fun c =>
   zm (Nat.shiftRight c 1) fun i =>
   let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=jw i ws
   let wt:=if Nat.beq ta 3 then 2 else 0
   zm (Nat.xor a all1v) fun w =>
   let r:=q38 i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   zm (Nat.sub code 33) fun rem =>
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=jw i ws
   let (b,tb):=jw j ws
   let r:=q38 i (q38 j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     zm (Nat.land a b) fun w =>
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (w,wt)::r2
   else
     zm (Nat.lor a b) fun w =>
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (w,0)::r2
def q120 (all1v:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (Nat × Nat)
 | 0,_,_ => xs
 | d+1,s,j =>
   zm (q192 (PT s) j) fun e =>
   zm (Nat.land e 1023) fun code =>
   if Nat.beq code 0 then xs
   else zm (Nat.land (Nat.shiftRight e 10) 8191) fun pidx =>
     q203 all1v code (q120 all1v xs PT d (Nat.add s 1) pidx)
def Rgen (all1v cap:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat) (s j:Nat):List (Nat × Nat) :=
 q120 all1v xs PT (Nat.sub cap s) s j
def vm (salt:Nat) (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat):List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->Bool
 | [],ztt =>
   zm (q75 salt ztt) fun h =>
   zm (q85 NN FL HT s h) fun j =>
   !(Nat.beq j 999999)&&jk ztt (Rtt s j)
 | g::rest,ztt =>
   zm (q75 salt ztt) fun h =>
   zm (q85 NN FL HT s h) fun j =>
   if !(Nat.beq j 999999)&&jk ztt (Rtt s j) then true
   else vm salt Rtt NN FL HT s rest (wx g ztt)
def findAutPath (shTT salt:Nat) (path:List (List (Nat × Nat × Nat × Nat)))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 vm salt Rtt NN FL HT s path (q72 shTT zs)
def findAutGen (shTT salt:Nat) (gens:List (List (Nat × Nat × Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT PT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let zsc:=q186 gens (q72 shTT zs)
 zm (q75 salt zsc) fun h =>
 zm (q85 NN FL HT s h) fun j =>
 if Nat.beq j 999999 then false
 else
   zm (Nat.shiftRight (q192 (PT s) j) 23) fun aidx =>
   jk zsc (wx (aut aidx) (Rtt s j))
def bar (cfg:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (R:Nat->Nat->List (Nat × Nat)):Nat->Nat->Bool
 | 0,i => match R 0 i with
   | [(w,_)] => !(Nat.beq w cfg.goalv)
   | _ => true
 | s+1,i =>
   let ws:=R (Nat.add s 1) i
   !(scanAll cfg s ws fun zs =>
       !(findFn s zs)&&(Nat.beq s 0||scanInline cfg (Nat.sub s 1) zs))
def span (f:Nat->Bool):Nat->Nat->Bool
 | 0,_ => true
 | n+1,i => f i&&span f n (Nat.add i 1)
def q1 (n r:Nat):Fin n->Bool:=fun i => r.testBit i.val
def q146 {n:Nat} (x:Fin n->Bool):Nat :=
 (List.finRange n).foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0
lemma qp {m:Nat} (hm:m≠0):(1:Nat).testBit m=false:=by
 cases m with
 | zero => contradiction
 | succ k => simp [Nat.testBit_succ]
lemma z7 {x m:Nat} (h:x.testBit m=true) :
   (x / 2 ^ m) % 2=1:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 exact of_decide_eq_true h
lemma z5 {x m:Nat} (h:x.testBit m=false) :
   (x / 2 ^ m) % 2=0:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 have:=of_decide_eq_false h
 omega
lemma zg {x m:Nat} (h:x.testBit m=true) : 2 ^ m<=x:=by
 have h1:=z7 h
 have h2 : 1<=x / 2 ^ m:=by generalize x / 2 ^ m=q at h1 ⊢;omega
 have h3:=Nat.mul_le_mul_right (2 ^ m) h2
 have h4:=Nat.div_mul_le_self x (2 ^ m)
 omega
lemma vz {y m:Nat} (h:y.testBit m=false) :
   y % 2 ^ (m+1) < 2 ^ m:=by
 have h0:(y / 2 ^ m) % 2=0:=z5 h
 have h1:y % 2 ^ (m+1) / 2 ^ m=(y / 2 ^ m) % 2:=by
   rw [Nat.pow_succ,Nat.mod_mul_right_div_self]
 have h2:y % 2 ^ (m+1) / 2 ^ m=0:=by rw [h1,h0]
 exact (Nat.div_eq_zero_iff.1 h2).resolve_left (Nat.ne_of_gt (n2P m))
lemma vk {y m:Nat} (h:y.testBit m=false) (k:Nat) :
   (y+2 ^ m).testBit k=if k=m then true else y.testBit k:=by
 by_cases hkm:k=m
 . subst hkm
   have h0:=z5 h
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.add_div_right _ (n2P k)]
   simp;omega
 . simp only [hkm,↓reduceIte]
   by_cases hlt:k < m
   . have hdv : 2 ^ m=2 ^ k*2 ^ (m - k):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hlt)]
     have hge : 1<=m - k:=by omega
     have hev : 2 ^ (m - k) % 2=0:=by
       obtain ⟨q,hq⟩:=Nat.exists_eq_add_of_le' hge
       rw [hq,Nat.pow_succ];omega
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hdv,
         Nat.mul_comm (2 ^ k),Nat.add_mul_div_right _ _ (n2P k)]
     have:(y / 2 ^ k+2 ^ (m - k)) % 2=(y / 2 ^ k) % 2:=by omega
     rw [this]
   . have hge:m+1<=k:=by omega
     have hrem:y % 2 ^ (m+1)+2 ^ m < 2 ^ (m+1):=by
       have hltm:=vz h
       have hpw : 2 ^ (m+1)=2 ^ m*2:=Nat.pow_succ 2 m
       omega
     have hdiv1:(y+2 ^ m) / 2 ^ (m+1)=y / 2 ^ (m+1):=by
       have hd:y=2 ^ (m+1)*(y / 2 ^ (m+1))+y % 2 ^ (m+1) :=
         (Nat.div_add_mod y (2 ^ (m+1))).symm
       conv_lhs => rw [hd,nAA]
       rw [Nat.mul_add_div (n2P (m+1)),Nat.div_eq_of_lt hrem,nAZ]
     have hpow : 2 ^ k=2 ^ (m+1)*2 ^ (k - (m+1)):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' hge]
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hpow,
         ← Nat.div_div_eq_div_mul,← Nat.div_div_eq_div_mul,hdiv1]
lemma qs {y m:Nat} (h:y.testBit m=false) :
   y+2 ^ m=y^^^2 ^ m:=by
 apply nEQ;intro k
 rw [vk h,nTX,Nat.testBit_two_pow]
 by_cases hkm:k=m
 . subst hkm;simp [h]
 . simp [hkm,Ne.symm hkm]
lemma jl {n:Nat} (x:Fin n->Bool) (k:Nat) :
   (q146 x).testBit k=if h:k < n then x ⟨k,h⟩ else false:=by
 have hgen:∀ (l:List (Fin n)),l.Nodup ->
     (l.foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0).testBit k =
     if h:k < n then (if ⟨k,h⟩ ∈ l then x ⟨k,h⟩ else false) else false:=by
   intro l hnd
   induction l with
   | nil => simp
   | cons a t ih =>
     obtain ⟨hat,hndt⟩:=List.nodup_cons.1 hnd
     simp only [lFC]
     have iht:=ih hndt
     by_cases hxa:x a=true
     . simp only [hxa,↓reduceIte,nTO,Nat.testBit_shiftLeft,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . subst heq;simp [hxa]
         . have hne:k≠a.val:=fun e => heq (Fin.ext e)
           have h0:(decide (a.val<=k)&&(1:Nat).testBit (k - a.val))=false:=by
             cases hle:decide (a.val<=k)
             . simp
             . have hle':a.val<=k:=of_decide_eq_true hle
               simp [qp (by omega:k - a.val≠0)]
           simp [heq,h0]
       . have hne:a.val < k:=by omega
         simp [hk,qp (by omega:k - a.val≠0)]
     . simp only [hxa,bFT,↓reduceIte,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . rw [heq];simp [hat,hxa]
         . simp [heq]
       . simp [hk]
 have h:=hgen (List.finRange n) (List.nodup_finRange n)
 simpa [q146,List.mem_finRange] using h
lemma q178 {n:Nat} (x:Fin n->Bool):q146 x < 2 ^ n:=by
 apply Nat.lt_pow_two_of_testBit
 intro k hk
 rw [jl]
 simp [show ¬ k < n by omega]
lemma q57 {n:Nat} (x:Fin n->Bool):q1 n (q146 x)=x:=by
 funext i
 simp [q1,jl,i.isLt]
def encL {n:Nat} (rows:List Nat) (f:BFn n):Nat :=
 rows.foldr (fun r acc => acc*2+if f (q1 n r) then 1 else 0) 0
def encTT (n:Nat) (f:BFn n):Nat:=encL (List.range (2 ^ n)) f
lemma z8 {n:Nat} (rows:List Nat) (f:BFn n) (i:Nat) :
   (encL rows f).testBit i=match rows[i]? with | some r => f (q1 n r) | none => false:=by
 induction rows generalizing i with
 | nil => simp [encL]
 | cons r rest ih =>
   have hcons:encL (r::rest) f=encL rest f*2+if f (q1 n r) then 1 else 0:=rfl
   rw [hcons]
   cases i with
   | zero =>
     cases h:f (q1 n r) <;> simp [h,Nat.testBit_zero]
   | succ k =>
     rw [Nat.testBit_succ]
     have hd:(encL rest f*2+if f (q1 n r) then 1 else 0) / 2=encL rest f:=by
       cases h:f (q1 n r) <;> simp only [h,↓reduceIte,bFT] <;> omega
     rw [hd]
     exact ih k
lemma q39 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => false)=0:=by
 apply nEQ;intro i
 rw [z8];cases rows[i]? <;> simp
lemma q177 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => true)=2 ^ rows.length - 1:=by
 apply nEQ;intro i
 rw [z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]
lemma q160 {n:Nat} (rows:List Nat) (f:BFn n) :
   encL rows (invF f)=Nat.xor (encL rows f) (2 ^ rows.length - 1):=by
 apply nEQ;intro i
 rw [nXO,nTX,z8,z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi,invF]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]
lemma q143 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (meetF f g)=Nat.land (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLA,nTA,z8,z8,z8]
 cases rows[i]? <;> simp [meetF]
lemma q144 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (joinF f g)=Nat.lor (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLO,nTO,z8,z8,z8]
 cases rows[i]? <;> simp [joinF]
lemma vr {n:Nat} (f:BFn n) (r:Nat) :
   (encTT n f).testBit r=if r < 2 ^ n then f (q1 n r) else false:=by
 unfold encTT;rw [z8]
 by_cases hr:r < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]
lemma yc {n:Nat}:Function.Injective (encTT n):=by
 intro f g h
 funext x
 have h1:=congrArg (fun m => m.testBit (q146 x)) h
 rw [vr,vr] at h1
 simp only [q178 x,↓reduceIte,q57] at h1
 exact h1
lemma q116 {n:Nat} (pre:List Nat) (f:BFn n) :
   Nat.shiftRight (encL (pre++List.range (2 ^ n)) f) pre.length=encTT n f:=by
 apply nEQ;intro i
 change ((encL (pre++List.range (2 ^ n)) f) >>> pre.length).testBit i=(encTT n f).testBit i
 rw [Nat.shiftRight_eq_div_pow,Nat.testBit_div_two_pow,z8,vr]
 rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel]
 by_cases hi:i < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hi])];simp [hi]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hi]
lemma q89 {n:Nat} (pre:List Nat) :
   Function.Injective (encL (n:=n) (pre++List.range (2 ^ n))):=by
 intro f g h
 apply yc
 rw [← q116 pre f,← q116 pre g,h]
def yh {n:Nat} (i j:Fin n) (x:Fin n->Bool):Fin n->Bool :=
 fun k => x (if k=i then j else if k=j then i else k)
lemma q104 {n:Nat} (i j:Fin n) (x:Fin n->Bool) :
   yh i j (yh i j x)=x:=by
 funext k;unfold yh
 by_cases h1:k=i
 . rw [h1];by_cases h2:j=i <;> simp [h2]
 . by_cases h2:k=j
   . rw [h2];simp [Ne.symm h1]
   . simp [h1,h2]
def yu (i j r:Nat):Nat :=
 let bi:=r.testBit i
 let bj:=r.testBit j
 if bi==bj then r else Nat.xor r (Nat.lor (1 <<< i) (1 <<< j))
lemma q162 {n i j r:Nat} (hi:i < n) (hj:j < n) (hr:r < 2 ^ n) :
   yu i j r < 2 ^ n:=by
 unfold yu;dsimp only
 split
 . exact hr
 . apply Nat.lt_pow_two_of_testBit
   intro k hk
   rw [nXO,nTX,nLO,nTO,
       Nat.testBit_shiftLeft,Nat.testBit_shiftLeft]
   have hr0:r.testBit k=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hk))
   simp [hr0,qp (by omega:k - i≠0),qp (by omega:k - j≠0)]
lemma z9 {n i j r:Nat} (hi:i < n) (hj:j < n) :
   q1 n (yu i j r)=yh ⟨i,hi⟩ ⟨j,hj⟩ (q1 n r):=by
 funext k
 simp only [q1,yh,yu]
 by_cases heq:r.testBit i=r.testBit j
 . simp only [heq,beq_self_eq_true,↓reduceIte]
   by_cases hki:k=⟨i,hi⟩
   . rw [hki];simp [heq]
   . by_cases hkj:k=⟨j,hj⟩
     . rw [hkj];split <;> simp [heq]
     . simp [hki,hkj]
 . have hbeq:(r.testBit i==r.testBit j)=false:=beq_false_of_ne heq
   simp only [hbeq,bFT,↓reduceIte,nXO,nTX,nLO,
     nTO,Nat.testBit_shiftLeft]
   by_cases hki:k=⟨i,hi⟩
   . subst hki
     simp only [↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
     cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
   . by_cases hkj:k=⟨j,hj⟩
     . subst hkj
       simp only [hki,↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
       cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
     . have h1:k.val≠i:=fun e => hki (Fin.ext e)
       have h2:k.val≠j:=fun e => hkj (Fin.ext e)
       have hb:∀ m,k.val≠m->(decide (m<=k.val)&&(1:Nat).testBit (k.val - m))=false:=by
         intro m hne
         cases hle:decide (m<=k.val)
         . simp
         . have hle':m<=k.val:=of_decide_eq_true hle
           simp [qp (by omega:k.val - m≠0)]
       simp [hki,hkj,hb i h1,hb j h2]
def w9 (n i j:Nat):Nat × Nat × Nat × Nat :=
 let d:=2 ^ j - 2 ^ i
 let N:=2 ^ n
 let m01:=(List.range N).foldr (fun x acc => acc*2+if !(x.testBit i)&&x.testBit j then 1 else 0) 0
 let m10:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i&&!(x.testBit j) then 1 else 0) 0
 let mEq:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i==x.testBit j then 1 else 0) 0
 (d,m01,m10,mEq)
lemma jx (N:Nat) (P:Nat->Bool) (r:Nat) :
   ((List.range N).foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
   if r < N then P r else false:=by
 have hgen:∀ (l:List Nat) (r:Nat),
     (l.foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
     match l[r]? with | some x => P x | none => false:=by
   intro l
   induction l with
   | nil => intro r;simp
   | cons a t ih =>
     intro r;simp only [lFC]
     cases r with
     | zero => cases h:P a <;> simp [h,Nat.testBit_zero]
     | succ k =>
       rw [Nat.testBit_succ]
       have hd:((t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0)*2+if P a then 1 else 0) / 2
           = t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0:=by
         cases P a <;> simp only [↓reduceIte,bFT] <;> omega
       rw [hd];exact ih k
 rw [hgen]
 by_cases hr:r < N
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]
lemma j3 {n i j:Nat} (hij:i < j) (hjn:j < n) (g:BFn n) :
   q76 (w9 n i j) (encTT n g) =
     encTT n (fun x => g (yh ⟨i,by omega⟩ ⟨j,hjn⟩ x)):=by
 have hi:i < n:=by omega
 have hpow : 2 ^ i < 2 ^ j:=Nat.pow_lt_pow_right (by omega) hij
 have hsub_bit:∀ x m,x.testBit m=true->x - 2 ^ m+2 ^ m=x/\(x - 2 ^ m).testBit m=false:=by
   intro x m hm
   have hle : 2 ^ m<=x:=zg hm
   refine ⟨Nat.sub_add_cancel hle,?_⟩
   rw [Nat.testBit_eq_decide_div_mod_eq]
   have hd:(x - 2 ^ m) / 2 ^ m=x / 2 ^ m - 1:=by
     have h1:x=(x - 2 ^ m)+2 ^ m:=(Nat.sub_add_cancel hle).symm
     have h2:((x - 2 ^ m)+2 ^ m) / 2 ^ m=(x - 2 ^ m) / 2 ^ m+1 :=
       Nat.add_div_right (x - 2 ^ m) (n2P m)
     rw [← h1] at h2;rw [h2];simp
   have hm1:=z7 hm
   rw [hd];simp;generalize x / 2 ^ m=q at hm1 ⊢;omega
 have hsw_val:∀ (a b:Nat),a < b->b < n->∀ x < 2 ^ n,
     (x.testBit a=false->x.testBit b=true->x - (2 ^ b - 2 ^ a)=yu a b x) /\
     (x.testBit a=true->x.testBit b=false->x+(2 ^ b - 2 ^ a)=yu a b x):=by
   intro a b hab hbn x _
   have hpa : 2 ^ a < 2 ^ b:=Nat.pow_lt_pow_right (by omega) hab
   have hsh:∀ (m k:Nat),(decide (m<=k)&&(1:Nat).testBit (k - m))=decide (m=k):=by
     intro m k
     by_cases hmk:m=k
     . subst hmk;simp
     . cases hle:decide (m<=k)
       . simp [hmk]
       . have hle':m<=k:=of_decide_eq_true hle
         simp [hmk,qp (by omega:k - m≠0)]
   constructor
   . intro ha0 hb1
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x b hb1
     have hsub_a0:(x - 2 ^ b).testBit a=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit a) h2
       rw [nTX,Nat.testBit_two_pow,ha0] at htb
       have hba:b≠a:=by omega
       simp [hba] at htb;exact htb
     have h2:x - (2 ^ b - 2 ^ a)=(x - 2 ^ b)+2 ^ a:=by
       conv_lhs => rw [← hsub_eq]
       rw [Nat.add_sub_assoc (Nat.sub_le _ _),Nat.sub_sub_self (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ b)^^^2 ^ b:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ b)+2 ^ a=(x - 2 ^ b)^^^2 ^ a:=qs hsub_a0
     unfold yu;dsimp only
     simp only [ha0,hb1]
     change ((x - 2 ^ b)+2 ^ a).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
   . intro ha1 hb0
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x a ha1
     have hsub_b0:(x - 2 ^ a).testBit b=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit b) h2
       rw [nTX,Nat.testBit_two_pow,hb0] at htb
       have hab':a≠b:=by omega
       simp [hab'] at htb;exact htb
     have h2:x+(2 ^ b - 2 ^ a)=(x - 2 ^ a)+2 ^ b:=by
       conv_lhs => rw [← hsub_eq]
       rw [nAA,Nat.add_sub_cancel' (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ a)^^^2 ^ a:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ a)+2 ^ b=(x - 2 ^ a)^^^2 ^ b:=qs hsub_b0
     unfold yu;dsimp only
     simp only [ha1,hb0]
     change ((x - 2 ^ a)+2 ^ b).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
 have hodd_ji:(2 ^ (j - i) - 1) % 2=1:=by
   have hge : 1<=j - i:=by omega
   have hev : 2 ^ (j - i) % 2=0:=by
     obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge
     rw [hm,Nat.pow_succ];omega
   have hpos : 2<=2 ^ (j - i):=by
     have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge;simpa using this
   omega
 have hflip_add_i:∀ r,(r+(2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r+(2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i+(2 ^ (j - i) - 1):=by
     rw [hdv,Nat.mul_comm,Nat.add_mul_div_right _ _ (n2P i)]
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q;generalize 2 ^ (j - i) - 1=c at hodd_ji ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hflip_sub_i:∀ r,2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r hle
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r - (2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i - (2 ^ (j - i) - 1):=by
     have h2:r=(r - (2 ^ j - 2 ^ i))+(2 ^ j - 2 ^ i):=(Nat.sub_add_cancel hle).symm
     have h3:((r - (2 ^ j - 2 ^ i))+2 ^ i*(2 ^ (j - i) - 1)) / 2 ^ i
         = (r - (2 ^ j - 2 ^ i)) / 2 ^ i+(2 ^ (j - i) - 1):=by
       rw [Nat.mul_comm (2 ^ i),Nat.add_mul_div_right _ _ (n2P i)]
     rw [← hdv,← h2] at h3;rw [h3,Nat.add_sub_cancel]
   have hle_div : 2 ^ (j - i) - 1<=r / 2 ^ i:=by
     rw [hdv] at hle
     exact (Nat.le_div_iff_mul_le (n2P i)).2 (by rw [Nat.mul_comm];exact hle)
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q at hle_div ⊢;generalize 2 ^ (j - i) - 1=c at hodd_ji hle_div ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hshl_tb:∀ (x d k:Nat),(Nat.shiftLeft x d).testBit k=(decide (d<=k)&&x.testBit (k - d)):=by
   intro x d k
   change (x <<< d).testBit k=_
   rw [Nat.testBit_shiftLeft]
 apply nEQ
 intro r
 unfold q76 w9
 simp only [nLO,nLA,Nat.shiftRight_eq,Nat.shiftRight_eq_div_pow,
   nTO,nTA,Nat.testBit_div_two_pow,hshl_tb,
   jx,vr]
 by_cases hr:r < 2 ^ n
 . simp only [hr,↓reduceIte]
   have hsw:=hsw_val i j hij hjn r hr
   cases hri:r.testBit i <;> cases hrj:r.testBit j
   ·
     have h00_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h00_eq]
     have hmid:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hsub_j : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
       intro hle
       have h1:(r - (2 ^ j - 2 ^ i))+2 ^ j=r+2 ^ i:=by omega
       have hle_div : 1<=r / 2 ^ j:=by
         have hne0:r / 2 ^ j≠0:=by
           intro hz
           have hlt:r < 2 ^ j:=(Nat.div_eq_zero_iff.1 hz).resolve_left (Nat.ne_of_gt (n2P j))
           have hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ i:=by omega
           have hbi:(r - (2 ^ j - 2 ^ i)).testBit i=false:=Nat.testBit_lt_two_pow hlt2
           have:=hsub_i hle;rw [hbi] at this;cases this
         generalize r / 2 ^ j=q at hne0 ⊢;omega
       have hsub_div:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=r / 2 ^ j - 1:=by
         have h2:(r+2 ^ i) / 2 ^ j=r / 2 ^ j:=by
           have hrem:r % 2 ^ j+2 ^ i < 2 ^ j:=by
             have hm0:(r % 2 ^ j).testBit i=false:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
             have hlt1:r % 2 ^ j < 2 ^ j:=Nat.mod_lt r (n2P j)
             apply Nat.lt_pow_two_of_testBit;intro k hk
             rw [vk hm0]
             have hne:k≠i:=by omega
             simp only [hne,↓reduceIte]
             exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) hk))
           have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
           conv_lhs => rw [hdiv,nAA]
           rw [Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hrem,nAZ]
         have h3:((r - (2 ^ j - 2 ^ i))+2 ^ j) / 2 ^ j=(r - (2 ^ j - 2 ^ i)) / 2 ^ j+1 :=
           Nat.add_div_right _ (n2P j)
         rw [h1,h2] at h3;omega
       have hrj0:=z5 hrj
       rw [Nat.testBit_eq_decide_div_mod_eq,hsub_div];simp
       generalize r / 2 ^ j=q at hle_div hrj0 ⊢;omega
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_j hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
   ·
     have hle_j : 2 ^ j<=r:=zg hrj
     have hle : 2 ^ j - 2 ^ i<=r:=le_trans (Nat.sub_le _ _) hle_j
     have hsw_eq:r - (2 ^ j - 2 ^ i)=yu i j r:=hsw.1 hri hrj
     have hsw_lt:r - (2 ^ j - 2 ^ i) < 2 ^ n:=by omega
     have hsw_i:(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r - (2 ^ j - 2 ^ i)).testBit j=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hmid_i:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_i]
     rw [hterm1]
     simp [hle,hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have hsw_eq:r+(2 ^ j - 2 ^ i)=yu i j r:=hsw.2 hri hrj
     have hsw_lt:r+(2 ^ j - 2 ^ i) < 2 ^ n:=by rw [hsw_eq];exact q162 hi hjn hr
     have hsw_i:(r+(2 ^ j - 2 ^ i)).testBit i=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r+(2 ^ j - 2 ^ i)).testBit j=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm2]
     simp [hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have h11_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h11_eq]
     have hmid_j:(r+(2 ^ j - 2 ^ i)).testBit j=false:=by
       have hle_i : 2 ^ i<=r:=zg hri
       have hsub_rem:(r - 2 ^ i) / 2 ^ j=r / 2 ^ j:=by
         have hm1:(r % 2 ^ j).testBit i=true:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
         have hmod_i : 2 ^ i<=r % 2 ^ j:=zg hm1
         have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
         have hsub:r - 2 ^ i=2 ^ j*(r / 2 ^ j)+(r % 2 ^ j - 2 ^ i):=by omega
         have hlt:r % 2 ^ j - 2 ^ i < 2 ^ j:=lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt r (n2P j))
         rw [hsub,Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hlt,nAZ]
       have h1:r+(2 ^ j - 2 ^ i)=(r - 2 ^ i)+2 ^ j:=by omega
       rw [Nat.testBit_eq_decide_div_mod_eq,h1,Nat.add_div_right _ (n2P j),hsub_rem]
       have hr1:=z7 hrj
       simp;omega
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_j]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
 ·
   have hge1 : ¬ (r+(2 ^ j - 2 ^ i) < 2 ^ n):=by omega
   simp only [hr,hge1,↓reduceIte,Bool.and_false,Bool.false_or]
   by_cases hle : 2 ^ j - 2 ^ i<=r
   . by_cases hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ n
     . have hsub_j:(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
         have hge_q : 2 ^ (n - j) - 1<=(r - (2 ^ j - 2 ^ i)) / 2 ^ j:=by
           have h1 : 2 ^ j*(2 ^ (n - j) - 1)=2 ^ n - 2 ^ j:=by
             rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           have h2 : 2 ^ n - 2 ^ j<=r - (2 ^ j - 2 ^ i) :=
             le_trans (Nat.sub_le_sub_left (Nat.sub_le _ _) _) (Nat.sub_le_sub_right (by omega : 2 ^ n<=r) _)
           exact (Nat.le_div_iff_mul_le (n2P j)).2 (by rw [Nat.mul_comm,h1];exact h2)
         have hlt_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j < 2 ^ (n - j):=by
           have h1 : 2 ^ n=2 ^ j*2 ^ (n - j):=by
             rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           exact (Nat.div_lt_iff_lt_mul (n2P j)).2 (by rw [Nat.mul_comm,← h1];exact hlt2)
         have heq_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=2 ^ (n - j) - 1:=by omega
         rw [Nat.testBit_eq_decide_div_mod_eq,heq_q]
         have hge1' : 1<=n - j:=by omega
         have hev : 2 ^ (n - j) % 2=0:=by
           obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge1'
           rw [hm,Nat.pow_succ];omega
         have hpos : 2<=2 ^ (n - j):=by
           have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge1';simpa using this
         simp;omega
       simp [hle,hlt2,hsub_j]
     . simp [hle,hlt2]
   . simp [hle]
def q163 (n:Nat) (ps:List (Nat × Nat)):List (Nat × Nat × Nat × Nat) :=
 ps.map fun p => w9 n p.1 p.2
def kq (n:Nat) (ps:List (Nat × Nat)):Bool :=
 ps.all fun p => decide (p.1 < p.2)&&decide (p.2 < n)
def zc {n:Nat}:List (Nat × Nat)->(Fin n->Bool)->(Fin n->Bool)
 | [],x => x
 | (i,j)::rest,x =>
   if h:i < n/\j < n then yh ⟨i,h.1⟩ ⟨j,h.2⟩ (zc rest x)
   else zc rest x
lemma wv {n:Nat} (ps:List (Nat × Nat)) (x:Fin n->Bool) :
   zc ps.reverse (zc ps x)=x:=by
 have hcomp:∀ (a b:List (Nat × Nat)) (y:Fin n->Bool),
     zc (a++b) y=zc a (zc b y):=by
   intro a;induction a with
   | nil => intro b y;rfl
   | cons p t ih =>
     intro b y;rcases p with ⟨i,j⟩
     simp only [lCA,zc];split <;> rw [ih]
 induction ps generalizing x with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨i,j⟩
   simp only [lRC,hcomp,zc]
   split
   . rename_i h
     rw [q104,ih]
   . exact ih x
lemma jm {n:Nat} (ps:List (Nat × Nat)) (hv:kq n ps=true) (g:BFn n) :
   ym (q163 n ps) (encTT n g)=encTT n (fun x => g (zc ps x)):=by
 induction ps generalizing g with
 | nil => rfl
 | cons p rest ih =>
   rcases p with ⟨i,j⟩
   simp only [kq,List.all_cons,bAT,decide_eq_true_eq] at hv
   obtain ⟨⟨hij,hjn⟩,hrest⟩:=hv
   change ym (w9 n i j::q163 n rest) (encTT n g)=_
   simp only [ym]
   rw [j3 hij hjn g,ih hrest]
   congr 1;funext x
   have hlt:i < n/\j < n:=by omega
   simp only [zc]
   split
   . rfl
   . contradiction
def vh {n:Nat} (f:BFn n) (sws:List (Nat × Nat × Nat × Nat)):Prop :=
 ∃ π:(Fin n->Bool)->(Fin n->Bool),
   Function.Bijective π/\(∀ x,f (π x)=f x) /\
   ∀ g:BFn n,ym sws (encTT n g)=encTT n (fun x => g (π x))
lemma kw {n:Nat} (f:BFn n) (ps:List (Nat × Nat))
   (hv:kq n ps=true)
   (hfix:ym (q163 n ps) (encTT n f)=encTT n f) :
   vh f (q163 n ps):=by
 refine ⟨zc ps,?_,?_,fun g => jm ps hv g⟩
 . constructor
   . intro x y h
     have:=congrArg (zc ps.reverse) h
     simpa [wv] using this
   . intro y
     refine ⟨zc ps.reverse y,?_⟩
     have:=wv ps.reverse y
     simpa using this
 . intro x
   rw [jm ps hv f] at hfix
   exact congrFun (yc hfix) x
lemma q138 {n:Nat} (f:BFn n):vh f [] :=
 ⟨id,Function.bijective_id,fun _ => rfl,fun _ => rfl⟩
lemma wp {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (π:(Fin n->Bool)->(Fin n->Bool)) (hbij:Function.Bijective π) (hfix:∀ x,f (π x)=f x)
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws) :
   TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s
     (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 let φ:BFn n->BFn n:=fun g x => g (π x)
 have hφ:Function.Injective φ:=by
   intro g1 g2 heq;funext y
   obtain ⟨x,rfl⟩:=hbij.2 y
   exact congrFun heq x
 exact @TagRun.map (BFn n) (BFn n) φ hφ
   invF meetF joinF (fun _ => false) (fun _ => true) f
   invF meetF joinF (fun _ => false) (fun _ => true) f
   rfl rfl (funext hfix) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) s ws h
def z6 (x i:Nat):Nat:=(x / 64 ^ i) % 64
lemma q185 (i:Nat) : 64 ^ i=2 ^ (6*i):=by
 rw [show (64:Nat)=2 ^ 6 by decide,← Nat.pow_mul]
lemma qo (x i k:Nat) :
   (z6 x i).testBit k=if k < 6 then x.testBit (6*i+k) else false:=by
 unfold z6
 rw [q185,show (64:Nat)=2 ^ 6 by decide,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
 by_cases hk:k < 6
 . simp [hk,nAC]
 . simp [hk]
lemma wg {x y:Nat} (h:∀ i,z6 x i=z6 y i):x=y:=by
 apply nEQ;intro k
 have h1:=congrArg (fun z => z.testBit (k % 6)) (h (k / 6))
 have hm:k % 6 < 6:=Nat.mod_lt k (by decide)
 rw [qo,qo] at h1
 simp only [hm,↓reduceIte,Nat.div_add_mod] at h1
 exact h1
lemma z1 (x i:Nat):z6 (x / 64) i=z6 x (i+1):=by
 unfold z6
 rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (64 ^ i) 64]
lemma q24:∀ {x y:Nat},(∀ i,z6 y i<=z6 x i)->y<=x:=by
 intro x y h
 induction hn:x+y using Nat.strong_induction_on generalizing x y with
 | _ n ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   by_cases hq:x / 64+y / 64 < x+y
   . have hdiv:y / 64<=x / 64 :=
       ih (x / 64+y / 64) (by omega) (fun i => by rw [z1,z1];exact h (i+1)) rfl
     omega
   . omega
lemma q25 {x y:Nat} (h:∀ j,z6 x j+z6 y j < 64) (i:Nat) :
   z6 (x+y) i=z6 x i+z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   have hdiv:(x+y) / 64=x / 64+y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))
lemma q188 {x y:Nat} (h:∀ j,z6 y j<=z6 x j) (i:Nat) :
   z6 (x - y) i=z6 x i - z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   have hdiv:(x - y) / 64=x / 64 - y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))
lemma v9 (x y i:Nat):z6 (Nat.land x y) i=Nat.land (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTA]
lemma wb (x y i:Nat):z6 (Nat.lor x y) i=Nat.lor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLO,nLO,nTO,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTO]
lemma q110 (x y i:Nat):z6 (Nat.xor x y) i=Nat.xor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nXO,nXO,nTX,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTX]
def qe (m val:Nat):Nat :=
 match m with
 | 0 => 0
 | m'+1 => val+64*qe m' val
lemma v0 (m val i:Nat) (hv:val < 64) :
   z6 (qe m val) i=if i < m then val else 0:=by
 induction m generalizing i with
 | zero => simp [qe,z6]
 | succ m ih =>
   cases i with
   | zero => simp only [qe,z6,Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,↓reduceIte];omega
   | succ k =>
     rw [← z1]
     have hd:qe (m+1) val / 64=qe m val:=by simp only [qe];omega
     rw [hd,ih k]
     by_cases h:k < m <;> simp [h,show k+1 < m+1 ↔ k < m by omega]
def v6 (a b c d e f:Bool):Nat :=
 let nd:=!d;let ne:=!e;let nf:=!f
 (if nd&&b then 1 else 0)+(if nd&&c then 1 else 0) +
 (if a&&ne then 1 else 0)+(if a&&nf then 1 else 0) -
 (if (a&&nd)&&((b||c)&&(ne||nf)) then 1 else 0)
def zq (a b c d e f:Bool):Nat :=
 max (v6 a b c d e f) (v6 (!a) (!b) (!c) (!d) (!e) (!f))
lemma q122:v6 true true true false false false=3:=by decide
lemma yr:∀ a b c d e f:Bool,v6 a b c d e f<=3:=by decide
lemma q52:∀ a b c d e f:Bool,zq a b c d e f<=3:=by decide
lemma k7:∀ a b c d e f:Bool,v6 a b c d e f<=zq a b c d e f:=by decide
lemma jp:∀ a b c d e f:Bool,zq (!a) (!b) (!c) (!d) (!e) (!f)=zq a b c d e f:=by decide
lemma w4:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma kl:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma q14 (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=w4 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=kl (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_or]
 omega
lemma je (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=kl a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=w4 (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_and]
 omega
lemma wc (w s m i:Nat) :
   z6 (Nat.land (Nat.shiftRight w s) (qe m 1)) i =
     if i < m then (if w.testBit (6*i+s) then 1 else 0) else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (w >>> s).testBit (6*i)=_
     rw [nTS,nAC s (6*i)]
     cases h:w.testBit (6*i+s) <;> simp [h]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     cases w.testBit (6*i+s) <;> simp [qp (by omega:k'+1≠0)]
 . simp [hi,nLA]
lemma yy (m w0 i:Nat) :
   z6 (qi (qe m 1) w0) i =
     if i < m then
       v6 (w0.testBit (6*i)) (w0.testBit (6*i+1)) (w0.testBit (6*i+2))
               (w0.testBit (6*i+3)) (w0.testBit (6*i+4)) (w0.testBit (6*i+5))
     else 0:=by
 unfold qi
 simp only [v5]
 have hbit:∀ s j,z6 (Nat.land (Nat.shiftRight w0 s) (qe m 1)) j =
     if j < m then (if w0.testBit (6*j+s) then 1 else 0) else 0:=fun s j => wc w0 s m j
 have hbit0:∀ j,z6 (Nat.land w0 (qe m 1)) j =
     if j < m then (if w0.testBit (6*j) then 1 else 0) else 0:=fun j => by
   have:=hbit 0 j;simpa using this
 have hxor:∀ s j,z6 (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1))) j =
     if j < m then (if !(w0.testBit (6*j+s)) then 1 else 0) else 0:=by
   intro s j
   rw [q110,v0 m 1 j (by decide),hbit s j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte];cases w0.testBit (6*j+s) <;> decide
   . simp [hj]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set nd:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 3) (qe m 1))
 set ne:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 4) (qe m 1))
 set nf:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 5) (qe m 1))
 have h_and_b:∀ bx by_:Bool,
     Nat.land (if bx then 1 else 0) (if by_ then 1 else 0)=if bx&&by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have h_or_b:∀ bx by_:Bool,
     Nat.lor (if bx then 1 else 0) (if by_ then 1 else 0)=if bx||by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have hL:∀ j,z6 (Nat.land nd b) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+1) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 1 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL2:∀ j,z6 (Nat.land nd c) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+2) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 2 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL3:∀ j,z6 (Nat.land a ne) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+4)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 4 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL4:∀ j,z6 (Nat.land a nf) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+5)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 5 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hSub:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j =
     if j < m then (if (w0.testBit (6*j)&&!(w0.testBit (6*j+3))) &&
       ((w0.testBit (6*j+1)||w0.testBit (6*j+2)) &&
        (!(w0.testBit (6*j+4))||!(w0.testBit (6*j+5)))) then 1 else 0) else 0:=by
   intro j
   rw [v9 (Nat.land a nd),v9 a nd,v9 (Nat.lor b c),wb b c,wb ne nf,
       hbit0 j,hxor 3 j,hbit 1 j,hbit 2 j,hxor 4 j,hxor 5 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,h_and_b,h_or_b]
   . simp [hj]
 have hSum1:∀ j,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j:=fun j =>
   q25 (fun l => by rw [hL l,hL2 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSum2:∀ j,z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) j =
     z6 (Nat.land a ne) j+z6 (Nat.land a nf) j:=fun j =>
   q25 (fun l => by rw [hL3 l,hL4 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSumAll:∀ j,z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j+(z6 (Nat.land a ne) j+z6 (Nat.land a nf) j):=by
   intro j
   have hlt:∀ l,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) l+z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) l < 64:=by
     intro l;rw [hSum1 l,hSum2 l,hL l,hL2 l,hL3 l,hL4 l]
     by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> split <;> split <;> omega
   change z6 (_+_) j=_
   rw [q25 hlt j,hSum1 j,hSum2 j]
 have hSubLe:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j <=
     z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j:=by
   intro j;rw [hSumAll j,hSub j,hL j,hL2 j,hL3 j,hL4 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte]
     cases w0.testBit (6*j) <;> cases w0.testBit (6*j+1) <;> cases w0.testBit (6*j+2) <;>
       cases w0.testBit (6*j+3) <;> cases w0.testBit (6*j+4) <;> cases w0.testBit (6*j+5) <;> decide
   . simp [hj]
 change z6 (_ - _) i=_
 rw [q188 hSubLe i,hSumAll i,hSub i,hL i,hL2 i,hL3 i,hL4 i]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte,v6]
   omega
 . simp [hi]
lemma q51:∀ v1 v2:Nat,v1<=3->v2<=3 ->
   let u:=Nat.lor v1 v2
   let hi:=Nat.land u 2
   Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                       (Nat.land (Nat.land u 1) (Nat.xor 1 (Nat.shiftRight hi 1))))=max v1 v2:=by
 intro v1 v2 h1 h2
 interval_cases v1 <;> interval_cases v2 <;> decide
lemma ya {v:Nat} (hv:∀ j,z6 v j<=3) (i:Nat) :
   z6 (Nat.land v (Nat.shiftRight v 1)) i=Nat.land (z6 v i) (Nat.shiftRight (z6 v i) 1):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo]
 by_cases hk:k < 6
 . simp only [hk,↓reduceIte,nTA]
   change (v.testBit (6*i+k)&&(v >>> 1).testBit (6*i+k)) =
     (v.testBit (6*i+k)&&((z6 v i) >>> 1).testBit k)
   rw [nTS,nTS,qo]
   by_cases hk5:k < 5
   . have hk1 : 1+k < 6:=by omega
     simp only [hk1,↓reduceIte]
     have : 1+(6*i+k)=6*i+(1+k):=by omega
     rw [this]
   . have hk_eq:k=5:=by omega
     subst hk_eq
     have hvi:z6 v i < 4:=by have:=hv i;omega
     have htb5:(z6 v i).testBit 5=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hvi (by decide))
     rw [qo] at htb5
     simp only [show 5 < 6 by decide,↓reduceIte] at htb5
     simp [htb5]
 . simp [hk]
lemma jv {hi:Nat} (hhi:∀ j,z6 hi j=0\/z6 hi j=2) (i:Nat) :
   z6 (Nat.land (Nat.shiftRight hi 1) (qe m 1)) i =
     if i < m then Nat.shiftRight (z6 hi i) 1 else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (hi >>> 1).testBit (6*i)=((z6 hi i) >>> 1).testBit 0
     rw [nTS,nTS,qo]
     simp [nAC]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     rcases hhi i with h0 | h2
     . rw [h0];simp
     . rw [h2];change false=((2 >>> 1:Nat).testBit (k'+1));simp [qp (by omega:k'+1≠0)]
 . simp [hm,nLA]
lemma kh (sh1 m w i:Nat) :
   z6 (yg sh1 (qe m 1) (qe m 2) w) i =
     if i < m then
       zq (w.testBit (sh1+6*i)) (w.testBit (sh1+6*i+1)) (w.testBit (sh1+6*i+2))
               (w.testBit (sh1+6*i+3)) (w.testBit (sh1+6*i+4)) (w.testBit (sh1+6*i+5))
     else 0:=by
 unfold yg
 simp only [v5]
 set w0:=Nat.shiftRight w sh1
 have hw0:∀ k,w0.testBit k=w.testBit (sh1+k):=fun k => by
   change (w >>> sh1).testBit k=_;rw [nTS,nAC]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set d:=Nat.land (Nat.shiftRight w0 3) (qe m 1)
 set e:=Nat.land (Nat.shiftRight w0 4) (qe m 1)
 set f:=Nat.land (Nat.shiftRight w0 5) (qe m 1)
 set nd:=Nat.xor (qe m 1) d
 set ne:=Nat.xor (qe m 1) e
 set nf:=Nat.xor (qe m 1) f
 set na:=Nat.xor (qe m 1) a
 set nb:=Nat.xor (qe m 1) b
 set nc:=Nat.xor (qe m 1) c
 set v1:=Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                   (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
 set v2:=Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                   (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))
 have hv1_eq:v1=qi (qe m 1) w0:=by
   unfold qi;simp only [v5];rfl
 have hv1:∀ j,z6 v1 j=if j < m then
     v6 (w0.testBit (6*j)) (w0.testBit (6*j+1)) (w0.testBit (6*j+2))
             (w0.testBit (6*j+3)) (w0.testBit (6*j+4)) (w0.testBit (6*j+5)) else 0:=by
   intro j;rw [hv1_eq,yy]
 have hv2_eq:v2=qi (qe m 1) (Nat.xor w0 (2 ^ (6*m) - 1)):=by
   have hbit_inv:∀ s,s < 6->Nat.land (Nat.shiftRight (Nat.xor w0 (2 ^ (6*m) - 1)) s) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1)):=by
     intro s hs
     apply wg;intro j
     rw [wc,q110,v0 m 1 j (by decide),wc]
     by_cases hj:j < m
     . have hlt : 6*j+s < 6*m:=by omega
       simp only [hj,↓reduceIte,nXO,nTX,nTB,hlt,decide_true]
       cases w0.testBit (6*j+s) <;> decide
     . simp [hj]
   have hbit_inv0:Nat.land (Nat.xor w0 (2 ^ (6*m) - 1)) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land w0 (qe m 1)):=by
     have:=hbit_inv 0 (by decide);simpa using this
   have hxor_inv:∀ x,Nat.xor (qe m 1) (Nat.xor (qe m 1) x)=x:=by
     intro x;apply nEQ;intro k
     rw [nXO,nXO,nTX,nTX]
     cases (qe m 1).testBit k <;> cases x.testBit k <;> decide
   unfold qi;simp only [v5]
   rw [hbit_inv0,hbit_inv 1 (by decide),hbit_inv 2 (by decide),
       hbit_inv 3 (by decide),hbit_inv 4 (by decide),hbit_inv 5 (by decide),
       hxor_inv,hxor_inv,hxor_inv]
 have hv2:∀ j,z6 v2 j=if j < m then
     v6 (!(w0.testBit (6*j))) (!(w0.testBit (6*j+1))) (!(w0.testBit (6*j+2)))
             (!(w0.testBit (6*j+3))) (!(w0.testBit (6*j+4))) (!(w0.testBit (6*j+5))) else 0:=by
   intro j;rw [hv2_eq,yy]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,nXO,nTX,nTB]
     simp only [show 6*j < 6*m by omega,show 6*j+1 < 6*m by omega,
       show 6*j+2 < 6*m by omega,show 6*j+3 < 6*m by omega,
       show 6*j+4 < 6*m by omega,show 6*j+5 < 6*m by omega,
       decide_true,bBT]
   . simp [hj]
 have hv1_le3:∀ j,z6 v1 j<=3:=fun j => by
   rw [hv1 j];split;exact yr _ _ _ _ _ _;omega
 have hv2_le3:∀ j,z6 v2 j<=3:=fun j => by
   rw [hv2 j];split;exact yr _ _ _ _ _ _;omega
 set u:=Nat.lor v1 v2
 set hi:=Nat.land u (qe m 2)
 have hhi_lane:∀ j,z6 hi j=if j < m then Nat.land (Nat.lor (z6 v1 j) (z6 v2 j)) 2 else 0:=by
   intro j;rw [v9,wb,v0 m 2 j (by decide)]
   by_cases hj:j < m <;> simp [hj,nLA]
 have hhi02:∀ j,z6 hi j=0\/z6 hi j=2:=by
   intro j;rw [hhi_lane j]
   split
   . have h1:=hv1_le3 j;have h2:=hv2_le3 j
     generalize z6 v1 j=x at h1;generalize z6 v2 j=y at h2
     interval_cases x <;> interval_cases y <;> decide
   . left;rfl
 have hlast:z6 (Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1))) i =
     if i < m then Nat.land (Nat.land (Nat.lor (z6 v1 i) (z6 v2 i)) 1) (Nat.xor 1 (Nat.shiftRight (z6 hi i) 1)) else 0:=by
   have hrew:Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1)) =
       Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight hi 1) (qe m 1))):=by
     apply nEQ;intro k
     simp only [nLA,nXO,nTA,nTX]
     cases (qe m 1).testBit k <;> simp
   rw [hrew,v9,v9,wb,q110,v0 m 1 i (by decide),
       jv (m:=m) hhi02 i]
   by_cases hm:i < m <;> simp [hm,nLA]
 rw [wb,wb,wb,ya hv1_le3 i,
     ya hv2_le3 i,hlast,hhi_lane i]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   have hmain:=q51 (z6 v1 i) (z6 v2 i) (hv1_le3 i) (hv2_le3 i)
   simp only at hmain
   rw [hmain,hv1 i,hv2 i]
   simp only [hm,↓reduceIte,hw0,zq]
   have ha1:sh1+(6*i+1)=sh1+6*i+1:=by omega
   have ha2:sh1+(6*i+2)=sh1+6*i+2:=by omega
   have ha3:sh1+(6*i+3)=sh1+6*i+3:=by omega
   have ha4:sh1+(6*i+4)=sh1+6*i+4:=by omega
   have ha5:sh1+(6*i+5)=sh1+6*i+5:=by omega
   rw [ha1,ha2,ha3,ha4,ha5]
 . simp only [hm,↓reduceIte,hv1 i,hv2 i];decide
lemma q47 {α:Type} (f : α->Nat) (m:Nat)
   (hf:∀ x i,z6 (f x) i<=(if i < m then 3 else 0))
   (xs:List α) (hlen:xs.length<=11) (i:Nat) :
   z6 (xs.foldr (fun x acc => Nat.add (f x) acc) 0) i=(xs.map fun x => z6 (f x) i).sum /\
   (xs.map fun x => z6 (f x) i).sum<=if i < m then 3*xs.length else 0:=by
 induction xs generalizing i with
 | nil => simp [z6]
 | cons a t ih =>
   simp only [lLC] at hlen
   have ih_all:∀ j,z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j =
       (t.map fun x => z6 (f x) j).sum /\
       (t.map fun x => z6 (f x) j).sum<=if j < m then 3*t.length else 0 :=
     fun j => ih (by omega) j
   have hlt:∀ j,z6 (f a) j+z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j < 64:=by
     intro j
     have h1:=hf a j
     have ⟨h2,h3⟩:=ih_all j
     rw [h2]
     by_cases hj:j < m <;> simp only [hj,↓reduceIte] at h1 h3 <;> omega
   simp only [lFC,lMC,List.sum_cons,lLC]
   have hadd:=q25 hlt i
   have hfa:=hf a i
   have ⟨h2,h3⟩:=ih_all i
   refine ⟨?_,?_⟩
   . change z6 (_+_) i=_;rw [hadd,h2]
   . by_cases hi:i < m <;> simp only [hi,↓reduceIte] at hfa h3 ⊢ <;> omega
lemma ky (S m:Nat)
   (hS_bound:∀ i,z6 S i<=if i < m then 33 else 0)
   (hS_ge3:∀ i < m,3<=z6 S i) :
   Nat.beq (Nat.land (Nat.add S (qe m 29)) (qe m 32)) (qe m 32)=true:=by
 rw [Nat.beq_eq]
 apply wg;intro i
 have hlt:∀ j,z6 S j+z6 (qe m 29) j < 64:=by
   intro j;rw [v0 m 29 j (by decide)]
   have hb:=hS_bound j
   by_cases hj:j < m <;> simp only [hj,↓reduceIte] at hb ⊢ <;> omega
 rw [v9]
 change Nat.land (z6 (S+qe m 29) i) (z6 (qe m 32) i)=z6 (qe m 32) i
 rw [q25 hlt i,v0 m 29 i (by decide),v0 m 32 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   have hb:=hS_bound i;simp only [hi,↓reduceIte] at hb
   have hge:=hS_ge3 i hi
   have h1 : 32<=z6 S i+29:=by omega
   have h2:z6 S i+29 < 64:=by omega
   generalize z6 S i+29=v at h1 h2
   interval_cases v <;> decide
 . simp [hi,nLA]
def j5 (rp:Nat):Nat->Nat->List Nat
 | 0,_ => []
 | m+1,idx => Nat.land (Nat.shiftRight rp (Nat.mul 7 idx)) 127::j5 rp m (Nat.add idx 1)
lemma q32 (rp m idx:Nat):(j5 rp m idx).length=m:=by
 induction m generalizing idx with
 | zero => rfl
 | succ m ih => simp [j5,ih]
def q106 (rp shTT:Nat):List Nat:=j5 rp shTT 0
def allRows (n rp shTT:Nat):List Nat:=q106 rp shTT++List.range (2 ^ n)
lemma jj (rp shTT:Nat):(q106 rp shTT).length=shTT :=
 q32 rp shTT 0
lemma zl (n rp shTT:Nat):(allRows n rp shTT).length=shTT+2 ^ n:=by
 simp [allRows,jj]
structure CfgOk (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Prop where
 sh0_eq:c.sh0=2*c.k
 sh0_le:c.sh0<=c.sh1
 sh1_le:c.sh1<=c.shTT
 p0_dvd:(c.sh1 - c.sh0) % 6=0
 p1_dvd:(c.shTT - c.sh1) % 6=0
 all1v_eq:c.all1v=2 ^ (c.shTT+2 ^ n) - 1
 goalv_eq:c.goalv=encL (allRows n rp c.shTT) f
 lok_eq:c.lok=2 ^ c.k - 1
 m0all_eq:c.m0all=2 ^ (6*((c.sh1 - c.sh0) / 6)) - 1
 m0_eq:c.m0=qe ((c.sh1 - c.sh0) / 6) 1
 a29_0_eq:c.a29_0=qe ((c.sh1 - c.sh0) / 6) 29
 b5_0_eq:c.b5_0=qe ((c.sh1 - c.sh0) / 6) 32
 m1_eq:c.m1=qe ((c.shTT - c.sh1) / 6) 1
 m12_eq:c.m12=qe ((c.shTT - c.sh1) / 6) 2
 a29_1_eq:c.a29_1=qe ((c.shTT - c.sh1) / 6) 29
 b5_1_eq:c.b5_1=qe ((c.shTT - c.sh1) / 6) 32
 cov_ok:∀ i < c.k,
   f (q1 n ((allRows n rp c.shTT).getD i 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.k+i) 0))=true
 p0_ok:∀ i < (c.sh1 - c.sh0) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+5) 0))=false
 p1_ok:∀ i < (c.shTT - c.sh1) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+5) 0))=false
def w3 (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Bool :=
 let np0:=(c.sh1 - c.sh0) / 6
 let np1:=(c.shTT - c.sh1) / 6
 Nat.beq c.sh0 (2*c.k) &&
 Nat.ble c.sh0 c.sh1 &&
 Nat.ble c.sh1 c.shTT &&
 Nat.beq ((c.sh1 - c.sh0) % 6) 0 &&
 Nat.beq ((c.shTT - c.sh1) % 6) 0 &&
 Nat.beq c.all1v (2 ^ (c.shTT+2 ^ n) - 1) &&
 Nat.beq c.goalv (encL (allRows n rp c.shTT) f) &&
 Nat.beq c.lok (2 ^ c.k - 1) &&
 Nat.beq c.m0all (2 ^ (6*np0) - 1) &&
 Nat.beq c.m0 (qe np0 1) &&
 Nat.beq c.a29_0 (qe np0 29) &&
 Nat.beq c.b5_0 (qe np0 32) &&
 Nat.beq c.m1 (qe np1 1) &&
 Nat.beq c.m12 (qe np1 2) &&
 Nat.beq c.a29_1 (qe np1 29) &&
 Nat.beq c.b5_1 (qe np1 32) &&
 Nat.beq (Nat.land c.goalv c.lok) 0 &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.k) c.lok) c.lok &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh0) c.m0all) (qe np0 7) &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh1) (2 ^ (6*np1) - 1)) (qe np1 7)
lemma qm {n:Nat} (rows:List Nat) (f:BFn n) {idx:Nat} (h:idx < rows.length) :
   (encL rows f).testBit idx=f (q1 n (rows.getD idx 0)):=by
 rw [z8,List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]
lemma jn (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg)
   (h:w3 n f rp c=true):CfgOk n f rp c:=by
 unfold w3 at h
 simp only [bAT,Nat.beq_eq,Nat.ble_eq] at h
 rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh0,h01⟩,h1t⟩,hp0d⟩,hp1d⟩,hall1⟩,hgoal⟩,hlok⟩,hm0all⟩,
   hm0⟩,ha29_0⟩,hb5_0⟩,hm1⟩,hm12⟩,ha29_1⟩,hb5_1⟩,hcov0⟩,hcov1⟩,hp0m⟩,hp1m⟩
 have hlen:(allRows n rp c.shTT).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hbit_goal:∀ idx < c.shTT,c.goalv.testBit idx=f (q1 n ((allRows n rp c.shTT).getD idx 0)):=by
   intro idx hidx
   rw [hgoal,qm _ _ (by rw [hlen];exact Nat.lt_add_right (2 ^ n) hidx)]
 have hlane7:∀ (sh m:Nat),sh+6*m<=c.shTT ->
     Nat.land (Nat.shiftRight c.goalv sh) (2 ^ (6*m) - 1)=qe m 7 ->
     ∀ i < m,
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+1) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+2) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+3) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+4) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+5) 0))=false:=by
   intro sh m hbound heq i hi
   have htb:∀ off < 6,f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+off) 0))=(7:Nat).testBit off:=by
     intro off hoff
     have h1:=congrArg (fun z => z6 z i) heq
     rw [v0 m 7 i (by decide)] at h1
     simp only [hi,↓reduceIte] at h1
     have h2:=congrArg (fun z => z.testBit off) h1
     rw [qo] at h2
     simp only [hoff,↓reduceIte,nLA,nTA,nTB,
       show 6*i+off < 6*m by omega,decide_true,bATR] at h2
     change (c.goalv >>> sh).testBit (6*i+off)=_ at h2
     rw [nTS,← nAA] at h2
     rw [← hbit_goal (sh+6*i+off) (by omega)]
     exact h2
   exact ⟨by simpa using htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
          htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)⟩
 refine ⟨hsh0,h01,h1t,hp0d,hp1d,hall1,hgoal,hlok,hm0all,hm0,ha29_0,hb5_0,hm1,hm12,ha29_1,hb5_1,?_,?_,?_⟩
 . intro i hi
   constructor
   . have h1:=congrArg (fun z => z.testBit i) hcov0
     rw [nLA,nTA,hlok,nTB,nZT] at h1
     simp only [hi,decide_true,bATR] at h1
     rw [← hbit_goal i (by omega)];exact h1
   . have h1:=congrArg (fun z => z.testBit i) hcov1
     rw [nLA,nTA,hlok,nTB] at h1
     simp only [hi,decide_true,bATR] at h1
     change (c.goalv >>> c.k).testBit i=true at h1
     rw [nTS] at h1
     rw [← hbit_goal (c.k+i) (by omega)];exact h1
 . apply hlane7 c.sh0 ((c.sh1 - c.sh0) / 6) (by omega)
   rw [← hm0all];exact hp0m
 . apply hlane7 c.sh1 ((c.shTT - c.sh1) / 6) (by omega) hp1m
def AllTagsLe3 {α:Type} (ws:List (α × Nat)):Prop:=∀ p ∈ ws,p.2<=3
lemma AllTagsLe3.perm {α:Type} {xs ys:List (α × Nat)} (hp:xs.Perm ys)
   (h:AllTagsLe3 xs):AllTagsLe3 ys :=
 fun p hm => h p (hp.symm.subset hm)
lemma TagRun.inv_zero {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal 0 ws) :
   ∃ tg,ws=[(goal,tg)]:=by
 generalize hs:(0:Nat)=s at h
 induction h with
 | done tg => exact ⟨tg,rfl⟩
 | perm hp _ ih =>
   obtain ⟨tg,rfl⟩:=ih hs
   exact ⟨tg,List.perm_singleton.1 hp.symm⟩
 | uNot _ _ _ _ _ _ _ _ _ => cases hs
 | bOr _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
lemma TagRun.inv_succ {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s:Nat} {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal (s+1) ws) :
   (∃ a ta r save,ws.Perm ((a,ta)::r) /\
     ta≠1/\ta≠2/\(ta=3->save=false) /\
     inv a≠zero/\inv a≠one/\inv a≠a/\(∀ x ∈ r,x.1≠inv a) /\
     TagRun inv meet join zero one goal s ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r)) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠2/\tb≠2/\(ta=1->ka=false)/\(tb=1->kb=false) /\
     join a b≠zero/\join a b≠one/\join a b≠a/\join a b≠b/\(∀ x ∈ r,x.1≠join a b) /\
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r))) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠1/\tb≠1/\(ta≠0->ka=false)/\(tb≠0->kb=false) /\
     meet a b≠zero/\meet a b≠one/\meet a b≠a/\meet a b≠b/\(∀ x ∈ r,x.1≠meet a b) /\
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize hs:s+1=s' at h
 induction h with
 | done _ => cases hs
 | perm hp _ ih =>
   rcases ih hs with ⟨a,ta,r,save,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩
   . exact Or.inl ⟨a,ta,r,save,hp.symm.trans hp',rest⟩
   . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
   . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
 | @uNot s0 a ta r save h1 h2 h3 h4 h5 h6 h7 hsub _ =>
   cases hs
   exact Or.inl ⟨a,ta,r,save,lPR _,h1,h2,h3,h4,h5,h6,h7,hsub⟩
 | @bOr s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
 | @bAnd s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
lemma q68 {α:Type} {ws:List α} {a : α} {r:List α} (hp:ws.Perm (a::r)) :
   ∃ pre suf,ws=pre++a::suf/\r.Perm (pre++suf):=by
 have hmem:a ∈ ws:=hp.symm.subset (by simp)
 obtain ⟨pre,suf,hws⟩:=List.append_of_mem hmem
 refine ⟨pre,suf,hws,?_⟩
 rw [hws] at hp
 exact (List.perm_cons a).1 (hp.symm.trans lPM)
lemma q67 {α:Type} {ws:List α} {a b : α} {r:List α} (hp:ws.Perm (a::b::r)) :
   (∃ pre mid suf,ws=pre++a::mid++b::suf/\r.Perm (pre++mid++suf)) \/
   (∃ pre mid suf,ws=pre++b::mid++a::suf/\r.Perm (pre++mid++suf)):=by
 obtain ⟨p1,s1,hws,hbr⟩:=q68 hp
 have hmem:b ∈ p1++s1:=hbr.subset (by simp)
 rcases List.mem_append.1 hmem with hbp | hbs
 . obtain ⟨pre,mid,hp1⟩:=List.append_of_mem hbp
   right
   refine ⟨pre,mid,s1,by rw [hws,hp1,lAA,lCA],?_⟩
   rw [hp1,lAA] at hbr
   have hmid:(pre++b::(mid++s1)).Perm (b::(pre++(mid++s1))):=lPM
   have h1:=(List.perm_cons b).1 (hbr.trans hmid)
   simpa [lAA] using h1
 . obtain ⟨mid,suf,hs1⟩:=List.append_of_mem hbs
   left
   refine ⟨p1,mid,suf,by simp [hws,hs1,lAA],?_⟩
   rw [hs1] at hbr
   have hmid:((p1++mid)++b::suf).Perm (b::((p1++mid)++suf)):=lPM
   rw [← lAA] at hbr
   exact (List.perm_cons b).1 (hbr.trans hmid)
lemma z4 {α:Type} (k:Bool) (a : α) (r:List α) (x : α) :
   x ∈ qk k a r ↔ (k=true/\x=a)\/x ∈ r:=by
 cases k <;> simp [qk]
lemma yd {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (u v:Fin n->Bool) (hu:f u=false) (hv:f v=true) :
   ∃ p ∈ ws,p.1 u≠p.1 v:=by
 induction h with
 | done tg => exact ⟨(f,tg),by simp,by simp [hu,hv]⟩
 | perm hp _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   exact ⟨p,hp.subset hm,hne⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . exact ⟨(a,ta),by simp,fun e => hne (by dsimp only at e;simp [invF,e])⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . exact ⟨p,by simp [hm3],hne⟩
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [joinF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [meetF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
lemma zk {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (joinF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [joinF,Bool.or_eq_false_iff,bOT] at hu hv
   rcases hv with hva | hvb
   . exact ⟨(a,ta),by simp,hu.1,hva⟩
   . exact ⟨(b,tb),by simp,hu.2,hvb⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩
lemma za {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (meetF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [meetF,Bool.and_eq_false_iff,bAT] at hu hv
   rcases hu with hua | hub
   . exact ⟨(a,ta),by simp,hua,hv.1⟩
   . exact ⟨(b,tb),by simp,hub,hv.2⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩
lemma qf {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1) :
   ∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true:=by
 induction h with
 | done tg => intro u v hu hv;exact ⟨(f,tg),by simp,hu,hv⟩
 | perm hp _ ih =>
   intro u v hu hv
   obtain ⟨p,hm,h1,h2⟩:=ih (by rw [hp.length_eq];exact hlen) u v hu hv
   exact ⟨p,hp.subset hm,h1,h2⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact zk (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact za (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
lemma kk {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1)
   (r0 r1 r2 r3 r4 r5:Fin n->Bool)
   (h0:f r0=true) (h1:f r1=true) (h2:f r2=true)
   (h3:f r3=false) (h4:f r4=false) (h5:f r5=false) :
   3<=(ws.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
 induction h with
 | done tg => simp [h0,h1,h2,h3,h4,h5,q122]
 | perm hp _ ih =>
   rw [← (hp.map _).sum_eq]
   exact ih (by rw [hp.length_eq];exact hlen)
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at hih ⊢
   have hsub6:=w4 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at hih ⊢
   have hsub6:=kl (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
lemma qh {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s) :
   (∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) \/
   (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum):=by
 induction h with
 | done tg => simp at hlen
 | perm hp _ ih =>
   rcases ih (by rw [hp.length_eq];exact hlen) with hcov | hsym
   . left;intro u v hu hv
     obtain ⟨p,hm,h1,h2⟩:=hcov u v hu hv
     exact ⟨p,hp.subset hm,h1,h2⟩
   . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     rw [← (hp.map _).sum_eq]
     exact hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save
   . right
     intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hv:=kk hsub (by simp [qk] at hlen ⊢;omega) r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hle_s:∀ l:List (BFn n × Nat),
         (l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
         (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
       intro l;induction l with
       | nil => simp
       | cons x t iht =>
         simp only [lMC,List.sum_cons]
         have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5)
         omega
     have hs:=le_trans hv (hle_s _)
     simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs ⊢
     exact hs
   . simp [qk] at hlen hle;omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact zk (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at h1 ⊢
       have hsub6:=q14 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact zk (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact zk (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact za (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at h1 ⊢
       have hsub6:=je (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact za (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact za (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
abbrev aR (n rp:Nat) (c:Cfg):=allRows n rp c.shTT
abbrev TR {n:Nat} (f:BFn n):=TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f
lemma qz {a b:Nat} (h:a=b):Nat.beq a b=true:=Eq.mpr Nat.beq_eq h
lemma q0 (a:Nat):Nat.beq a a=true:=Eq.mpr Nat.beq_eq rfl
lemma q2 {a b:Nat} (h:a≠b):Nat.beq a b=false:=by
 cases hb:Nat.beq a b
 . rfl
 . exact absurd (Eq.mp Nat.beq_eq hb) h
lemma y3 {a b:Nat} (h:Nat.beq a b=false):a≠b :=
 fun e => by subst e;rw [q0] at h;cases h
lemma zh {a b:Nat}:(Nat.beq a b=false) ↔ a≠b :=
 ⟨y3,q2⟩
lemma q4 {b e:Bool} (h:e=true):(if b=true then true else e)=true:=by
 cases b <;> simp [h]
lemma q5 {b e:Bool} (h:b=true):(if b=true then true else e)=true:=by
 rw [h];rfl
lemma v8 (a b:Nat):Nat.add a b=a+b:=rfl
def encWs {n:Nat} (rows:List Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encL rows p.1,p.2)
abbrev eW {n:Nat} (rp:Nat) (c:Cfg) (ws:List (BFn n × Nat)):=encWs (aR n rp c) ws
abbrev eL {n:Nat} (rp:Nat) (c:Cfg) (g:BFn n):=encL (aR n rp c) g
lemma q41 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (joinF a b)=Nat.lor (eL rp c a) (eL rp c b):=q144 _ a b
lemma q40 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (meetF a b)=Nat.land (eL rp c a) (eL rp c b):=q143 _ a b
def encTTWs (n:Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encTT n p.1,p.2)
lemma qy {n:Nat} (rows:List Nat) (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encWs rows (p::ws)=(encL rows p.1,p.2)::encWs rows ws:=rfl
lemma kj {n:Nat} (rows:List Nat) (xs ys:List (BFn n × Nat)) :
   encWs rows (xs++ys)=encWs rows xs++encWs rows ys:=lMA
lemma q49 {n:Nat} (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encTTWs n (p::ws)=(encTT n p.1,p.2)::encTTWs n ws:=rfl
lemma q18 (xs ys:List (Nat × Nat)):qx xs ys=xs.reverse++ys:=by
 induction xs generalizing ys with
 | nil => rfl
 | cons a t ih => simp [qx,ih,lAA]
lemma q187 (ws:List (Nat × Nat)):q164 ws=ws.length:=by
 induction ws with
 | nil => rfl
 | cons _ t ih => simp [q164,ih,v8];omega
lemma wh (x:Nat) (ws:List (Nat × Nat)) :
   yz x ws=false ↔ ∀ p ∈ ws,p.1≠x:=by
 induction ws with
 | nil => simp [yz]
 | cons a t ih =>
   rcases a with ⟨w,tg⟩
   simp only [yz,lMM,forall_eq_or_imp]
   by_cases h:x=w
   . subst h;simp [q0]
   . simp [q2 h,ih,Ne.symm h]
lemma jo {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (ws:List (BFn n × Nat)) (g:BFn n)
   (h0:g≠fun _ => false) (h1:g≠fun _ => true) (hmem:∀ p ∈ ws,p.1≠g) :
   qj c.all1v (eW rp c ws) (eL rp c g)=true:=by
 have hinj:=q89 (n:=n) (q106 rp c.shTT)
 have hlen:(aR n rp c).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hne0:eL rp c g≠0:=fun e => by
   rw [← q39 (n:=n) (aR n rp c)] at e;exact h0 (hinj e)
 have hne1:eL rp c g≠c.all1v:=fun e => by
   rw [hc.all1v_eq,← hlen,← q177 (n:=n) (aR n rp c)] at e;exact h1 (hinj e)
 have hnc:yz (eL rp c g) (eW rp c ws)=false:=by
   rw [wh]
   intro p hp;rcases List.mem_map.1 hp with ⟨q,hq,rfl⟩
   exact fun e => hmem q hq (hinj e)
 unfold qj
 simp [q2 hne0,q2 hne1,hnc]
lemma qc {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (joinF a b)=Nat.lor (encL rows a) (encL rows b):=q144 rows a b
lemma q9 {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (meetF a b)=Nat.land (encL rows a) (encL rows b):=q143 rows a b
lemma q145 {n:Nat} (rows:List Nat) (a:BFn n) :
   encL rows (invF a)=Nat.xor (encL rows a) (2 ^ rows.length - 1):=q160 rows a
lemma qv {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:BFn n) :
   eL rp c (invF a)=Nat.xor (eL rp c a) c.all1v:=by
 unfold eL;rw [q160,zl,← hc.all1v_eq]
def wi (c:Cfg) (w:Nat):Nat:=Nat.land w c.lok
def q63 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.k) c.lok
def k1 (c:Cfg) (w:Nat):Nat:=Nat.xor c.lok (q63 c w)
def wC (c:Cfg) (w:Nat):Nat:=Nat.xor (wi c w) (q63 c w)
def wU (c:Cfg) (w:Nat):Nat:=Nat.land (wC c w) (q63 c w)
def wA0 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
def wV0 (c:Cfg) (w:Nat):Nat:=qi c.m0 (wA0 c w)
def wV1 (c:Cfg) (w:Nat):Nat:=yg c.sh1 c.m1 c.m12 w
def yx (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wC c p.1) acc) 0
def v4 (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wU c p.1) acc) 0
def zf (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0
def va (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0
lemma qq (a b d:Nat):Nat.lor (Nat.lor a b) d=Nat.lor a (Nat.lor b d):=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_assoc]
lemma q7 (a b:Nat):Nat.lor a b=Nat.lor b a:=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_comm]
lemma q108 (a b:Nat):Nat.land a b=Nat.land b a:=by
 apply nEQ;intro i;simp [nLA,nTA,Bool.and_comm]
lemma q46 (a:Nat):Nat.lor 0 a=a:=by
 apply nEQ;intro i;simp [nLO,nTO]
lemma qt (a b:Nat):Nat.add a b=Nat.add b a:=nAC a b
lemma y9 (a b d:Nat):Nat.add (Nat.add a b) d=Nat.add a (Nat.add b d):=nAA a b d
lemma yp (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):yx c (p::ws)=Nat.lor (wC c p.1) (yx c ws):=rfl
lemma vo (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):v4 c (p::ws)=Nat.lor (wU c p.1) (v4 c ws):=rfl
lemma k0 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):zf c (p::ws)=Nat.add (wV0 c p.1) (zf c ws):=rfl
lemma w1 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):va c (p::ws)=Nat.add (wV1 c p.1) (va c ws):=rfl
lemma vc (c:Cfg) (xs ys:List (Nat × Nat)):yx c (xs++ys)=Nat.lor (yx c xs) (yx c ys):=by
 induction xs with | nil => simp [yx,q46] | cons a t ih => simp only [lCA,yx,lFC] at ih ⊢;rw [ih,qq]
lemma zu (c:Cfg) (xs ys:List (Nat × Nat)):v4 c (xs++ys)=Nat.lor (v4 c xs) (v4 c ys):=by
 induction xs with | nil => simp [v4,q46] | cons a t ih => simp only [lCA,v4,lFC] at ih ⊢;rw [ih,qq]
lemma zy (c:Cfg) (xs ys:List (Nat × Nat)):zf c (xs++ys)=Nat.add (zf c xs) (zf c ys):=by
 induction xs with | nil => simp [zf,v8] | cons a t ih => simp only [lCA,zf,lFC,v8] at ih ⊢;omega
lemma y6 (c:Cfg) (xs ys:List (Nat × Nat)):va c (xs++ys)=Nat.add (va c xs) (va c ys):=by
 induction xs with | nil => simp [va,v8] | cons a t ih => simp only [lCA,va,lFC,v8] at ih ⊢;omega
lemma yo (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):yx c xs=yx c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [yx,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [yx,lFC];rw [← qq,q7 (wC c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma y0 (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):v4 c xs=v4 c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [v4,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [v4,lFC];rw [← qq,q7 (wU c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma vu (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):zf c xs=zf c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [zf,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [zf,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma kz (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):va c xs=va c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [va,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [va,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma q149 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (yx c ws).testBit i=ws.any (fun p => (wC c p.1).testBit i):=by
 induction ws with
 | nil => simp [yx]
 | cons _ _ ih => simp only [yx,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma q148 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (v4 c ws).testBit i=ws.any (fun p => (wU c p.1).testBit i):=by
 induction ws with
 | nil => simp [v4]
 | cons _ _ ih => simp only [v4,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma zw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wi c w).testBit i=if i < c.k then w.testBit i else false:=by
 unfold wi;rw [nLA,nTA,hc.lok_eq,nTB]
 by_cases hi:i < c.k <;> simp [hi]
lemma vl {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (q63 c w).testBit i=if i < c.k then w.testBit (c.k+i) else false:=by
 unfold q63;rw [nLA,nTA,hc.lok_eq,nTB]
 change ((w >>> c.k).testBit i&&decide (i < c.k))=_
 rw [nTS];by_cases hi:i < c.k <;> simp [hi]
lemma q13 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (k1 c w).testBit i=if i < c.k then !(w.testBit (c.k+i)) else false:=by
 unfold k1;rw [nXO,nTX,hc.lok_eq,nTB,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma vp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wC c w).testBit i=if i < c.k then (w.testBit i ^^ w.testBit (c.k+i)) else false:=by
 unfold wC;rw [nXO,nTX,zw hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma vd {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wU c w).testBit i=if i < c.k then (!(w.testBit i)&&w.testBit (c.k+i)) else false:=by
 unfold wU;rw [nLA,nTA,vp hc,vl hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases w.testBit i <;> cases w.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q197 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wC c (Nat.xor a c.all1v)=wC c a:=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vp hc,vp hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q168 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wU c (Nat.xor a c.all1v)=Nat.land (wC c a) (wi c a):=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vd hc,nLA,nTA,vp hc,zw hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q78 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   Nat.lor (wU c (Nat.xor a c.all1v)) (wU c a)=wC c a:=by
 rw [q168 hc];apply nEQ;intro i
 rw [nLO,nLA,nTO,nTA,vp hc,zw hc,vd hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q169 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.lor a b)=Nat.xor (Nat.lor (wi c a) (wi c b)) (Nat.lor (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLO,nLO,nLO,
     nTX,nTO,nTO,nTO,nTO,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma q121 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.land a b)=Nat.xor (Nat.land (wi c a) (wi c b)) (Nat.land (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLA,nLA,nLA,
     nTX,nTA,nTA,nTA,nTA,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma q170 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wA0 c (Nat.xor a c.all1v)=Nat.xor (wA0 c a) c.m0all:=by
 have h2n:=n2P n
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nXO,nTA,nTX,hc.m0all_eq,nTB]
 change (((a^^^c.all1v) >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) =
   (((a >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) ^^ decide (i < 6*((c.sh1 - c.sh0) / 6)))
 rw [nTS,nTS,nTX,hc.all1v_eq,nTB]
 by_cases hi:i < 6*((c.sh1 - c.sh0) / 6)
 . simp [hi,show c.sh0+i < c.shTT+2 ^ n by omega]
 . simp [hi]
lemma q198 (c:Cfg) (a b:Nat):wA0 c (Nat.lor a b)=Nat.lor (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nLO,nTA,nTO]
 change (((a|||b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)||((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTO]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide
lemma q171 (c:Cfg) (a b:Nat):wA0 c (Nat.land a b)=Nat.land (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nTA]
 change (((a&&&b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)&&((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTA]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide
lemma q200 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wV1 c (Nat.xor a c.all1v)=wV1 c a:=by
 have h2n:=n2P n
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 apply wg;intro i;unfold wV1
 rw [hc.m1_eq,hc.m12_eq,kh,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show c.sh1+6*i < c.shTT+2 ^ n by omega,show c.sh1+6*i+1 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+2 < c.shTT+2 ^ n by omega,show c.sh1+6*i+3 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+4 < c.shTT+2 ^ n by omega,show c.sh1+6*i+5 < c.shTT+2 ^ n by omega,
     decide_true,bBT,jp]
 . simp [hi]
lemma y4 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.lor a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0/\Nat.land (Nat.xor c.lok rU) (wi c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,zw hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])
lemma q10 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.lor a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,zw hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]
lemma vw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.land a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0/\Nat.land (Nat.xor c.lok rU) (k1 c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,q13 hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])
lemma jb {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.land a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,q13 hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]
lemma wk {m x y:Nat} (hx:Nat.land m x=0) (hy:Nat.land m y=0) :
   Nat.land m (Nat.lor x y)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hx
 have h2:=congrArg (fun z => z.testBit i) hy
 simp only [nLA,nLO,nTA,nTO,nZT] at h1 h2 ⊢
 revert h1 h2;cases m.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> decide
lemma zz {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u≠p.1 v) :
   yx c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q149,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hne⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vp hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega)]
   cases h1:p.1 (q1 n ((aR n rp c).getD i 0)) <;>
     cases h2:p.1 (q1 n ((aR n rp c).getD (c.k+i) 0)) <;> simp_all
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vp hc,if_neg hi] at htb;cases htb
lemma q6 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) :
   v4 c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q148,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hpu,hpv⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vd hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),hpu,hpv];rfl
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vd hc,if_neg hi] at htb;cases htb
lemma q112 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV0 c (eL rp c g)) i =
     if i < (c.sh1 - c.sh0) / 6 then
       let rows:=aR n rp c
       v6 (g (q1 n (rows.getD (c.sh0+6*i) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 unfold wV0;rw [hc.m0_eq,yy]
 by_cases hi:i < (c.sh1 - c.sh0) / 6
 . simp only [hi,↓reduceIte]
   have htb:∀ off < 6,(wA0 c (eL rp c g)).testBit (6*i+off) =
       g (q1 n ((aR n rp c).getD (c.sh0+6*i+off) 0)):=by
     intro off hoff;unfold wA0
     rw [nLA,nTA,hc.m0all_eq,nTB]
     simp only [show 6*i+off < 6*((c.sh1 - c.sh0) / 6) by omega,decide_true,bATR]
     change ((eL rp c g) >>> c.sh0).testBit (6*i+off)=_
     rw [nTS,← nAA,qm _ _ (by rw [hlen];omega)]
   rw [show 6*i=6*i+0 by omega,htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
       htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)]
   simp only [nAZ]
 . simp [hi]
lemma q111 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV1 c (eL rp c g)) i =
     if i < (c.shTT - c.sh1) / 6 then
       let rows:=aR n rp c
       zq (g (q1 n (rows.getD (c.sh1+6*i) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte]
   rw [qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega)]
 . simp [hi]
lemma zi {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {g:BFn n} {tg:Nat} {r:List (BFn n × Nat)}
   (hs:s<=10)
   (htr:TR f s ((g,tg)::r))
   (hlen:((g,tg)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (wV0 c (eL rp c g))=true:=by
 set rows:=aR n rp c
 set m:=(c.sh1 - c.sh0) / 6
 have hsum:Nat.add (zf c (encWs rows r)) (wV0 c (encL rows g))=zf c (encWs rows ((g,tg)::r)):=by
   simp only [encWs,lMC,zf,lFC,v8];omega
 unfold qb;rw [hsum,hc.a29_0_eq,hc.b5_0_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV0 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV0;rw [hc.m0_eq,yy];split;exact yr _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV0 c p.1) m hf_le (encWs rows ((g,tg)::r)) (by rw [encWs,lLM,hlen];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ((g,tg)::r)).length=s+1:=by rw [encWs,lLM,hlen]
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ((g,tg)::r)).map fun p => z6 (wV0 c p.1) i) =
       ((g,tg)::r).map fun p =>
         v6 (p.1 (q1 n (rows.getD (c.sh0+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q112 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p0_ok i hi
   exact kk htr hlen _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'
lemma vt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)} (hlen:ws.length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (va c (eW rp c ws))=true:=by
 set rows:=aR n rp c
 set m:=(c.shTT - c.sh1) / 6
 unfold z3;rw [hc.a29_1_eq,hc.b5_1_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV1 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh];split;exact q52 _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV1 c p.1) m hf_le (encWs rows ws) (by rw [encWs,lLM];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ws).length=ws.length:=lLM _
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ws).map fun p => z6 (wV1 c p.1) i) =
       ws.map fun p =>
         zq (p.1 (q1 n (rows.getD (c.sh1+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q111 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p1_ok i hi
   exact hsym _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'
abbrev PN (c:Cfg) (w tg:Nat) (l2:List (Nat × Nat)) (pl2:PList):PList :=
 PList.cons w tg (wi c w) (q63 c w) (k1 c w) (wC c w) (wU c w) (wA0 c w) (wV0 c w) (wV1 c w)
   (yx c l2) (v4 c l2) (zf c l2) (va c l2) pl2
inductive PListSpec (c:Cfg):PList->List (Nat × Nat)->Prop where
 | nil:PListSpec c PList.nil []
 | cons (w tg:Nat) (tl:PList) (rest:List (Nat × Nat)) :
     PListSpec c tl rest ->
     PListSpec c
       (PN c w tg rest tl)
       ((w,tg)::rest)
lemma q82 (c:Cfg) (ws:List (Nat × Nat)) :
   ∃ pl,kt c ws=(yx c ws,v4 c ws,zf c ws,va c ws,pl)/\PListSpec c pl ws:=by
 induction ws with
 | nil => exact ⟨PList.nil,rfl,PListSpec.nil⟩
 | cons p rest ih =>
   rcases p with ⟨w,tg⟩;obtain ⟨tl,htl,hsp⟩:=ih
   refine ⟨_,?_,PListSpec.cons w tg tl rest hsp⟩;simp only [kt,htl];rfl
lemma PListSpec.pToList {c:Cfg} {pl:PList} {ws:List (Nat × Nat)} (h:PListSpec c pl ws) :
   pToList pl=ws:=by
 induction h with | nil => rfl | cons _ _ _ _ _ ih => exact congrArg _ ih
lemma q84 (c:Cfg) (ws:List (Nat × Nat)) (a ta alo nahi a0 v0a:Nat)
   (pre mid:List (Nat × Nat)) (pmU pmV0:Nat) (pl:PList) :
   we c ws a ta alo nahi a0 v0a pmU pmV0 pl =
     vx c ws (fun _ => true) a ta alo nahi a0 v0a pre pmU pmV0 mid pl:=by
 induction pl generalizing pmU pmV0 mid with
 | nil => rfl
 | cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post ih =>
   simp only [we,vx]
   have hor :
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          okOrB&&qj c.all1v ws w||!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)
        else false) =
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          if (okOrB&&qj c.all1v ws w&&true)=true then true
          else if (!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land blo).beq 0 <;> cases qj c.all1v ws (a.lor b) <;>
         cases ta.beq 1 <;> cases tb.beq 1 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.lor b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0)) <;> rfl
       . split <;> simp
   have hand :
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          okAndB&&qj c.all1v ws w||ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)
        else false) =
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          if (okAndB&&qj c.all1v ws w&&true)=true then true
          else if (ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land nbhi).beq 0 <;> cases qj c.all1v ws (a.land b) <;>
         cases ta.beq 0 <;> cases tb.beq 0 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.land b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0)) <;> rfl
       . split <;> simp
   rw [hor,hand,ih ((b,tb)::mid) (Nat.lor pmU ub) (Nat.add pmV0 v0b)]
lemma q140 (c:Cfg) (ws:List (Nat × Nat)) (preU preV0:Nat) (pre:List (Nat × Nat)) (pl:PList) :
   q26 c ws preU preV0 pl=js c ws (fun _ => true) preU preV0 pre pl:=by
 induction pl generalizing preU preV0 pre with
 | nil => rfl
 | cons a ta alo ahi nahi ca ua a0 v0a v1a postC postU postV0 postV1 suf ih =>
   simp only [q26,js,q84 c ws a ta alo nahi a0 v0a pre [] preU preV0 suf]
   split;rfl;exact ih _ _ _
lemma wu (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) :
   scanInline c s ws=scanAll c s ws (fun _ => true):=by
 unfold scanInline scanAll
 split
 . rfl
 . cases kt c ws with
   | mk totC r1 => cases r1 with
   | mk totU r2 => cases r2 with
   | mk totV0 r3 => cases r3 with
   | mk totV1 pl =>
     dsimp only
     cases Nat.sub (Nat.add s 2) (q164 ws) with
     | zero => rfl
     | succ d =>
       cases d with
       | zero =>
         cases z3 c totV1
         . simp only [bFT,↓reduceIte];rw [q140 c ws 0 0 []]
         . rfl
       | succ d2 => cases d2 <;> rfl
lemma y8 {α:Type} (x : α) (a b:List α):(x::a++b).Perm (a++x::b) :=
 List.perm_middle.symm
lemma v7 {α:Type} (p:List α) (x : α) (a b:List α) :
   (p++x::a++b).Perm (p++a++x::b):=by
 simpa [lAA] using (lPM (a:=x) (l₁:=a) (l₂:=b)).symm.append_left p
lemma q130 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w7 c ws onSurv (v4 c (pre++l1)) (zf c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w7 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w7;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q128 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w6 c ws onSurv (yx c (pre++l1)) (v4 c (pre++l1)) (zf c (pre++l1)) (va c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w6 c ws onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w6;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q126 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w5 c ws onSurv (yx c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w5 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w5;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q132 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold ke;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q97 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q98 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q98;apply q5
     apply q132 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q98;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q105 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold vx;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q65 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   js c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold js;apply q5
     apply q105 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold js;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q131 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV0 pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid))
   (hV0:pmV0=zf c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmC pmU pmV0 pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV0 pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kd;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q95 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q96 c ws hasUp onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q96;apply q5
     apply q131 c ws hasUp onSurv a ta pre mid l2 [] b tb preC preU preV0 preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV0]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q96;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q129 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre pmC pmU pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kc;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q93 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q94 c ws hasUp totV0 onSurv preC preU preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q94;apply q5
     apply q129 c ws hasUp totV0 onSurv a ta pre mid l2 [] b tb preC preU preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q94;apply q4
     apply ih ((w,tg)::pre) _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q127 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2)) (hC:pmC=yx c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre
       (yx c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre pmC mid pl=true:=by
 induction m1 generalizing mid pmC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold k9;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q91 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q92 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q92;apply q5
     apply q127 c ws onSurv a ta pre mid l2 [] b tb preC tl htl (by simp [hC])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q92;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q81 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (htr:TR f 1 ws) :
   j6 c (eW rp c ws)=true:=by
 set rows:=aR n rp c
 have hlen_rows:=zl n rp c.shTT
 rcases htr.inv_succ with
   ⟨a,ta,r,save,hperm,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases save <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hinv,_⟩,rfl⟩:=heq
     rw [List.perm_singleton.1 hperm];simp only [encWs,lMC,List.map_nil,j6,Nat.beq_eq]
     rw [← qv hc,hinv,hc.goalv_eq]
   . cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hj,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . left;rw [← qc,hj,hc.goalv_eq]
     . left;rw [q7,← qc,hj,hc.goalv_eq]
   all_goals cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hm,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . right;rw [← q9,hm,hc.goalv_eq]
     . right;rw [q108,← q9,hm,hc.goalv_eq]
   all_goals cases heq.2
lemma jc {α:Type} {a w : α} {ta:Nat} {r:List (α × Nat)} {save:Bool}
   (h:AllTagsLe3 ((a,ta)::r)):AllTagsLe3 ((w,if ta=3 then 2 else 0)::qk save (a,0) r):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . exact h p (List.mem_cons_of_mem _ hp3)
lemma k5 {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;split <;> omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;split <;> omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))
lemma yw {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))
lemma kv {n:Nat} (a b:BFn n):joinF a b=joinF b a:=by funext x;simp [joinF,Bool.or_comm]
lemma ku {n:Nat} (a b:BFn n):meetF a b=meetF b a:=by funext x;simp [meetF,Bool.and_comm]
lemma q137 {α:Type} (ka kb:Bool) (a b : α) (r:List α) :
   (qk ka a (qk kb b r)).Perm (qk kb b (qk ka a r)):=by
 cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte]
 . exact lPR _
 . exact lPR _
 . exact lPR _
 . exact List.Perm.swap _ _ _
lemma ql {α:Type} (l1 mid l2:List α) (a b : α) :
   (l1++a::mid++b::l2).Perm (a::b::(l1++mid++l2)):=by
 have h1:(l1++a::(mid++b::l2)).Perm (a::(l1++mid++b::l2)):=by
   simpa [lAA] using (lPM (a:=a) (l₁:=l1) (l₂:=mid++b::l2))
 have h2:(l1++mid++b::l2).Perm (b::(l1++mid++l2)) :=
   lPM (a:=b) (l₁:=l1++mid) (l₂:=l2)
 simpa [lAA] using h1.trans (lPC a h2)
lemma q135 (a b d:Nat):Nat.lor (Nat.lor d b) a=Nat.lor a (Nat.lor b d):=by
 rw [q7 _ a,q7 d b]
lemma jq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((joinF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.lor (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.lor (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,qc,q169 hc] at h0
 rw [q7];exact h0
lemma wq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((meetF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.land (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.land (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,q9,q121 hc] at h0
 rw [q7];exact h0
lemma zx {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((w,tw)::(x,tx)::r)) :
   Nat.lor (Nat.lor (yx c (eW rp c r)) (wC c (eL rp c x)))
     (wC c (eL rp c w))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp] at h0
 rw [q135];exact h0
lemma zp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (wi c (eL rp c a))=0:=by
 apply q10 hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0
lemma zn {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (k1 c (eL rp c a))=0:=by
 apply jb hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0
lemma yj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)} (hlen:((w,tw)::(x,tx)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,tw)::(x,tx)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h1:=vt hc hlen hsym
 simp only [qy,w1] at h1
 have heq:Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (wV1 c (eL rp c w)) =
     Nat.add (wV1 c (eL rp c w))
       (Nat.add (wV1 c (eL rp c x)) (va c (eW rp c r))):=by
   simp only [v8];omega
 rw [show yg c.sh1 c.m1 c.m12 (eL rp c w)=wV1 c (eL rp c w) from rfl,heq]
 exact h1
lemma k2 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.lor (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0;rw [q7];exact h0
lemma yt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.land (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0;rw [q7];exact h0
lemma kr {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::r))
   (hlen:((joinF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q41,q198] at h0;exact h0
lemma k8 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::r))
   (hlen:((meetF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q40,q171] at h0;exact h0
lemma vq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::(x,tx)::r))
   (hlen:((joinF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q41,q198] at h0;exact h0
lemma vf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::(x,tx)::r))
   (hlen:((meetF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q40,q171] at h0;exact h0
lemma q16 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::r))
   (hlen:((invF a,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0
lemma q15 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::(a,tx)::r))
   (hlen:((invF a,t)::(a,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c a)))
     (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0
lemma jf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w:BFn n} {t:Nat} {r:List (BFn n × Nat)} (hlen:((w,t)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,t)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (va c (eW rp c r)) (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h0:=vt hc hlen hsym
 simp only [qy,w1] at h0;rw [qt] at h0;exact h0
lemma q17 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b)
   (onSurv:List (Nat × Nat)->Bool)
   (hon:∀ zs_b,AllTagsLe3 zs_b ->
     TR f s zs_b ->
     onSurv (eW rp c zs_b)=true) :
   scanAll c s (eW rp c ws_b) onSurv=true:=by
 cases s with
 | zero => unfold scanAll;simp only [q0,↓reduceIte];exact q81 hc htr
 | succ s' =>
   have hs_nz:Nat.beq (s'+1) 0=false:=q2 (Nat.succ_ne_zero s')
   unfold scanAll;simp only [hs_nz,bFT,↓reduceIte]
   obtain ⟨pl,hprep,hsp⟩:=q82 c (eW rp c ws_b)
   rw [hprep];dsimp only;rw [q187,show (eW rp c ws_b).length=ws_b.length from lLM _]
   have hws_len_le:ws_b.length<=s'+3:=htr.len_le
   have hun_split:∀ {a ta r save},ws_b.Perm ((a,ta)::r) ->
       ta≠1->ta≠2->(ta=3->save=false) ->
       invF a≠(fun _ => false)->invF a≠(fun _ => true)->invF a≠a->(∀ x ∈ r,x.1≠invF a) ->
       TR f (s'+1) ((invF a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
       ∃ l1 l2,ws_b=l1++(a,ta)::l2/\(save=true->ta=0) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (invF a))=true /\
         AllTagsLe3 ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) /\
         TR f (s'+1)
           ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)):=by
     intro a ta r save hp h1 h2 h3 h0 h1' hna hnr hsub
     have hvw:=jo hc ws_b (invF a) h0 h1' fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm;exact hnr p hpm2
     have htags':=htags.perm hp
     have hta_le:ta<=3:=htags' (a,ta) (by simp)
     have hsave0:save=true->ta=0:=fun hst => by
       have hne3:ta≠3:=fun e => by rw [h3 e] at hst;cases hst
       omega
     obtain ⟨l1,l2,hws,hrp⟩:=q68 hp
     have hkp:((invF a,if ta=3 then 2 else 0)::qk save (a,0) r).Perm
         ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) :=
       lPC _ (by cases save <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _)
     exact ⟨l1,l2,hws,hsave0,hvw,(jc htags').perm hkp,TagRun.perm hkp hsub⟩
   have hor_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
       joinF a b≠(fun _ => false)->joinF a b≠(fun _ => true)->joinF a b≠a->joinF a b≠b->(∀ x ∈ r,x.1≠joinF a b) ->
       TR f (s'+1)
         ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠2/\tb'≠2/\(ta'=1->ka'=false)/\(tb'=1->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (joinF a' b'))=true /\
         AllTagsLe3 ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (joinF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF b a,0)::qk kb (b,if tb=3 then 1 else 0) (qk ka (a,if ta=3 then 1 else 0) (l1++mid++l2))):=by
         rw [kv b a];apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [kv a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
   have hand_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
       meetF a b≠(fun _ => false)->meetF a b≠(fun _ => true)->meetF a b≠a->meetF a b≠b->(∀ x ∈ r,x.1≠meetF a b) ->
       TR f (s'+1)
         ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠1/\tb'≠1/\(ta'≠0->ka'=false)/\(tb'≠0->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (meetF a' b'))=true /\
         AllTagsLe3 ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (meetF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF b a,if tb=3\/ta=3 then 1 else 0)::qk kb (b,0) (qk ka (a,0) (l1++mid++l2))):=by
         have hcond:(if tb=3\/ta=3 then 1 else 0)=(if ta=3\/tb=3 then 1 else 0):=by
           by_cases h1:ta=3 <;> by_cases h2:tb=3 <;> simp [h1,h2]
         rw [ku b a,hcond]
         apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [ku a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
   have hacc_rest:∀ (l1 mid l2:List (BFn n × Nat)),
       Nat.lor (yx c ([]++eW rp c l1++eW rp c mid)) (yx c (eW rp c l2))=yx c (eW rp c (l1++mid++l2)) /\
       Nat.lor (v4 c ([]++eW rp c l1++eW rp c mid)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++mid++l2)) /\
       Nat.add (zf c ([]++eW rp c l1++eW rp c mid)) (zf c (eW rp c l2))=zf c (eW rp c (l1++mid++l2)) /\
       Nat.add (va c ([]++eW rp c l1++eW rp c mid)) (va c (eW rp c l2))=va c (eW rp c (l1++mid++l2)) /\
       qx ((eW rp c l1).reverse++[]) (qx (eW rp c mid).reverse (eW rp c l2))=eW rp c (l1++mid++l2):=by
     intro l1 mid l2
     refine ⟨?_,?_,?_,?_,?_⟩
     . rw [← vc];simp [encWs,lAA]
     . rw [← zu];simp [encWs,lAA]
     . rw [← zy];simp [encWs,lAA]
     . rw [← y6];simp [encWs,lAA]
     . simp [q18,encWs,lAA]
   generalize hsl:Nat.sub (Nat.add (s'+1) 2) ws_b.length=slack
   cases slack with
   | zero =>
     have hlen:ws_b.length=s'+3:=by simp at hsl;omega
     have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc (qf htr hlen)
     simp only [hup,q0,bTA]
     rcases htr.inv_succ with
       ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
     . have hle:=hsub.len_le;have hp_len:=hp.length_eq
       cases save <;> simp [qk] at hlen hle hp_len <;> omega
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q5
       have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=k2 hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
       have hval0:=kr hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← qc,hvw,bTA]
       exact hsurv
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q4;apply q5
       have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=yt hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
       have hval0:=k8 hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← q9,hvw,hwt,bTA]
       exact hsurv
   | succ slack' =>
     cases slack' with
     | zero =>
       have hlen:ws_b.length=s'+2:=by simp at hsl;omega
       have hlen11:ws_b.length<=11:=by omega
       cases hsym1:z3 c (va c (eW rp c ws_b))
       . have hno_sym : ¬ (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
             3<=(ws_b.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :=
           fun h => by rw [vt hc hlen11 h] at hsym1;cases hsym1
         have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc ((qh htr hlen).resolve_right hno_sym)
         simp only [bFT,↓reduceIte,hup,q0,bTA]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . exfalso;have hle:=hsub.len_le;have hp_len:=hp.length_eq
           cases save
           . apply hno_sym;intro r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hv:=kk hsub (by simp [qk] at hlen hp_len ⊢;omega) r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hle_s:∀ l:List (BFn n × Nat),(l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
                 (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
               intro l;induction l with | nil => simp | cons x t iht => simp only [lMC,List.sum_cons];have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5);omega
             have hs1:=le_trans hv (hle_s _)
             simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs1
             rw [(hp.map _).sum_eq];exact hs1
           . simp [qk] at hlen hle hp_len;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,joinF] at h1s ⊢
               have:=q14 (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=k2 hc hch_up_p
             have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← qc,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [kv] at h0;exact zp hc h0
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))) 0=true:=qz hm2
             split
             . apply q4;apply q4
               simp only [q2 htb1,bNF,hokB,hval0,← qc,hvw,bTA,htb3];exact hsurv
             . simp only [hokB,q2 htb1,bNF,bTA,↓reduceIte,hval0,← qc,hvw,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zp hc (qf hsub' hch_len)
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             simp only [q2 hta1,bNF,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,meetF] at h1s ⊢
               have:=je (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=yt hc hch_up_p
             have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← q9,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [ku] at h0;exact zn hc h0
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))) 0=true:=qz hm2
             have hwt0:(if ta'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by subst htb0;simp [Nat.beq_eq]
             split
             . apply q4;apply q4
               rw [hwt];simp only [qz htb0,hokB,hval0,← q9,hvw,bTA];exact hsurv
             . rw [hwt0];simp only [hokB,qz htb0,bTA,↓reduceIte,hval0,← q9,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zn hc (qf hsub' hch_len)
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             rw [hwt];simp only [qz hta0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
       ·
         simp only [↓reduceIte,bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,_,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+l2.length+1=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           cases save
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc,q168 hc] at h0u
               rw [q7];exact h0u
             have hval0:=q16 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
             apply q130 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 pl hsp' rfl rfl
             intro pl2 hpl2;unfold w7;dsimp only;rw [hpl2.pToList,q18];apply q5
             have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
             have h1v:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [h1u,h1v,lANil,lRR,← kj,q2 hta1,q2 hta2,
               bNF,hch_up,q0,hval0,← qv hc,hvw,hta3b,bTA]
             exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=jq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=k2 hc hcu
               have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← qc,hvw];exact hsurv
             . have hcs':=jf hc (by omega:((joinF a' b',0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← qc,hcs',bOTR,bTA,hvw];exact hsurv
               . simp only [hcov,q0,← qc,hcs',bTA,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               rw [kv] at hcu;exact zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             simp only [q2 htb1,bNF,hm2,q0,hval0,← qc,hvw,bTA,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             simp only [q2 hta1,bNF,hm1,q0,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=wq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=yt hc hcu
               have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← q9,hvw,hwt];exact hsurv
             . have hcs':=jf hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← q9,hcs',bOTR,bTA,hvw,hwt];exact hsurv
               . simp only [hcov,q0,← q9,hcs',bTA,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               rw [ku] at hcu;exact zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             rw [hwt];simp only [qz htb0,hm2,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             rw [hwt];simp only [qz hta0,hm1,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
     | succ slack'' =>
       cases slack'' with
       | zero =>
         have hlen:ws_b.length=s'+1:=by simp at hsl;omega
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hl_eq:l1.length+l2.length+1=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q128 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold w6;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
           have h1v0:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
           have h1v1:Nat.add (va c ([]++eW rp c l1)) (va c (eW rp c l2))=va c (eW rp c (l1++l2)):=by rw [← y6];simp [encWs]
           simp only [h1c,h1u,h1v0,h1v1,lANil,lRR,q2 hta1,q2 hta2,
             bOS,bFT,↓reduceIte,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+1:=by simp;omega
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hor_u:(Nat.beq (Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))) c.lok ||
                 z3 c (Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a))))=true:=by
               rcases qh hsub' hch_len with hcu | hcs
               . have h0u:=q6 hc hcu
                 simp only [qy,vo,qv hc,q168 hc] at h0u
                 rw [q7] at h0u;rw [h0u,q0];rfl
               . have h1s:=vt hc (by omega:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length<=11) hcs
                 simp only [qy,w1,qv hc,q200 hc] at h1s
                 have hcomm:Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a)) =
                     Nat.add (wV1 c (eL rp c a)) (va c (eW rp c (l1++l2))):=by simp;omega
                 rw [hcomm,h1s];simp
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,hor_u,← qv hc,hvw,hta3b,← kj,bTA];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl
             rw [h03] at htc hsub'
             have hch_len:((invF a,0)::(a,0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc] at h0u
               rw [← qq,q78 hc,q7] at h0u;exact h0u
             have hval0:=q15 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hta0,q0,hch_up,hval0,← qv hc,hvw,← kj,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=jq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← qc,hvw,bTA,bOT]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
                 rw [kv] at hcu;exact zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               simp only [q2 htb1,bNF,hcov,hm2,q0,bTOR,← qc,hvw,htb3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,htb3b,bTA];exact hsurv
               . right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,hvw,htb3b,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               simp only [q2 hta1,bNF,hcov,hm1,q0,bTOR,← qc,hvw,hta3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,hta3b,bTA];exact hsurv
               . left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,hvw,hta3b,bTA];exact hsurv
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have htot_eq:zf c (eW rp c ((a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)))=zf c (eW rp c ws_b):=by
               have h1:zf c (eW rp c ws_b)=zf c (eW rp c ((a',ta')::(b',tb')::(l1++mid++l2))):=by
                 rw [hws];exact vu c ((ql l1 mid l2 _ _).map _)
               rw [h1];rfl
             have hval0:=kr hc hs hsub' hch_len;rw [htot_eq] at hval0
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [q2 hta1,q2 htb1,bNF,hval0,← qc,hvw,hta3b,htb3b,bTA]
             exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=wq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← q9,hvw,bTA,bOT,hwt_or]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
                 rw [ku] at hcu;exact zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               rw [hwt_or];simp only [qz htb0,hcov,hm2,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               rw [hwt_or];simp only [qz hta0,hcov,hm1,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_len:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             have hval0:=k8 hc hs (TagRun.perm hch_perm hsub') (by rw [← hch_perm.length_eq];exact hch_len)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [hta0,htb0,q0,hval0,← q9,hvw,bTA];exact hsurv
       | succ _ =>
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q126 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 pl hsp' rfl
           intro pl2 hpl2;unfold w5;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           simp only [h1c,lANil,lRR,q2 hta1,q2 hta2,
             bNF,bTA,← qv hc,hvw,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,bTA,hta3b,← kj];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl;rw [h03] at htc hsub'
             have hch_perm:((invF a,0)::(a,0)::(l1++l2)).Perm ((invF a,0)::ws_b) :=
               lPC _ (by rw [hws,hta0];exact List.perm_middle.symm)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hta0,q0,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← qc,hvw,bOT]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [jq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;right;simp only [q2 htb1,bNF,hcov,q0,htb3b,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;left;right;simp only [q2 hta1,bNF,hcov,q0,hta3b,bTA];exact hon _ htc hsub'
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             right;simp only [q2 hta1,q2 htb1,bNF,hta3b,htb3b,bTA];exact hon _ htc hsub'
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q4;apply q5
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← q9,hvw,bOT,hwt_or]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [wq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;right;simp only [qz htb0,q0,hcov,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;left;right;simp only [qz hta0,q0,hcov,bTA];exact hon _ htc hsub'
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             right;simp only [hta0,htb0,q0,bTA]
             exact hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
lemma wj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b) :
   scanInline c s (eW rp c ws_b)=true:=by
 rw [wu]
 exact q17 hc hs htags htr (fun _ => true) (fun _ _ _ => rfl)
def ki {n:Nat}:Nat->List (BFn n × Nat)->BFn n × Nat
 | _,[] => ((fun _ => false),0)
 | 0,a::_ => a
 | k+1,_::rest => ki k rest
def yl {n:Nat}:Nat->List (BFn n × Nat)->List (BFn n × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::yl k rest
def q136 {n:Nat} (code:Nat) (ws:List (BFn n × Nat)):List (BFn n × Nat) :=
 if Nat.ble code 32 then
   let c:=Nat.sub code 1;let i:=Nat.shiftRight c 1;let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=ki i ws;let wt:=if Nat.beq ta 3 then 2 else 0
   let w:=invF a;let r:=yl i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   let rem:=Nat.sub code 33
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=ki i ws;let (b,tb):=ki j ws
   let r:=yl i (yl j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (meetF a b,wt)::r2
   else
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (joinF a b,0)::r2
def q31 {n:Nat} (xs_b:List (BFn n × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (BFn n × Nat)
 | 0,_,_ => xs_b
 | d+1,s,j =>
   let e:=q192 (PT s) j;let code:=Nat.land e 1023
   if Nat.beq code 0 then xs_b
   else q136 code (q31 xs_b PT d (Nat.add s 1) (Nat.land (Nat.shiftRight e 10) 8191))
def RgenB {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat):List (BFn n × Nat) :=
 q31 xs_b PT (Nat.sub cap s) s j
lemma q27 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   jw i (encWs rows ws)=(encL rows (ki i ws).1,(ki i ws).2):=by
 induction i generalizing ws with
 | zero => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ _ => rfl
 | succ k ih => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ t => exact ih t
lemma q28 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   q38 i (encWs rows ws)=encWs rows (yl i ws):=by
 induction i generalizing ws with
 | zero => cases ws <;> rfl
 | succ k ih => cases ws with | nil => rfl | cons p t => simp only [qy,q38,yl,ih]
lemma q153 {n:Nat} (rows:List Nat) (code:Nat) (ws:List (BFn n × Nat)) :
   q203 (2 ^ rows.length - 1) code (encWs rows ws)=encWs rows (q136 code ws):=by
 unfold q203 q136;simp only [v5]
 split
 . simp only [q27,q28];split <;> simp [encWs,q145]
 . simp only [q27,q28]
   split
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,q9]
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,qc]
lemma q119 {n:Nat} (rows:List Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (d s j:Nat) :
   q120 (2 ^ rows.length - 1) (encWs rows xs_b) PT d s j=encWs rows (q31 xs_b PT d s j):=by
 induction d generalizing s j with
 | zero => rfl
 | succ d ih => simp only [q120,q31,v5];split;rfl;rw [ih,q153]
lemma q102 {n:Nat} (rows:List Nat) (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ rows.length - 1) cap (encWs rows xs_b) PT s j=encWs rows (RgenB cap xs_b PT s j) :=
 q119 rows xs_b PT (Nat.sub cap s) s j
lemma q150 {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ (2 ^ n) - 1) cap (encTTWs n xs_b) PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 have hlen:(List.range (2 ^ n)).length=2 ^ n:=List.length_range
 simpa [encTTWs,encWs,encTT,hlen] using q102 (List.range (2 ^ n)) cap xs_b PT s j
lemma wm {n:Nat} (i:Nat) (ws:List (BFn n × Nat)):(yl i ws).Sublist ws:=by
 induction i generalizing ws with
 | zero => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons a (List.Sublist.refl t)
 | succ k ih => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons_cons a (ih t)
lemma vj {α:Type} (b:Bool) (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (if b then x::l else l):=by
 intro p hp;cases b
 . exact hl p hp
 . rcases List.mem_cons.1 hp with rfl | h'
   . exact hx
   . exact hl p h'
lemma vn {α:Type} (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (x::l):=by
 intro p hp;rcases List.mem_cons.1 hp with rfl | h';exact hx;exact hl p h'
lemma q43 {n:Nat} (code:Nat) {ws:List (BFn n × Nat)} (h:AllTagsLe3 ws) :
   AllTagsLe3 (q136 code ws):=by
 unfold q136
 have her:∀ i,AllTagsLe3 (yl i ws):=fun i p hp => h p ((wm i ws).subset hp)
 have her2:∀ i j,AllTagsLe3 (yl i (yl j ws)):=fun i j p hp => her j p ((wm i _).subset hp)
 split
 . dsimp only;split
   . exact vn _ _ (by split <;> omega) (vn _ _ (by omega) (her _))
   . exact vn _ _ (by split <;> omega) (her _)
 . dsimp only;split
   . exact vn _ _ (by split <;> omega)
       (vj _ _ _ (by omega) (vj _ _ _ (by omega) (her2 _ _)))
   . exact vn _ _ (by omega)
       (vj _ _ _ (by split <;> omega) (vj _ _ _ (by split <;> omega) (her2 _ _)))
lemma q59 {n:Nat} (cap:Nat) {xs_b:List (BFn n × Nat)} (h:AllTagsLe3 xs_b)
   (PT:Nat->Nat) (s j:Nat):AllTagsLe3 (RgenB cap xs_b PT s j):=by
 unfold RgenB;generalize Nat.sub cap s=d
 induction d generalizing s j with
 | zero => exact h
 | succ d ih => simp only [q31];split;exact h;exact q43 _ (ih _ _)
lemma q195 (T h fuel lo hi:Nat) (hlo:lo < hi):q167 T h fuel lo hi < hi:=by
 induction fuel generalizing lo hi with
 | zero => exact hlo
 | succ fuel ih =>
   simp only [q167,v5];split
   . rename_i hle;have hle':lo+2<=hi:=Eq.mp Nat.ble_eq hle
     have hdiv:Nat.div (Nat.add lo hi) 2=(lo+hi) / 2:=rfl
     have hmid_lt:Nat.div (Nat.add lo hi) 2 < hi:=by rw [hdiv];omega
     have hlo_lt_mid:lo < Nat.div (Nat.add lo hi) 2:=by rw [hdiv];omega
     split;exact ih _ hi hmid_lt;exact lt_trans (ih lo _ hlo_lt_mid) hmid_lt
   . exact hlo
lemma j8 (NN FL HT:Nat->Nat) (s h:Nat) (hne:q85 NN FL HT s h≠999999) :
   q85 NN FL HT s h < NN s:=by
 unfold q85 at hne ⊢;simp only [v5] at hne ⊢
 cases hz:Nat.beq (NN s) 0
 . rw [hz] at hne;simp only [bFT,↓reduceIte] at hne ⊢
   have hpos : 0 < NN s:=by have:=y3 hz;omega
   cases hm:Nat.beq (q205 (HT s) (q167 (HT s) h (FL s) 0 (NN s))) h
   . rw [hm] at hne;simp only [bFT,↓reduceIte] at hne;exact absurd rfl hne
   . simp only [↓reduceIte];exact q195 (HT s) h (FL s) 0 (NN s) hpos
 . rw [hz] at hne;exact absurd rfl hne
lemma q181 (a b:Nat × Nat):twEq a b=true ↔ a=b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;simp [twEq,Nat.beq_eq]
lemma q142 (x:Nat × Nat) (bs bs':List (Nat × Nat)) (h:jy x bs=some bs'):bs.Perm (x::bs'):=by
 induction bs generalizing bs' with
 | nil => simp [jy] at h
 | cons a t ih =>
   simp only [jy] at h;split at h
   . rename_i heq;cases h;rw [(q181 x a).1 heq]
   . cases he:jy x t with
     | none => rw [he] at h;cases h
     | some r => rw [he] at h;cases h;exact (lPC a (ih r he)).trans (List.Perm.swap x a r)
lemma y5 (xs ys:List (Nat × Nat)) (h:jk xs ys=true):xs.Perm ys:=by
 induction xs generalizing ys with
 | nil => cases ys with | nil => exact List.Perm.nil | cons _ _ => simp [jk] at h
 | cons a t ih =>
   simp only [jk] at h
   cases he:jy a ys with
   | none => rw [he] at h;cases h
   | some ys' => rw [he] at h;exact (lPC a (ih ys' h)).trans (q142 a ys ys' he).symm
lemma q113 (x:Nat × Nat) (xs:List (Nat × Nat)):(q62 x xs).Perm (x::xs):=by
 induction xs with | nil => exact lPR _ | cons a t ih => simp only [q62];split;exact lPR _;exact (lPC a ih).trans (List.Perm.swap x a t)
lemma q64 (xs:List (Nat × Nat)):(q125 xs).Perm xs:=by
 induction xs with | nil => exact List.Perm.nil | cons a t ih => exact (q113 a (q125 t)).trans (lPC a ih)
lemma kg {n:Nat} (rp shTT:Nat) (ws:List (BFn n × Nat)) :
   q72 shTT (encWs (allRows n rp shTT) ws)=encTTWs n ws:=by
 induction ws with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨g,tg⟩;simp only [qy,q49,q72,v5,ih]
   have hsh:=q116 (n:=n) (q106 rp shTT) g
   rw [jj rp shTT] at hsh;rw [allRows,hsh]
lemma yk {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g) (ws:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     wx g (encTTWs n ws)=encTTWs n (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 obtain ⟨π,hbij,hfix,happ⟩:=hg;refine ⟨π,hbij,hfix,?_⟩
 induction ws with | nil => rfl | cons p t ih => rcases p with ⟨h,tg⟩;simp only [q49,lMC,wx,v5,happ,ih]
lemma yv {α β:Type} {f : α->β} (hf:Function.Injective f) :
   ∀ {xs ys:List α},(xs.map f).Perm (ys.map f)->xs.Perm ys
 | [],ys,hp => by cases ys with | nil => exact List.Perm.nil | cons _ _ => exact absurd hp.length_eq (by simp)
 | x::xs,ys,hp => by
   have hmem:f x ∈ ys.map f:=hp.subset (by simp)
   obtain ⟨y,hy,heq⟩:=List.mem_map.1 hmem
   have hxy:y=x:=hf heq;subst hxy
   obtain ⟨l1,l2,rfl⟩:=List.append_of_mem hy
   have hp2:(f y::xs.map f).Perm (f y::(l1++l2).map f) :=
     hp.trans (by simpa [lMA] using (lPM (a:=f y) (l₁:=l1.map f) (l₂:=l2.map f)))
   exact (lPC y (yv hf (List.Perm.cons_inv hp2))).trans List.perm_middle.symm
lemma zv {n:Nat} (xs ys:List (BFn n × Nat)):(encTTWs n xs).Perm (encTTWs n ys) ↔ xs.Perm ys:=by
 constructor
 . intro hp
   have hinj:Function.Injective (fun p:BFn n × Nat => (encTT n p.1,p.2)):=fun ⟨_,_⟩ ⟨_,_⟩ e => by
     simp only [Prod.mk.injEq] at e;exact Prod.ext (yc e.1) e.2
   exact yv hinj hp
 . exact fun hp => hp.map _
lemma q19 {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g)
   (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q69 g ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q69;dsimp only;split
 . obtain ⟨π,hbij,hfix,hmg⟩:=yk hg ws_b;refine ⟨π,hbij,hfix,?_⟩
   have hmap_eq:∀ l,wx g l=l.map (fun p => (ym g p.1,p.2)):=fun l => by
     induction l with | nil => rfl | cons p t ih => simp [wx,v5,ih]
   have hmgp:(wx g ws).Perm (wx g (encTTWs n ws_b)):=by rw [hmap_eq,hmap_eq];exact hp.map _
   exact (q64 _).trans (hmgp.trans (by rw [hmg]))
 . exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hp⟩
lemma q20 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q35 gens ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 induction gens generalizing ws ws_b with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa [q35] using hp⟩
 | cons g rest ih =>
   obtain ⟨π1,hb1,hf1,hp1⟩:=q19 (hgens g (by simp)) ws ws_b hp
   obtain ⟨π2,hb2,hf2,hp2⟩:=ih (fun g' hm => hgens g' (List.mem_cons_of_mem g hm)) (q69 g ws) _ hp1
   exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [q35,lMMp,fCD] using hp2⟩
lemma q152 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws_b:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q186 gens (encTTWs n ws_b)).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q186;have hs0:=q64 (encTTWs n ws_b)
 cases gens with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hs0⟩
 | cons g rest =>
   cases rest with
   | nil => exact q19 (hgens g (by simp)) _ ws_b hs0
   | cons g2 rest2 =>
     obtain ⟨π1,hb1,hf1,hp1⟩:=q20 (g::g2::rest2) hgens _ ws_b hs0
     obtain ⟨π2,hb2,hf2,hp2⟩:=q20 (g::g2::rest2) hgens _ _ hp1
     exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hp2⟩
def w2 {n:Nat} (f:BFn n) (rows:List Nat) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Prop :=
 ∀ s zs_b,findFn s (encWs rows zs_b)=true ->
   ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),
     Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (zs_b.map fun p => ((fun x => p.1 (π x)),p.2)).Perm (R_bfn s j)
lemma q37 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (path:List (List (Nat × Nat × Nat × Nat))) (hpath:∀ g ∈ path,vh f g)
   (NN FL HT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutPath shTT salt path Rtt NN FL HT):=by
 have hloop:∀ p:List (List (Nat × Nat × Nat × Nat)),(∀ g ∈ p,vh f g)->∀ s (zs_b:List (BFn n × Nat)),
     vm salt Rtt NN FL HT s p (encTTWs n zs_b)=true ->
     ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
       (zs_b.map fun q => ((fun x => q.1 (π x)),q.2)).Perm (R_bfn s j):=by
   intro p;induction p with
   | nil =>
     intro _ s zs_b h
     simp only [vm,v5,bAT,bNT,zh] at h
     obtain ⟨hne,hpeq⟩:=h;rw [hRtt] at hpeq
     exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
       by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
   | cons g rest ih =>
     intro hp s zs_b h;simp only [vm,v5] at h
     split at h
     . rename_i h0;simp only [bAT,bNT,zh] at h0
       obtain ⟨hne,hpeq⟩:=h0;rw [hRtt] at hpeq
       exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
         by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
     . obtain ⟨π1,hb1,hf1,hmg⟩:=yk (hp g (by simp)) zs_b;rw [hmg] at h
       obtain ⟨j,hj,π2,hb2,hf2,hperm⟩:=ih (fun g' hm => hp g' (List.mem_cons_of_mem g hm)) s _ h
       exact ⟨j,hj,π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hperm⟩
 intro s zs_b h;unfold findAutPath at h;rw [kg] at h;exact hloop path hpath s zs_b h
lemma q55 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (gens:List (List (Nat × Nat × Nat × Nat))) (hgens:∀ g ∈ gens,vh f g)
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (haut:∀ k,vh f (aut k))
   (NN FL HT PT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutGen shTT salt gens aut Rtt NN FL HT PT):=by
 intro s zs_b h;unfold findAutGen at h;simp only [v5,kg] at h
 split at h;· cases h
 . rename_i hne_b
   have hne:=y3 (Bool.eq_false_iff.2 hne_b)
   set j:=q85 NN FL HT s (q75 salt (q186 gens (encTTWs n zs_b)))
   have hj:j < NN s:=j8 NN FL HT s _ hne
   set aidx:=Nat.shiftRight (q192 (PT s) j) 23
   obtain ⟨π1,hb1,hf1,hori⟩:=q152 gens hgens zs_b
   obtain ⟨π2,hb2,hf2,hmg⟩:=yk (haut aidx) (R_bfn s j)
   rw [hRtt,hmg] at h
   have hperm_b:=(zv _ _).1 (hori.symm.trans (y5 _ _ h))
   obtain ⟨π2_inv,hleft,hright⟩:=Function.bijective_iff_has_inverse.1 hb2
   have hinv_bij:Function.Bijective π2_inv:=Function.bijective_iff_has_inverse.2 ⟨π2,hright,hleft⟩
   have hinv_fix:∀ x,f (π2_inv x)=f x:=fun x => by have:=hf2 (π2_inv x);rw [hright x] at this;exact this.symm
   refine ⟨j,hj,π1 ∘ π2_inv,hb1.comp hinv_bij,fun x => by simp [hf1,hinv_fix],?_⟩
   have hmap_inv:=hperm_b.map (fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2))
   have hrhs:(((R_bfn s j).map fun p => ((fun x => p.1 (π2 x)),p.2)).map fun p => ((fun x => p.1 (π2_inv x)),p.2))=R_bfn s j:=by
     rw [lMMp]
     have hfg:((fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2)) ∘ fun p:BFn n × Nat => ((fun x => p.1 (π2 x)),p.2))=id:=by
       funext ⟨g,tg⟩;simp only [fCD,id];congr 1;funext x;exact congrArg g (hright x)
     rw [hfg,List.map_id]
   rw [hrhs] at hmap_inv
   simpa [lMMp,fCD] using hmap_inv
lemma span_sound (P:Nat->Bool) (len start:Nat) (h:span P len start=true) :
   ∀ i,start<=i->i < start+len->P i=true:=by
 induction len generalizing start with
 | zero => intro i h1 h2;omega
 | succ m ih =>
   simp only [span,bAT] at h;intro i h1 h2
   by_cases heq:i=start
   . subst heq;exact h.1
   . exact ih (start+1) h.2 i (by omega) (by omega)
lemma q179 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (cap:Nat) (hcap:cap<=11) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (R:Nat->Nat->List (Nat × Nat))
   (hR:∀ s j,R s j=eW rp c (R_bfn s j))
   (hTags:∀ s j,AllTagsLe3 (R_bfn s j))
   (findFn:Nat->List (Nat × Nat)->Bool)
   (hFind:w2 f (aR n rp c) NN R_bfn findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true) :
   ∀ s ≤ cap,∀ i < NN s,
     ¬ TR f s (R_bfn s i):=by
 intro s;induction s with
 | zero =>
   intro _ i hi htr;have hb:=hBar 0 (nZL cap) i hi;obtain ⟨tg,heq⟩:=htr.inv_zero
   simp only [bar,hR,heq,encWs,lMC,List.map_nil,hc.goalv_eq,q0] at hb;cases hb
 | succ s ih =>
   intro hs i hi htr
   have hih:=ih (by omega)
   have hb:=hBar (s+1) hs i hi
   simp only [bar,v8] at hb
   have hscan_false:scanAll c s (R (s+1) i)
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=false:=by simpa using hb
   have hscan_true:scanAll c s (eW rp c (R_bfn (s+1) i))
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=true:=by
     apply q17 hc (by omega:s<=10) (hTags (s+1) i) htr
     intro zs_b hzt htr_z
     have hnf:findFn s (eW rp c zs_b)=false:=by
       cases hf:findFn s (eW rp c zs_b)
       . rfl
       . exfalso;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s zs_b hf
         exact hih j hj (TagRun.perm hperm (wp π hbij hfix htr_z))
     simp only [hnf,bNF,bTA]
     cases s with
     | zero => rfl
     | succ s' =>
       simp only [q2 (Nat.succ_ne_zero s'),Bool.false_or]
       exact wj hc (by omega:s'<=10) hzt htr_z
   rw [hR,hscan_true] at hscan_false;cases hscan_false
def checkGenList (n:Nat) (f:BFn n):List (List (Nat × Nat × Nat × Nat))->List (List (Nat × Nat))->Bool
 | [],[] => true
 | sw::sws,ps::pss =>
   kq n ps&&(q163 n ps==sw)&&(ym sw (encTT n f)==encTT n f)&&checkGenList n f sws pss
 | _,_ => false
lemma ye (n:Nat) (f:BFn n) (gsw:List (List (Nat × Nat × Nat × Nat)))
   (gsp:List (List (Nat × Nat))) (h:checkGenList n f gsw gsp=true) :
   ∀ sw ∈ gsw,vh f sw:=by
 induction gsw generalizing gsp with
 | nil => intro _ hm;cases hm
 | cons sw sws ih =>
   cases gsp with
   | nil => simp [checkGenList] at h
   | cons ps pss =>
     simp only [checkGenList,bAT,beq_iff_eq] at h
     obtain ⟨⟨⟨hv,hmk⟩,hfix⟩,hrest⟩:=h
     intro g hg;rcases List.mem_cons.1 hg with rfl | hg2
     . rw [← hmk] at hfix ⊢;exact kw f ps hv hfix
     . exact ih pss hrest g hg2
def checkAutFn (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat))):Bool :=
 (List.range autp.length).all fun i =>
   let ps:=autp.getD i []
   kq n ps&&(q163 n ps==aut i)&&(ym (aut i) (encTT n f)==encTT n f)
lemma q58 (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat))
   (autp:List (List (Nat × Nat))) (h:checkAutFn n f aut autp=true) (hdef:∀ i ≥ autp.length,aut i=[]) :
   ∀ i,vh f (aut i):=by
 intro i;by_cases hi:i < autp.length
 . have h1:=List.all_eq_true.1 h i (List.mem_range.2 hi)
   simp only [bAT,beq_iff_eq] at h1
   obtain ⟨⟨hv,hmk⟩,hfix⟩:=h1;rw [← hmk] at hfix ⊢;exact kw f (autp.getD i []) hv hfix
 . rw [hdef i (by omega)];exact q138 f
def w8 (n:Nat) (f:BFn n):Bool :=
 let t:=encTT n f;!(Nat.beq t 0)&&!(Nat.beq t (2 ^ (2 ^ n) - 1))
lemma ju (n:Nat) (f:BFn n) (h:w8 n f=true) :
   ∃ y y':Fin n->Bool,f y≠f y':=by
 unfold w8 at h;simp only [bAT,bNT,zh] at h
 obtain ⟨hne0,hne1⟩:=h
 have hex1:∃ r < 2 ^ n,f (q1 n r)=true:=by
   by_contra hall;push Not at hall;apply hne0;apply nEQ;intro r
   rw [vr,nZT];split;exact Bool.eq_false_iff.2 (hall r ‹_›);rfl
 have hex0:∃ r < 2 ^ n,f (q1 n r)=false:=by
   by_contra hall;push Not at hall;apply hne1;apply nEQ;intro r
   rw [vr,nTB];split
   . rename_i hr;have:f (q1 n r)=true:=by cases hf:f (q1 n r);exact absurd hf (hall r hr);rfl
     simp [hr,this]
   . rename_i hr;simp [hr]
 obtain ⟨r1,_,h1⟩:=hex1;obtain ⟨r0,_,h0⟩:=hex0
 exact ⟨q1 n r1,q1 n r0,by rw [h1,h0];decide⟩
def q77 (n:Nat) (f:BFn n):Bool :=
 (List.finRange n).all fun v =>
   (List.range (2 ^ n)).any fun r => let x:=q1 n r;f (Function.update x v (!x v))!=f x
lemma q44 (n:Nat) (f:BFn n) (h:q77 n f=true) :
   ∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x:=by
 intro v;have h1:=List.all_eq_true.1 h v (List.mem_finRange v)
 obtain ⟨r,_,hr⟩:=List.any_eq_true.1 h1;exact ⟨q1 n r,bne_iff_ne.1 hr⟩
def q147 (c:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (xs:List (Nat × Nat)) (s0:Nat):Bool :=
 findFn s0 xs||!(Nat.beq s0 0||scanInline c (Nat.sub s0 1) xs)
def verifyBase (n cap:Nat) (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Bool :=
 let rows:=aR n rp c
 let xs_b:=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 Nat.ble cap 11&&w3 n f rp c&&w8 n f&&q77 n f &&
 ((List.finRange n).all fun i => Nat.ble (initTags i) 3) &&
 (xs==encWs rows xs_b)&&(xstt==encTTWs n xs_b) &&
 ((List.range (cap+1)).all fun s0 => Nat.blt (Nat.add s0 1) n||q147 c findFn xs s0)
lemma prove_base {n cap:Nat} (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (NN PT:Nat->Nat) (findFn:Nat->List (Nat × Nat)->Bool)
   (hBase:verifyBase n cap f rp c initTags xs xstt findFn=true)
   (hFind:w2 f (aR n rp c) NN
     (RgenB cap (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)) PT) findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 unfold verifyBase at hBase
 simp only [bAT,Nat.ble_eq,beq_iff_eq] at hBase
 rcases hBase with ⟨⟨⟨⟨⟨⟨⟨hcap,hcfg_b⟩,hnc_b⟩,hdep_b⟩,htags_b⟩,hxs⟩,hxstt⟩,hroots⟩
 have hc:=jn n f rp c hcfg_b
 have hnc:=ju n f hnc_b
 have hdep:=q44 n f hdep_b
 set xs_b:List (BFn n × Nat):=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 have hTags_xs:AllTagsLe3 xs_b:=fun p hp => by
   rw [List.mem_ofFn] at hp;obtain ⟨i,rfl⟩:=hp
   exact Eq.mp Nat.ble_eq (List.all_eq_true.1 htags_b i (List.mem_finRange i))
 have hlen_rows:=zl n rp c.shTT
 have hR:∀ s j,Rgen c.all1v cap xs PT s j=eW rp c (RgenB cap xs_b PT s j):=fun s j => by
   rw [hxs,hc.all1v_eq,← hlen_rows,q102]
 have hNoRun:=q179 hc cap hcap NN (RgenB cap xs_b PT) (Rgen c.all1v cap xs PT) hR
   (fun s j => q59 cap hTags_xs PT s j) findFn hFind hBar
 intro t hcirc;by_contra hlt;have hle:t<=cap:=by omega
 obtain ⟨s0,hs0,htr⟩:=q88 f cap initTags hnc hdep htag t hle hcirc
 have hroot:=List.all_eq_true.1 hroots s0 (List.mem_range.2 (by omega))
 simp only [bOT] at hroot
 rcases hroot with hlen_small | hchk
 . have hlt_n:s0+1 < n:=by simpa [Nat.blt_eq,v8] using hlen_small
   have htr_len:n<=s0+1:=by simpa using htr.len_le
   omega
 . unfold q147 at hchk;simp only [bOT] at hchk
   rcases hchk with hfound | hkill
   . rw [hxs] at hfound;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s0 xs_b hfound
     exact hNoRun s0 hs0 j hj (TagRun.perm hperm (wp π hbij hfix htr))
   . simp only [bNT,Bool.or_eq_false_iff,zh] at hkill
     obtain ⟨hs0_nz,hinl_f⟩:=hkill
     cases s0 with
     | zero => exact hs0_nz rfl
     | succ s' =>
       rw [hxs] at hinl_f;have hinl_t:=wj hc (by omega:s'<=10) hTags_xs htr
       change scanInline c s' (eW rp c xs_b)=false at hinl_f
       rw [hinl_t] at hinl_f;cases hinl_f
lemma Rgen_encTTWs_eq {n all1tt cap:Nat} (hall:all1tt=2 ^ 2 ^ n - 1)
   (xs_b:List (BFn n × Nat)) (xstt:List (Nat × Nat)) (hxs:xstt=encTTWs n xs_b)
   (PT:Nat->Nat) (s j:Nat) :
   Rgen all1tt cap xstt PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 rw [hall,hxs];exact q150 cap xs_b PT s j
lemma span_all_sound {P:Nat->Nat->Bool} {cap:Nat} {NN:Nat->Nat}
   (h:(List.range (cap+1)).all (fun s => span (P s) (NN s) 0)=true) :
   ∀ s ≤ cap,∀ i < NN s,P s i=true:=fun s hs i hi =>
 span_sound (P s) (NN s) 0 (List.all_eq_true.1 h s (List.mem_range.2 (by omega))) i (nZL _) (by omega)
lemma fun_eq_of_encTT {n:Nat} (f g:BFn n) (h:Nat.beq (encTT n f) (encTT n g)=true):f=g :=
 yc (Eq.mp Nat.beq_eq h)
lemma prove_basePath {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw path:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (hsub:path.all (fun g => gsw.contains g)=true)
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutPath c.shTT salt path (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutPath c.shTT salt path (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 have hg:=ye n f gsw gsp hgen
 have hp:∀ g ∈ path,vh f g:=fun g hgp =>
   hg g (List.contains_iff_mem.1 (List.all_eq_true.1 hsub g hgp))
 exact prove_base f rp c initTags xs xstt NN PT _ hBase
   (q37 f rp c.shTT salt path hp NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_baseGen {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (haut:checkAutFn n f aut autp=true)
   (hdef:∀ i ≥ autp.length,aut i=[])
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q55 f rp c.shTT salt gsw (ye n f gsw gsp hgen)
     aut (q58 n f aut autp haut hdef) NN FL HT PT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
structure BaseEntry where
 k:Nat
 E:List (Fin k × Fin k)
 lb:Nat
def BaseTableOk (bs:List BaseEntry):Prop :=
 ∀ b ∈ bs,∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s
def q61 {n:Nat}:List (Fin n)->Bool
 | [] => true
 | a::t => !t.contains a&&q61 t
lemma q83 {n:Nat} (l:List (Fin n)) (h:q61 l=true):l.Nodup:=by
 induction l with
 | nil => exact List.nodup_nil
 | cons a t ih =>
   simp only [q61,bAT,bNT] at h
   exact List.nodup_cons.2 ⟨by simpa [List.contains_eq_mem] using h.1,ih h.2⟩
inductive GTree (n:Nat) where
 | emp
 | base (idx:Nat) (π:List Nat)
 | f0 (p:Fin n) (t:GTree n)
 | f1 (p:Fin n) (t:GTree n)
 | b2 (p:Fin n) (t0 t1:GTree n)
def checkGTree (bs:List BaseEntry) (n:Nat)
   (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1))) (req:Nat):GTree (n+1)->Bool
 | GTree.emp => E.isEmpty&&q61 A&&Nat.ble req (A.length - 1)
 | GTree.base idx π =>
   match bs[idx]? with
   | none => false
   | some b =>
     if h : 0 < b.k then
       A.isEmpty&&Nat.ble req b.lb &&
       isoCheck E b.E (fun i => ⟨π.getD i.1 0 % b.k,Nat.mod_lt _ h⟩)
     else false
 | GTree.f0 p t =>
   let A':=fix0A A p;let E':=fix0E E p
   depCheck A E p&&(!A'.isEmpty||!E'.isEmpty)&&checkGTree bs n A' E' (req - 1) t
 | GTree.f1 p t =>
   let A':=fix1A A E p;let E':=fix1E A E p
   depCheck A E p&&!A.contains p&&E.all (fun e => e.1!=e.2) &&
     (!A'.isEmpty||!E'.isEmpty)&&checkGTree bs n A' E' (req - 1) t
 | GTree.b2 p t0 t1 =>
   let A0:=fix0A A p;let E0:=fix0E E p
   let A1:=fix1A A E p;let E1:=fix1E A E p
   depCheck A E p&&!A.contains p&&E.all (fun e => e.1!=e.2) &&
     (!A0.isEmpty||!E0.isEmpty)&&(!A1.isEmpty||!E1.isEmpty) &&
     checkGTree bs n A0 E0 (req - 2) t0&&checkGTree bs n A1 E1 (req - 2) t1
lemma checkGTree_sound (bs:List BaseEntry) (hbs:BaseTableOk bs) {n:Nat}
   (t:GTree (n+1)) (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1))) (req:Nat)
   (h:checkGTree bs n A E req t=true) :
   ∀ s:Nat,HasCircuitSize (n+1) (gfn A E) s->req<=s:=by
 induction t generalizing A E req with
 | emp =>
   simp only [checkGTree,bAT,List.isEmpty_iff] at h
   rcases h with ⟨⟨rfl,hnd⟩,hle⟩
   intro s hs;have h1:=q176 A (q83 A hnd) s hs
   have h2:req<=A.length - 1:=Eq.mp Nat.ble_eq hle;omega
 | base idx π =>
   unfold checkGTree at h
   cases hb:bs[idx]? with
   | none => rw [hb] at h;cases h
   | some b =>
     rw [hb] at h;dsimp only at h
     split at h
     . rename_i hk
       simp only [bAT,List.isEmpty_iff] at h
       rcases h with ⟨⟨rfl,hle⟩,hiso⟩
       have hbmem:b ∈ bs:=List.mem_of_getElem? hb
       intro s hs
       have h1:=q191 E b.E (fun i => ⟨π.getD i.1 0 % b.k,Nat.mod_lt _ hk⟩) hiso (hbs b hbmem) s hs
       have h2:req<=b.lb:=Eq.mp Nat.ble_eq hle;omega
     . cases h
 | f0 p t ih =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨hdep,hnc⟩,hsub⟩
   intro s hs;have h1:=q190 A E p (fix0A A p) (fix0E E p) (req - 1) hdep rfl rfl hnc (ih _ _ _ hsub) s hs;omega
 | f1 p t ih =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨⟨⟨hdep,hpA⟩,hloop⟩,hnc⟩,hsub⟩
   intro s hs;have h1:=q189 A E p (fix1A A E p) (fix1E A E p) (req - 1) hdep hpA hloop rfl rfl hnc (ih _ _ _ hsub) s hs;omega
 | b2 p t0 t1 ih0 ih1 =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨⟨⟨⟨⟨hdep,hpA⟩,hloop⟩,hnc0⟩,hnc1⟩,hsub0⟩,hsub1⟩
   intro s hs
   have h1:=q155 A E p (fix0A A p) (fix0E E p) (fix1A A E p) (fix1E A E p) (req - 2)
     hdep hpA hloop rfl rfl rfl rfl hnc0 hnc1 (ih0 _ _ _ hsub0) (ih1 _ _ _ hsub1) s hs;omega
def checkTags (bs:List BaseEntry) (n cap:Nat) (E:List (Fin (n+1) × Fin (n+1)))
   (initTags:Fin (n+1)->Nat) (trees:List (GTree (n+1))):Bool :=
 (List.finRange (n+1)).all fun v =>
   let tg:=initTags v
   let E0:=fix0E E v
   let tr:=trees.getD v.1 GTree.emp
   Nat.beq tg 0 ||
   (Nat.beq tg 1&&!E0.isEmpty&&checkGTree bs n [] E0 (cap - 1) tr) ||
   (Nat.beq tg 3&&!E0.isEmpty&&checkGTree bs n [] E0 (cap - 2) tr)
lemma checkTags_sound (bs:List BaseEntry) (hbs:BaseTableOk bs) {n cap:Nat}
   (f:BFn (n+1)) (E:List (Fin (n+1) × Fin (n+1))) (initTags:Fin (n+1)->Nat)
   (trees:List (GTree (n+1)))
   (hf:Nat.beq (encTT (n+1) f) (encTT (n+1) (gfn [] E))=true)
   (h:checkTags bs n cap E initTags trees=true) :
   ∀ v:Fin (n+1),initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize (n+1) (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize (n+1) (fun x => f (Function.update x v false)) s'->cap - 2<=s'):=by
 have hfeq:f=gfn [] E:=fun_eq_of_encTT _ _ hf
 intro v
 have hv:=List.all_eq_true.1 h v (List.mem_finRange v)
 simp only [bOT,bAT] at hv
 rcases hv with (h0 | ⟨⟨h1,hnc⟩,htr⟩) | ⟨⟨h3,hnc⟩,htr⟩
 . exact Or.inl (Eq.mp Nat.beq_eq h0)
 . refine Or.inr (Or.inl ⟨Eq.mp Nat.beq_eq h1,?_,?_⟩)
   . have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     obtain ⟨x,y,hxy⟩:=q99 [] (fix0E E v) (by simp [hnc])
     exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
   . intro s' hs'
     have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     rw [hres] at hs';exact checkGTree_sound bs hbs _ [] (fix0E E v) (cap - 1) htr s' hs'
 . refine Or.inr (Or.inr ⟨Eq.mp Nat.beq_eq h3,?_,?_⟩)
   . have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     obtain ⟨x,y,hxy⟩:=q99 [] (fix0E E v) (by simp [hnc])
     exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
   . intro s' hs'
     have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     rw [hres] at hs';exact checkGTree_sound bs hbs _ [] (fix0E E v) (cap - 2) htr s' hs'
lemma conj_of_gtree (bs:List BaseEntry) (hbs:BaseTableOk bs) {n req:Nat}
   (f:BFn (n+1)) (E:List (Fin (n+1) × Fin (n+1))) (t:GTree (n+1))
   (hf:Nat.beq (encTT (n+1) f) (encTT (n+1) (gfn [] E))=true)
   (h:checkGTree bs n [] E req t=true) :
   ∀ s:Nat,HasCircuitSize (n+1) f s->req<=s:=by
 rw [fun_eq_of_encTT _ _ hf]
 exact checkGTree_sound bs hbs t [] E req h
lemma baseTable_cons (b:BaseEntry) (bs:List BaseEntry)
   (hb:∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s)
   (hbs:BaseTableOk bs):BaseTableOk (b::bs):=fun x hx => by
 rcases List.mem_cons.1 hx with rfl | hx2;exact hb;exact hbs x hx2
lemma baseEntry_of_f {k lb:Nat} (f:BFn k) (E:List (Fin k × Fin k))
   (hf:Nat.beq (encTT k f) (encTT k (gfn [] E))=true)
   (h:∀ s:Nat,HasCircuitSize k f s->lb<=s) :
   ∀ s:Nat,HasCircuitSize k (gfn [] E) s->lb<=s:=by
 rw [← fun_eq_of_encTT _ _ hf];exact h
def a1t3:=0xff
def a1t5:=0xffffffff
def a1t6:=0xffffffffffffffff
def a1t7:=0xffffffffffffffffffffffffffffffff
def tv0:=0xaaaaaaaaaaaaaaaa
def tv1:=0xcccccccccccccccc
def tv2:=0xf0f0f0f0f0f0f0f0
def tv3:=0xff00ff00ff00ff00
def tv4:=0xffff0000ffff0000
def tv5:=0xffffffff00000000
def tv6:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def tv7:=0xcccccccccccccccccccccccccccccccc
def tv8:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def tv9:=0xff00ff00ff00ff00ff00ff00ff00ff00
def tv10:=0xffff0000ffff0000ffff0000ffff0000
def tv11:=0xffffffff00000000ffffffff00000000
def tv12:=0xffffffffffffffff0000000000000000
def sw0:Nat×Nat×Nat×Nat:=(2,0x30,0xc,0xc3)
def sw1:Nat×Nat×Nat×Nat:=(1,0x44,0x22,0x99)
def sw2:Nat×Nat×Nat×Nat:=(4,0xf000f00,0xf000f0,0xf00ff00f)
def sw3:Nat×Nat×Nat×Nat:=(14,0x33330000,0xcccc,0xcccc3333)
def sw4:Nat×Nat×Nat×Nat:=(12,0xf0f0000,0xf0f0,0xf0f00f0f)
def sw6:Nat×Nat×Nat×Nat:=(8,0xff0000,0xff00,0xff0000ff)
def sw7:Nat×Nat×Nat×Nat:=(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)
def sw8:Nat×Nat×Nat×Nat:=(6,0x33003300,0xcc00cc,0xcc33cc33)
def sw9:Nat×Nat×Nat×Nat:=(16,0xffff00000000,0xffff0000,0xffff00000000ffff)
def sw10:Nat×Nat×Nat×Nat:=(2,0x3030303030303030,0xc0c0c0c0c0c0c0c,0xc3c3c3c3c3c3c3c3)
def sw13:Nat×Nat×Nat×Nat:=(28,0xf0f0f0f00000000,0xf0f0f0f0,0xf0f0f0f00f0f0f0f)
def sw14:Nat×Nat×Nat×Nat:=(7,0x5500550055005500,0xaa00aa00aa00aa,0xaa55aa55aa55aa55)
def sw16:Nat×Nat×Nat×Nat:=(14,0x3333000033330000,0xcccc0000cccc,0xcccc3333cccc3333)
def sw17:Nat×Nat×Nat×Nat:=(12,0xf0f00000f0f0000,0xf0f00000f0f0,0xf0f00f0ff0f00f0f)
def sw21:Nat×Nat×Nat×Nat:=(30,0x3333333300000000,0xcccccccc,0xcccccccc33333333)
def sw23:Nat×Nat×Nat×Nat:=(32,0xffffffff0000000000000000,0xffffffff00000000,0xffffffff0000000000000000ffffffff)
def sw24:Nat×Nat×Nat×Nat:=(8,0xff000000ff000000ff000000ff0000,0xff000000ff000000ff000000ff00,0xff0000ffff0000ffff0000ffff0000ff)
def sw26:Nat×Nat×Nat×Nat:=(16,0xffff000000000000ffff00000000,0xffff000000000000ffff0000,0xffff00000000ffffffff00000000ffff)
def sw28:Nat×Nat×Nat×Nat:=(1,0x44444444444444444444444444444444,0x22222222222222222222222222222222,0x99999999999999999999999999999999)
def sw29:Nat×Nat×Nat×Nat:=(56,0xff00ff00ff00ff0000000000000000,0xff00ff00ff00ff00,0xff00ff00ff00ff0000ff00ff00ff00ff)
def sw32:Nat×Nat×Nat×Nat:=(48,0xffff0000ffff0000000000000000,0xffff0000ffff0000,0xffff0000ffff00000000ffff0000ffff)
def sw39:Nat×Nat×Nat×Nat:=(24,0xff00ff0000000000ff00ff00000000,0xff00ff0000000000ff00ff00,0xff00ff0000ff00ffff00ff0000ff00ff)
def mk0:=0x9e3779b97f4a7c15f39cc0605cedc835
def mk1:=0x3fffffffff
def mk2:=0x1ff
def mk3:=0x3f
def mk4:=0x1
def mk5:=0x1d
def mk6:=0x20
def mk7:=0x2
def mk9:=0x3ffffffffffff
def mk14:=0x1715609f7c746c6dc20fc1e1d0a4e909
def mk15:=0xfffffffffffffffffffffffffffffffffffffffffffff
def mk16:=0xfffffffff
def mk17:=0x41041041
def mk18:=0x75d75d75d
def mk19:=0x820820820
def mk20:=0x41
def mk21:=0x82
def mk22:=0x75d
def mk23:=0x820
def mk25:=0xffffffffffffffffff
def mk31:=0x3fffffffffffffffffff
def mk33:=0x3fffffffffffffffffffffffff
def mk36:=0x1041
def mk37:=0x2082
def mk38:=0x1d75d
def mk39:=0x20820
def mk40:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk41:=0x41041041041041041
def mk42:=0x75d75d75d75d75d75d
def mk43:=0x820820820820820820
def mk79:=0x82082082
def mk87:=0x1041041041041041041
def mk88:=0x1d75d75d75d75d75d75d
def mk89:=0x20820820820820820820
def mk93:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk94:=0x3ffffffffffffffffffffffffffffffffffffff
def E0:List (Fin 3×Fin 3):=[(0,1),(0,2),(1,2)]
abbrev f0:=gfn [] E0
def r0:=0x101081828304042060a0c1850c18286061418404041010804202
def x0:=[(0x2a934f2e54,0),(0x332596daa1,0),(0x3c0e39f50a,0)]
def xt0:=[(0xaa,0),(0xcc,0),(0xf0,0)]
def c0:Cfg:=⟨9,18,24,30,mk1,0x3a071ffe00,mk2,mk3,mk4,mk5,mk6,mk4,mk7,mk5,mk6⟩
def N0:Nat->Nat
 | 3=>1
 | _=>0
def L0:Nat->Nat
 | 3=>0
 | _=>0
def H0:Nat->Nat
 | 3=>0x790df1
 | _=>0
def P0:Nat->Nat
 | 3=>0x0
 | _=>0
def g0_0:=[sw0]
def g0_1:=[sw1]
def gs0:=[g0_0,g0_1]
def pa0:=[g0_0,g0_1,g0_0,g0_1,g0_0]
lemma b0_ok:(List.range 4).all (fun s=>span ((bar c0 (findAutPath c0.shTT mk0 pa0 (Rgen a1t3 3 xt0 P0) N0 L0 H0) (Rgen c0.all1v 3 x0 P0)) s) (N0 s) 0)=true:=by decide +kernel
lemma lb0:∀ t,HasCircuitSize 3 f0 t->4<=t:=prove_basePath f0 r0 mk0 c0 (fun _=>0) x0 xt0 gs0 pa0 [[(1,2)],[(0,1)]] N0 L0 H0 P0 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (span_all_sound b0_ok) (fun _=>Or.inl rfl)
def E2:List (Fin 5×Fin 5):=[(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
abbrev f2:=gfn [] E2
def r2:=0x8041060614808024449818045060614201244430520200911260202021418624045180644501246088930188890a0cc06222428330188890a0cc0622242833018e1a3044e1a3024b0e0c14b0e0c0ca9322345890a0ca142850a142448912244860c183060c142850a14280811828401284880124281012830201284880c1420202
def x2:=[(0xaaaaaaaa4ce4d538e4d33cf3cf04447fc000003111100,0),(0xcccccccc38038a013aa8451451513bd240fc0fc44e049,0),(0xf0f0f0f0940963025000492492623fa4bf03f00880e92,0),(0xff00ff00013a004c0325924924bbd1070003ffce0441c,0),(0xffff000002500c94094ea28a28bfa2383ffc0000e88e0,0)]
def xt2:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def c2:Cfg:=⟨50,100,136,148,mk15,0xffeaeae81c71c71c71c7ffffffffffffc000000000000,mk9,mk16,mk17,mk18,mk19,mk20,mk21,mk22,mk23⟩
def N2:Nat->Nat
 | 5=>3
 | 6=>10
 | 7=>1
 | _=>0
def L2:Nat->Nat
 | 5=>2
 | 6=>4
 | 7=>0
 | _=>0
def H2:Nat->Nat
 | 5=>0xbb49cd5b9db55b9db4
 | 6=>0xfb774bef6629cd7f96cb72d6ad30b16e3b0069d9355b9db43cfc9803e857
 | 7=>0x5b9db4
 | _=>0
def P2:Nat->Nat
 | 5=>0x43900000c3500000000
 | 6=>0x48008000040000000100000024008000030000002800000034000000000000003800000044
 | 7=>0x0
 | _=>0
def gs2:=[[sw6],[sw7],[sw4,sw8]]
def au2:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw2,sw3]
 | _=>[]
def ap2:List (List (Nat×Nat)):=[[],[(2,3),(1,4)]]
lemma b2_ok:(List.range 8).all (fun s=>span ((bar c2 (findAutGen c2.shTT mk14 gs2 au2 (Rgen a1t5 7 xt2 P2) N2 L2 H2 P2) (Rgen c2.all1v 7 x2 P2)) s) (N2 s) 0)=true:=by decide +kernel
lemma lb2:∀ t,HasCircuitSize 5 f2 t->8<=t:=prove_baseGen f2 r2 mk14 c2 (fun _=>0) x2 xt2 gs2 [[(3,4)],[(1,2)],[(2,4),(1,3)]] au2 ap2 N2 L2 H2 P2 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b2_ok) (fun _=>Or.inl rfl)
def E7:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def f7:BFn 6:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 3&&x 5)||(x 4&&x 5)
def r7:=0x10108182830808085061890a44c951a2208a060a0d201441818514046060a0c60114181852228918062490128182832421130506100820c0c280808085061908a44a01892804906061501010a0c3060a0c0612141b050603090a0d828301848506c14180c2428360a0c0612141b050603090a0d828301848506c14180c2428368c98b058a943464c581c346162a52a0e1a32604a64a58a8e0c153232c4c706069519526345890a0d22448912244889122448912242850a142850942850a142850912244891224448912244891183060c183060a142850a1428a12224060a1091121403050848890a02848890028909222281014884a1118100a4445090c1420202
def x7:=[(0x2aaaaaaaaaaaaaaa933808d34d38d30003a34c00e1c3870e1c38720408aa54ffc000fe0007f000081022a95200,0),(0x3333333333333333254ff54e94e6a5a004da380122448912244894489115bfaa407f0003f8001fd122445600a9,3),(0x3c3c3c3c3c3c3c3c0e9403a53a500e000940940142850a142850a891221feb54bf8001fc000fe022448800ad52,3),(0x3fc03fc03fc03fc000013000a285404d301500e68d1a3468d1a340e1ffe1020700000000000fffc3870004081c,0),(0x3fffc0003fffc00000025a00000b2894e000a13a142850a142850f1fc3c60c18000001fffff0003c000f183060,3),(0x3fffffffc00000000000e0280000003a502c025c183060c183060ffe3c1830603ffffe000000000078f060c180,3)]
def xt7:=[(tv0,0),(tv1,3),(tv2,3),(tv3,0),(tv4,3),(tv5,3)]
def c7:Cfg:=⟨102,204,276,294,mk40,0x3ffffffa3ffa3aba071c71c71c71c71c71c71c7fffffffffffffffffffffffffc0000000000000000000000000,mk33,mk25,mk41,mk42,mk43,mk36,mk37,mk38,mk39⟩
def N7:Nat->Nat
 | 5=>2
 | 6=>8
 | 7=>29
 | 8=>10
 | 9=>1
 | _=>0
def L7:Nat->Nat
 | 5=>1
 | 6=>3
 | 7=>5
 | 8=>4
 | 9=>0
 | _=>0
def H7:Nat->Nat
 | 5=>0xdb6fbcb59fba
 | 6=>0xff4208b8920aa522bf75dad66127d83e4ab5329e30073865
 | 7=>0xf6a0f1cdee20cc92b8cb3eaabe18aeb8920aabab409e48b08bb10987d58b7fd1897e822678ec1b73bbc36127d854ce3551601750a3d94acccc477f9a42f4983e088739321e2aff512322a72181e91a87070e618f0260cc
 | 8=>0xf6a0f1be18ae9f3eed73bbc36127d842f49840121b2181e91a870713d354
 | 9=>0x6127d8
 | _=>0
def P7:Nat->Nat
 | 5=>0x1c3d01000839
 | 6=>0x1801c4a01000c3900002c3d0080542d000000000000043d0080489900805441
 | 7=>0x145c00800c7a000000720080105601001403010008390000107200801042000010520180104a00801876008018a20100083b008014540000000000801c720000243e000008010200184a01001001000014240180103d0000003e0000083a010024a20000144000801401010010620080189a
 | 8=>0x5c01000003008000020080005400000000000000240000003c000000400080000100000034
 | 9=>0x0
 | _=>0
def tg7:Fin 6->Nat | 0=>0 | 1=>3 | 2=>3 | 3=>0 | 4=>3 | 5=>3
def gs7:=[[sw9],[sw10],[sw13,sw16,sw14]]
def au7:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw13,sw16,sw14]
 | 2=>[sw17,sw21,sw14]
 | 3=>[sw10]
 | 4=>[sw9]
 | _=>[]
def ap7:List (List (Nat×Nat)):=[[],[(2,5),(1,4),(0,3)],[(2,4),(1,5),(0,3)],[(1,2)],[(4,5)]]
lemma b7_ok:(List.range 10).all (fun s=>span ((bar c7 (findAutGen c7.shTT mk0 gs7 au7 (Rgen a1t6 9 xt7 P7) N7 L7 H7 P7) (Rgen c7.all1v 9 x7 P7)) s) (N7 s) 0)=true:=by decide +kernel
def part7 : List BaseEntry := [⟨3,E0,4⟩]
lemma part7_ok : BaseTableOk part7 := (baseTable_cons _ _ (baseEntry_of_f f0 E0 (by decide +kernel) lb0) (fun _ h => by cases h))
lemma lb7:∀ t,HasCircuitSize 6 f7 t->10<=t:=prove_baseGen f7 r7 mk0 c7 tg7 x7 xt7 gs7 [[(4,5)],[(1,2)],[(2,5),(1,4),(0,3)]] au7 ap7 N7 L7 H7 P7 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 5<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b7_ok) (checkTags_sound part7 part7_ok f7 E7 tg7 [.emp,.b2 2 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.b2 1 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.emp,.b2 5 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2])),.b2 4 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2]))] (by decide +kernel) (by decide))
def E17:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)]
def f17:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 1&&x 6)||(x 3&&x 4)||(x 5&&x 6)
def r17:=0x4012060889608543852c420114385850808085061a020050916060a10b152e0a012444305420a0e006892024214186240451812464025181142500a4608489801506049182090e007088080244498880a08506194216060889808014245806011424305c0621220c444850780c4244188890a0f018848831112141e031091062224283c0621220c444850780c4244188890a0f018848831112141e031091062224283e9c3668c987052950ba70d9a3261c0c9522b9628bc70c4e1a3046e5892f1c293868c098a94b0e0c16b529d2a34384d992e54991a22c38303ab466c98ad58ad5294a9322345890a0ea54a952a54a952a4c993264c993264c83060c183060c182d1a3468d1a3468d162c58b162c58b162142850a142850a124489122448912242850a142850a1429a3058a12214048502a9426488906012140a64882b14211828401a9420b46084a1220060a12428101a942648890603460b14244280a0c0806a50992223460b1424284880c1420202
def x17:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa934d3380395a8e4c0013a8e3930150783c1e0f0783c1e0f0401024491c41021ffffc0000ff80001ff0000010040912471040840000,0),(0x333333333333333333333333333333330000e4ce00a4d3a134c04c04c038a389c4e271389c4e27101c07010043bffff001240000000000000ffffc0701c04010e000000049,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c00025940023025000000000940023090482412090482412a82a092248fea54ead64bffff007fffe0000002a0a82489200a953ab592,1),(0x3fc03fc03fc03fc03fc03fc03fc03fc02538e0004c00003a8a0e01302502c422110884422110884308c2dbbff10c1843187001ff00003fe00007fcc230b6e000430610c61c,3),(0x3fffc0003fffc0003fffc0003fffc0000e94000096c00094002502500e000442211088442211088c1304fff6e230608c6383fe00007fc0000ff80304c1000db88c182318e0,3),(0x3fffffffc00000003fffffffc000000000fc0013fc096800e9683000384c0904824120904824120fe3ff1c0704007f007c000000007ffffff00003f8000701c1001fc01f00,3),(0x3fffffffffffffffc00000000000000000000025000300025380940a00940a05028140a05028140ffff8e038083f800f8003ffffff80000000000000fe380e020fe003e000,3)]
def xt17:=[(tv6,0),(tv7,0),(tv8,1),(tv9,3),(tv10,3),(tv11,3),(tv12,3)]
def c17:Cfg:=⟨154,308,386,422,mk93,0x3ffffffffffbbbbb3ffbbbbb3ffababa071c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000,mk94,mk31,mk87,mk88,mk89,mk17,mk79,mk18,mk19⟩
def N17:Nat->Nat
 | 6=>1
 | 7=>22
 | 8=>150
 | 9=>118
 | 10=>10
 | 11=>1
 | _=>0
def L17:Nat->Nat
 | 6=>0
 | 7=>5
 | 8=>8
 | 9=>7
 | 10=>4
 | 11=>0
 | _=>0
def H17:Nat->Nat
 | 6=>0xfe6ca4
 | 7=>0xf34f09ede643e13e8fdf7df8c6c8f4b90e4aa7c723a3af8a95cbd78ede908d6e9a78d09c4c000449c339460eb043fea32825b0212d581b1b5c1192700e70ff009426
 | 8=>0xff1cdffe5ad8fdda50f8f832f76961f6db80efdc38ed8c62ed1f81e9adc8e5ed05e4bc5ee485b3de75c9dd8aa1dd3b9cd3fa0ad217d8d06dabd01d73ceee53cde00ecd16a4cb3bb7cad2a5ca8e1cc94d9fc62ca7c5eb99c468b2c425e5c21e8dbfb62bbdc0bbb90e4aaeec42ae0d81a73515a66d49a60e0aa5db2da464a1a1a59da13d3ca0d225a0618f9d8cab9ad392960f4f960a2995dc63951bd695044f94bfc393333091c53e8f7ea78e2c048d6e9a88728e863af9856c498101928062ef8033177f62c97f4aa07ed93d7ea8117bf56a7b40c977d0d376e33574f56771bbe4710f1b70d5346ec5b56d50d16b76f0671fe066f3c1645cf4644a2f635bdc6117626005445d6aa45cbc285c337d5acc585990815822c557820156368355b25a5426405338374fe19f4c31494965c1477739460eb0419255418c553e712b3d86033d29ba3c88d83a99223a806b3a2c403941183840ba383829367f633678f735a826343deb3417eb339d5c31c4983177a82f14662eac422e62642bf052259aca24042822f0a42155df1de9dc1d804219dc481941d6189e4d16ec9215110c11927010a41d10810c0cc5150bc6090bb2060834e804d059044ecd019bdb01569c00cd0f
 | 9=>0xf47c21f30b62f0d9d1ef9260ed8c62eb30b0eaa960e8ff1fe8c1e8e6d02ed89e43d68772d23d62d217d8d074fdd05282cfe8e8cde954cde00eca8e1cc6e577c648dfc62ca7c3fb16c2e8e4c21e8dc09ce2c083a6bf9f22b9f0abb90e4ab69706b42f5dac7d2baafdaaaa1283a6de49a26195a1f7fb9d2137962caf960a2991c53e9128ea9113698fe1798f7ea78e56598c90e98af8798a765b894e3888728e85088f8105457ed93d7dceb77cf6c278ed5c76ad4e730588728c7b71bbe470a19b7038016dcf0a69a7b4686e05648140644a2f637534607df660145c5fe91054268a4cb3774aa4604872cf45149b43eab6428aa03e712b3e608b3d86033d29ba3840ba367f633678f7339d5c32d8f032b48a32199c31c4983087852c2c282c0ccc281c76259aca1de9dc1d80421d45db19a192197e9e18e46614abf213e0441354a111927010a41d1082100e5fa30d4d85068f3004d0590330fc02467001569c00cd0f
 | 10=>0xc62ca7c3fb16c09ce2960a29644a2f54268a3e712b1de9dc1d8042119270
 | 11=>0x119270
 | _=>0
def P17:Nat->Nat
 | 6=>0x801826
 | 7=>0x2808871020080cd010234250001c43d00804041010190510101bc2d0080a04900006c5100008c3e0081744100816c3a01016c260080bc420081742d0080bc3101006c71010170590300d061000000000100244900817c59
 | 8=>0x807cc901015c2401015c0101807c01018080320000049a0080dc010100900100819c6103018c7202815c840300743e0080002d03015c5c020088a30000dc73000084320000ac0100001801000070990300742e0100904a0101487900014875008168560081782e0180dc9b010028070081909a0380007a0081983d0080903e0080a0510301346a010130510000dc510300fc610000543d010078d200813801008104ca0080e43d008114a50101b89d00807ccb0001003d0101c03d00807c5101007029000028280281046a0301749d02807c730080887b00811c5a0001303b0080907a008010a200811c410000909a00807c2b0100380b0080849a0080e8560100f82d0000dc530101c43e010048d2010110cd0301049d0000345103018c7a0200cc3e0000182800016c3e0000203d00015c2800005c3d0080d03d0100a0710081889a0280f4a2020104a200802801010128cd010150070081b43900000c3d008104560300048a00005057008000ca00006056010070a5010104010001902e0300f47a0300fc9d0001ac5100013c3d0300742d0200785a00811c2d00818836010108750000283c010130530081782a00807c5300019c3d00009c3d0000184401012c5b0081789a0300244a00804c3e01804c820300248c0001389a01000401030090820000483e00018c3e0100c8290000505203009429010080cd0001300100018c3d0001b03d00014859008028740000288c0300dc2b0001702e018080010180789a0281d429000000000300907501011c2f0000dc710101b451010190320300f8d200804cd20101b4990000008a0000ac520080aca2
 | 9=>0x200040202802484008020ac0080202c01000c010100245c0080209c0080205c0080203600000cc4000010380080143c008020640000100100000c7c008020a4008020bc0000205201000c4a0080202e00800874008008f401000007008000020000185c00800c3e0000006c00801c010080084000801404010018510000043c0080146c0000140300000c3c0000180200802032008018a4000018bc00000c7203000c77000000280000183b0080147c00001c400080142400800c7a00000cfc00800c40008014740080083c0080205a00000c9a00000c8c0000105c010004d2000018520080203000001037008008ca008020fc0080144400001c3e008020a20080148c008008c40200040101800802008008d40080000100000cb4008010a4000010bc000004400000002400000ca40100243800802038000018940000105400801c020000003c00802409010018530080202a0080209a0080083e0180088203000c8201000c020200240b00000c9c0000043e00001c9a0000088c00801c56000004fc00001801008000740000008c008014280000200601800801010014070000100200802094008014c40000000003000c7500001cfc0180140b0000183900802034008008d2000010940000185400001052008010a2
 | 10=>0x1000007008000020000006c0000002800800001000000240000003c008000740000008c00000000
 | 11=>0x0
 | _=>0
def tg17:Fin 7->Nat | 0=>0 | 1=>0 | 2=>1 | 3=>3 | 4=>3 | 5=>3 | 6=>3
def gs17:=[[sw23],[sw24],[sw32,sw39,sw28]]
def au17:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw32,sw39,sw28]
 | 2=>[sw26,sw29,sw28]
 | 3=>[sw23]
 | 4=>[sw23,sw24]
 | 5=>[sw23,sw26,sw29,sw28]
 | 6=>[sw24]
 | 7=>[sw23,sw32,sw39,sw28]
 | _=>[]
def ap17:List (List (Nat×Nat)):=[[],[(4,6),(3,5),(0,1)],[(4,5),(3,6),(0,1)],[(5,6)],[(5,6),(3,4)],[(5,6),(4,5),(3,6),(0,1)],[(3,4)],[(5,6),(4,6),(3,5),(0,1)]]
lemma b17_ok:(List.range 12).all (fun s=>span ((bar c17 (findAutGen c17.shTT mk0 gs17 au17 (Rgen a1t7 11 xt17 P17) N17 L17 H17 P17) (Rgen c17.all1v 11 x17 P17)) s) (N17 s) 0)=true:=by decide +kernel
def part17 : List BaseEntry := [⟨6,E7,10⟩,⟨5,E2,8⟩]
lemma part17_ok : BaseTableOk part17 := (baseTable_cons _ _ (baseEntry_of_f f7 E7 (by decide +kernel) lb7) (baseTable_cons _ _ (baseEntry_of_f f2 E2 (by decide +kernel) lb2) (fun _ h => by cases h)))
lemma lb17:∀ t,HasCircuitSize 7 f17 t->12<=t:=prove_baseGen f17 r17 mk0 c17 tg17 x17 xt17 gs17 [[(5,6)],[(3,4)],[(4,6),(3,5),(0,1)]] au17 ap17 N17 L17 H17 P17 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 8<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b17_ok) (checkTags_sound part17 part17_ok f17 E17 tg17 [.emp,.emp,.base 0 [0,3,0,1,2,4,5],.f0 4 (.base 1 [1,0,2,0,0,3,4]),.f0 3 (.base 1 [1,0,2,0,0,3,4]),.f0 6 (.base 1 [0,1,2,3,4]),.f0 5 (.base 1 [0,1,2,3,4])] (by decide +kernel) (by decide))
def pendTable : List BaseEntry := [⟨5,E2,8⟩]
lemma pendTable_ok : BaseTableOk pendTable := (baseTable_cons _ _ (baseEntry_of_f f2 E2 (by decide +kernel) lb2) (fun _ h => by cases h))
def pendBound:=conj_of_gtree (req:=11) pendTable pendTable_ok (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 3&&x 4)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)] (.b2 6 (.f0 5 (.base 0 [0,1,2,3,4])) (.f0 5 (.base 0 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def pendE : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)]
def coTable : List BaseEntry := [⟨7,E17,12⟩,⟨7,pendE,11⟩]
lemma coTable_ok : BaseTableOk coTable := (baseTable_cons _ _ (baseEntry_of_f f17 E17 (by decide +kernel) lb17) (baseTable_cons _ _ (baseEntry_of_f _ pendE (by decide +kernel) pendBound) (fun _ h => by cases h)))
def target10939 (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 6) || (x 0 && x 8) || (x 1 && x 5) || (x 1 && x 7) || (x 2 && x 6) || (x 3 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 7 && x 8)
theorem lower14 (t : Nat) (h : HasCircuitSize 9 target10939 t) : 14 ≤ t := by
  have eqv : target10939 = gfn ([] : List (Fin 9)) [(0, 4), (0, 6), (0, 8), (1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.f0 2 (.f0 4 (.base 0 [5, 3, 0, 2, 0, 4, 6, 0, 1]))) [] [(0, 4), (0, 6), (0, 8), (1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] 14 (by decide +kernel) t h
theorem lower_2_false (t : Nat) (h : HasCircuitSize 9 (fun x : Fin 9 → Bool => target10939 (Function.update x 2 false)) t) : 13 ≤ t := by
  have eqv : (fun x : Fin 9 → Bool => target10939 (Function.update x 2 false)) = gfn ([] : List (Fin 9)) [(0, 4), (0, 6), (0, 8), (1, 5), (1, 7), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.f0 4 (.base 0 [5, 3, 0, 2, 0, 4, 6, 0, 1])) [] [(0, 4), (0, 6), (0, 8), (1, 5), (1, 7), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] 13 (by decide +kernel) t h
theorem lower_2_true (t : Nat) (h : HasCircuitSize 9 (fun x : Fin 9 → Bool => target10939 (Function.update x 2 true)) t) : 12 ≤ t := by
  have eqv : (fun x : Fin 9 → Bool => target10939 (Function.update x 2 true)) = gfn ([6] : List (Fin 9)) [(0, 4), (0, 8), (1, 5), (1, 7), (3, 7), (3, 8), (5, 7), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.f0 6 (.base 1 [5, 3, 0, 2, 6, 4, 0, 0, 1])) [6] [(0, 4), (0, 8), (1, 5), (1, 7), (3, 7), (3, 8), (5, 7), (7, 8)] 12 (by decide +kernel) t h
theorem lower_center_6_false (t : Nat) (h : HasCircuitSize 9 (fun x : Fin 9 → Bool => (fun x : Fin 9 → Bool => target10939 (Function.update x 2 true)) (Function.update x 6 false)) t) : 11 ≤ t := by
  have eqv : (fun x : Fin 9 → Bool => (fun x : Fin 9 → Bool => target10939 (Function.update x 2 true)) (Function.update x 6 false)) = gfn ([] : List (Fin 9)) [(0, 4), (0, 8), (1, 5), (1, 7), (3, 7), (3, 8), (5, 7), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.base 1 [5, 3, 0, 2, 6, 4, 0, 0, 1]) [] [(0, 4), (0, 8), (1, 5), (1, 7), (3, 7), (3, 8), (5, 7), (7, 8)] 11 (by decide +kernel) t h
theorem lower_4_false (t : Nat) (h : HasCircuitSize 9 (fun x : Fin 9 → Bool => target10939 (Function.update x 4 false)) t) : 13 ≤ t := by
  have eqv : (fun x : Fin 9 → Bool => target10939 (Function.update x 4 false)) = gfn ([] : List (Fin 9)) [(0, 6), (0, 8), (1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.f0 2 (.base 0 [5, 3, 0, 2, 0, 4, 6, 0, 1])) [] [(0, 6), (0, 8), (1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] 13 (by decide +kernel) t h
theorem lower_4_true (t : Nat) (h : HasCircuitSize 9 (fun x : Fin 9 → Bool => target10939 (Function.update x 4 true)) t) : 12 ≤ t := by
  have eqv : (fun x : Fin 9 → Bool => target10939 (Function.update x 4 true)) = gfn ([0] : List (Fin 9)) [(1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.f0 0 (.base 1 [0, 3, 6, 2, 0, 4, 5, 0, 1])) [0] [(1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] 12 (by decide +kernel) t h
theorem lower_center_0_false (t : Nat) (h : HasCircuitSize 9 (fun x : Fin 9 → Bool => (fun x : Fin 9 → Bool => target10939 (Function.update x 4 true)) (Function.update x 0 false)) t) : 11 ≤ t := by
  have eqv : (fun x : Fin 9 → Bool => (fun x : Fin 9 → Bool => target10939 (Function.update x 4 true)) (Function.update x 0 false)) = gfn ([] : List (Fin 9)) [(1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] := funext (by decide +kernel)
  rw [eqv] at h
  exact checkGTree_sound coTable coTable_ok (n:=8) (.base 1 [0, 3, 6, 2, 0, 4, 5, 0, 1]) [] [(1, 5), (1, 7), (2, 6), (3, 7), (3, 8), (5, 7), (6, 8), (7, 8)] 11 (by decide +kernel) t h
end Basis

section
open Basis

abbrev ComputesNine (C : Circuit) (f : (Fin 9 → Bool) → Bool) :=
  ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = f x

def pinnedFun (f : (Fin 9 → Bool) → Bool) (p : Fin 9) (b : Bool) (x : Fin 9 → Bool) :=
  f (Function.update x p b)

private theorem nthOfFn {n : Nat} (x : Fin n→Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

theorem pinRow_fn (p : Fin 9) (b : Bool) (x : Fin 9 → Bool) :
    pinRow 9 p.val b (List.ofFn x) = List.ofFn (Function.update x p b) := by
  unfold pinRow
  apply congrArg List.ofFn
  funext i
  by_cases eq : i=p
  · subst i
    simp
  · have ne : i.val≠p.val := fun h => eq (Fin.ext h)
    rw [if_neg ne,nthOfFn,Function.update_of_ne eq]

theorem floor_from_graph {C : Circuit} {f : (Fin 9→Bool)→Bool} {p : Fin 9} {b : Bool} {k : Nat}
   (computes : ComputesNine C f) (lower : ∀ t, HasCircuitSize 9 (pinnedFun f p b) t → k≤t) :
   PinFloor 9 p.val b C k := by
  intro D fan same
  apply lower D.size
  refine ⟨D,fan,le_rfl,?_⟩
  intro x
  rw [same _ (by simp), pinRow_fn, computes]
  rfl

private def row9 (s : List Nat) (i : Fin 9) := s.contains i.val

theorem varies_from_rows {C : Circuit} {f : (Fin 9→Bool)→Bool} {p : Fin 9} {b : Bool}
   (computes : ComputesNine C f)
   (h : pinnedFun f p b (row9 []) ≠ pinnedFun f p b (row9 [1,5])) :
   PinVaries 9 p.val b C := by
  refine ⟨List.ofFn (row9 []),List.ofFn (row9 [1,5]),by simp,by simp,?_⟩
  rw [pinRow_fn,pinRow_fn,computes,computes]
  exact h

theorem raw_reader_from_variation {n : Nat} {C : Circuit} (back : ReadsBack n C)
   {v : Nat} (out : C.output≠v) {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
   (same : ∀ i<n, i≠v → x.getD i false=z.getD i false)
   (different : C.eval x≠C.eval z) : ∃ j<C.gates.length, v∈(gateAt C j).inputs := by
  by_contra none
  have values (w : Nat) : w≠v → val C x w=val C z w := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro ne
      by_cases raw : w<n
      · rw [val_input hx raw,val_input hz raw,same w raw ne]
      by_cases past : n+C.gates.length≤w
      · rw [val_ge hx past,val_ge hz past]
      obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
      have jl : j<C.gates.length := by omega
      rw [val_gate hx jl,val_gate hz jl]
      congr 1
      apply List.map_congr_left
      intro u hu
      have lt := back j jl u hu
      rw [if_pos lt,if_pos lt]
      exact ih u lt (fun eq => none ⟨j,jl,eq ▸ hu⟩)
  exact different (values C.output out)

theorem out_ge_nine {C : Circuit} {f : (Fin 9→Bool)→Bool}
   (computes : ComputesNine C f) (h : ∀ i : Fin 9, ∃ s : Fin 9→Bool, f s ≠ s i) :
   9≤C.output := by
  by_contra! small
  let i : Fin 9 := ⟨C.output,small⟩
  obtain ⟨x,diff⟩ := h i
  have e := computes x
  change val C (List.ofFn x) C.output=f x at e
  rw [val_input (by simp) small] at e
  apply diff
  exact e.symm.trans (nthOfFn x i)

theorem essential_to_reader {C : Circuit} {f : (Fin 9→Bool)→Bool} {p : Fin 9}
    (back : ReadsBack 9 C) (computes : ComputesNine C f) (out : C.output≠p.val)
    (existsRow : ∃ x : Fin 9→Bool, pinnedFun f p false x≠pinnedFun f p true x) :
    ∃ j<C.gates.length, p.val∈(gateAt C j).inputs := by
  obtain ⟨x,h⟩ := existsRow
  apply raw_reader_from_variation back out (x:=List.ofFn (Function.update x p false))
    (z:=List.ofFn (Function.update x p true)) (by simp) (by simp)
  · intro i hi ne
    have hne : (⟨i,hi⟩ : Fin 9) ≠ p := fun e => ne (congrArg Fin.val e)
    rw [nthOfFn _ (⟨i,hi⟩ : Fin 9),nthOfFn _ (⟨i,hi⟩ : Fin 9),Function.update_of_ne hne,Function.update_of_ne hne]
  · rw [computes,computes]
    exact h

theorem single_reject_from {C : Circuit} {f : (Fin 9→Bool)→Bool} {p : Fin 9}
    (computes : ComputesNine C f) (h : ∃ x : Fin 9→Bool, x p=true ∧ f x=false) :
    ∃ x : List Bool, x.length=9 ∧ x.getD p.val false=true ∧ C.eval x=false := by
  obtain ⟨x,hp,hf⟩ := h
  exact ⟨List.ofFn x, by simp, (nthOfFn x p).trans hp, (computes x).trans hf⟩

theorem output_leaf2 {C : Circuit} (h : ComputesNine C target10939) : 9≤C.output := out_ge_nine h (by decide +kernel)
theorem used_leaf2 {C : Circuit} (back : ReadsBack 9 C) (h : ComputesNine C target10939) : ∃ j<C.gates.length, 2∈(gateAt C j).inputs := by
  have large := output_leaf2 h
  exact essential_to_reader (p:=(2:Fin 9)) back h (by change C.output≠2; omega) (by decide +kernel)
theorem rejects_leaf2 {C : Circuit} (h : ComputesNine C target10939) : ∃ x : List Bool, x.length=9 ∧ x.getD 2 false=true ∧ C.eval x=false := single_reject_from (p:=(2:Fin 9)) h (by decide +kernel)
theorem floor_leaf2_false {C : Circuit} (h : ComputesNine C target10939) : PinFloor 9 2 false C 13 := floor_from_graph (p:=(2:Fin 9)) h lower_2_false
theorem varies_leaf2_false {C : Circuit} (h : ComputesNine C target10939) : PinVaries 9 2 false C := varies_from_rows (p:=(2:Fin 9)) h (by decide +kernel)
theorem floor_leaf2_true {C : Circuit} (h : ComputesNine C target10939) : PinFloor 9 2 true C 12 := floor_from_graph (p:=(2:Fin 9)) h lower_2_true
theorem varies_leaf2_true {C : Circuit} (h : ComputesNine C target10939) : PinVaries 9 2 true C := varies_from_rows (p:=(2:Fin 9)) h (by decide +kernel)
theorem output_center6 {C : Circuit} (h : ComputesNine C (pinnedFun target10939 2 true)) : 9≤C.output := out_ge_nine h (by decide +kernel)
theorem used_center6 {C : Circuit} (back : ReadsBack 9 C) (h : ComputesNine C (pinnedFun target10939 2 true)) : ∃ j<C.gates.length, 6∈(gateAt C j).inputs := by
  have large := output_center6 h
  exact essential_to_reader (p:=(6:Fin 9)) back h (by change C.output≠6; omega) (by decide +kernel)
theorem floor_center6_false {C : Circuit} (h : ComputesNine C (pinnedFun target10939 2 true)) : PinFloor 9 6 false C 11 := floor_from_graph (p:=(6:Fin 9)) h lower_center_6_false
theorem varies_center6_false {C : Circuit} (h : ComputesNine C (pinnedFun target10939 2 true)) : PinVaries 9 6 false C := varies_from_rows (p:=(6:Fin 9)) h (by decide +kernel)

theorem output_leaf4 {C : Circuit} (h : ComputesNine C target10939) : 9≤C.output := out_ge_nine h (by decide +kernel)
theorem used_leaf4 {C : Circuit} (back : ReadsBack 9 C) (h : ComputesNine C target10939) : ∃ j<C.gates.length, 4∈(gateAt C j).inputs := by
  have large := output_leaf4 h
  exact essential_to_reader (p:=(4:Fin 9)) back h (by change C.output≠4; omega) (by decide +kernel)
theorem rejects_leaf4 {C : Circuit} (h : ComputesNine C target10939) : ∃ x : List Bool, x.length=9 ∧ x.getD 4 false=true ∧ C.eval x=false := single_reject_from (p:=(4:Fin 9)) h (by decide +kernel)
theorem floor_leaf4_false {C : Circuit} (h : ComputesNine C target10939) : PinFloor 9 4 false C 13 := floor_from_graph (p:=(4:Fin 9)) h lower_4_false
theorem varies_leaf4_false {C : Circuit} (h : ComputesNine C target10939) : PinVaries 9 4 false C := varies_from_rows (p:=(4:Fin 9)) h (by decide +kernel)
theorem floor_leaf4_true {C : Circuit} (h : ComputesNine C target10939) : PinFloor 9 4 true C 12 := floor_from_graph (p:=(4:Fin 9)) h lower_4_true
theorem varies_leaf4_true {C : Circuit} (h : ComputesNine C target10939) : PinVaries 9 4 true C := varies_from_rows (p:=(4:Fin 9)) h (by decide +kernel)
theorem output_center0 {C : Circuit} (h : ComputesNine C (pinnedFun target10939 4 true)) : 9≤C.output := out_ge_nine h (by decide +kernel)
theorem used_center0 {C : Circuit} (back : ReadsBack 9 C) (h : ComputesNine C (pinnedFun target10939 4 true)) : ∃ j<C.gates.length, 0∈(gateAt C j).inputs := by
  have large := output_center0 h
  exact essential_to_reader (p:=(0:Fin 9)) back h (by change C.output≠0; omega) (by decide +kernel)
theorem floor_center0_false {C : Circuit} (h : ComputesNine C (pinnedFun target10939 4 true)) : PinFloor 9 0 false C 11 := floor_from_graph (p:=(0:Fin 9)) h lower_center_0_false
theorem varies_center0_false {C : Circuit} (h : ComputesNine C (pinnedFun target10939 4 true)) : PinVaries 9 0 false C := varies_from_rows (p:=(0:Fin 9)) h (by decide +kernel)
end

section
open Basis

theorem before_leaf_and {n p : Nat} {C : Circuit} (back : ReadsBack n C) (L : LeafPair n C p)
    {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    (same : ∀ i<n, i≠p → x.getD i false=z.getD i false) :
    ∀ w, w<n+L.gate → w≠p → w≠n+L.first.gate → val C x w=val C z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro lim nr ng
    by_cases raw : w<n
    · rw [val_input hx raw,val_input hz raw,same w raw nr]
    obtain ⟨j,rfl⟩ : ∃ j,w=n+j := ⟨w-n,by omega⟩
    have jl : j<C.gates.length := by have := L.valid; omega
    rw [val_gate hx jl,val_gate hz jl]
    congr 1
    apply List.map_congr_left
    intro a ha
    have lt := back j jl a ha
    rw [if_pos lt,if_pos lt]
    exact ih a lt (by omega) (fun e => by have q := L.first.unique j jl (e ▸ ha); omega)
      (fun e => by have q := L.unique j jl (e ▸ ha); omega)

private theorem nthRow {n : Nat} (u : Fin n→Bool) (i : Fin n) :
    (List.ofFn u).getD i.val false=u i := by simp [List.getD_eq_getElem?_getD]

private theorem same_update {n : Nat} (u : Fin n→Bool) (p : Fin n) (b : Bool) :
    ∀ i<n, i≠p.val → (List.ofFn u).getD i false=(List.ofFn (Function.update u p b)).getD i false := by
  intro i hi diff
  let j : Fin n := ⟨i,hi⟩
  have ne : j≠p := fun h => diff (congrArg Fin.val h)
  rw [nthRow _ j,nthRow _ j,Function.update_of_ne ne]

private theorem recover_row {n : Nat} (x : List Bool) (hx : x.length=n) :
    List.ofFn (fun i : Fin n => x.getD i.val false)=x := by
  apply List.ext_getElem
  · simp [hx]
  · intro i h₁ h₂
    rw [List.getElem_ofFn]
    simp [List.getD_eq_getElem?_getD,h₂]

theorem early_or_absorbs {C : Circuit} (back : ReadsBack 9 C)
    {p y : Fin 9} (L : LeafPair 9 C p.val) (R : SoleOr 9 C y.val)
    (early : R.gate<L.gate) (diffp : R.other≠p.val) (diffg : R.other≠9+L.first.gate)
    {f : (Fin 9→Bool)→Bool} (computes : ComputesNine C f)
    (independent : ∀ u : Fin 9→Bool, f (Function.update u y false) =
      f (Function.update (Function.update u y false) p true))
    (edge : ∀ u : Fin 9→Bool, f (Function.update (Function.update (Function.update u y false) p true) y true)=true) :
    ∀ x : List Bool, x.length=9 → val C x R.other=true → C.eval x=true := by
  intro x hx orig
  let u : Fin 9→Bool := fun i => x.getD i.val false
  have eqx : List.ofFn u=x := recover_row x hx
  let u0 := Function.update u y false
  let u1 := Function.update u0 p true
  let u2 := Function.update u1 y true
  have hv : val C (List.ofFn u) R.other=true := by simpa only [eqx] using orig
  have mask0 := mask_raw back (x:=List.ofFn u) (z:=List.ofFn u0) (by simp) (by simp)
    R.valid R.early R.different R.op R.unique (same_update u y false) hv
  have hc0 : val C (List.ofFn u0) R.other=true := (mask0 _ R.different).symm.trans hv
  have eqc := before_leaf_and back L (x:=List.ofFn u0) (z:=List.ofFn u1) (by simp) (by simp)
    (same_update u0 p true) R.other (by have t:=R.early; omega) diffp diffg
  have mask1 := mask_raw back (x:=List.ofFn u1) (z:=List.ofFn u2) (by simp) (by simp)
    R.valid R.early R.different R.op R.unique (same_update u1 y true) (eqc.symm.trans hc0)
  calc
    C.eval x = C.eval (List.ofFn u) := by rw [eqx]
    _ = C.eval (List.ofFn u0) := mask0 _ R.notOutput
    _ = f u0 := computes _
    _ = f u1 := independent u
    _ = C.eval (List.ofFn u1) := (computes _).symm
    _ = C.eval (List.ofFn u2) := mask1 _ R.notOutput
    _ = f u2 := computes _
    _ = true := edge u

theorem leaf2_early_or_absorbs {C : Circuit} (back : ReadsBack 9 C)
    (L : LeafPair 9 C 2) (R : SoleOr 9 C 6)
    (early : R.gate<L.gate) (dp : R.other≠2) (dg : R.other≠9+L.first.gate)
    (h : ComputesNine C target10939) :
    ∀ x : List Bool, x.length=9 → val C x R.other=true → C.eval x=true :=
  early_or_absorbs (p:=(2:Fin 9)) (y:=(6:Fin 9)) back L R early dp dg h (by decide +kernel) (by decide +kernel)

theorem leaf4_early_or_absorbs {C : Circuit} (back : ReadsBack 9 C)
    (L : LeafPair 9 C 4) (R : SoleOr 9 C 0)
    (early : R.gate<L.gate) (dp : R.other≠4) (dg : R.other≠9+L.first.gate)
    (h : ComputesNine C target10939) :
    ∀ x : List Bool, x.length=9 → val C x R.other=true → C.eval x=true :=
  early_or_absorbs (p:=(4:Fin 9)) (y:=(0:Fin 9)) back L R early dp dg h (by decide +kernel) (by decide +kernel)
end

section
open Basis

private def witnessBits (s : List Nat) (i : Fin 9) := s.contains i.val

private theorem witness_excludes_raw {C : Circuit} (back : ReadsBack 9 C)
    {y p : Nat} (R : SoleOr 9 C y) (hp : p<9) {a b : Fin 9→Bool}
    (pa : (List.ofFn a).getD p false=true)
    (same : ∀ i : Fin 9, i.val≠y →
      (List.ofFn a).getD i.val false=(List.ofFn b).getD i.val false)
    (diff : C.eval (List.ofFn a)≠C.eval (List.ofFn b)) : R.other≠p := by
  intro eq
  have comp : val C (List.ofFn a) R.other=true := by rw [eq,val_input (by simp) hp,pa]
  exact diff (mask_raw back (by simp) (by simp) R.valid R.early R.different R.op R.unique
    (fun i hi => same ⟨i,hi⟩) comp C.output R.notOutput)

theorem first_gate_distinct {n p y : Nat} {C : Circuit} (L : LeafPair n C p)
    (R : SoleOr n C y) (yp : p≠y) (other : R.other≠p) :
    R.gate ≠ L.first.gate := by
  intro eq
  have rd : p∈(gateAt C R.gate).inputs := by
    rw [eq]
    rcases L.first.op with h|h <;> rw [h] <;> simp
  rcases R.op with h|h <;> rw [h] at rd <;> simp [yp,Ne.symm other] at rd

theorem early_not_first_wire {n p y : Nat} {C : Circuit} (L : LeafPair n C p)
    (R : SoleOr n C y) (early : R.gate<L.gate) : R.other≠n+L.first.gate := by
  intro eq
  have rd : R.other ∈ (gateAt C R.gate).inputs := by rcases R.op with h|h <;> rw [h] <;> simp
  have same := L.unique R.gate R.valid (eq ▸ rd)
  omega

theorem reject_excludes_first {n p : Nat} {C : Circuit} (hp : p<n) (L : LeafPair n C p)
    (reject : ∃ x : List Bool, x.length=n ∧ x.getD p false=true ∧ C.eval x=false) :
    C.output≠n+L.first.gate := by
  intro same
  obtain ⟨x,hx,px,fx⟩ := reject
  have op : (gateAt C L.first.gate).op=.or := by rcases L.first.op with h|h <;> rw [h]
  have mem : p∈(gateAt C L.first.gate).inputs := by rcases L.first.op with h|h <;> rw [h] <;> simp
  have hi : val C x (n+L.first.gate)=true := (val_or hx L.first.valid op).mpr
    ⟨p,mem,by omega,by rw [val_input hx hp,px]⟩
  rw [eval_eq_val,same,hi] at fx
  contradiction

theorem center0_companion_ne_leaf2 {C : Circuit} (back : ReadsBack 9 C)
    (computes : ComputesNine C target10939) (R : SoleOr 9 C 0) : R.other≠2 := by
  apply witness_excludes_raw back R (by decide)
    (a:=witnessBits [2,8]) (b:=witnessBits [2,8,0]) (by decide) (by decide)
  rw [computes,computes]
  decide

theorem center0_companion_ne_leaf4 {C : Circuit} (back : ReadsBack 9 C)
    (computes : ComputesNine C target10939) (R : SoleOr 9 C 0) : R.other≠4 := by
  apply witness_excludes_raw back R (by decide)
    (a:=witnessBits [4,8]) (b:=witnessBits [4,8,0]) (by decide) (by decide)
  rw [computes,computes]
  decide

theorem center6_companion_ne_leaf2 {C : Circuit} (back : ReadsBack 9 C)
    (computes : ComputesNine C target10939) (R : SoleOr 9 C 6) : R.other≠2 := by
  apply witness_excludes_raw back R (by decide)
    (a:=witnessBits [2,8]) (b:=witnessBits [2,8,6]) (by decide) (by decide)
  rw [computes,computes]
  decide

theorem center6_companion_ne_leaf4 {C : Circuit} (back : ReadsBack 9 C)
    (computes : ComputesNine C target10939) (R : SoleOr 9 C 6) : R.other≠4 := by
  apply witness_excludes_raw back R (by decide)
    (a:=witnessBits [4,8]) (b:=witnessBits [4,8,6]) (by decide) (by decide)
  rw [computes,computes]
  decide
end

section
open Basis AnchorMove

theorem leaf2_before_center6 {C : Circuit} {budget : ℕ} (good : Representative 9 budget target10939 C)
    (A : LeafPair 9 C 2) (B : LeafPair 9 C 4)
    (min : LeastAnchorSum (budget := budget) (F := target10939) A B) (R : SoleOr 9 C 6) :
    A.gate<R.gate := by
  by_contra no
  have ne := and_ne_or A R
  have early : R.gate<A.gate := by omega
  have d₂ := center6_companion_ne_leaf2 good.back good.computes R
  have d₄ := center6_companion_ne_leaf4 good.back good.computes R
  exact least_forbids_move good A B min R (by decide) (by decide) (by decide)
    (by decide) (by decide) (first_gate_distinct A R (by decide) d₂).symm
    (first_gate_distinct B R (by decide) d₄).symm
    (reject_excludes_first (by decide) A (rejects_leaf2 good.computes))
    (reject_excludes_first (by decide) B (rejects_leaf4 good.computes))
    (Or.inl early) (leaf2_early_or_absorbs good.back A R early d₂
      (early_not_first_wire A R early) good.computes)

theorem leaf4_before_center0 {C : Circuit} {budget : ℕ} (good : Representative 9 budget target10939 C)
    (A : LeafPair 9 C 2) (B : LeafPair 9 C 4)
    (min : LeastAnchorSum (budget := budget) (F := target10939) A B) (R : SoleOr 9 C 0) :
    B.gate<R.gate := by
  by_contra no
  have ne := and_ne_or B R
  have early : R.gate<B.gate := by omega
  have d₂ := center0_companion_ne_leaf2 good.back good.computes R
  have d₄ := center0_companion_ne_leaf4 good.back good.computes R
  exact least_forbids_move good A B min R (by decide) (by decide) (by decide)
    (by decide) (by decide) (first_gate_distinct A R (by decide) d₂).symm
    (first_gate_distinct B R (by decide) d₄).symm
    (reject_excludes_first (by decide) A (rejects_leaf2 good.computes))
    (reject_excludes_first (by decide) B (rejects_leaf4 good.computes))
    (Or.inr early) (leaf4_early_or_absorbs good.back B R early d₄
      (early_not_first_wire B R early) good.computes)


end

section
theorem bypass_unused_value {n : Nat} {C : Circuit} {x : List Bool} (hx : x.length=n)
    {r i : Nat} (hr : r < C.gates.length) (hi : i < n+r)
    (unused : ∀ j < C.gates.length, n+r ∉ (gateAt C j).inputs) :
    ∀ u, u≠n+r → val (bypass n C r i) x (aliasWire (n+r) i u)=val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro different
    by_cases hlt : u < n+r
    · rw [aliasWire_lt_self hlt,bypass_val_lt hx hr u hlt]
    rw [aliasWire_gt_self (by omega)]
    by_cases out : n+C.gates.length ≤ u
    · rw [val_ge hx out, val_ge hx (by rw [bypass_length]; omega)]
    obtain ⟨k,rfl⟩ : ∃ k, u=n+(k+1) := ⟨u-n-1,by omega⟩
    have hk : k+1<C.gates.length := by omega
    have kr : ¬ k<r := by omega
    have eq : n+(k+1)-1=n+k := by omega
    have hd : k<(bypass n C r i).gates.length := by rw [bypass_length]; omega
    rw [eq,val_gate hx hd,val_gate hx hk,gateAt_bypass (by omega),if_neg kr]
    simp only [aliasGate,List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply]
    by_cases early : a<n+(k+1)
    · have mappedEarly := aliasWire_lt hi (by omega : n+r ≤ n+k) (by omega : a < n+k+1)
      rw [if_pos early,if_pos mappedEarly]
      exact ih a early (fun hit => unused _ hk (hit ▸ ha))
    · have later : n+r<a := by omega
      rw [if_neg early,aliasWire_gt_self later,if_neg (by omega)]

theorem bypass_unused_compact {n : Nat} {C : Circuit} (hn : 0<n)
    (fan : FanInTwo C) (back : ReadsBack n C) (proper : ProperNot C)
    {r : Nat} (hr : r<C.gates.length) (out : C.output≠n+r)
    (unused : ∀ j<C.gates.length, n+r ∉ (gateAt C j).inputs) :
    ∃ D : Circuit, FanInTwo D ∧ ReadsBack n D ∧ ProperNot D ∧ D.size<C.size ∧
      ∀ x : List Bool, x.length=n → D.eval x=C.eval x := by
  let D:=bypass n C r 0
  have hi : 0<n+r := by omega
  refine ⟨D,?_,bypass_readsBack hi back,?_,?_,?_⟩
  · intro g hg
    obtain ⟨g',hm,op,inputs⟩ := bypass_mem g hg
    rw [op,inputs]
    exact fan _ hm
  · intro g hg en
    obtain ⟨g',hm,op,inputs⟩ := bypass_mem g hg
    rw [inputs]
    exact proper g' hm (op.symm.trans en)
  · change (bypass n C r 0).gates.length<C.gates.length
    rw [bypass_length]
    omega
  · intro x hx
    exact bypass_unused_value hx hr hi unused C.output out

theorem live_reader {n : Nat} {C : Circuit} (hn : 0<n)
    (fan : FanInTwo C) (back : ReadsBack n C) (proper : ProperNot C)
    (minimal : ∀ D : Circuit, FanInTwo D → ReadsBack n D → ProperNot D →
      (∀ x : List Bool, x.length=n → D.eval x=C.eval x) → C.size ≤ D.size)
    {r : Nat} (hr : r<C.gates.length) (out : C.output≠n+r) :
    ∃ j, j<C.gates.length ∧ r<j ∧ n+r ∈ (gateAt C j).inputs := by
  by_contra no
  have unused : ∀ j<C.gates.length, n+r ∉ (gateAt C j).inputs := by
    intro j hj mem
    have lt := back j hj _ mem
    exact no ⟨j,hj,by omega,mem⟩
  obtain ⟨D,df,db,dp,ds,same⟩ := bypass_unused_compact hn fan back proper hr out unused
  exact (Nat.not_le_of_lt ds) (minimal D df db dp same)
end

section
open Basis

def asListFun (f : (Fin 9→Bool)→Bool) (x : List Bool) : Bool :=
  f (fun i => x.getD i.val false)

private theorem row_entry {n : Nat} (x : Fin n→Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false=x i := by simp [List.getD_eq_getElem?_getD]

theorem asListFun_ofFn (f : (Fin 9→Bool)→Bool) (x : Fin 9→Bool) :
    asListFun f (List.ofFn x)=f x := congrArg f (funext (row_entry x))

theorem computes_from_fits {C : Circuit} {s : Nat} {f : (Fin 9→Bool)→Bool}
    (fit : Fits 9 s (asListFun f) C) : ComputesNine C f := by
  intro x
  exact (fit.2.2.2.2.2 _ (by simp)).trans (asListFun_ofFn f x)

theorem min_at_bound {C : Circuit} {k : Nat} {f : (Fin 9→Bool)→Bool}
    (small : C.size≤k) (computes : ComputesNine C f)
    (lower : ∀ t, HasCircuitSize 9 f t → k≤t) : MinEval 9 C := by
  intro D fan same
  apply small.trans
  refine lower D.size ⟨D,fan,le_rfl,?_⟩
  intro x
  exact (same _ (by simp)).trans (computes x)

theorem live_from_min {n : Nat} {C : Circuit} (hn : 0<n) (fan : FanInTwo C)
    (back : ReadsBack n C) (proper : ProperNot C) (min : MinEval n C) : GateLive n C := by
  intro j valid out
  obtain ⟨k,kl,jk,r⟩ := live_reader hn fan back proper
    (fun D fd _ _ eq => min D fd eq) valid out
  exact ⟨k,jk,kl,r⟩

theorem fit_shape_center6 {C : Circuit} (fit : Fits 9 12 (asListFun (pinnedFun target10939 2 true)) C) :
    Nonempty (SoleOr 9 C 6) := by
  have comp := computes_from_fits fit
  obtain ⟨fan,back,out,small,proper,correct⟩ := fit
  have min := min_at_bound small comp lower_2_true
  have large := output_center6 comp
  exact raw_zero_sole_or (by decide) fan back proper min (live_from_min (by decide) fan back proper min)
    (by omega) small (floor_center6_false comp) (varies_center6_false comp) (used_center6 back comp)

theorem center6_sufficient (x : List Bool) (_hx : x.length=9) (on : x.getD 6 false=true) :
    asListFun (pinnedFun target10939 2 true) x=true := by
  have finite : ∀ u : Fin 9→Bool, u 6=true → pinnedFun target10939 2 true u=true := by decide +kernel
  exact finite (fun i => x.getD i.val false) on

theorem cut_center6_descendants {C : Circuit}
    (fit : Fits 9 12 (asListFun (pinnedFun target10939 2 true)) C) :
    ∀ j<C.gates.length, Reach 9 C 6 (9+j) → (gateAt C j).op=GateOp.or :=
  sufficient_or_descendants (by decide) center6_sufficient (fun _ h => fit_shape_center6 h) fit

theorem fit_shape_center0 {C : Circuit} (fit : Fits 9 12 (asListFun (pinnedFun target10939 4 true)) C) :
    Nonempty (SoleOr 9 C 0) := by
  have comp := computes_from_fits fit
  obtain ⟨fan,back,out,small,proper,correct⟩ := fit
  have min := min_at_bound small comp lower_4_true
  have large := output_center0 comp
  exact raw_zero_sole_or (by decide) fan back proper min (live_from_min (by decide) fan back proper min)
    (by omega) small (floor_center0_false comp) (varies_center0_false comp) (used_center0 back comp)

theorem center0_sufficient (x : List Bool) (_hx : x.length=9) (on : x.getD 0 false=true) :
    asListFun (pinnedFun target10939 4 true) x=true := by
  have finite : ∀ u : Fin 9→Bool, u 0=true → pinnedFun target10939 4 true u=true := by decide +kernel
  exact finite (fun i => x.getD i.val false) on

theorem cut_center0_descendants {C : Circuit}
    (fit : Fits 9 12 (asListFun (pinnedFun target10939 4 true)) C) :
    ∀ j<C.gates.length, Reach 9 C 0 (9+j) → (gateAt C j).op=GateOp.or :=
  sufficient_or_descendants (by decide) center0_sufficient (fun _ h => fit_shape_center0 h) fit
end

namespace Normalization


def trimInputs (cap : ℕ) (xs : List ℕ) : List ℕ :=
  xs.filter (fun i => decide (i < cap))

def gate (cap : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if ∀ i ∈ g.inputs, i < cap then g else ⟨.or,[]⟩
  | .or => ⟨.or,trimInputs cap g.inputs⟩
  | .not => ⟨.not,trimInputs cap (g.inputs.take 1)⟩
  | _ => ⟨.or,[]⟩

def gates (cap : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => gate cap g :: gates (cap+1) gs

def norm (n : ℕ) (C : Circuit) : Circuit := ⟨gates n C.gates,C.output⟩

def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def legal (cap : ℕ) (g : Gate) : Prop :=
  allowed g ∧ (∀ i ∈ g.inputs, i < cap) ∧ (g.op=.not → g.inputs.length ≤ 1)

theorem trimInputs_length (cap : ℕ) (xs : List ℕ) :
    (trimInputs cap xs).length ≤ xs.length := List.length_filter_le _ _

theorem trimInputs_bound {cap : ℕ} {xs : List ℕ} {i : ℕ} (mem : i∈trimInputs cap xs) :
    i<cap := of_decide_eq_true (List.mem_filter.mp mem).2

theorem gate_legal (cap : ℕ) (g : Gate) (small : g.inputs.length≤2) : legal cap (gate cap g) := by
  cases g with
  | mk op xs =>
    change xs.length≤2 at small
    cases op with
    | and =>
      change legal cap (if ∀ i∈xs, i<cap then (⟨.and,xs⟩ : Gate) else ⟨.or,[]⟩)
      split
      · rename_i good
        exact ⟨⟨by simp,small⟩,good,by simp⟩
      · simp [legal,allowed]
    | or =>
      refine ⟨⟨by simp [gate],(trimInputs_length _ _).trans small⟩,
        fun _ => trimInputs_bound,by simp [gate]⟩
    | not =>
      have len : (trimInputs cap (xs.take 1)).length≤1 :=
        (trimInputs_length _ _).trans (by simp [List.length_take])
      exact ⟨⟨by simp [gate],len.trans (by decide)⟩,
        fun _ => trimInputs_bound,fun _ => len⟩
    | mod m => simp [gate,legal,allowed]
    | maj => simp [gate,legal,allowed]

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

theorem gate_value (w : List Bool) (g : Gate) (good : allowed g) :
    gateValue w (gate w.length g) = gateValue w g := by
  rcases g with ⟨op,xs⟩
  have hop := good.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  change op = .and ∨ op = .or ∨ op = .not at hop
  rcases hop with rfl | rfl | rfl
  · change gateValue w
      (if ∀ i∈xs, i<w.length then (⟨.and,xs⟩ : Gate) else ⟨.or,[]⟩) =
      gateValue w ⟨.and,xs⟩
    split
    · rfl
    · rename_i bad
      change false = (xs.map fun i => w.getD i false).all id
      symm
      apply Bool.eq_false_iff.mpr
      intro on
      apply bad
      intro i mem
      by_contra beyond
      have ix := List.all_eq_true.mp on (w.getD i false) (List.mem_map.mpr ⟨i,mem,rfl⟩)
      have miss : w.getD i false=false := List.getD_eq_default _ _ (by omega)
      rw [id_eq,miss] at ix
      contradiction
  · change ((trimInputs w.length xs).map fun i => w.getD i false).any id =
      (xs.map fun i => w.getD i false).any id
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq,trimInputs,
      List.mem_filter,decide_eq_true_eq]
    constructor
    · rintro ⟨i,⟨mem,_⟩,val⟩
      exact ⟨i,mem,val⟩
    · rintro ⟨i,mem,val⟩
      refine ⟨i,⟨mem,?_⟩,val⟩
      by_contra beyond
      have miss : w.getD i false=false := List.getD_eq_default _ _ (by omega)
      rw [miss] at val
      contradiction
  · cases xs with
    | nil => rfl
    | cons i xs =>
      by_cases keep : i<w.length
      · simp [gateValue,gate,trimInputs,GateOp.eval,keep]
      · have miss : w.getD i false=false := List.getD_eq_default _ _ (by omega)
        simp [gateValue,gate,trimInputs,GateOp.eval,keep,miss]

theorem gates_length (cap : ℕ) (gs : List Gate) : (gates cap gs).length=gs.length := by
  induction gs generalizing cap with
  | nil => rfl
  | cons g gs ih => simp [gates,ih]

theorem gates_get (cap : ℕ) (gs : List Gate) (j : ℕ) (hj : j<gs.length) :
    (gates cap gs)[j]'(by rwa [gates_length]) = gate (cap+j) gs[j] := by
  induction gs generalizing cap j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [gates]
    | succ j =>
      simpa [gates,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (ih (cap+1) j (Nat.lt_of_succ_lt_succ hj))

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [gateValue v g]) w

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [gateValue w g])).length = _
    rw [ih]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem gates_run (gs : List Gate) (good : ∀ g∈gs, allowed g) (w : List Bool) :
    run (gates w.length gs) w=run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have valid := good g (by simp)
    change run (gates (w.length+1) gs) (w ++ [gateValue w (gate w.length g)]) =
      run gs (w ++ [gateValue w g])
    rw [gate_value _ _ valid]
    have len : (w++[gateValue w g]).length=w.length+1 := by simp
    rw [←len]
    exact ih (fun g' mem => good g' (List.mem_cons_of_mem _ mem)) _

theorem output_good {n : ℕ} {C : Circuit}
    (nonconstant : ∃ x z : List Bool, x.length=n ∧ z.length=n ∧ C.eval x ≠ C.eval z) :
    C.output<n+C.gates.length := by
  by_contra beyond
  obtain ⟨x,z,hx,hz,ne⟩ := nonconstant
  have bad (w : List Bool) (len : w.length=n) : C.eval w=false := by
    change (run C.gates w).getD C.output false = _
    apply List.getD_eq_default
    rw [run_length,len]
    omega
  exact ne ((bad x hx).trans (bad z hz).symm)

theorem normalize_any {n : ℕ} {C : Circuit} (fan : FanInTwo C)
    (nonconstant : ∃ x z : List Bool, x.length=n ∧ z.length=n ∧ C.eval x ≠ C.eval z) :
    ∃ D, FanInTwo D ∧ ReadsBack n D ∧ ProperNot D ∧ D.size≤C.size ∧
      D.output<n+D.gates.length ∧ ∀ x : List Bool, x.length=n → D.eval x=C.eval x := by
  let D := norm n C
  have len : D.gates.length=C.gates.length := gates_length _ _
  have get_base (j : ℕ) (hj : j<C.gates.length) :
      D.gates[j]'(by rwa [len]) = gate (n+j) C.gates[j] := gates_get n C.gates j hj
  have indexed (j : ℕ) (hj : j<D.gates.length) : legal (n+j) D.gates[j] := by
    have hj' : j<C.gates.length := len ▸ hj
    rw [get_base j hj']
    exact gate_legal _ _ (fan _ (List.getElem_mem hj')).2
  have member (g : Gate) (hg : g∈D.gates) : allowed g ∧ (g.op=.not → g.inputs.length≤1) := by
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    exact ⟨(indexed j hj).1,(indexed j hj).2.2⟩
  refine ⟨D,(fun g hg => (member g hg).1),?_,(fun g hg => (member g hg).2),?_,?_,?_⟩
  · intro j hj i mem
    have eq : gateAt D j = D.gates[j] := by
      simp [gateAt,List.getD_eq_getElem?_getD,hj]
    rw [eq] at mem
    exact (indexed j hj).2.1 i mem
  · exact len.le
  · exact len.symm ▸ (output_good nonconstant)
  · intro x hx
    change (run (gates n C.gates) x).getD C.output false = (run C.gates x).getD C.output false
    rw [← hx, gates_run _ fan]

end Normalization

section
open Basis

structure NaturalLeaf (n : Nat) (C : Circuit) (p y : Nat) where
  leafGate : Nat
  centerGate : Nat
  companion : Nat
  leafValid : leafGate < C.gates.length
  centerValid : centerGate < C.gates.length
  distinctCompanion : companion ≠ p
  leafShape : gateAt C leafGate = ⟨.or,[p,companion]⟩ ∨ gateAt C leafGate = ⟨.or,[companion,p]⟩
  centerShape : gateAt C centerGate = ⟨.and,[y,n+leafGate]⟩ ∨ gateAt C centerGate = ⟨.and,[n+leafGate,y]⟩
  leafSole : ∀ j < C.gates.length, p ∈ (gateAt C j).inputs → j = leafGate
  centerSole : ∀ j < C.gates.length, y ∈ (gateAt C j).inputs → j = centerGate

private theorem sole_prefix_agree {n : Nat} {C : Circuit} (back : ReadsBack n C)
    {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    {v r : Nat} (sole : ∀ j < C.gates.length, v ∈ (gateAt C j).inputs → j = r)
    (same : ∀ i<n, i≠v → x.getD i false=z.getD i false) :
    ∀ w, w<n+r → w≠v → val C x w=val C z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro limit different
    by_cases raw : w<n
    · rw [val_input hx raw,val_input hz raw,same w raw different]
    by_cases past : n+C.gates.length≤w
    · rw [val_ge hx past,val_ge hz past]
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have jl : j<C.gates.length := by omega
    rw [val_gate hx jl,val_gate hz jl]
    congr 1
    apply List.map_congr_left
    intro a ha
    have early := back j jl a ha
    rw [if_pos early,if_pos early]
    exact ih a early (by omega) (fun e => by have h := sole j jl (e ▸ ha); omega)

private theorem sole_agree {n : Nat} {C : Circuit} (back : ReadsBack n C)
    {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    {v r : Nat} (sole : ∀ j < C.gates.length, v ∈ (gateAt C j).inputs → j = r)
    (same : ∀ i<n, i≠v → x.getD i false=z.getD i false)
    (gateValue : val C x (n+r)=val C z (n+r)) :
    ∀ w, w≠v → val C x w=val C z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro different
    by_cases raw : w<n
    · rw [val_input hx raw,val_input hz raw,same w raw different]
    by_cases past : n+C.gates.length≤w
    · rw [val_ge hx past,val_ge hz past]
    obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    have jl : j<C.gates.length := by omega
    by_cases eq : j=r
    · simpa [eq] using gateValue
    rw [val_gate hx jl,val_gate hz jl]
    congr 1
    apply List.map_congr_left
    intro a ha
    have early := back j jl a ha
    rw [if_pos early,if_pos early]
    exact ih a early (fun e => eq (sole j jl (e ▸ ha)))

private theorem center_eval {n : Nat} {C : Circuit} (back : ReadsBack n C)
    {p y : Nat} (a : NaturalLeaf n C p y) {x : List Bool} (hx : x.length=n) :
    val C x (n+a.centerGate) = (val C x y && val C x (n+a.leafGate)) := by
  have L := back _ a.centerValid y (by rcases a.centerShape with h|h <;> rw [h] <;> simp)
  have R := back _ a.centerValid (n+a.leafGate) (by rcases a.centerShape with h|h <;> rw [h] <;> simp)
  rcases a.centerShape with h|h <;> rw [val_gate hx a.centerValid,h] <;> simp [GateOp.eval,L,R,Bool.and_comm]

private theorem single_center_false {n : Nat} {C : Circuit} (back : ReadsBack n C)
    {p y : Nat} (a : NaturalLeaf n C p y) {x z : List Bool} (hx : x.length=n) (hz : z.length=n)
    (hp : p<n) (notOutput : C.output≠p) (off : x.getD p false=false)
    (same : ∀ i<n, i≠p → x.getD i false=z.getD i false)
    (diff : C.eval x ≠ C.eval z) : val C x (n+a.centerGate)=false := by
  have L := back _ a.leafValid p (by rcases a.leafShape with h|h <;> rw [h] <;> simp)
  have R := back _ a.leafValid a.companion (by rcases a.leafShape with h|h <;> rw [h] <;> simp)
  have comp : val C x a.companion=false := by
    cases hv : val C x a.companion with
    | false => rfl
    | true =>
      exact False.elim (diff (mask_raw back hx hz a.leafValid R a.distinctCompanion a.leafShape a.leafSole same hv C.output notOutput))
  have low : val C x (n+a.leafGate)=false := by
    rcases a.leafShape with h|h <;> rw [val_gate hx a.leafValid,h] <;> simp [GateOp.eval,L,R,comp,val_input hx hp] <;> exact off
  rw [center_eval back a hx,low,Bool.and_false]

private theorem earlier_mask {n : Nat} {C : Circuit} (back : ReadsBack n C)
    {p y q v : Nat} (a : NaturalLeaf n C p y) (b : NaturalLeaf n C q v)
    (ordered : a.centerGate<b.centerGate) (out : C.output≠y) (hy : y<n) (hv : v<n)
    {left right pair : List Bool} (hl : left.length=n) (hr : right.length=n) (hp : pair.length=n)
    (sameL : ∀ i<n, i≠v → left.getD i false=pair.getD i false)
    (sameR : ∀ i<n, i≠y → pair.getD i false=right.getD i false)
    (rawOff : right.getD y false=false)
    (earlierLow : val C left (n+a.centerGate)=false) : C.eval pair=C.eval right := by
  have lowPair := sole_prefix_agree back hl hp b.centerSole sameL (n+a.centerGate) (by omega) (by
    have h := back _ b.centerValid v (by rcases b.centerShape with t|t <;> rw [t] <;> simp)
    have hvraw : v<n ∨ n≤v := by omega
    rcases hvraw with h'|h'
    · omega
    · exact fun eq => by subst v; have read := back _ a.centerValid y (by rcases a.centerShape with t|t <;> rw [t] <;> simp); omega)
  have lowR : val C right (n+a.centerGate)=false := by
    rw [center_eval back a hr,val_input hr hy,rawOff,Bool.false_and]
  exact sole_agree back hp hr a.centerSole sameR (lowPair.symm.trans (earlierLow.trans lowR.symm)) _ out
private def testVector (s : List Nat) : List Bool :=
  List.ofFn (fun i : Fin 9 => s.contains i.val)

private theorem liftNine {P : Nat → Prop} (h : ∀ i : Fin 9, P i.val) : ∀ i<9, P i :=
  fun i hi => h ⟨i,hi⟩

theorem not_both_natural {C : Circuit} (back : ReadsBack 9 C) (out : 9 ≤ C.output)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target10939 x)
    (a : NaturalLeaf 9 C 4 0) (b : NaturalLeaf 9 C 2 6) : False := by
  have ev (s : List Nat) : C.eval (testVector s) = target10939 (fun i => s.contains i.val) := computes _
  have s0 : C.eval (testVector [0])=false := (ev _).trans (by decide)
  have s6 : C.eval (testVector [6])=false := (ev _).trans (by decide)
  have s04 : C.eval (testVector [0,4])=true := (ev _).trans (by decide)
  have s62 : C.eval (testVector [6,2])=true := (ev _).trans (by decide)
  have s06 : C.eval (testVector [0,6])=true := (ev _).trans (by decide)
  have low0 := single_center_false back a (x:=testVector [0]) (z:=testVector [0,4])
    (by decide) (by decide) (by decide) (by omega) (by decide) (liftNine (by decide)) (by simp [s0,s04])
  have low6 := single_center_false back b (x:=testVector [6]) (z:=testVector [6,2])
    (by decide) (by decide) (by decide) (by omega) (by decide) (liftNine (by decide)) (by simp [s6,s62])
  have different : a.centerGate≠b.centerGate := by
    intro same
    rcases a.centerShape with ha|ha <;> rcases b.centerShape with hb|hb <;>
      rw [same,hb] at ha <;> simp at ha <;> omega
  rcases lt_or_gt_of_ne different with ab|ba
  · have eqv := earlier_mask back a b ab (by omega) (by decide) (by decide)
        (left:=testVector [0]) (right:=testVector [6]) (pair:=testVector [0,6])
        (by decide) (by decide) (by decide) (liftNine (by decide)) (liftNine (by decide))
        (by decide) low0
    simp [s06,s6] at eqv
  · have eqv := earlier_mask back b a ba (by omega) (by decide) (by decide)
        (left:=testVector [6]) (right:=testVector [0]) (pair:=testVector [0,6])
        (by decide) (by decide) (by decide) (liftNine (by decide)) (liftNine (by decide))
        (by decide) low6
    simp [s06,s0] at eqv
end

section
open Basis
open AnchorMove Normalization

private def singleRow (p : Fin 9) (i : Fin 9) : Bool := decide (i=p)
private def twoRow (p y : Fin 9) (i : Fin 9) : Bool := decide (i=p ∨ i=y)

private theorem entry {n : ℕ} (x : Fin n→Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false=x i := by simp [List.getD_eq_getElem?_getD]

private theorem encodeList (x : List Bool) (hx : x.length=9) :
    List.ofFn (fun i : Fin 9=>x.getD i.val false)=x := by
  apply List.ext_getElem
  · simp [hx]
  · intro i h₁ h₂
    rw [List.getElem_ofFn]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h₂,Option.getD_some]

private theorem row_same {p : Fin 9} {a b : Fin 9→Bool}
    (agree : ∀ j, j≠p → a j=b j) :
    ∀ i<9, i≠p.val → (List.ofFn a).getD i false=(List.ofFn b).getD i false := by
  intro i hi ne
  let j : Fin 9 := ⟨i,hi⟩
  change (List.ofFn a).getD j.val false=(List.ofFn b).getD j.val false
  rw [entry,entry]
  exact agree j (fun e=>ne (congrArg Fin.val e))

private theorem center_not_in_leaf {C : Circuit} {p y : Fin 9}
    (ne : p≠y) (comp : ComputesNine C target10939) (back : ReadsBack 9 C)
    (L : LeafPair 9 C p.val)
    (single : target10939 (singleRow y)=false) (pair : target10939 (twoRow p y)=true) :
    y.val ∉ (gateAt C L.first.gate).inputs := by
  intro rd
  have rawNe : y.val≠p.val := fun e => ne (Fin.ext e.symm)
  have companion : L.first.other=y.val := by
    rcases L.first.op with e|e <;> rw [e] at rd <;>
      simpa [rawNe,eq_comm] using rd
  have too : val C (List.ofFn (singleRow y)) L.first.other=true := by
    rw [companion,val_input (by simp) y.isLt,entry]
    simp [singleRow]
  have agree := mask_raw back (by simp) (by simp) L.first.valid L.first.early
    L.first.different L.first.op L.first.unique (row_same (p := p) (a := singleRow y) (b := twoRow p y) (fun j h => by simp [singleRow,twoRow,h])) too
    C.output L.first.notOutput
  change C.eval (List.ofFn (singleRow y))=C.eval (List.ofFn (twoRow p y)) at agree
  rw [comp,comp,single,pair] at agree
  contradiction

private theorem edge_essential {C : Circuit} {p y : Fin 9} (back : ReadsBack 9 C)
    (comp : ComputesNine C target10939)
    (single : target10939 (singleRow p)=false) (pair : target10939 (twoRow p y)=true) :
    Reach 9 C y.val C.output := by
  apply difference_implies_reach back (x := List.ofFn (singleRow p))
    (z := List.ofFn (twoRow p y)) (by simp) (by simp)
    (row_same (fun j h => by simp [singleRow,twoRow,h]))
  rw [comp,comp,single,pair]
  decide

private theorem cut_fits {C : Circuit} {p : Fin 9}
    (rep : Representative 9 14 target10939 C) (L : LeafPair 9 C p.val)
    (outFirst : C.output≠9+L.first.gate) :
    Fits 9 12 (asListFun (pinnedFun target10939 p true)) (cutLeaf L) := by
  obtain ⟨fan,back,norm,sz,correct⟩ := cut_leaf_true p.isLt rep.fan rep.back rep.proper L outFirst
  refine ⟨fan,back,cut_leaf_valid L p.isLt rep.validOutput,?_,norm,?_⟩
  · have h := rep.small
    omega
  · intro x hx
    let row : Fin 9→Bool := fun i=>x.getD i.val false
    have enc : List.ofFn row=x := encodeList x hx
    rw [correct x hx,←enc,pinRow_fn,rep.computes]
    unfold asListFun pinnedFun
    congr 1
    apply congrArg (fun u : Fin 9→Bool => Function.update u p true)
    funext i
    rw [entry]

private def natural_from_case {C : Circuit} {p y : ℕ} (L : LeafPair 9 C p)
    (occ : L.other=y ∧ ∀ j<C.gates.length, y∈(gateAt C j).inputs → j=L.gate) :
    NaturalLeaf 9 C p y := by
  refine ⟨L.first.gate,L.gate,L.first.other,L.first.valid,L.valid,L.first.different,
    L.first.op,?_,L.first.unique,occ.2⟩
  have op := L.op
  rw [occ.1] at op
  exact op.symm
end


section
open Basis
open AnchorMove Normalization

private theorem used_from_path {n y w : ℕ} {C : Circuit} (reach : Reach n C y w) :
    w=y ∨ ∃ j<C.gates.length, y∈(gateAt C j).inputs := by
  induction reach with
  | start => exact Or.inl rfl
  | @step i j jl read _ ih =>
    rcases ih with e|e
    · exact Or.inr ⟨j,jl,e ▸ read⟩
    · exact Or.inr e

private theorem finish_center {C : Circuit} {p y : Fin 9}
    (rep : Representative 9 14 target10939 C) (minimum : MinEval 9 C) (live : GateLive 9 C)
    (L : LeafPair 9 C p.val) (ne : p≠y)
    (singleP : target10939 (singleRow p)=false) (singleY : target10939 (singleRow y)=false)
    (edgePY : target10939 (twoRow p y)=true)
    (sole : SoleOr 9 (cutLeaf L) y.val)
    (orDesc : ∀ j<(cutLeaf L).gates.length,
      Reach 9 (cutLeaf L) y.val (9+j) → (gateAt (cutLeaf L) j).op=.or)
    (lt : ∀ R : SoleOr 9 C y.val, L.gate<R.gate) :
    Nonempty (NaturalLeaf 9 C p.val y.val) := by
  have out := output_leaf2 rep.computes
  have notOut : C.output≠y.val := by have := y.isLt; omega
  have reaches := edge_essential rep.back rep.computes singleP edgePY
  have used := (used_from_path reaches).resolve_left notOut
  rcases center_cut_case p.isLt y.isLt rep.fan rep.back minimum live L
      (center_not_in_leaf ne rep.computes rep.back L singleY edgePY) notOut used sole with n|⟨R,_,_⟩
  · exact ⟨natural_from_case L n⟩
  · exfalso
    let x := List.ofFn (singleRow y)
    have hx : x.length=9 := by simp [x]
    have yx : x.getD y.val false=true := by
      change (List.ofFn (singleRow y)).getD y.val false=true
      rw [entry]
      simp [singleRow]
    have reject : C.eval x=false := by rw [show x=List.ofFn (singleRow y) by rfl,rep.computes,singleY]
    exact no_late_center p.isLt y.isLt rep.back L R (lt R) orDesc reaches hx yx reject

theorem proved10939 (t : ℕ) (has : HasCircuitSize 9 target10939 t) : 15≤t := by
  by_contra! bad
  obtain ⟨C,fan,sz,correct⟩ := has
  have nonconstant : ∃ x z : List Bool, x.length=9 ∧ z.length=9 ∧ C.eval x≠C.eval z := by
    refine ⟨List.ofFn (singleRow 2),List.ofFn (twoRow 2 6),by simp,by simp,?_⟩
    rw [correct,correct]
    decide +kernel
  obtain ⟨D,fd,bd,pd,ds,vo,same⟩ := normalize_any fan nonconstant
  have small : D.size≤14 := by omega
  have computes : ComputesNine D target10939 :=
    fun x => (same _ (by simp)).trans (correct x)
  have min := min_at_bound small computes lower14
  have live := live_from_min (by decide) fd bd pd min
  have out := output_leaf2 computes
  obtain ⟨r2⟩ := raw_zero_sole_or (by decide) fd bd pd min live (by omega) small
    (floor_leaf2_false computes) (varies_leaf2_false computes) (used_leaf2 bd computes)
  obtain ⟨r4⟩ := raw_zero_sole_or (by decide) fd bd pd min live (by omega) small
    (floor_leaf4_false computes) (varies_leaf4_false computes) (used_leaf4 bd computes)
  have A := leaf_pair_of_reader (by decide) fd bd pd min live small r2
    (floor_leaf2_true computes) (varies_leaf2_true computes) (rejects_leaf2 computes)
  have B := leaf_pair_of_reader (by decide) fd bd pd min live small r4
    (floor_leaf4_true computes) (varies_leaf4_true computes) (rejects_leaf4 computes)
  have rep : Representative 9 14 target10939 D := ⟨fd,bd,pd,small,vo,computes⟩
  obtain ⟨E,L2,L4,good,least⟩ := exists_least_anchors ⟨D,A,B,rep⟩
  have emin := min_at_bound good.small good.computes lower14
  have elive := live_from_min (by decide) good.fan good.back good.proper emin
  have fit2 := cut_fits (p := 2) good L2
    (reject_excludes_first (by decide) L2 (rejects_leaf2 good.computes))
  have fit4 := cut_fits (p := 4) good L4
    (reject_excludes_first (by decide) L4 (rejects_leaf4 good.computes))
  obtain ⟨s6⟩ := fit_shape_center6 fit2
  obtain ⟨s0⟩ := fit_shape_center0 fit4
  obtain ⟨na2⟩ := finish_center (p := 2) (y := 6) good emin elive L2
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s6 (cut_center6_descendants fit2) (leaf2_before_center6 good L2 L4 least)
  obtain ⟨na4⟩ := finish_center (p := 4) (y := 0) good emin elive L4
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    s0 (cut_center0_descendants fit4) (leaf4_before_center0 good L2 L4 least)
  exact not_both_natural good.back (output_leaf2 good.computes) good.computes na4 na2
end

section
open Basis

def original10938 : (Fin 9 → Bool) → Bool := fun x =>
  (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) ||
  (x 0 && x 7) || (x 3 && x 7) || (x 6 && x 7) || (x 0 && x 8) ||
  (x 1 && x 8) || (x 4 && x 8) || (x 5 && x 8)

def coordinates10938 : Fin 9 → Fin 9 := ![8,1,2,4,3,5,6,0,7]

theorem permute10938 : (fun x => original10938 (x ∘ coordinates10938)) = target10939 :=
  funext (by decide +kernel)
end

end PEqualNP.Outside.L_meta_10938_aux

open PEqualNP.Outside.L_meta_10938_aux PEqualNP.Outside.L_meta_10938_aux.Basis in
theorem PEqualNP.Outside.L_meta_10938 : ∀ t : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool =>
      (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) ||
      (x 0 && x 7) || (x 3 && x 7) || (x 6 && x 7) || (x 0 && x 8) ||
      (x 1 && x 8) || (x 4 && x 8) || (x 5 && x 8)) t → 15 ≤ t := by
  intro t h
  have mapped := yn coordinates10938 original10938 t h
  rw [PEqualNP.Outside.L_meta_10938_aux.permute10938] at mapped
  exact PEqualNP.Outside.L_meta_10938_aux.proved10939 t mapped
