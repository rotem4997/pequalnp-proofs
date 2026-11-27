import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6574_aux

-- Constant propagation and sensitive restriction from L_meta_2958 by ylwang0701.
-- Basic circuit semantics and constant propagation from the project proof of L_meta_720.
open PEqualNP.MetaComplexity
namespace Helpers
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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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
      simp [simpAnd] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

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
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
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

noncomputable def charged (g : Gate) : Bool :=
  GateOp.rec true true false (fun _ => true) true g.op

noncomputable def cost (gs : List Gate) : ℕ := gs.countP charged

-- A surviving charged gate has two live operands. A surviving NOT has one.
-- Hence if no charged gate is lost, probes agreeing on live wires still agree.
theorem step_account (op : GateOp) (m : ℕ) (ins : List ℕ)
    (M : ℕ → Stat) (u v : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2) (hag : ∀ i j, M i = Sum.inr j → u i = v i) :
    let r := simplify op m (ins.map M)
    let original := cost [⟨op, ins⟩]
    cost r.1.toList ≤ original ∧
      (cost r.1.toList = original → ∀ j, r.2 = Sum.inr j →
        op.eval (ins.map u) = op.eval (ins.map v)) := by
  rcases hop with rfl | rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try have ha := hag a; cases hma : M a) <;>
    (try have hb := hag b; cases hmb : M b) <;>
    simp_all [simplify, simpAnd, simpOr, simpNot, cost, charged, GateOp.eval]

theorem weakCost (n : ℕ) (gs : List Gate) : ∀ (acc : List Stat × List Gate),
    (∀ g ∈ gs, Ok g) → cost (elim n gs acc).2 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil => intros; simp [elim,cost]
  | cons g gs ih =>
    intro acc hok
    have hg := hok g List.mem_cons_self
    have h := (step_account g.op (n + acc.2.length) g.inputs
        (fun i => acc.1.getD i (Sum.inl false)) (fun _ => false) (fun _ => false)
        hg.1 hg.2 (fun _ _ _ => rfl)).1
    change cost (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ≤ cost [g] at h
    have ht := ih (elimStep n acc g) (fun g' h' => hok g' (List.mem_cons_of_mem _ h'))
    show cost (elim n gs (elimStep n acc g)).2 ≤ _
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    rw [hcons]
    have hadd : cost (elimStep n acc g).2 = cost acc.2 +
        cost (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList :=
      List.countP_append
    rw [hadd] at ht
    omega

theorem strictCost (n : ℕ) (gs : List Gate) (out j : ℕ) :
    ∀ (acc : List Stat × List Gate) (u v : List Bool),
      (∀ g ∈ gs, Ok g) → u.length = acc.1.length → v.length = acc.1.length →
      (∀ i k, acc.1.getD i (Sum.inl false) = Sum.inr k → u.getD i false = v.getD i false) →
      (elim n gs acc).1.getD out (Sum.inl false) = Sum.inr j →
      (wiresFrom gs u).getD out false ≠ (wiresFrom gs v).getD out false →
      cost (elim n gs acc).2 + 1 ≤ cost acc.2 + cost gs := by
  induction gs with
  | nil =>
    intro acc u v _ _ _ hag hj hdiff
    exact (hdiff (hag out j hj)).elim
  | cons g gs ih =>
    intro acc u v hok hu hv hag hj hdiff
    let M := fun i => acc.1.getD i (Sum.inl false)
    let r := simplify g.op (n + acc.2.length) (g.inputs.map M)
    have hg := hok g List.mem_cons_self
    have ha := step_account g.op (n + acc.2.length) g.inputs M
      (fun i => u.getD i false) (fun i => v.getD i false) hg.1 hg.2 hag
    change cost r.1.toList ≤ cost [g] ∧ _ at ha
    have hcost : cost (elimStep n acc g).2 = cost acc.2 + cost r.1.toList := by
      apply List.countP_append
    have hcons : cost (g::gs) = cost [g] + cost gs := List.countP_append
      (p := charged) (l₁ := [g]) (l₂ := gs)
    have htail (g' : Gate) (h' : g' ∈ gs) := hok g' (List.mem_cons_of_mem _ h')
    change cost (elim n gs (elimStep n acc g)).2 + 1 ≤ _
    rw [hcons]
    by_cases heq : cost r.1.toList = cost [g]
    · let U := g.op.eval (g.inputs.map fun i => u.getD i false)
      let V := g.op.eval (g.inputs.map fun i => v.getD i false)
      have hnext := ih (elimStep n acc g) (u ++ [U]) (v ++ [V]) htail
        (by simp [elimStep,hu]) (by simp [elimStep,hv]) (by
          intro i k h
          change (acc.1 ++ [r.2]).getD i (Sum.inl false) = Sum.inr k at h
          by_cases hi : i = acc.1.length
          · subst i
            rw [getD_snoc_eq] at h
            rw [← hu, getD_snoc_eq, hu, ← hv, getD_snoc_eq]
            exact ha.2 heq k h
          · rw [getD_snoc_ne _ _ _ _ hi] at h
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag i k h) hj hdiff
      omega
    · have hweak := weakCost n gs (elimStep n acc g) htail
      omega

-- Track the surviving input wire for each occurrence in the original input list.
def pinStat {n : ℕ} (p : Fin (n+1)) : Fin (n+1) → Stat :=
  Fin.insertNth (α := fun _ => Stat) p (Sum.inl false) (fun j => Sum.inr j.val)

theorem pinStat_valid {n : ℕ} (p i : Fin (n+1)) : (pinStat p i).Valid n := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.Valid]
  · rename_i j
    simp [pinStat, Stat.Valid]

theorem pinStat_val {n : ℕ} (p i : Fin (n+1)) (y : Fin n → Bool) :
    (pinStat p i).val (List.ofFn y) = Fin.insertNth (α := fun _ => Bool) p false y i := by
  cases i using Fin.succAboveCases p
  · simp [pinStat, Stat.val]
  · rename_i j
    simp only [pinStat, Fin.insertNth_apply_succAbove, Stat.val]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt),List.getElem_ofFn]

theorem getMap {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d : β) :
    (l.map f).getD i d = if h : i < l.length then f l[i] else d := by
  by_cases h : i < l.length
  · rw [dite_eq_left h,List.getD_eq_getElem _ _ (by simpa using h),List.getElem_map]
  · rw [dite_eq_right h,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]

theorem pinValid {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).Valid n := by
  rw [getMap]; split
  · exact pinStat_valid _ _
  · trivial

theorem pinMap {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (y : Fin n → Bool) (k : ℕ) :
    ((l.map (pinStat p)).getD k (Sum.inl false)).val (List.ofFn y) =
      (l.map (Fin.insertNth (α := fun _ => Bool) p false y)).getD k false := by
  rw [getMap,getMap]; split
  · exact pinStat_val _ _ _
  · rfl

theorem pinAgree {n : ℕ} (p : Fin (n+1)) (l : List (Fin (n+1))) (x : Fin (n+1) → Bool) (k j : ℕ)
    (h : (l.map (pinStat p)).getD k (Sum.inl false) = Sum.inr j) :
    (l.map (Function.update x p true)).getD k false = (l.map (Function.update x p false)).getD k false := by
  rw [getMap] at h
  rw [getMap,getMap]
  by_cases hk : k < l.length
  · simp only [dite_eq_left hk] at h ⊢
    have e : l[k] ≠ p := by
      intro e
      simp [e,pinStat] at h
    simp [Function.update_of_ne e]
  · simp [hk]

theorem restrictSensitive (n : Nat) (p : Fin (n+1)) (C : Circuit) (l : List (Fin (n+1)))
    (hfan : FanInTwo C)
    (hprobe : ∃ x : Fin (n+1) → Bool, C.eval (l.map (Function.update x p true)) ≠
      C.eval (l.map (Function.update x p false)))
    (hnc : ∃ a b : Fin n → Bool, C.eval (l.map (p.insertNth false a)) ≠ C.eval (l.map (p.insertNth false b))) :
    ∃ D : Circuit, FanInTwo D ∧ cost D.gates+1 ≤ cost C.gates ∧
      circuitFun n D = fun y => C.eval (l.map (p.insertNth false y)) := by
  obtain ⟨x, hx⟩ := hprobe
  let M := l.map (pinStat p)
  let gs := C.gates
  let acc := elim n gs (M,[])
  have hok (g) (hg : g ∈ gs) : Ok g := hfan g hg
  have hval (y : Fin n → Bool) : (acc.1.getD C.output (Sum.inl false)).val
      (wiresFrom acc.2 (List.ofFn y)) = C.eval (l.map (p.insertNth false y)) := by
    let z := l.map (p.insertNth false y)
    have hi : Inv n (List.ofFn y) z (M,[]) := by
      refine ⟨by simp [M,z],?_⟩
      intro k
      exact ⟨pinValid p l k,pinMap p l y k⟩
    have he := ((inv_elim n (List.ofFn y) (by simp) gs z (M,[]) hok hi).2 C.output).2
    exact he
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨a,c,hac⟩ := hnc
    exact (hac (by rw [← hval a, ← hval c, ho]; rfl)).elim
  | inr j =>
    let u := l.map (Function.update x p true)
    let v := l.map (Function.update x p false)
    have hdiff : (wiresFrom gs u).getD C.output false ≠ (wiresFrom gs v).getD C.output false := by
      exact hx
    have hs := strictCost n gs C.output j (M,[]) u v hok
      (by simp [u,M]) (by simp [v,M]) (pinAgree p l x) ho hdiff
    refine ⟨⟨acc.2,j⟩, elim_ok n gs (M,[]) (by simp), ?_, ?_⟩
    · change cost acc.2 + 1 ≤ cost gs
      simpa only [show cost [] = 0 from rfl, Nat.zero_add] using hs
    · funext y
      have h := hval y
      rw [ho] at h
      exact h

end Helpers

-- Signed truth-column semantics adapted from L_meta_3202 (PRs 5972 and 6505).
namespace Theta

/- Each sampled signal carries its phase. The four binary operations represent AND and OR on signed inputs, and inverting a signal changes only its phase. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A wire is a phase and a column of sampled truth values. Complementing a wire is free.
abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_zero]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = Helpers.wiresFrom gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = Helpers.wiresFrom gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

end Theta

namespace Triangle
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Theta

-- Three-variable majority has truth mask 232. Its complement is 23.
def target (z : Nat) : Bool := z &&& 255 == 232 || z &&& 255 == 23

def choices (av : List Nat) := (List.range 4).flatMap fun d => av.flatMap fun a => av.flatMap fun b =>
  let z := combine d a b
  if a≠0 ∧ b≠0 ∧ a≠b ∧ z ∉ av then [z] else []

def scan : Nat → List Nat → Bool
  | 0, av => av.any target
  | k+1, av => scan k av || (choices av).any fun z => scan k (z :: av)

private theorem whole (gs : List Gate) (w : List Wire) (av : List Nat) (i : Nat)
    (hasZero : 0 ∈ av) (contains : ∀ t ∈ reps w, t ∈ av)
    (success : target (((execute gs w).getD i zero).2) = true) :
    scan (gs.countP counted) av = true := by
  induction gs generalizing w av with
  | nil =>
    apply List.any_eq_true.mpr
    exact ⟨_,(get_simple w i).elim (fun e => e ▸ hasZero) (fun h => contains _ h),success⟩
  | cons g gs ih =>
    let t := gate w g
    let z := t.2
    have tail : target (((execute gs (w++[t])).getD i zero).2) = true := success
    have recur (next : List Nat) (old : ∀ a ∈ av, a ∈ next) (zmem : z ∈ next) :
        scan (gs.countP counted) next = true :=
      ih _ _ (old _ hasZero) (fun a h => by
        rcases (show a ∈ reps w ∨ a=z by simpa [reps,t,z] using h) with mem|rfl
        · exact old _ (contains _ mem)
        · exact zmem) tail
    by_cases inside : z ∈ av
    · have again := recur av (fun _ h => h) inside
      cases hp : counted g <;> simp [hp,scan,again]
    · rcases gate_priced w g with small|⟨pay,d,hd,a,ha,b,hb,pa,pb,diff,eq⟩
      · change simple w z at small
        exact False.elim (inside (small.elim (fun h => h ▸ hasZero) (contains _)))
      · have later := recur (z::av) (fun _ h => List.mem_cons_of_mem _ h) List.mem_cons_self
        change z=combine d a b at eq
        rw [List.countP_cons,pay]
        apply Bool.or_eq_true_iff.mpr; right
        apply List.any_eq_true.mpr
        refine ⟨z,?_,later⟩
        simp only [choices,List.mem_flatMap]
        exact ⟨d,List.mem_range.mpr hd,a,contains a ha,b,contains b hb,by simp [←eq,pa,pb,diff,inside]⟩

def inputs : List Wire := [(false,170),(false,204),(false,240)]
def maj (x : Fin 3 → Bool) := x 0 && x 1 || x 0 && x 2 || x 1 && x 2

private theorem base0 : scan 2 (10 :: [0,170,204,240]) = false := by decide +kernel
private theorem base1 : scan 2 (12 :: [0,170,204,240]) = false := by decide +kernel
private theorem base2 : scan 2 (34 :: [0,170,204,240]) = false := by decide +kernel
private theorem base3 : scan 2 (48 :: [0,170,204,240]) = false := by decide +kernel
private theorem base4 : scan 2 (68 :: [0,170,204,240]) = false := by decide +kernel
private theorem base5 : scan 2 (80 :: [0,170,204,240]) = false := by decide +kernel
private theorem base6 : scan 2 (136 :: [0,170,204,240]) = false := by decide +kernel
private theorem base7 : scan 2 (160 :: [0,170,204,240]) = false := by decide +kernel
private theorem base8 : scan 2 (192 :: [0,170,204,240]) = false := by decide +kernel
private theorem base9 : scan 2 (238 :: [0,170,204,240]) = false := by decide +kernel
private theorem base10 : scan 2 (250 :: [0,170,204,240]) = false := by decide +kernel
private theorem base11 : scan 2 (252 :: [0,170,204,240]) = false := by decide +kernel
private theorem little : scan 3 [0,170,204,240] = false := by
  have skip : scan 2 [0,170,204,240] = false := by decide +kernel
  have next : choices [0,170,204,240] = [136,160,136,192,160,192,238,250,238,252,250,252,34,10,68,12,80,48,68,80,34,48,10,12] := by decide
  rw [scan,next,skip]
  simp only [List.any_cons,List.any_nil,Bool.false_or,base0,base1,base2,base3,base4,base5,base6,base7,base8,base9,base10,base11]

private theorem read_target (s : Wire) (run : ∀ p : Fin 8, read p.val s = (232 : Nat).testBit p.val) :
    target s.2=true := by
  let m : Fin 256 := Fin.ofNat 256 s.2
  have modBit (p : Fin 8) : m.val.testBit p.val = s.2.testBit p.val := by
    change (s.2 % 2^8).testBit p.val = _
    rw [Nat.testBit_mod_two_pow s.2 8 p.val,decide_eq_true p.isLt]; rfl
  have finite : ∀ (z : Fin 256) (phase : Bool), (∀ p : Fin 8, (phase != z.val.testBit p.val) = (232 : Nat).testBit p.val) →
      z.val=232 ∨ z.val=23 := by decide +kernel
  have hh := finite m s.1 (fun p => by rw [modBit]; exact run p)
  have val : s.2 &&& 255 = m.val := (Nat.and_two_pow_sub_one_eq_mod _ 8)
  rcases hh with h|h <;> simp [target,val,h]

theorem majority_lower (C : Circuit) (legal : FanInTwo C) (computes : circuitFun 3 C = maj) :
    4 ≤ C.gates.countP counted := by
  let W := execute C.gates inputs
  let s := W.getD C.output zero
  let x (p : Fin 8) (i : Fin 3) := p.val.testBit i.val
  have row : ∀ p, inputs.map (read p.val) = List.ofFn (x p) := by decide
  have val : ∀ p, maj (x p) = (232 : Nat).testBit p.val := by decide
  have observed (p : Fin 8) : read p.val s = (232 : Nat).testBit p.val := by
    rw [←val,←computes]
    change read p.val (W.getD C.output zero) = (Helpers.wiresFrom C.gates (List.ofFn (x p))).getD C.output false
    rw [←row,←execute_read _ _ _ legal,read_get]
  have yes := whole C.gates inputs [0,170,204,240] C.output (by decide)
    (by intro t ht; exact List.mem_cons_of_mem _ ht) (read_target s observed)
  rcases Nat.lt_or_ge (C.gates.countP counted) 4 with bound|ok
  · have mono (a b : Nat) (le : a≤b) (av : List Nat) (h : scan a av = true) : scan b av = true := by
      induction le with
      | refl => exact h
      | step _ ih => simp [scan,ih]
    have contra := mono _ 3 (by omega) _ yes
    rw [little] at contra; contradiction
  · exact ok
end Triangle
end PEqualNP.Outside.L_meta_6574_aux

namespace PEqualNP.Outside.L_meta_6574_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

-- Restrict a sensitive input to false when the cofactor is nonconstant. The
-- paid-gate measure skips all NOT gates, including any made by propagation.
private theorem drop (n : Nat) (C : Circuit) (f : (Fin (n+1) → Bool) → Bool) (g : (Fin n → Bool) → Bool)
    (legal : FanInTwo C) (correct : circuitFun (n+1) C = f)
    (sen : ∃ x, f (Function.update x (Fin.last n) true) ≠ f (Function.update x (Fin.last n) false))
    (cof : ∀ x, f ((Fin.last n).insertNth false x) = g x) (nc : ∃ x y, g x ≠ g y) :
    ∃ D : Circuit, FanInTwo D ∧ Helpers.cost D.gates+1 ≤ Helpers.cost C.gates ∧ circuitFun n D = g := by
  let p := Fin.last n
  let pins := List.finRange (n+1)
  have obs (x : Fin (n+1) → Bool) : C.eval (pins.map x) = f x := by
    rw [show pins.map x=List.ofFn x from List.ofFn_eq_map.symm]
    exact congrFun correct x
  obtain ⟨x,source⟩ := sen
  obtain ⟨a,b,diff⟩ := nc
  obtain ⟨D,ok,small,same⟩ := Helpers.restrictSensitive n p C pins legal
    ⟨x,by simpa only [obs] using source⟩
    ⟨a,b,fun eq => diff ((cof a).symm.trans ((obs _).symm.trans (eq.trans ((obs _).trans (cof b)))))⟩
  exact ⟨D,ok,small,funext fun y => ((congrFun same y).trans (obs _)).trans (cof _)⟩

private def graph (n : Nat) (x : Fin n → Bool) :=
  let v := fun i => (List.ofFn x).getD i false
  (v 0 && v 1) || (v 0 && v 2) || (v 0 && v 3) || (v 0 && v 4) ||
  (v 0 && v 5) || (v 1 && v 2) || (v 1 && v 6) || (v 1 && v 7)

private theorem count_eq (gs : List Gate) : Helpers.cost gs = gs.countP Theta.counted := by
  unfold Helpers.cost
  congr 1
  funext g
  cases g with | mk op ins => cases op <;> rfl

end PEqualNP.Outside.L_meta_6574_aux
open PEqualNP.Outside.L_meta_6574_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each of the five pendant inputs is sensitive before its restriction to false.
-- The remaining triangle needs four binary gates even when negations are free.

theorem PEqualNP.Outside.L_meta_6574 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 1 && x 7)) t → 9 ≤ t := by
  rintro t ⟨C8,ok8,size8,compute8⟩
  have eq8 : circuitFun 8 C8 = graph 8 := by
    funext x
    exact (compute8 x).trans (by rfl)
  obtain ⟨C7,ok7,paid7,eq7⟩ := drop 7 C8 (graph 8) (graph 7) ok8 eq8
    ⟨fun i => i.val == 1,by decide⟩ (by decide +kernel) ⟨fun _ => false,fun _ => true,by decide⟩
  obtain ⟨C6,ok6,paid6,eq6⟩ := drop 6 C7 (graph 7) (graph 6) ok7 eq7
    ⟨fun i => i.val == 1,by decide⟩ (by decide +kernel) ⟨fun _ => false,fun _ => true,by decide⟩
  obtain ⟨C5,ok5,paid5,eq5⟩ := drop 5 C6 (graph 6) (graph 5) ok6 eq6
    ⟨fun i => i.val == 0,by decide⟩ (by decide +kernel) ⟨fun _ => false,fun _ => true,by decide⟩
  obtain ⟨C4,ok4,paid4,eq4⟩ := drop 4 C5 (graph 5) (graph 4) ok5 eq5
    ⟨fun i => i.val == 0,by decide⟩ (by decide +kernel) ⟨fun _ => false,fun _ => true,by decide⟩
  obtain ⟨C3,ok3,paid3,eq3⟩ := drop 3 C4 (graph 4) (graph 3) ok4 eq4
    ⟨fun i => i.val == 0,by decide⟩ (by decide +kernel) ⟨fun _ => false,fun _ => true,by decide⟩
  have endFn : graph 3 = Triangle.maj := funext (by decide)
  have hard := Triangle.majority_lower C3 ok3 (eq3.trans endFn)
  have counted : Helpers.cost C8.gates ≤ C8.size := List.countP_le_length
  rw [←count_eq] at hard
  omega
