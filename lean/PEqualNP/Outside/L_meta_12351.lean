import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12351.Credit

abbrev Signal (α : Type) := α → Bool

def fixed {α : Type} (b : Bool) : Signal α := fun _ => b

def inverse {α : Type} (f : Signal α) : Signal α := fun x => !f x

def combine {α : Type} (tag : Bool) (a b : Signal α) : Signal α :=
  if tag then fun x => a x && b x else fun x => a x || b x

def pull {α β : Type} (q : β → α) (f : Signal α) : Signal β := fun x => f (q x)

def Constant {α : Type} (f : Signal α) := ∃ b, f = fixed b

def Available {α : Type} (s : Set (Signal α)) (f : Signal α) : Prop :=
  Constant f ∨ ∃ u ∈ s, f = u ∨ f = inverse u

theorem member {α : Type} {s : Set (Signal α)} {f} (h : f ∈ s) : Available s f :=
  Or.inr ⟨f, h, Or.inl rfl⟩

theorem availConst {α : Type} (s : Set (Signal α)) (c : Bool) : Available s (fixed c) :=
  Or.inl ⟨c, rfl⟩

theorem inverse_inverse {α : Type} (f : Signal α) : inverse (inverse f) = f := by
  funext x
  simp [inverse]

theorem availNeg {α : Type} {s : Set (Signal α)} {f} (h : Available s f) :
    Available s (inverse f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact availConst s (!b)
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · rw [inverse_inverse]
    exact member hu

theorem availInsert {α : Type} {s : Set (Signal α)} {f} (g) (h : Available s f) :
    Available (insert g s) f := by
  rcases h with hc | ⟨u, hu, he⟩
  · exact Or.inl hc
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, he⟩

theorem pullCombine {α β : Type} (q : β → α) (tag) (a b : Signal α) :
    pull q (combine tag a b) = combine tag (pull q a) (pull q b) := by
  cases tag <;> rfl

theorem availMap {α β : Type} {s : Set (Signal α)} {t : Set (Signal β)} {q : β → α}
    (hs : ∀ u ∈ s, Available t (pull q u)) {f} (h : Available s f) :
    Available t (pull q f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact availConst _ _
  · exact hs _ hu
  · exact availNeg (hs _ hu)

theorem cheap {α : Type} {s : Set (Signal α)} (tag) {a b}
    (ha : Available s a) (hb : Available s b) (hc : Constant a ∨ Constant b) :
    Available s (combine tag a b) := by
  rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases v <;> cases tag <;>
    simp [combine, fixed] <;>
    first | exact ha | exact hb

inductive Program {α : Type} : Set (Signal α) → Signal α → Nat → Prop where
  | done {s f} (h : Available s f) : Program s f 0
  | gate {s f a b k} (tag : Bool) (ha : Available s a) (hb : Available s b)
      (tail : Program (insert (combine tag a b) s) f k) : Program s f (k + 1)

def Simple {α β : Type} (q : β → α) (x y : α) (f : Signal α) :=
  f x = f y ∨ Constant (pull q f)

theorem simpleNeg {α β : Type} {q : β → α} {x y : α} {f : Signal α}
    (h : Simple q x y f) : Simple q x y (inverse f) := by
  rcases h with hs | ⟨b, he⟩
  · exact Or.inl (congrArg Bool.not hs)
  · exact Or.inr ⟨!b, congrArg inverse he⟩

theorem simpleAvailable {α β : Type} {q : β → α} {x y : α} {s : Set (Signal α)}
    (hs : ∀ u ∈ s, Simple q x y u) {f} (h : Available s f) : Simple q x y f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl rfl
  · exact hs _ hu
  · exact simpleNeg (hs _ hu)

theorem restrictProgram {α β : Type} (q : β → α) (x y : α) {s : Set (Signal α)} {f k}
    (p : Program s f k) (t : Set (Signal β))
    (hs : ∀ u ∈ s, Available t (pull q u)) :
    ∃ j, j ≤ k ∧ Program t (pull q f) j ∧
      (j = k → (∀ u ∈ s, Simple q x y u) → Simple q x y f) := by
  induction p generalizing t with
  | done h =>
    exact ⟨0, le_rfl, .done (availMap hs h), fun _ h' => simpleAvailable h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    have pa := availMap hs ha
    have pb := availMap hs hb
    by_cases hc : Constant (pull q a) ∨ Constant (pull q b)
    · have mid : Available t (pull q (combine tag a b)) := by
        rw [pullCombine]
        exact cheap tag pa pb hc
      obtain ⟨j, hj, prog, _⟩ := ih t (fun v hv => by
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact mid
        · exact hs _ hu)
      exact ⟨j, by omega, prog, fun he => by omega⟩
    · let c := combine tag (pull q a) (pull q b)
      obtain ⟨j, hj, prog, active⟩ := ih (insert c t) (fun v hv => by
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · rw [pullCombine]
          exact member (Set.mem_insert _ _)
        · exact availInsert _ (hs _ hu))
      refine ⟨j+1, by omega, .gate tag pa pb prog, ?_⟩
      intro he ss
      apply active (by omega)
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | mem
      · have sta : a x = a y := (simpleAvailable ss ha).resolve_right (fun h => hc (.inl h))
        have stb : b x = b y := (simpleAvailable ss hb).resolve_right (fun h => hc (.inr h))
        left
        cases tag <;> simp [combine, sta, stb]
      · exact ss _ mem

theorem strictRestriction {α β : Type} (q : β → α) (x y : α) {s : Set (Signal α)} {f k}
    (p : Program s f k) (t : Set (Signal β))
    (hs : ∀ u ∈ s, Available t (pull q u)) (hi : ∀ u ∈ s, Simple q x y u)
    (hf : ¬ Simple q x y f) : ∃ j < k, Program t (pull q f) j := by
  obtain ⟨j, hj, hp, hh⟩ := restrictProgram q x y p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (hh he hi)), hp⟩

end PEqualNP.Outside.L_meta_12351.Credit

namespace PEqualNP.Outside.L_meta_12351.Credit

open PEqualNP.CircuitLowerBounds

def paid (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, _ :: _ :: _ => true
  | .or, _ :: _ :: _ => true
  | _, _ => false

def Legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def readWire {α : Type} (w : List (Signal α)) (i : Nat) := w.getD i (fixed false)

def gateVal {α : Type} (w : List (Signal α)) (g : Gate) : Signal α :=
  fun x => g.op.eval (g.inputs.map fun i => readWire w i x)

def extend {α : Type} (w : List (Signal α)) (g : Gate) := w ++ [gateVal w g]

theorem readAvailable {α : Type} {s : Set (Signal α)} {w : List (Signal α)}
    (hw : ∀ u ∈ w, Available s u) (i : Nat) : Available s (readWire w i) := by
  by_cases h : i < w.length
  · apply hw
    simp [readWire, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [readWire, List.getD_eq_default _ _ (by omega)]
    exact availConst s false

theorem classify {α : Type} {s : Set (Signal α)} (w : List (Signal α)) (g : Gate)
    (hg : Legal g) (hw : ∀ u ∈ w, Available s u) :
    if paid g then ∃ t a b, Available s a ∧ Available s b ∧ gateVal w g = combine t a b
    else Available s (gateVal w g) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [paid, gateVal, GateOp.eval] <;>
      first | exact availConst s true | exact availConst s false
  · rcases hop with rfl | rfl | rfl
    · change Available s (gateVal w ⟨.and, [i]⟩)
      rw [show gateVal w ⟨.and, [i]⟩ = readWire w i by funext x; simp [gateVal, GateOp.eval]]
      exact readAvailable hw i
    · change Available s (gateVal w ⟨.or, [i]⟩)
      rw [show gateVal w ⟨.or, [i]⟩ = readWire w i by funext x; simp [gateVal, GateOp.eval]]
      exact readAvailable hw i
    · exact availNeg (readAvailable hw i)
  · rcases hop with rfl | rfl | rfl
    · simp only [paid, if_true, Bool.true_eq]
      exact ⟨true, readWire w i, readWire w j, readAvailable hw i, readAvailable hw j,
        by funext x; simp [gateVal, GateOp.eval, combine]⟩
    · simp only [paid, if_true, Bool.true_eq]
      exact ⟨false, readWire w i, readWire w j, readAvailable hw i, readAvailable hw j,
        by funext x; simp [gateVal, GateOp.eval, combine]⟩
    · simp [paid, gateVal, GateOp.eval]
      exact availNeg (readAvailable hw i)
  · simp at hlen

theorem rawProgram {α : Type} (gs : List Gate) (o : Nat) (hg : ∀ g ∈ gs, Legal g)
    (w : List (Signal α)) (s : Set (Signal α)) (hw : ∀ u ∈ w, Available s u) :
    Program s (readWire (gs.foldl extend w) o) (gs.filter paid).length := by
  induction gs generalizing w s with
  | nil =>
    exact .done (readAvailable hw o)
  | cons g gs ih =>
    have hclass := classify w g (hg g (by simp)) hw
    have tail := ih (fun v hv => hg v (by simp [hv])) (extend w g)
    cases hp : paid g
    · simp only [hp, Bool.false_eq_true, if_false] at hclass
      simp only [List.foldl_cons, List.filter_cons_of_neg (by simp [hp] : ¬paid g = true)]
      apply tail s
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact hw _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hclass
    · simp only [hp, if_true, Bool.true_eq] at hclass
      obtain ⟨tag,a,b,ha,hb,eq⟩ := hclass
      simp only [List.foldl_cons, List.filter_cons_of_pos (by simp [hp] : paid g = true), List.length_cons]
      apply Program.gate tag ha hb
      apply tail (insert (combine tag a b) s)
      intro v hv
      rcases List.mem_append.mp hv with h | h
      · exact availInsert _ (hw _ h)
      · obtain rfl := List.mem_singleton.mp h
        rw [eq]
        exact member (Set.mem_insert _ _)

def input {n : Nat} (i : Fin n) : Signal (Fin n → Bool) := fun x => x i

def stock (n : Nat) : Set (Signal (Fin n → Bool)) := Set.range (@input n)

theorem readValues {α : Type} (w : List (Signal α)) (x : α) (i : Nat) :
    (w.map (fun f => f x)).getD i false = readWire w i x := by
  change (w.map (fun f => f x)).getD i ((fixed false : Signal α) x) = _
  rw [List.getD_map]
  rfl

theorem evalValues {α : Type} (gs : List Gate) (w : List (Signal α)) (x : α) :
    (gs.foldl extend w).map (fun f => f x) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
        (w.map fun f => f x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, extend, List.map_append, List.map_cons, List.map_nil,
      gateVal, readValues]

theorem programOf {n : Nat} (gs : List Gate) (o : Nat) (f : Signal (Fin n → Bool))
    (hg : ∀ g ∈ gs, Legal g) (he : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) :
    Program (stock n) f (gs.filter paid).length := by
  let w := List.ofFn (@input n)
  have hw : ∀ u ∈ w, Available (stock n) u := by
    intro u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact member ⟨i, rfl⟩
  have h := rawProgram gs o hg w (stock n) hw
  have ident : readWire (gs.foldl extend w) o = f := by
    funext x
    rw [← readValues, evalValues]
    have init : (w.map fun p => p x) = List.ofFn x := by
      simp [w, List.map_ofFn, Function.comp_def, input]
    rw [init, ← he x]
    rfl
  rwa [ident] at h

theorem notSimple {α β : Type} (q : β → α) (f : Signal α) (x y : α) (a b : β)
    (hc : f x ≠ f y) (hn : f (q a) ≠ f (q b)) : ¬ Simple q x y f := by
  rintro (hs | ⟨c, hb⟩)
  · exact hc hs
  · apply hn
    exact (congrFun hb a).trans (congrFun hb b).symm

end PEqualNP.Outside.L_meta_12351.Credit

namespace PEqualNP.Outside.L_meta_12351.Signed

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 494
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 247 := ((x >>> 247) ^^^ x).setWidth 247
def cuts (ws : List W) : BitVec 247 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 247) ++ (0 : BitVec 247)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def differs (i : Fin 247) (w : W) : Prop :=
  w.getLsbD (247+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 247) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 247+i.val < 494 := by omega
  have hi' : i.val < 494 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 247) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 247)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
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
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 494 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 494)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))



end PEqualNP.Outside.L_meta_12351.Signed

namespace PEqualNP.Outside.L_meta_12351.Generic

open PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Signed

variable {β : Type} (sample : Fin 494 → β)

def Agrees (f : Signal β) (w : W) := ∀ k : Fin 494, w[k.val] = f (sample k)

def Represents (av : Finset W) (f : Signal β) := ∃ w, holds av w ∧ Agrees sample f w

theorem onesBit : ∀ k : Fin 494, (~~~(0 : W))[k.val] = true := by decide +kernel

theorem representAvailable {s : Set (Signal β)} {av : Finset W}
    (hs : ∀ u ∈ s, Represents sample av u) {f} (hf : Available s f) : Represents sample av f := by
  rcases hf with ⟨c,rfl⟩ | ⟨u,hu,rfl | rfl⟩
  · cases c
    · exact ⟨0, Or.inl rfl, fun _ => by simp [fixed]⟩
    · exact ⟨~~~0, Or.inr (Or.inl rfl), onesBit⟩
  · exact hs _ hu
  · obtain ⟨w, hw, hv⟩ := hs _ hu
    exact ⟨~~~w, holds_not hw, fun k => by simp [inverse, ← hv k]⟩

set_option maxRecDepth 12000 in
theorem simulate {s : Set (Signal β)} {f k} (p : Program s f k) :
    ∀ (target : ∀ i : Fin 494, f (sample i) = (~~~goal)[i.val])
      (av : Finset W), (∀ u ∈ s, Represents sample av u) →
      ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t k av := by
  induction p with
  | done h =>
    intro target av hs
    obtain ⟨w,hw,hv⟩ := representAvailable sample hs h
    have eq : w = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      exact (hv ⟨i,hi⟩).trans (target ⟨i,hi⟩)
    rw [eq] at hw
    rcases hw with hz | ho | ⟨t,ht,he | he⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) hz)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ho)
    · exact ⟨t, .inr he.symm, ht⟩
    · exact ⟨t, .inl (by simpa using congrArg (fun v : W => ~~~v) he.symm), ht⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro target av hs
    obtain ⟨u,hu,ua⟩ := representAvailable sample hs ha
    obtain ⟨v,hv,vb⟩ := representAvailable sample hs hb
    let z := if tag then u &&& v else u ||| v
    have rz : reachable av z := by
      cases tag <;> first | exact or_reach hu hv | exact and_reach hu hv
    have az : Agrees sample (combine tag a b) z := by
      intro i
      cases tag <;> simp [z, combine, ua i, vb i]
    have follow (av' : Finset W) (old : ∀ u ∈ s, Represents sample av' u) (new : holds av' z) :=
      ih target av' (fun q hq => by
        rcases Set.mem_insert_iff.mp hq with rfl | h
        · exact ⟨z, new, az⟩
        · exact old _ h)
    rcases rz with same | ⟨x,hx,y,hy,ne,res,op,new⟩
    · obtain ⟨t,ht,run⟩ := follow av hs same
      exact ⟨t,ht,Or.inl run⟩
    · have old (q) (hq : q ∈ s) : Represents sample (insert res av) q := by
        obtain ⟨w,hw,eq⟩ := hs q hq
        exact ⟨w,holds_insert hw,eq⟩
      obtain ⟨t,ht,run⟩ := follow (insert res av) old new
      exact ⟨t,ht,Or.inr ⟨x,hx,y,hy,ne,res,op,run⟩⟩

end PEqualNP.Outside.L_meta_12351.Generic

namespace PEqualNP.Outside.L_meta_12351.Small

open PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Signed
open PEqualNP.Outside.L_meta_12351


theorem onlyStart {k : Nat} (xs : List W)
    (single : xs.sublists.filter (fun w => decide (w.length ≤ k+1) && (cuts w == -1)) = [xs])
    (no : optimized k (k+1-xs.length) xs = false) : search k xs = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  obtain ⟨ws,mem,ok⟩ := List.any_eq_true.mp yes
  simp only [Bool.and_eq_true] at ok
  obtain ⟨room,found⟩ := ok
  have hm : ws ∈ xs.sublists.filter (fun w => decide (w.length ≤ k+1) && (cuts w == -1)) :=
    List.mem_filter.mpr ⟨mem,by simpa only [Bool.and_eq_true] using room⟩
  rw [single,List.mem_singleton] at hm
  subst ws
  exact Bool.noConfusion (no.symm.trans found)

def byPair (k extra : Nat) (ws : List W) (i : Nat) : Bool :=
  let abc := (pairs ws).getD i (0,0,[])
  dispatch extra (optimized k) abc.1 abc.2.1 abc.2.2

theorem allPairs {k extra n : Nat} (ws : List W) (sz : (pairs ws).length = n)
    (notEnd : (ws == [goal] || ws == [~~~goal]) = false)
    (no : ∀ i : Fin n, byPair k extra ws i.val = false) :
    optimized (k+1) extra ws = false := by
  apply Bool.eq_false_iff.mpr
  intro yes
  simp only [optimized,notEnd,Bool.false_or,List.any_eq_true] at yes
  obtain ⟨v,mem,found⟩ := yes
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  have bad := no ⟨i,by omega⟩
  simp only [byPair,List.getD_eq_getElem _ _ hi,eq] at bad
  rcases v with ⟨a,b,r⟩
  exact Bool.noConfusion (bad.symm.trans found)

def atTable {n : Nat} (t : Nat) (x : Fin n → Bool) : Bool :=
  t.testBit (∑ i : Fin n, if x i then 2 ^ (i : Nat) else 0)

def sample {n : Nat} (ws : List W) (i : Fin 494) (j : Fin n) : Bool :=
  (ws.getD j.val 0)[i.val]

theorem wordLower {n cap : Nat} (ws : List W) (f : Signal (Fin n → Bool))
    (nd : ws.Nodup) (support : ∀ j : Fin n, ws.getD j.val 0 ∈ ws)
    (agrees : ∀ i : Fin 494, f (sample ws i) = (~~~goal)[i.val])
    (excluded : search cap ws = false)
    {k : Nat} (p : Program (stock n) f k) : cap+1 ≤ k := by
  by_contra! small
  obtain ⟨g,hg,run⟩ := Generic.simulate (sample ws) p agrees ws.toFinset (fun u hu => by
    obtain ⟨i,rfl⟩ := hu
    exact ⟨ws.getD i.val 0, .inr (.inr ⟨_,List.mem_toFinset.mpr (support i),.inl rfl⟩),fun _ => rfl⟩)
  have up {a b : Nat} (h : a ≤ b) (work : build basicOps g a ws.toFinset) :
      build basicOps g b ws.toFinset := by
    induction h with
    | refl => exact work
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (excluded.symm.trans (search_complete hg cap ws nd (up (by omega) run)))

end PEqualNP.Outside.L_meta_12351.Small

-- The signed search excludes seven gates for the five-input cofactor.
namespace PEqualNP.Outside.L_meta_12351.Small

open PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Signed
open PEqualNP.Outside.L_meta_12351

def wA : List W := [0x7ffc001fff0000003ffe000fff8000001fff0007ffc001fff0005b6edb76dbb6ddb6edb76dbb6ddb6edb76dbb6ddb6edb76dbb6ddb6edb76db,0x7fffffe0000000003ffffff0000003ffe0000007fffffe0000006db76dbb6ddb6edb76dbb6ddb6edb76dbb6ddb6edb76dbb6ddb6edb76dbb6d,0x3ffe000fff80000000000007ffc0000000000003fffffffff800000000000071ff8ffc7fe3ff1ff8ffc7fe3ff1ff8ffc7fe3ff1ff8ffc7fe3ff1ff8ffc7f,0x3ffffff00000000000000007fffffffffffffffc00000000000000000000007e3bf1df8efc77e3bf1df8efc77e3bf1df8efc77e3bf1df8efc77e3bf1df8e,0x3ffffffffffffffffffffff8000000000000000000000000000000000000007fc3fe1ff0ff87fc3fe1ff0ff87fc3fe1ff0ff87fc3fe1ff0ff87fc3fe1ff0]

def fA : Signal (Fin 5 → Bool) := atTable 4007714944

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA0 : byPair 6 3 wA 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA1 : byPair 6 3 wA 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA2 : byPair 6 3 wA 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA3 : byPair 6 3 wA 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA4 : byPair 6 3 wA 4 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA5 : byPair 6 3 wA 5 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA6 : byPair 6 3 wA 6 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA7 : byPair 6 3 wA 7 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA8 : byPair 6 3 wA 8 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairA9 : byPair 6 3 wA 9 = false := by decide +kernel

theorem rowsA (i : Fin 10) : byPair 6 3 wA i.val = false := by
  fin_cases i
  · exact pairA0
  · exact pairA1
  · exact pairA2
  · exact pairA3
  · exact pairA4
  · exact pairA5
  · exact pairA6
  · exact pairA7
  · exact pairA8
  · exact pairA9

set_option maxRecDepth 16000 in
theorem rejectA : search 7 wA = false := by
  apply onlyStart _ (by decide +kernel)
  exact allPairs wA (by decide +kernel : (pairs wA).length = 10) (by decide +kernel) rowsA

set_option maxRecDepth 16000 in
theorem lowerA {k : Nat} (p : Program (stock 5) fA k) : 8 ≤ k :=
  wordLower wA fA (by decide +kernel) (by decide +kernel) (by decide +kernel) rejectA p

end PEqualNP.Outside.L_meta_12351.Small

-- The four-input threshold function needs seven binary gates even with free complements.
namespace PEqualNP.Outside.L_meta_12351.Small

open PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Signed
open PEqualNP.Outside.L_meta_12351

def wK : List W := [0x1ffc00000000003ff800000000007ff00000000000ffe00000000001ffc006eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5bab756eadd5b,0x3e00000000001ffc00000000003ff800000000007ff00000000000ffe000003736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6dcdb9b736e6d,0xffe00000000001ffc00000000003ff800000000007ff000000003bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778ef1de3bc778e,0x7ff00000000000ffe00000000001ffc00000000003ff8000000000043f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0fe1fc3f87f0]

def fK : Signal (Fin 4 → Bool) := atTable 65256

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairK0 : byPair 5 3 wK 0 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairK1 : byPair 5 3 wK 1 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairK2 : byPair 5 3 wK 2 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairK3 : byPair 5 3 wK 3 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairK4 : byPair 5 3 wK 4 = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem pairK5 : byPair 5 3 wK 5 = false := by decide +kernel

theorem rowsK (i : Fin 6) : byPair 5 3 wK i.val = false := by
  fin_cases i
  · exact pairK0
  · exact pairK1
  · exact pairK2
  · exact pairK3
  · exact pairK4
  · exact pairK5

set_option maxRecDepth 16000 in
theorem rejectK : search 6 wK = false := by
  apply onlyStart _ (by decide +kernel)
  exact allPairs wK (by decide +kernel : (pairs wK).length = 6) (by decide +kernel) rowsK

set_option maxRecDepth 16000 in
theorem lowerK {k : Nat} (p : Program (stock 4) fK k) : 7 ≤ k :=
  wordLower wK fK (by decide +kernel) (by decide +kernel) (by decide +kernel) rejectK p

end PEqualNP.Outside.L_meta_12351.Small

-- Fixing a suitable input simplifies the first gate and removes a second binary gate.
namespace PEqualNP.Outside.L_meta_12351.Prune

open PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Small

abbrev X4 := Fin 4 → Bool
abbrev X5 := Fin 5 → Bool
abbrev X6 := Fin 6 → Bool

def target : Signal X6 := atTable (4278124032 * 2 ^ 32 + 4261472256)
def five (b : Bool) : Signal X5 := if b then atTable 0xfefefee8 else atTable 0xfe00e800
def fixedIndex (b : Bool) : Fin 5 := if b then 4 else 3
def remaining (b : Bool) (i : Fin 5) : Fin 4 :=
  (if b then (![0,1,2,3,0] : Fin 5 → Fin 4) else ![0,1,2,0,3]) i
def project (b : Bool) (z : X4) (i : Fin 5) :=
  if i = fixedIndex b then !b else z (remaining b i)
def before (b : Bool) (i : Fin 5) := ((if b then 1 else 3) : Nat).testBit i.val
def after (b : Bool) (i : Fin 5) := decide (i = fixedIndex b) || before b i

theorem identity4 : ∀ b z, five b (project b z) = atTable 0xfee8 z := by decide +kernel
theorem changes4 : ∀ b, five b (before b) ≠ five b (after b) ∧
    five b (project b (fun _ => false)) ≠ five b (project b (fun _ => true)) := by decide +kernel

theorem fiveBound (core : ∀ {k : Nat}, Program (stock 4) (atTable 0xfee8) k → 7 ≤ k)
    (b : Bool) {k : Nat} (p : Program (stock 5) (five b) k) : 8 ≤ k := by
  have mapped : ∀ u ∈ stock 5, Available (stock 4) (pull (project b) u) := by
    rintro _ ⟨i,rfl⟩
    by_cases h : i = fixedIndex b
    · subst i
      rw [show pull (project b) (input (fixedIndex b)) = fixed (!b) by
        funext z; simp [pull,project,input,fixed]]
      exact availConst _ _
    · rw [show pull (project b) (input i) = input (remaining b i) by
        funext z; simp [pull,project,input,h]]
      exact member ⟨_,rfl⟩
  have clean : ∀ u ∈ stock 5, Simple (project b) (before b) (after b) u := by
    rintro _ ⟨i,rfl⟩
    by_cases h : i = fixedIndex b
    · subst i
      exact Or.inr ⟨!b,by funext z; simp [pull,project,input,fixed]⟩
    · exact Or.inl (by simp [input,after,h])
  have bad := notSimple (project b) (five b) (before b) (after b) (fun _ => false)
    (fun _ => true) (changes4 b).1 (changes4 b).2
  obtain ⟨j,hj,pj⟩ := strictRestriction (project b) (before b) (after b) p (stock 4) mapped clean bad
  rw [show pull (project b) (five b) = atTable 0xfee8 from funext (identity4 b)] at pj
  have low := core pj
  omega

def small (v : Fin 6) : Signal X5 := if v.val < 3 then atTable 0xeee0e080 else five (decide (v.val = 3))
def assigned (v : Fin 6) : Bool := decide (v.val = 3)

def lit6 (i : Fin 14) : Signal X6 := ![fixed false, fixed true, input 0, input 1, input 2, input 3, input 4, input 5, inverse (input 0), inverse (input 1), inverse (input 2), inverse (input 3), inverse (input 4), inverse (input 5)] i

def lit5 (i : Fin 12) : Signal X5 := ![fixed false, fixed true, input 0, input 1, input 2, input 3, input 4, inverse (input 0), inverse (input 1), inverse (input 2), inverse (input 3), inverse (input 4)] i

theorem possible {a : Signal X6} (ha : Available (stock 6) a) : ∃ j, a = lit6 j := by
  rcases ha with ⟨b,rfl⟩ | ⟨u, ⟨i,rfl⟩, rfl | rfl⟩
  · cases b
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  · fin_cases i <;> first
      | exact ⟨2,rfl⟩
      | exact ⟨3,rfl⟩
      | exact ⟨4,rfl⟩
      | exact ⟨5,rfl⟩
      | exact ⟨6,rfl⟩
      | exact ⟨7,rfl⟩
  · fin_cases i <;> first
      | exact ⟨8,rfl⟩
      | exact ⟨9,rfl⟩
      | exact ⟨10,rfl⟩
      | exact ⟨11,rfl⟩
      | exact ⟨12,rfl⟩
      | exact ⟨13,rfl⟩

theorem available5 (j : Fin 12) : Available (stock 5) (lit5 j) := by
  fin_cases j <;> first
    | exact availConst _ false
    | exact availConst _ true
    | exact member (s := stock 5) ⟨(0 : Fin 5),rfl⟩
    | exact member (s := stock 5) ⟨(1 : Fin 5),rfl⟩
    | exact member (s := stock 5) ⟨(2 : Fin 5),rfl⟩
    | exact member (s := stock 5) ⟨(3 : Fin 5),rfl⟩
    | exact member (s := stock 5) ⟨(4 : Fin 5),rfl⟩
    | exact availNeg (member (s := stock 5) ⟨(0 : Fin 5),rfl⟩)
    | exact availNeg (member (s := stock 5) ⟨(1 : Fin 5),rfl⟩)
    | exact availNeg (member (s := stock 5) ⟨(2 : Fin 5),rfl⟩)
    | exact availNeg (member (s := stock 5) ⟨(3 : Fin 5),rfl⟩)
    | exact availNeg (member (s := stock 5) ⟨(4 : Fin 5),rfl⟩)

def index5 (v i : Fin 6) : Fin 5 := (![![0, 0, 1, 2, 3, 4], ![0, 0, 1, 2, 3, 4], ![0, 1, 0, 2, 3, 4], ![0, 1, 2, 0, 3, 4], ![0, 1, 2, 3, 0, 4], ![0, 1, 2, 3, 4, 0]] : Fin 6 → Fin 6 → Fin 5) v i

def erase (v : Fin 6) (z : X5) (i : Fin 6) :=
  if i = v then assigned v else z (index5 v i)
def source (p : Fin 64) (i : Fin 6) : Bool := p.val.testBit i.val
def altered (p : Fin 64) (v i : Fin 6) : Bool := decide (i = v) || source p i

def codes : List Nat :=
  [60, 444, 60, 828, 1212, 1596, 1980, 2364, 444, 2748, 3132, 3516, 3900, 4284, 444, 444, 444, 444, 444, 444,
   444, 444, 444, 444, 444, 444, 444, 444, 60, 444, 60, 828, 1224, 1596, 2064, 2544, 444, 2760, 3132, 3744,
   3900, 4284, 828, 444, 828, 828, 1225, 1591, 2065, 2545, 444, 444, 3127, 3745, 3895, 4279, 1212, 444, 1224, 1225,
   1212, 1592, 2066, 2546, 444, 439, 444, 3746, 3896, 4280, 1596, 444, 1596, 1591, 1592, 1596, 405, 405, 444, 439,
   440, 444, 405, 405, 1980, 444, 2064, 2065, 2066, 405, 1980, 2506, 444, 439, 440, 2025, 444, 4282, 2364, 444,
   2544, 2545, 2546, 405, 2506, 2364, 444, 439, 440, 2505, 442, 444, 444, 444, 444, 444, 444, 444, 444, 444,
   444, 444, 444, 444, 444, 444, 2748, 444, 2760, 444, 439, 439, 439, 439, 444, 2748, 439, 439, 439, 439,
   3132, 444, 3132, 3127, 444, 440, 440, 440, 444, 439, 3132, 440, 440, 440, 3516, 444, 3744, 3745, 3746, 444,
   2025, 2505, 444, 439, 440, 3516, 3861, 4245, 3900, 444, 3900, 3895, 3896, 405, 444, 442, 444, 439, 440, 3861,
   3900, 442, 4284, 444, 4284, 4279, 4280, 405, 4282, 444, 444, 439, 440, 4245, 442, 4284, 60, 60, 60, 60,
   60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 444, 60, 828, 1212, 1596, 1980, 2364, 444, 2748,
   3132, 3516, 3900, 4284, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 828,
   60, 828, 55, 55, 55, 55, 840, 60, 55, 55, 55, 55, 60, 1212, 60, 55, 1212, 56, 56, 56,
   1212, 1207, 60, 56, 56, 56, 60, 1596, 60, 55, 56, 1596, 1941, 2325, 1824, 1825, 1826, 60, 3945, 4425,
   60, 1980, 60, 55, 56, 1941, 1980, 58, 1980, 1975, 1976, 21, 60, 58, 60, 2364, 60, 55, 56, 2325,
   58, 2364, 2364, 2359, 2360, 21, 2362, 60, 60, 444, 60, 840, 1212, 1824, 1980, 2364, 444, 2748, 3144, 3516,
   3984, 4464, 60, 2748, 60, 60, 1207, 1825, 1975, 2359, 2748, 2748, 3145, 3511, 3985, 4465, 60, 3132, 60, 55,
   60, 1826, 1976, 2360, 3144, 3145, 3132, 3512, 3986, 4466, 60, 3516, 60, 55, 56, 60, 21, 21, 3516, 3511,
   3512, 3516, 21, 21, 60, 3900, 60, 55, 56, 3945, 60, 2362, 3984, 3985, 3986, 21, 3900, 4426, 60, 4284,
   60, 55, 56, 4425, 58, 60, 4464, 4465, 4466, 21, 4426, 4284]

def code (t : Bool) (a b : Fin 14) := codes.getD ((if t then 196 else 0) + 14*a.val + b.val) 0
def vertex (c : Nat) : Fin 6 := ⟨c%6,Nat.mod_lt _ (by decide)⟩
def pairAt (c : Nat) : Fin 64 := ⟨(c/6)%64,Nat.mod_lt _ (by decide)⟩
def imageLit (c : Nat) : Fin 12 := ⟨(c/384)%12,Nat.mod_lt _ (by decide)⟩

abbrev GateCase (t : Bool) (a b : Fin 14) : Prop :=
  let c := code t a b
  let v := vertex c
  let p := pairAt c
  let j := imageLit c
  let g := combine t (lit6 a) (lit6 b)
  target (source p) ≠ target (altered p v) ∧ (∀ z, g (erase v z) = lit5 j z) ∧
    (g (source p) = g (altered p v) ∨ j = 0 ∨ j = 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_0 : ∀ b, GateCase false 0 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_1 : ∀ b, GateCase false 1 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_2 : ∀ b, GateCase false 2 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_3 : ∀ b, GateCase false 3 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_4 : ∀ b, GateCase false 4 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_5 : ∀ b, GateCase false 5 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_6 : ∀ b, GateCase false 6 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_7 : ∀ b, GateCase false 7 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_8 : ∀ b, GateCase false 8 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_9 : ∀ b, GateCase false 9 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_10 : ∀ b, GateCase false 10 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_11 : ∀ b, GateCase false 11 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_12 : ∀ b, GateCase false 12 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_false_13 : ∀ b, GateCase false 13 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_0 : ∀ b, GateCase true 0 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_1 : ∀ b, GateCase true 1 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_2 : ∀ b, GateCase true 2 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_3 : ∀ b, GateCase true 3 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_4 : ∀ b, GateCase true 4 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_5 : ∀ b, GateCase true 5 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_6 : ∀ b, GateCase true 6 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_7 : ∀ b, GateCase true 7 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_8 : ∀ b, GateCase true 8 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_9 : ∀ b, GateCase true 9 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_10 : ∀ b, GateCase true 10 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_11 : ∀ b, GateCase true 11 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_12 : ∀ b, GateCase true 12 b := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem gate_true_13 : ∀ b, GateCase true 13 b := by decide +kernel

theorem certificate : ∀ t a b, GateCase t a b := by
  intro t a
  cases t
  · fin_cases a
    · exact gate_false_0
    · exact gate_false_1
    · exact gate_false_2
    · exact gate_false_3
    · exact gate_false_4
    · exact gate_false_5
    · exact gate_false_6
    · exact gate_false_7
    · exact gate_false_8
    · exact gate_false_9
    · exact gate_false_10
    · exact gate_false_11
    · exact gate_false_12
    · exact gate_false_13
  · fin_cases a
    · exact gate_true_0
    · exact gate_true_1
    · exact gate_true_2
    · exact gate_true_3
    · exact gate_true_4
    · exact gate_true_5
    · exact gate_true_6
    · exact gate_true_7
    · exact gate_true_8
    · exact gate_true_9
    · exact gate_true_10
    · exact gate_true_11
    · exact gate_true_12
    · exact gate_true_13

theorem identity5 : ∀ (v : Fin 6) z, target (erase v z) = small v z := by decide +kernel
theorem varies : ∀ v, target (erase v (fun _ => false)) ≠ target (erase v (fun _ => true)) := by decide +kernel
theorem notLit : ∀ j, ∃ x, target x ≠ lit6 j x := by decide +kernel

theorem ten (aBound : ∀ {k : Nat}, Program (stock 5) (atTable 0xeee0e080) k → 8 ≤ k)
    (kBound : ∀ {k : Nat}, Program (stock 4) (atTable 0xfee8) k → 7 ≤ k)
    {k : Nat} (h : Program (stock 6) target k) : 10 ≤ k := by
  cases h with
  | done known =>
    obtain ⟨j,eq⟩ := possible known
    obtain ⟨x,hx⟩ := notLit j
    exact False.elim (hx (congrFun eq x))
  | gate t ha hb tail =>
    obtain ⟨a,rfl⟩ := possible ha
    obtain ⟨b,rfl⟩ := possible hb
    let c := code t a b
    let v := vertex c
    let p := pairAt c
    let j := imageLit c
    let g := combine t (lit6 a) (lit6 b)
    obtain ⟨hp,hform,hfirst⟩ := certificate t a b
    have img : pull (erase v) g = lit5 j := funext hform
    have mapped : ∀ u ∈ insert g (stock 6), Available (stock 5) (pull (erase v) u) := by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | ⟨i,rfl⟩
      · rw [img]
        exact available5 j
      · by_cases he : i = v
        · subst i
          rw [show pull (erase v) (input v) = fixed (assigned v) by funext z; simp [pull,erase,input,fixed]]
          exact availConst _ _
        · rw [show pull (erase v) (input i) = input (index5 v i) by funext z; simp [pull,erase,input,he]]
          exact member ⟨_,rfl⟩
    have clean : ∀ u ∈ insert g (stock 6), Simple (erase v) (source p) (altered p v) u := by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | ⟨i,rfl⟩
      · rcases hfirst with eq | eq | eq
        · exact Or.inl eq
        · exact Or.inr ⟨false,img.trans (show lit5 j = fixed false by change j = 0 at eq; rw [eq]; rfl)⟩
        · exact Or.inr ⟨true,img.trans (show lit5 j = fixed true by change j = 1 at eq; rw [eq]; rfl)⟩
      · by_cases he : i = v
        · subst i
          exact Or.inr ⟨assigned v,by funext z; simp [pull,erase,input,fixed]⟩
        · exact Or.inl (by simp [input,altered,he])
    have bad := notSimple (erase v) target (source p) (altered p v) (fun _ => false) (fun _ => true)
      hp (varies v)
    obtain ⟨m,hm,prog⟩ := strictRestriction (erase v) (source p) (altered p v) tail (stock 5) mapped clean bad
    rw [show pull (erase v) target = small v from funext (identity5 v)] at prog
    have h8 : 8 ≤ m := by
      by_cases le : v.val < 3
      · simp only [small,le,if_true] at prog
        exact aBound prog
      · simp only [small,le,if_false] at prog
        exact fiveBound kBound _ prog
    omega

end PEqualNP.Outside.L_meta_12351.Prune

-- With t = x4 OR x5, the target is the conjunction of two conditions. At least two of
-- x0, x1, x2 and t hold, and either x3 holds or both x4 and x5 hold.
namespace PEqualNP.Outside.L_meta_12351.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Small PEqualNP.Outside.L_meta_12351.Prune

def witness : Circuit := ⟨[
  ⟨.or,[4,5]⟩, ⟨.or,[0,1]⟩, ⟨.and,[0,1]⟩, ⟨.or,[2,6]⟩, ⟨.and,[2,6]⟩,
  ⟨.and,[7,9]⟩, ⟨.or,[8,10]⟩, ⟨.or,[11,12]⟩, ⟨.and,[4,5]⟩, ⟨.or,[3,14]⟩,
  ⟨.and,[13,15]⟩],16⟩

theorem monotoneWitness : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem values : ∀ x : X6, witness.eval (List.ofFn x) = target x := by decide +kernel

end PEqualNP.Outside.L_meta_12351.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_12351.Credit PEqualNP.Outside.L_meta_12351.Small PEqualNP.Outside.L_meta_12351.Prune PEqualNP.Outside.L_meta_12351.Main in
theorem PEqualNP.Outside.L_meta_12351 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124032 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124032 * 2 ^ 32 + 4261472256) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨C,legal,sz,computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g,hg,op⟩ := hasNot
    have fits : ∀ u ∈ C.gates, Legal u := by
      intro u hu
      exact ⟨(legal u hu).1,(legal u hu).2⟩
    have work := programOf C.gates C.output target fits computes
    have lower := ten lowerA lowerK work
    have fewer : (C.gates.filter paid).length < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := paid)).mpr ⟨g,hg,by simp [paid,op]⟩
    have sz' : C.gates.length ≤ s := sz
    exact ⟨witness,monotoneWitness,by change 11 ≤ s; omega,values⟩
  · refine ⟨C,?_,sz,computes⟩
    intro g hg
    refine ⟨?_,(legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hasNot ⟨g,hg,h⟩)
