import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_701

-- The live-wire search follows lisn0's L-meta-719 and jackboykin's L-meta-618.
-- A narrow union produces a marked wire. A second step makes its value available.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def build {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {available : Finset α} (h : build ops goal k available) :
    ∃ s ⊆ available, live ops goal k s := by
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

theorem live_card {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {s : Finset α} (h : live ops goal k s) : s.card ≤ k + 1 := by
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

theorem live_separates {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    (D : α → Prop) (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
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

theorem first_live {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : ℕ} {s : Finset α} (h : live ops goal (k + 1) s) :
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

abbrev Word := BitVec 100
abbrev W := Word × Bool

def bit (k : Fin 100) (z : Word) : Bool := z[k.val]

def singletonRow (i : Fin 5) : Fin 100 := ⟨i.val, by omega⟩

def wide (z : Word) : Bool :=
  decide (∃ u v : Fin 5, u ≠ v ∧ bit (singletonRow u) z = true ∧ bit (singletonRow v) z = true)

def ops (a b : W) : List W :=
  if a.2 then
    if b.2 then [(a.1, false), (b.1, false)] else [(a.1, false)]
  else if b.2 then [(b.1, false)]
  else [(a.1 &&& b.1, false), (a.1 ||| b.1, !wide (a.1 ||| b.1))]

def sep (x : W) : BitVec 50 := ((x.1 >>> 50) &&& ~~~x.1).setWidth 50

def cuts (ws : List W) : BitVec 50 := ws.foldr (fun w v => sep w ||| v) 0

def goalWord : Word := (-1 : BitVec 50) ++ (0 : BitVec 50)
def goal : W := (goalWord, false)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List Word :=
  [0x3ff003ffffc812048120481,
   0xffc00ffd224892248922,
   0xfffff002449124491244,
   0xfffff00000000681a0681a068,
   0xffc000000000390e4390e4390]

def inputs : List W := rawInputs.map (fun u => (u, false))

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

abbrev basicOps (a b : W) := (ops a b).toFinset

def differs (i : Fin 50) (w : W) : Prop :=
  w.1.getLsbD (50 + i.val) = true ∧ w.1.getLsbD i.val = false

theorem ops_differs (i : Fin 50) (a b z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  obtain ⟨u, au⟩ := a
  obtain ⟨v, bv⟩ := b
  cases au <;> cases bv <;> simp [basicOps, ops] at hz
  all_goals first | (rcases hz with rfl | rfl) | subst z
  all_goals unfold differs at hd ⊢
  all_goals simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at *
  all_goals first | exact .inl hd | exact .inr hd | revert hd; cases u.getLsbD (50+i.val) <;> cases u.getLsbD i.val <;> cases v.getLsbD (50+i.val) <;> cases v.getLsbD i.val <;> decide

theorem goal_differs : ∀ i : Fin 50, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 50) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 100 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 50)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  obtain ⟨a, x⟩ := a
  obtain ⟨b, y⟩ := b
  cases x <;> cases y <;> ext t <;> simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm, or_comm]

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
    · exact List.nodup_cons.mpr ⟨(fun h => (List.nodup_cons.mp habr).1 (List.mem_cons_of_mem _ h)), (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2⟩
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

private theorem read_bit (w : List Word) (i : ℕ) (k : Fin 100) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List Word) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def isUnion : GateOp → Bool
  | .or => true
  | _ => false

def combine (u : Bool) (a b : Word) : Word :=
  if u then a ||| b else a &&& b

def gateWord (g : Gate) (w : List Word) : Word :=
  match g.inputs with
  | [] => if isUnion g.op then 0 else BitVec.allOnes 100
  | [i] => w.getD i 0
  | i :: j :: _ => combine (isUnion g.op) (w.getD i 0) (w.getD j 0)

def push (w : List Word) (g : Gate) := w ++ [gateWord g w]

def run (gs : List Gate) (w : List Word) := gs.foldl push w

private theorem bit_push (w : List Word) (g : Gate) (h : legal g) (k : Fin 100) :
    (push w g).map (bit k) = step (w.map (bit k)) g := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := h
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨t, rest⟩⟩⟩
  all_goals first | simp at hlen | skip
  all_goals rcases hop with rfl | rfl <;>
    simp only [push, gateWord, step, isUnion, List.map_append, List.map_cons, List.map_nil, read_bit]
  all_goals simp [GateOp.eval, combine, bit, -List.getD_eq_getElem?_getD]
  all_goals decide +revert

private theorem bits_run (gs : List Gate) (w : List Word) (h : ∀ g ∈ gs, legal g) (k : Fin 100) :
    (run gs w).map (bit k) = gs.foldl step (w.map (bit k)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (push w g)).map _ = gs.foldl _ (step _ g)
    rw [ih (push w g) (fun g' hg => h g' (by simp [hg])), bit_push w g (h g (by simp))]

private theorem run_prefix (gs : List Gate) (w : List Word) : ∃ t, run gs w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (push w g)
    exact ⟨gateWord g w :: t, by simpa [run, push] using ht⟩

private theorem head_word (g : Gate) (gs : List Gate) (w : List Word) :
    (run (g :: gs) w).getD w.length 0 = gateWord g w := by
  change (run gs (push w g)).getD _ _ = _
  obtain ⟨t, ht⟩ := run_prefix gs (push w g)
  rw [ht]
  simp [push, List.append_assoc, List.getD_eq_getElem?_getD]

def represents (av : Finset Word) (w : List Word) : Prop :=
  ∀ v ∈ w, v = 0 ∨ v = BitVec.allOnes 100 ∨ v ∈ av

def embedded (av : Finset Word) : Finset W := av.image (fun a => (a, false))

private theorem unary_class {av : Finset Word} {w : List Word} (hr : represents av w) (j : ℕ) :
    w.getD j 0 = 0 ∨ w.getD j 0 = BitVec.allOnes 100 ∨ w.getD j 0 ∈ av := by
  rcases read_wire w j with h | h
  · exact .inl h
  · exact hr _ h

private theorem classify_pair {av : Finset Word} (u : Bool) {a b : Word}
    (ha : a = 0 ∨ a = BitVec.allOnes 100 ∨ a ∈ av)
    (hb : b = 0 ∨ b = BitVec.allOnes 100 ∨ b ∈ av) :
    let z := combine u a b
    (z = 0 ∨ z = BitVec.allOnes 100 ∨ z ∈ av) ∨
      ∃ x ∈ av, ∃ y ∈ av, x ≠ y ∧ z = combine u x y := by
  dsimp only
  by_cases eq : a = b
  · subst b
    left
    cases u <;> simpa [combine] using ha
  rcases ha with rfl | rfl | ha <;> rcases hb with rfl | rfl | hb
  all_goals first | exact .inr ⟨_, ha, _, hb, eq, rfl⟩ | left
  all_goals cases u <;> simp only [combine, Bool.false_eq_true, if_false, if_true, BitVec.allOnes_and, BitVec.and_allOnes, BitVec.allOnes_or, BitVec.or_allOnes, BitVec.zero_and, BitVec.and_zero, BitVec.zero_or, BitVec.or_zero] <;> simp [*]

private theorem classify {av : Finset Word} (g : Gate) (w : List Word) (hr : represents av w) :
    let z := gateWord g w
    (z = 0 ∨ z = BitVec.allOnes 100 ∨ z ∈ av) ∨
      ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ z = combine (isUnion g.op) a b := by
  obtain ⟨op, args⟩ := g
  rcases args with _ | ⟨i, _ | ⟨j, tail⟩⟩
  · cases h : isUnion op <;> simp [gateWord, h]
  · exact .inl (unary_class hr i)
  · exact classify_pair _ (unary_class hr i) (unary_class hr j)

theorem build_more {m n : ℕ} {s : Finset W} (h : m ≤ n) (hb : build basicOps goal m s) :
    build basicOps goal n s := by
  induction h with
  | refl => exact hb
  | step _ ih => exact Or.inl ih

theorem build_enlarge {n : ℕ} {s t : Finset W} (hs : s ⊆ t) (hb : build basicOps goal n s) :
    build basicOps goal n t := by
  induction n generalizing s t with
  | zero => exact hs hb
  | succ n ih =>
    rcases hb with h | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hs h)
    · exact Or.inr ⟨a, hs ha, b, hs hb, hab, z, hz, ih (Finset.insert_subset_insert _ hs) tail⟩

private theorem add_gate {m n : ℕ} {av : Finset Word} {a b : Word}
    (ha : a ∈ av) (hb : b ∈ av) (hab : a ≠ b) (u : Bool)
    (cheap : m + 1 ≤ n) (paid : u = true → wide (combine u a b) = false → m + 2 ≤ n)
    (tail : build basicOps goal m (embedded (insert (combine u a b) av))) :
    build basicOps goal n (embedded av) := by
  have hA : (a, false) ∈ embedded av := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hB : (b, false) ∈ embedded av := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hAB : (a, false) ≠ (b, false) := fun h => hab (congrArg Prod.fst h)
  simp only [embedded, Finset.image_insert] at tail
  cases u with
  | false =>
    apply build_more cheap
    exact Or.inr ⟨_, hA, _, hB, hAB, _, by simp [basicOps, ops, combine], tail⟩
  | true =>
    cases hw : wide (a ||| b) with
    | true =>
      apply build_more cheap
      exact Or.inr ⟨_, hA, _, hB, hAB, _, by simp [basicOps, ops, combine, hw], tail⟩
    | false =>
      apply build_more (paid rfl (by simpa [combine] using hw))
      let p : W := (a ||| b, true)
      refine Or.inr ⟨_, hA, _, hB, hAB, p, by simp [p, basicOps, ops, hw], ?_⟩
      refine Or.inr ⟨p, Finset.mem_insert_self _ _, (a, false), Finset.mem_insert_of_mem hA,
        by simp [p], (a ||| b, false), by simp [p, basicOps, ops], build_enlarge ?_ tail⟩
      apply Finset.insert_subset_insert
      exact Finset.subset_insert _ _

def remaining (S : Finset ℕ) (i : ℕ) := (S.filter (i ≤ ·)).card

private theorem remaining_step (S : Finset ℕ) (i : ℕ) :
    remaining S i = remaining S (i+1) + (if i ∈ S then 1 else 0) := by
  by_cases h : i ∈ S
  · have he : S.filter (i ≤ ·) = insert i (S.filter (i+1 ≤ ·)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      grind
    simp [remaining, he, h]
  · have he : S.filter (i ≤ ·) = S.filter (i+1 ≤ ·) := by
      ext x
      simp only [Finset.mem_filter]
      grind
    simp [remaining, he, h]

def budget (A B D : Finset ℕ) (i : ℕ) := remaining A i + remaining B i + 2 * remaining D i

private theorem compile (gs : List Gate) (w : List Word) (out i : ℕ) (av : Finset Word)
    (A B D : Finset ℕ) (hw : represents av w)
    (he : (run gs w).getD out 0 = goalWord)
    (rules : ∀ j g, gs[j]? = some g →
       ((i+j ∈ A ∨ i+j ∈ B ∨ i+j ∈ D) ∧
         (isUnion g.op = true → i+j ∉ D → wide ((run gs w).getD (w.length+j) 0) = true))) :
    build basicOps goal (budget A B D i) (embedded av) := by
  induction gs generalizing w i av with
  | nil =>
    change w.getD out 0 = goalWord at he
    rcases unary_class hw out with h | h | h
    · exact False.elim ((by decide : goalWord ≠ 0) (he ▸ h))
    · exact False.elim ((by decide : goalWord ≠ BitVec.allOnes 100) (he ▸ h))
    · apply build_more (Nat.zero_le _)
      exact Finset.mem_image.mpr ⟨goalWord, he ▸ h, rfl⟩
  | cons g gs ih =>
    let z := gateWord g w
    have curr := rules 0 g rfl
    simp only [Nat.add_zero, head_word] at curr
    have tailRule (j g') (hj : gs[j]? = some g') := rules (j+1) g' (by simpa using hj)
    have go {av' : Finset Word} (h : represents av' (push w g)) :
        build basicOps goal (budget A B D (i+1)) (embedded av') := by
      apply ih _ _ _ h he
      intro j g' hj
      simpa [run, push, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailRule j g' hj
    have next : budget A B D (i+1) + 1 ≤ budget A B D i := by
      unfold budget
      rw [remaining_step A i, remaining_step B i, remaining_step D i]
      rcases curr.1 with ha | hb | hd <;> simp [*] <;> omega
    have two (ud : isUnion g.op = true) (small : wide z = false) :
        budget A B D (i+1) + 2 ≤ budget A B D i := by
      have hd : i ∈ D := by
        by_contra h
        have := curr.2 ud h
        simp [z, this] at small
      unfold budget
      rw [remaining_step A i, remaining_step B i, remaining_step D i]
      simp [hd]
      omega
    rcases classify g w hw with hz | ⟨a, ha, b, hb, hab, hz⟩
    · apply build_more (by omega : budget A B D (i+1) ≤ budget A B D i)
      apply go
      intro v hv
      rcases List.mem_append.mp hv with old | fresh
      · exact hw _ old
      · exact List.mem_singleton.mp fresh ▸ hz
    · have hr : represents (insert z av) (push w g) := by
        intro v hv
        rcases List.mem_append.mp hv with old | fresh
        · exact (hw _ old).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
        · exact .inr (.inr (List.mem_singleton.mp fresh ▸ Finset.mem_insert_self _ _))
      have h : z = combine (isUnion g.op) a b := hz
      have tail := go hr
      rw [h] at tail two
      exact add_gate ha hb hab _ next two tail


def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)]

def assignment (k : Fin 100) (i : Fin 5) : Bool := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 50) := [1, 0, 10, 30, 43]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      !(b.1.getLsbD (50 + i.val) && !b.1.getLsbD i.val) || b == a))) = true := by decide
  obtain ⟨i, _, hAll⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    obtain ⟨h1, h2⟩ := hd
    simpa [h1, h2] using hrow
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 100) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows : ∀ k : Fin 100, (∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧
    assignment k u = true ∧ assignment k v = true) ↔ bit k goalWord = true := by
  decide +kernel

theorem input_live (k : ℕ) (hb : build basicOps goal k inputs.toFinset) :
    live basicOps goal k inputs.toFinset := by
  obtain ⟨S, hsub, hLive⟩ := compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : live basicOps goal m inputs.toFinset) :
    live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

-- A frontier contains the wire sets that still distinguish every test pair.
-- The certificate supplies the index of each surviving successor in the next frontier.
private def successors (k : ℕ) (ws : List W) : List (List W) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z ∈ a :: b :: r then [] else
        ((keepChoices a b r).filter fun kept =>
          decide (kept.length ≤ k) && cuts (z :: kept) == -1).map (z :: ·)

private theorem next_live {k : ℕ} {ws : List W} (hn : ws.Nodup)
    (h : live basicOps goal (k+1) ws.toFinset) (notDone : ws ≠ [goal]) :
    ∃ next ∈ successors k ws, next.Nodup ∧ live basicOps goal k next.toFinset := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact False.elim (notDone (singleton_list hn done))
  obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : W} (perm : ws.Perm (a :: b :: r))
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
      (hin : (a,b,r) ∈ pairs ws) :
      ∃ next ∈ successors k ws, next.Nodup ∧ live basicOps goal k next.toFinset := by
    obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
    have fresh : z ∉ a :: b :: r := fun hh => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hh))
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hl : live basicOps goal k (z :: kept).toFinset := by simpa only [List.toFinset_cons,hfin] using tail
    have cap := live_card hl
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at cap
    refine ⟨z :: kept, List.mem_flatMap.mpr ⟨(a,b,r), hin,
      List.mem_flatMap.mpr ⟨z, List.mem_toFinset.mp hop, ?_⟩⟩, hnd, hl⟩
    simp only [if_neg fresh, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨kept, ⟨hk, by omega, cuts_full hl⟩, rfl⟩
  rcases hm with h | h
  · exact go hp hs hz h
  · exact go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz) h

private def impossible (k : ℕ) (ws : List W) : Prop :=
  ws.Nodup → ¬live basicOps goal k ws.toFinset

private theorem empty_impossible (k : ℕ) : impossible k [] := by
  intro _ h
  obtain ⟨_, hx, _⟩ := live_separates (differs 0) (goal_differs 0) (ops_differs 0) h
  simpa using hx

private def refs (below : ℕ → List W) : List (List W) → List ℕ → Bool
  | [], ids => ids.isEmpty
  | _ :: _, [] => false
  | s :: ss, i :: ids => s.isPerm (below i) && refs below ss ids

private theorem refs_sound {k : ℕ} (below : ℕ → List W) (ok : ∀ i, impossible k (below i))
    (ss : List (List W)) (ids : List ℕ) (h : refs below ss ids = true) :
    ∀ s ∈ ss, impossible k s := by
  induction ss generalizing ids with
  | nil => simp
  | cons t ts ih =>
    cases ids with
    | nil => contradiction
    | cons i ids =>
      simp only [refs, Bool.and_eq_true] at h
      have hp := List.isPerm_iff.mp h.1
      intro s hs hn hh
      rcases List.mem_cons.mp hs with rfl | hs
      · have eq : s.toFinset = (below i).toFinset := by ext x; simp [hp.mem_iff]
        exact ok i (hp.nodup_iff.mp hn) (eq ▸ hh)
      · exact ih ids h.2 s hs hn hh

private abbrev Row := List ℕ × List ℕ

private def decode (alphabet : Array W) (row : Row) := row.1.map (fun i => alphabet[i]?.getD (0,false))

private def rowOK (alphabet : Array W) (below : ℕ → List W) (k : ℕ) (row : Row) : Bool :=
  let ws := decode alphabet row
  (ws != [goal]) && refs below (successors k ws) row.2

private def pick {k : ℕ} (alphabet : Array W) (below : ℕ → {s : List W // impossible k s})
    (batch : {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (below i).1) k) = true})
    (idx : ℕ) : {s : List W // impossible (k+1) s} :=
  ⟨decode alphabet (batch.1[idx]?.getD ([],[])), by
    cases hx : batch.1[idx]? with
    | none => simpa [hx, decode] using empty_impossible (k+1)
    | some row =>
      simp only [hx, Option.getD_some]
      have mem : row ∈ batch.1.toList := by simpa using Array.mem_of_getElem? hx
      have hc := List.all_eq_true.mp batch.2 row mem
      simp only [rowOK, Bool.and_eq_true, bne_iff_ne] at hc
      intro hn h
      obtain ⟨t, hm, ht, hl⟩ := next_live hn h hc.1
      exact refs_sound _ (fun i => (below i).2) _ row.2 hc.2 t hm ht hl⟩


-- Packed test results for the wires occurring in the certificate.
private def alphabet : Array W := #[
  (0x0,false),
  (0x200802008020,false),
  (0x401004010040,false),
  (0x601806018060,false),
  (0x802008020080,false),
  (0x1004010040100,false),
  (0x1204812048120,false),
  (0x1806018060180,false),
  (0x2008020080200,false),
  (0x2409024090240,false),
  (0x280a0280a0280,false),
  (0x300c0300c0300,false),
  (0x360d8360d8360,false),
  (0x380e0380e0380,false),
  (0xffc000000000000,false),
  (0xffc200802008020,false),
  (0xffc802008020080,false),
  (0xffd004010040100,false),
  (0xffd204812048120,false),
  (0x3ff000000000000000,false),
  (0x3ff000401004010040,false),
  (0x3ff000802008020080,false),
  (0x3ff002008020080200,false),
  (0x3ff002409024090240,false),
  (0x3ffffc000000000000,false),
  (0x3ffffc601806018060,false),
  (0x3ffffc802008020080,false),
  (0x3fffff00c0300c0300,false),
  (0xffc00000000000000000,false),
  (0xffc00000200802008020,false),
  (0xffc00000401004010040,false),
  (0xffc00001004010040100,false),
  (0xffc00001204812048120,false),
  (0xffc00002008020080200,false),
  (0xffc00002409024090240,false),
  (0xffc00ffc000000000000,false),
  (0xffc00ffc200802008020,false),
  (0xffc00ffd004010040100,false),
  (0xffc00ffd204812048120,false),
  (0xffc00ffd224892248922,false),
  (0xffc00ffd625896258962,false),
  (0xffc00ffda2689a2689a2,false),
  (0xffc00ffe80a0280a0280,false),
  (0xffc00fff22c8b22c8b22,false),
  (0xfffff000000000000000,false),
  (0xfffff000401004010040,false),
  (0xfffff001806018060180,false),
  (0xfffff002008020080200,false),
  (0xfffff002409024090240,false),
  (0xfffff002449124491244,false),
  (0xfffff002649926499264,false),
  (0xfffff002c4b12c4b12c4,false),
  (0xfffff00344d1344d1344,false),
  (0xfffffffc000000000000,false),
  (0xfffffffd224892248922,false),
  (0xfffffffe449124491244,false),
  (0xffffffff66d9b66d9b66,false),
  (0xffffffffe6f9be6f9be6,false),
  (0x3ff00000000000000000000,false),
  (0x3ff00000000200802008020,false),
  (0x3ff00000000401004010040,false),
  (0x3ff00000000601806018060,false),
  (0x3ff00000000802008020080,false),
  (0x3ff00000001a0681a0681a0,false),
  (0x3ff00000002c0b02c0b02c0,false),
  (0x3ff00000ffc000000000000,false),
  (0x3ff00000ffc802008020080,false),
  (0x3ff003ff000000000000000,false),
  (0x3ff003ff000802008020080,false),
  (0x3ff003ffffc000000000000,false),
  (0x3ff003ffffc802008020080,false),
  (0x3ff003ffffc812048120481,false),
  (0x3ff003ffffca1284a1284a1,false),
  (0x3ff003ffffcc1304c1304c1,false),
  (0x3ff003ffffd816058160581,false),
  (0x3ff003ffffe81a0681a0681,false),
  (0x3ffffc00ffc401004010040,false),
  (0x3ffffc00ffd224892248922,false),
  (0x3fffffff000200802008020,false),
  (0x3fffffff002449124491244,false),
  (0x3fffffffffc000000000000,false),
  (0x3fffffffffc812048120481,false),
  (0x3fffffffffd224892248922,false),
  (0x3fffffffffda368da368da3,false),
  (0x3fffffffffde378de378de3,false),
  (0x3fffffffffe449124491244,false),
  (0x3fffffffffec5b16c5b16c5,false),
  (0x3fffffffffee5b96e5b96e5,false),
  (0x3ffffffffff66d9b66d9b66,false),
  (0x3ffffffffffa3e8fa3e8fa3,false),
  (0x3ffffffffffc5f17c5f17c5,false),
  (0x3ffffffffffe7f9fe7f9fe7,false),
  (0xffc0000000000000000000000,false),
  (0xffc0000000000200802008020,false),
  (0xffc0000000000401004010040,false),
  (0xffc0000000000601806018060,false),
  (0xffc0000000000802008020080,false),
  (0xffc0000000001004010040100,false),
  (0xffc0000000001806018060180,false),
  (0xffc0000000002008020080200,false),
  (0xffc000000000280a0280a0280,false),
  (0xffc000000000300c0300c0300,false),
  (0xffc000000000380e0380e0380,false),
  (0xffc000000000390e4390e4390,false),
  (0xffc0000000003b0ec3b0ec3b0,false),
  (0xffc0000000003d0f43d0f43d0,false),
  (0xffc0000000ffc000000000000,false),
  (0xffc0000000ffca0280a0280a0,false),
  (0xffc0000000fff90e4390e4390,false),
  (0xffc00003ff000000000000000,false),
  (0xffc00003ff000c0300c0300c0,false),
  (0xffc00003ff00390e4390e4390,false),
  (0xffc00003fffff90e4390e4390,false),
  (0xffc00ffc00000000000000000,false),
  (0xffc00ffc00001405014050140,false),
  (0xffc00ffc00002208822088220,false),
  (0xffc00ffc0000390e4390e4390,false),
  (0xffc00ffc00ffc000000000000,false),
  (0xffc00ffc00ffd224892248922,false),
  (0xffc00ffc00fff90e4390e4390,false),
  (0xffc00ffc00fffb2ecbb2ecbb2,false),
  (0xffc00ffc00ffff2fcbf2fcbf2,false),
  (0xffc00fffff000000000000000,false),
  (0xffc00fffff002449124491244,false),
  (0xffc00fffff00390e4390e4390,false),
  (0xffc00fffff003d4f53d4f53d4,false),
  (0xffc00fffff003f4fd3f4fd3f4,false),
  (0xffc00ffffffff66d9b66d9b66,false),
  (0xffc00ffffffffb2ecbb2ecbb2,false),
  (0xffc00ffffffffd4f53d4f53d4,false),
  (0xffc00fffffffff6fdbf6fdbf6,false),
  (0xfffff00000000000000000000,false),
  (0xfffff00000000200802008020,false),
  (0xfffff00000000401004010040,false),
  (0xfffff00000000601806018060,false),
  (0xfffff00000000681a0681a068,false),
  (0xfffff00000000e83a0e83a0e8,false),
  (0xfffff00000001685a1685a168,false),
  (0xfffff00000002689a2689a268,false),
  (0xfffff0000000390e4390e4390,false),
  (0xfffff00000003f8fe3f8fe3f8,false),
  (0xfffff00000ffc000000000000,false),
  (0xfffff00000ffc681a0681a068,false),
  (0xfffff00000ffd004010040100,false),
  (0xfffff00000fff90e4390e4390,false),
  (0xfffff00000ffff8fe3f8fe3f8,false),
  (0xfffff003ff000000000000000,false),
  (0xfffff003ff000681a0681a068,false),
  (0xfffff003ff002008020080200,false),
  (0xfffff003ff00390e4390e4390,false),
  (0xfffff003ff003f8fe3f8fe3f8,false),
  (0xfffff003ffffc000000000000,false),
  (0xfffff003ffffc681a0681a068,false),
  (0xfffff003ffffc812048120481,false),
  (0xfffff003ffffca1284a1284a1,false),
  (0xfffff003ffffcc1304c1304c1,false),
  (0xfffff003ffffce93a4e93a4e9,false),
  (0xfffff003ffffd816058160581,false),
  (0xfffff003ffffde97a5e97a5e9,false),
  (0xfffff003ffffe81a0681a0681,false),
  (0xfffff003ffffee9ba6e9ba6e9,false),
  (0xfffff003fffff00c0300c0300,false),
  (0xfffff003fffff91e4791e4791,false),
  (0xfffff003fffffb1ec7b1ec7b1,false),
  (0xfffff003fffffd1f47d1f47d1,false),
  (0xfffff003ffffff9fe7f9fe7f9,false),
  (0xfffffffc00000000000000000,false),
  (0xfffffffc00000681a0681a068,false),
  (0xfffffffc00003f8fe3f8fe3f8,false),
  (0xfffffffc00ffc000000000000,false),
  (0xfffffffc00ffc681a0681a068,false),
  (0xfffffffc00ffd004010040100,false),
  (0xfffffffc00ffd224892248922,false),
  (0xfffffffc00ffd6a5a96a5a96a,false),
  (0xfffffffc00ffdea7a9ea7a9ea,false),
  (0xfffffffc00fff6adab6adab6a,false),
  (0xfffffffc00fffb2ecbb2ecbb2,false),
  (0xfffffffc00ffffafebfafebfa,false),
  (0xffffffffff000000000000000,false),
  (0xffffffffff000681a0681a068,false),
  (0xffffffffff002008020080200,false),
  (0xffffffffff002449124491244,false),
  (0xffffffffff0026c9b26c9b26c,false),
  (0xffffffffff002ecbb2ecbb2ec,false),
  (0xffffffffff0036cdb36cdb36c,false),
  (0xffffffffff003d4f53d4f53d4,false),
  (0xffffffffff003fcff3fcff3fc,false),
  (0xffffffffffffce93a4e93a4e9,false),
  (0xffffffffffffd6a5a96a5a96a,false),
  (0xffffffffffffda368da368da3,false),
  (0xffffffffffffdeb7adeb7adeb,false),
  (0xffffffffffffe6c9b26c9b26c,false),
  (0xffffffffffffec5b16c5b16c5,false),
  (0xffffffffffffeedbb6edbb6ed,false),
  (0xfffffffffffff66d9b66d9b66,false),
  (0xfffffffffffff6edbb6edbb6e,false),
  (0xfffffffffffff91e4791e4791,false),
  (0xfffffffffffffb3ecfb3ecfb3,false),
  (0xfffffffffffffd5f57d5f57d5,false),
  (0xfffffffffffffeffbfeffbfef,false),
  (0xffffffffffffff7fdff7fdff7,false),
  (0xffffffffffffffbfeffbfeffb,false),
  (0xffffffffffffffdff7fdff7fd,false),
  (0xffffffffffffffeffbfeffbfe,false),
  (0x200802008020,true),
  (0x401004010040,true),
  (0x601806018060,true),
  (0x802008020080,true),
  (0xa0280a0280a0,true),
  (0xc0300c0300c0,true),
  (0x1004010040100,true),
  (0x1204812048120,true),
  (0x1405014050140,true),
  (0x1806018060180,true),
  (0x2008020080200,true),
  (0x2208822088220,true),
  (0x2409024090240,true),
  (0x280a0280a0280,true),
  (0x300c0300c0300,true),
  (0xffc000000000000,true),
  (0xffc200802008020,true),
  (0xffc401004010040,true),
  (0xffc802008020080,true),
  (0xffd004010040100,true),
  (0xffe008020080200,true),
  (0x3ff000000000000000,true),
  (0x3ff000200802008020,true),
  (0x3ff000401004010040,true),
  (0x3ff000802008020080,true),
  (0x3ff001004010040100,true),
  (0x3ff002008020080200,true),
  (0x3ffffc000000000000,true),
  (0xffc00000000000000000,true),
  (0xffc00000200802008020,true),
  (0xffc00000401004010040,true),
  (0xffc00000802008020080,true),
  (0xffc00001004010040100,true),
  (0xffc00002008020080200,true),
  (0xffc00ffc000000000000,true),
  (0xffc00ffc200802008020,true),
  (0xffc00ffd004010040100,true),
  (0xffc00ffd224892248922,true),
  (0xffc00ffd625896258962,true),
  (0xffc00ffda2689a2689a2,true),
  (0xffc00fff22c8b22c8b22,true),
  (0xffc00fff62d8b62d8b62,true),
  (0xffc00fffa2e8ba2e8ba2,true),
  (0xfffff000000000000000,true),
  (0xfffff000401004010040,true),
  (0xfffff002008020080200,true),
  (0xfffff002449124491244,true),
  (0xfffff002649926499264,true),
  (0xfffff002c4b12c4b12c4,true),
  (0xfffff00344d1344d1344,true),
  (0xfffff00364d9364d9364,true),
  (0xfffff003c4f13c4f13c4,true),
  (0xfffffffc000000000000,true),
  (0xfffffffd224892248922,true),
  (0xfffffffd625896258962,true),
  (0xfffffffda2689a2689a2,true),
  (0xfffffffe449124491244,true),
  (0xfffffffe649926499264,true),
  (0xfffffffec4b12c4b12c4,true),
  (0xffffffff22c8b22c8b22,true),
  (0xffffffff44d1344d1344,true),
  (0x3ff00000000000000000000,true),
  (0x3ff00000000200802008020,true),
  (0x3ff00000000401004010040,true),
  (0x3ff00000000802008020080,true),
  (0x3ff00000001004010040100,true),
  (0x3ff00000002008020080200,true),
  (0x3ff00000ffc000000000000,true),
  (0x3ff003ff000000000000000,true),
  (0x3ff003ffffc000000000000,true),
  (0x3ff003ffffc812048120481,true),
  (0x3ff003ffffca1284a1284a1,true),
  (0x3ff003ffffcc1304c1304c1,true),
  (0x3ff003ffffce1384e1384e1,true),
  (0x3ff003ffffd816058160581,true),
  (0x3ff003ffffda1685a1685a1,true),
  (0x3ff003ffffe81a0681a0681,true),
  (0x3ff003ffffec1b06c1b06c1,true),
  (0x3ff003fffff81e0781e0781,true),
  (0x3ffffc00000000000000000,true),
  (0x3ffffc00ffc000000000000,true),
  (0x3ffffc00ffd224892248922,true),
  (0x3ffffc00ffd625896258962,true),
  (0x3ffffc00ffda2689a2689a2,true),
  (0x3fffffff000000000000000,true),
  (0x3fffffff002449124491244,true),
  (0x3fffffff002649926499264,true),
  (0x3fffffff002c4b12c4b12c4,true),
  (0x3fffffffffc000000000000,true),
  (0x3fffffffffc812048120481,true),
  (0x3fffffffffca1284a1284a1,true),
  (0x3fffffffffcc1304c1304c1,true),
  (0x3fffffffffd224892248922,true),
  (0x3fffffffffd816058160581,true),
  (0x3fffffffffe449124491244,true),
  (0x3fffffffffe81a0681a0681,true),
  (0xffc0000000000000000000000,true),
  (0xffc0000000000200802008020,true),
  (0xffc0000000000401004010040,true),
  (0xffc0000000000802008020080,true),
  (0xffc0000000001004010040100,true),
  (0xffc0000000001806018060180,true),
  (0xffc0000000002008020080200,true),
  (0xffc000000000280a0280a0280,true),
  (0xffc000000000300c0300c0300,true),
  (0xffc000000000390e4390e4390,true),
  (0xffc0000000003b0ec3b0ec3b0,true),
  (0xffc0000000003d0f43d0f43d0,true),
  (0xffc0000000003f0fc3f0fc3f0,true),
  (0xffc0000000ffc000000000000,true),
  (0xffc0000000ffc802008020080,true),
  (0xffc0000000ffd004010040100,true),
  (0xffc0000000ffe008020080200,true),
  (0xffc0000000fff90e4390e4390,true),
  (0xffc0000000fffb0ec3b0ec3b0,true),
  (0xffc00003ff000000000000000,true),
  (0xffc00003ff000802008020080,true),
  (0xffc00003ff001004010040100,true),
  (0xffc00003ff002008020080200,true),
  (0xffc00003ff00390e4390e4390,true),
  (0xffc00003ff003d0f43d0f43d0,true),
  (0xffc00003ffffc000000000000,true),
  (0xffc00003fffff90e4390e4390,true),
  (0xffc00ffc00000000000000000,true),
  (0xffc00ffc00000802008020080,true),
  (0xffc00ffc00001004010040100,true),
  (0xffc00ffc00002008020080200,true),
  (0xffc00ffc0000390e4390e4390,true),
  (0xffc00ffc00003b0ec3b0ec3b0,true),
  (0xffc00ffc00003d0f43d0f43d0,true),
  (0xffc00ffc00ffc000000000000,true),
  (0xffc00ffc00ffd004010040100,true),
  (0xffc00ffc00ffd224892248922,true),
  (0xffc00ffc00ffd625896258962,true),
  (0xffc00ffc00ffda2689a2689a2,true),
  (0xffc00ffc00fff22c8b22c8b22,true),
  (0xffc00ffc00fff90e4390e4390,true),
  (0xffc00fffff000000000000000,true),
  (0xffc00fffff002008020080200,true),
  (0xffc00fffff002449124491244,true),
  (0xffc00fffff002649926499264,true),
  (0xffc00fffff002c4b12c4b12c4,true),
  (0xffc00fffff00344d1344d1344,true),
  (0xffc00fffff00390e4390e4390,true),
  (0xfffff00000000000000000000,true),
  (0xfffff00000000200802008020,true),
  (0xfffff00000000401004010040,true),
  (0xfffff00000000681a0681a068,true),
  (0xfffff00000000802008020080,true),
  (0xfffff00000000e83a0e83a0e8,true),
  (0xfffff00000001004010040100,true),
  (0xfffff00000001685a1685a168,true),
  (0xfffff00000001e87a1e87a1e8,true),
  (0xfffff00000002008020080200,true),
  (0xfffff00000002689a2689a268,true),
  (0xfffff00000002e8ba2e8ba2e8,true),
  (0xfffff0000000368da368da368,true),
  (0xfffff0000000390e4390e4390,true),
  (0xfffff00000003b0ec3b0ec3b0,true),
  (0xfffff00000003d0f43d0f43d0,true),
  (0xfffff00000ffc000000000000,true),
  (0xfffff00000ffc681a0681a068,true),
  (0xfffff00000ffce83a0e83a0e8,true),
  (0xfffff00000ffd004010040100,true),
  (0xfffff00000ffd685a1685a168,true),
  (0xfffff00000fff90e4390e4390,true),
  (0xfffff003ff000000000000000,true),
  (0xfffff003ff000681a0681a068,true),
  (0xfffff003ff000e83a0e83a0e8,true),
  (0xfffff003ff002008020080200,true),
  (0xfffff003ff002689a2689a268,true),
  (0xfffff003ff00390e4390e4390,true),
  (0xfffff003ffffc000000000000,true),
  (0xfffff003ffffc681a0681a068,true),
  (0xfffff003ffffc812048120481,true),
  (0xfffff003ffffca1284a1284a1,true),
  (0xfffff003ffffcc1304c1304c1,true),
  (0xfffff003ffffd816058160581,true),
  (0xfffff003ffffe81a0681a0681,true),
  (0xfffff003fffff81e0781e0781,true),
  (0xfffff003fffff90e4390e4390,true),
  (0xfffffffc00000000000000000,true),
  (0xfffffffc00000681a0681a068,true),
  (0xfffffffc00001685a1685a168,true),
  (0xfffffffc00002689a2689a268,true),
  (0xfffffffc00ffc000000000000,true),
  (0xfffffffc00ffc681a0681a068,true),
  (0xfffffffc00ffd004010040100,true),
  (0xfffffffc00ffd224892248922,true),
  (0xffffffffff000000000000000,true),
  (0xffffffffff000681a0681a068,true),
  (0xffffffffff002008020080200,true),
  (0xffffffffff002449124491244,true),
  (0xffffffffffffc000000000000,true),
  (0xffffffffffffc681a0681a068,true),
  (0xffffffffffffc812048120481,true),
  (0xffffffffffffd224892248922,true),
  (0xffffffffffffe449124491244,true)]

-- The base frontier lists all wires left after eight steps.
private def layer0 (i : ℕ) : {s : List W // impossible 0 s} :=
  if i = 0 then ⟨[(0xffffffffffffc000000000000,true)], by intro _ h; simp [live, goal] at h⟩
  else ⟨[], empty_impossible 0⟩

private def f1b0 : Array Row := #[
  ([14,178],[0]),
  ([14,393],[]),
  ([19,169],[0]),
  ([19,389],[]),
  ([24,166],[0]),
  ([24,385],[]),
  ([24,389],[]),
  ([24,393],[]),
  ([28,151],[0]),
  ([28,376],[]),
  ([35,146],[0]),
  ([35,370],[]),
  ([35,376],[]),
  ([35,393],[]),
  ([44,141],[0]),
  ([44,364],[]),
  ([44,376],[]),
  ([44,389],[]),
  ([53,131],[0]),
  ([65,122],[0]),
  ([65,341],[]),
  ([65,393],[]),
  ([67,117],[0]),
  ([67,334],[]),
  ([67,389],[]),
  ([69,113],[0]),
  ([69,327],[]),
  ([69,334],[]),
  ([69,341],[]),
  ([69,385],[]),
  ([80,92],[0]),
  ([92,292],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f1b0ok : f1b0.toList.all (rowOK alphabet (fun i => (layer0 i).1) 0) = true := by decide +kernel

private def f1b1 : Array Row := #[
  ([131,256],[]),
  ([131,292],[]),
  ([189,401],[]),
  ([192,400],[]),
  ([195,399],[]),
  ([196,398],[]),
  ([231,385],[]),
  ([238,370],[]),
  ([247,364],[]),
  ([256,348],[]),
  ([256,364],[]),
  ([256,370],[]),
  ([256,376],[]),
  ([256,385],[]),
  ([256,389],[]),
  ([256,393],[]),
  ([271,341],[]),
  ([272,334],[]),
  ([273,327],[]),
  ([283,325],[]),
  ([284,319],[]),
  ([288,313],[]),
  ([292,327],[]),
  ([292,334],[]),
  ([292,341],[]),
  ([292,364],[]),
  ([292,370],[]),
  ([292,376],[]),
  ([327,376],[]),
  ([334,370],[]),
  ([341,364],[]),
  ([364,393],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f1b1ok : f1b1.toList.all (rowOK alphabet (fun i => (layer0 i).1) 0) = true := by decide +kernel

private def f1b2 : Array Row := #[
  ([370,389],[]),
  ([376,385],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f1b2ok : f1b2.toList.all (rowOK alphabet (fun i => (layer0 i).1) 0) = true := by decide +kernel

private def layer1 (i : ℕ) : {s : List W // impossible 1 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer0 i).1) 0) = true} :=
    #[⟨f1b0, f1b0ok⟩, ⟨f1b1, f1b1ok⟩, ⟨f1b2, f1b2ok⟩]
  pick alphabet layer0 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f2b0 : Array Row := #[
  ([14,19,385],[38]),
  ([14,28,370],[39]),
  ([14,39,393],[0]),
  ([14,44,131],[32,15,1]),
  ([14,44,348],[41]),
  ([14,44,364],[42,14]),
  ([14,44,393],[47,0]),
  ([14,49,393],[0]),
  ([14,58,341],[48]),
  ([14,67,327],[50]),
  ([14,71,393],[0]),
  ([14,83,393],[0]),
  ([14,92,288],[53]),
  ([14,103,393],[0]),
  ([14,131,247],[40]),
  ([14,131,256],[42,18]),
  ([14,131,393],[63,0]),
  ([14,135,393],[0]),
  ([14,162,393],[0]),
  ([14,189,396],[]),
  ([14,196,394],[]),
  ([14,393],[0]),
  ([17,71,393],[1]),
  ([19,28,364],[40]),
  ([19,35,131],[32,11,3]),
  ([19,35,348],[41]),
  ([19,35,370],[43,10]),
  ([19,35,389],[46,2]),
  ([19,39,389],[2]),
  ([19,49,389],[2]),
  ([19,58,334],[49]),
  ([19,65,327],[50])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b0ok : f2b0.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b1 : Array Row := #[
  ([19,71,389],[2]),
  ([19,86,389],[2]),
  ([19,92,284],[52]),
  ([19,103,389],[2]),
  ([19,131,238],[39]),
  ([19,131,256],[43,18]),
  ([19,131,389],[64,2]),
  ([19,135,389],[2]),
  ([19,162,389],[2]),
  ([19,192,392],[]),
  ([19,196,390],[]),
  ([19,389],[2]),
  ([22,71,389],[3]),
  ([24,28,131],[32,9,5]),
  ([24,28,348],[41]),
  ([24,28,376],[44,8]),
  ([24,28,385],[45,4]),
  ([24,35,131],[32,12,6]),
  ([24,39,385],[4]),
  ([24,44,131],[32,16,7]),
  ([24,49,385],[4]),
  ([24,56,385],[4]),
  ([24,58,327],[50]),
  ([24,71,385],[4]),
  ([24,92,283],[51]),
  ([24,103,385],[4]),
  ([24,131,256],[44,18]),
  ([24,131,385],[65,4]),
  ([24,135,385],[4]),
  ([24,162,385],[4]),
  ([24,196,386],[]),
  ([24,385],[4])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b1ok : f2b1.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b2 : Array Row := #[
  ([24,392,396],[]),
  ([27,71,385],[5]),
  ([28,39,376],[8]),
  ([28,49,376],[8]),
  ([28,56,376],[8]),
  ([28,58,325],[51]),
  ([28,65,319],[52]),
  ([28,67,313],[53]),
  ([28,69,92],[31,26,9]),
  ([28,69,131],[33,29,9]),
  ([28,69,327],[54,25]),
  ([28,69,376],[59,8]),
  ([28,71,376],[8]),
  ([28,92,273],[50]),
  ([28,92,292],[54,30]),
  ([28,92,376],[60,8]),
  ([28,103,376],[8]),
  ([28,131,231],[38]),
  ([28,131,256],[45,18]),
  ([28,131,376],[65,8]),
  ([28,135,376],[8]),
  ([28,152,162],[8]),
  ([28,153,195],[36,8]),
  ([28,156,161],[8]),
  ([28,162,376],[8]),
  ([28,162,377],[]),
  ([28,173,376],[8]),
  ([28,182,376],[8]),
  ([28,188,378],[]),
  ([28,191,378],[]),
  ([28,194,378],[]),
  ([28,195,376],[8])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b2ok : f2b2.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b3 : Array Row := #[
  ([28,195,378],[]),
  ([28,196,377],[]),
  ([28,376],[8]),
  ([28,377,378],[]),
  ([28,377,384],[]),
  ([29,49,376],[9]),
  ([30,39,376],[9]),
  ([35,39,370],[10]),
  ([35,44,131],[32,17,13]),
  ([35,49,370],[10]),
  ([35,58,319],[52]),
  ([35,67,92],[31,23,11]),
  ([35,67,131],[33,24,11]),
  ([35,67,334],[55,22]),
  ([35,67,370],[58,10]),
  ([35,69,92],[31,27,12]),
  ([35,71,370],[10]),
  ([35,86,370],[10]),
  ([35,92,272],[49]),
  ([35,92,292],[55,30]),
  ([35,92,370],[61,10]),
  ([35,103,370],[10]),
  ([35,131,256],[46,18]),
  ([35,131,370],[64,10]),
  ([35,135,370],[10]),
  ([35,147,162],[10]),
  ([35,148,156],[10]),
  ([35,153,182],[10]),
  ([35,162,370],[10]),
  ([35,162,371],[]),
  ([35,162,377],[]),
  ([35,162,394],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b3ok : f2b3.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b4 : Array Row := #[
  ([35,182,370],[10]),
  ([35,182,378],[]),
  ([35,182,381],[]),
  ([35,191,378],[]),
  ([35,195,378],[]),
  ([35,196,371],[]),
  ([35,370],[10]),
  ([35,371,375],[]),
  ([35,371,378],[]),
  ([35,378,396],[]),
  ([37,153,182],[]),
  ([37,182,378],[]),
  ([37,378,396],[]),
  ([39,44,364],[14]),
  ([39,49,151],[8]),
  ([39,49,376],[9]),
  ([39,65,341],[19]),
  ([39,67,334],[22]),
  ([39,69,327],[25]),
  ([39,71,178],[0]),
  ([39,71,393],[1]),
  ([39,86,146],[10]),
  ([39,86,370],[11]),
  ([39,86,376],[12]),
  ([39,86,393],[13]),
  ([39,92,292],[30]),
  ([39,131,256],[18]),
  ([39,146,192],[35,10]),
  ([39,153,181],[]),
  ([39,153,396],[]),
  ([39,153,401],[34]),
  ([39,181,378],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b4ok : f2b4.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b5 : Array Row := #[
  ([39,182,399],[36]),
  ([39,192,370],[11]),
  ([39,260,370],[]),
  ([39,260,376],[]),
  ([39,293,370],[]),
  ([39,293,393],[]),
  ([39,298,376],[]),
  ([39,343,376],[]),
  ([39,376,396],[]),
  ([39,378,393],[]),
  ([39,378,395],[]),
  ([39,378,396],[]),
  ([39,378,401],[]),
  ([44,49,364],[14]),
  ([44,58,313],[53]),
  ([44,65,92],[31,20,15]),
  ([44,65,131],[33,21,15]),
  ([44,65,341],[56,19]),
  ([44,65,364],[57,14]),
  ([44,69,92],[31,28,16]),
  ([44,71,364],[14]),
  ([44,83,364],[14]),
  ([44,92,271],[48]),
  ([44,92,292],[56,30]),
  ([44,92,364],[62,14]),
  ([44,103,364],[14]),
  ([44,131,256],[47,18]),
  ([44,131,364],[63,14]),
  ([44,135,364],[14]),
  ([44,142,162],[14]),
  ([44,143,156],[14]),
  ([44,153,173],[14])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b5ok : f2b5.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b6 : Array Row := #[
  ([44,162,364],[14]),
  ([44,162,365],[]),
  ([44,162,377],[]),
  ([44,162,390],[]),
  ([44,173,364],[14]),
  ([44,173,378],[]),
  ([44,173,382],[]),
  ([44,188,378],[]),
  ([44,195,378],[]),
  ([44,196,365],[]),
  ([44,364],[14]),
  ([44,365,369],[]),
  ([44,365,378],[]),
  ([44,378,392],[]),
  ([47,153,173],[]),
  ([47,173,378],[]),
  ([47,378,392],[]),
  ([49,65,341],[19]),
  ([49,67,334],[22]),
  ([49,69,327],[25]),
  ([49,71,169],[2]),
  ([49,71,389],[3]),
  ([49,83,141],[14]),
  ([49,83,364],[15]),
  ([49,83,376],[16]),
  ([49,83,389],[17]),
  ([49,92,292],[30]),
  ([49,131,256],[18]),
  ([49,141,189],[34,14]),
  ([49,153,172],[]),
  ([49,153,392],[]),
  ([49,153,400],[35])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b6ok : f2b6.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b7 : Array Row := #[
  ([49,172,378],[]),
  ([49,173,399],[36]),
  ([49,189,364],[15]),
  ([49,257,364],[]),
  ([49,257,376],[]),
  ([49,293,364],[]),
  ([49,293,389],[]),
  ([49,296,376],[]),
  ([49,336,376],[]),
  ([49,376,392],[]),
  ([49,378,389],[]),
  ([49,378,391],[]),
  ([49,378,392],[]),
  ([49,378,400],[]),
  ([53,135,162],[18]),
  ([53,135,196],[37,18]),
  ([54,86,131],[18]),
  ([55,83,131],[18]),
  ([56,69,327],[25]),
  ([56,71,166],[4]),
  ([56,71,385],[5]),
  ([56,71,389],[6]),
  ([56,71,393],[7]),
  ([56,81,131],[18]),
  ([56,92,292],[30]),
  ([56,131,256],[18]),
  ([56,131,293],[]),
  ([56,135,399],[36]),
  ([56,293,348],[]),
  ([56,293,385],[]),
  ([56,378,385],[]),
  ([58,92,256],[41])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b7ok : f2b7.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b8 : Array Row := #[
  ([65,71,341],[19]),
  ([65,83,341],[19]),
  ([65,92,247],[40]),
  ([65,92,292],[57,30]),
  ([65,92,341],[62,19]),
  ([65,103,341],[19]),
  ([65,135,341],[19]),
  ([65,173,341],[19]),
  ([65,189,343],[]),
  ([65,341],[19]),
  ([65,347,394],[]),
  ([67,71,334],[22]),
  ([67,86,334],[22]),
  ([67,92,238],[39]),
  ([67,92,292],[58,30]),
  ([67,92,334],[61,22]),
  ([67,103,334],[22]),
  ([67,135,334],[22]),
  ([67,182,334],[22]),
  ([67,192,336],[]),
  ([67,334],[22]),
  ([67,340,390],[]),
  ([69,71,327],[25]),
  ([69,92,292],[59,30]),
  ([69,92,327],[60,25]),
  ([69,103,327],[25]),
  ([69,135,327],[25]),
  ([69,173,327],[25]),
  ([69,182,327],[25]),
  ([69,195,327],[25]),
  ([69,327],[25]),
  ([69,331,386],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b8ok : f2b8.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b9 : Array Row := #[
  ([69,336,343],[]),
  ([71,77,341],[20]),
  ([71,79,334],[23]),
  ([71,88,327],[26]),
  ([71,92,292],[30]),
  ([71,113,195],[36,25]),
  ([71,117,182],[22]),
  ([71,118,396],[]),
  ([71,122,173],[19]),
  ([71,123,392],[]),
  ([71,131,256],[18]),
  ([71,171,182],[]),
  ([71,172,181],[]),
  ([71,172,343],[]),
  ([71,172,396],[]),
  ([71,173,180],[]),
  ([71,173,341],[20]),
  ([71,173,342],[]),
  ([71,173,393],[21]),
  ([71,173,395],[]),
  ([71,181,336],[]),
  ([71,181,392],[]),
  ([71,182,334],[23]),
  ([71,182,335],[]),
  ([71,182,389],[24]),
  ([71,182,391],[]),
  ([71,188,327],[26]),
  ([71,188,341],[28]),
  ([71,191,327],[26]),
  ([71,191,334],[27]),
  ([71,194,385],[29]),
  ([71,195,327],[26])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b9ok : f2b9.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b10 : Array Row := #[
  ([71,195,328],[]),
  ([71,195,334],[27]),
  ([71,195,341],[28]),
  ([71,195,385],[29]),
  ([71,257,385],[]),
  ([71,257,393],[]),
  ([71,260,385],[]),
  ([71,260,389],[]),
  ([71,263,385],[]),
  ([71,264,385],[]),
  ([71,285,341],[]),
  ([71,289,334],[]),
  ([71,296,327],[]),
  ([71,298,327],[]),
  ([71,327,377],[]),
  ([71,334,371],[]),
  ([71,336,396],[]),
  ([71,341,365],[]),
  ([71,343,392],[]),
  ([71,389,396],[]),
  ([71,391,396],[]),
  ([71,392,393],[]),
  ([71,392,395],[]),
  ([71,392,396],[]),
  ([77,343,378],[]),
  ([79,336,378],[]),
  ([80,103,135],[30]),
  ([81,92,195],[36,30]),
  ([81,103,398],[37]),
  ([82,86,92],[30]),
  ([83,85,92],[30]),
  ([83,92,292],[30])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b10ok : f2b10.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b11 : Array Row := #[
  ([83,92,298],[]),
  ([83,131,256],[18]),
  ([83,131,260],[]),
  ([83,131,298],[]),
  ([83,260,348],[]),
  ([83,260,364],[]),
  ([83,289,313],[]),
  ([83,298,364],[]),
  ([83,343,364],[]),
  ([83,364,396],[]),
  ([86,92,292],[30]),
  ([86,92,296],[]),
  ([86,131,256],[18]),
  ([86,131,257],[]),
  ([86,131,296],[]),
  ([86,257,348],[]),
  ([86,257,370],[]),
  ([86,285,319],[]),
  ([86,296,370],[]),
  ([86,336,370],[]),
  ([86,370,392],[]),
  ([88,92,293],[]),
  ([92,103,292],[30]),
  ([92,135,292],[30]),
  ([92,173,292],[30]),
  ([92,182,292],[30]),
  ([92,188,293],[]),
  ([92,189,298],[]),
  ([92,191,293],[]),
  ([92,192,296],[]),
  ([92,195,292],[30]),
  ([92,195,293],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b11ok : f2b11.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b12 : Array Row := #[
  ([92,292],[30]),
  ([92,293,296],[]),
  ([92,293,298],[]),
  ([92,296,298],[]),
  ([96,195,293],[]),
  ([97,135,292],[31]),
  ([99,135,292],[31]),
  ([101,135,292],[31]),
  ([103,131,256],[18]),
  ([103,135,292],[31]),
  ([103,292,365],[]),
  ([103,292,371],[]),
  ([103,292,377],[]),
  ([103,292,386],[]),
  ([103,292,390],[]),
  ([103,292,394],[]),
  ([103,293,398],[]),
  ([118,289,378],[]),
  ([123,285,378],[]),
  ([131,135,256],[18]),
  ([131,162,256],[18]),
  ([131,189,260],[]),
  ([131,192,257],[]),
  ([131,194,293],[]),
  ([131,195,293],[]),
  ([131,256],[18]),
  ([131,257,260],[]),
  ([131,257,293],[]),
  ([131,260,293],[]),
  ([131,263,293],[]),
  ([131,264,293],[]),
  ([135,162,256],[32])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b12ok : f2b12.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b13 : Array Row := #[
  ([135,162,292],[33]),
  ([135,196,256],[32]),
  ([135,256,361],[]),
  ([135,256,378],[]),
  ([135,292,331],[]),
  ([135,292,340],[]),
  ([135,292,347],[]),
  ([135,292,369],[]),
  ([135,292,375],[]),
  ([135,292,384],[]),
  ([143,182,293],[]),
  ([148,173,293],[]),
  ([153,285,343],[]),
  ([153,289,336],[]),
  ([153,336,396],[]),
  ([153,343,392],[]),
  ([153,392,396],[]),
  ([162,238,371],[]),
  ([162,247,365],[]),
  ([162,256,365],[]),
  ([162,256,371],[]),
  ([162,256,377],[]),
  ([162,256,386],[]),
  ([162,256,390],[]),
  ([162,256,394],[]),
  ([172,378,396],[]),
  ([173,247,378],[]),
  ([173,293,319],[]),
  ([173,293,341],[]),
  ([173,341,378],[]),
  ([181,378,392],[]),
  ([182,238,378],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b13ok : f2b13.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def f2b14 : Array Row := #[
  ([182,293,313],[]),
  ([182,293,334],[]),
  ([182,334,378],[]),
  ([195,293,327],[]),
  ([195,293,378],[]),
  ([195,327,378],[]),
  ([241,378,396],[]),
  ([250,378,392],[]),
  ([257,378,396],[]),
  ([260,378,392],[]),
  ([274,392,396],[]),
  ([285,343,378],[]),
  ([285,378,396],[]),
  ([289,336,378],[]),
  ([289,378,392],[]),
  ([293,392,396],[]),
  ([296,343,378],[]),
  ([298,336,378],[]),
  ([336,378,396],[]),
  ([343,378,392],[]),
  ([378,392,396],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f2b14ok : f2b14.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true := by decide +kernel

private def layer2 (i : ℕ) : {s : List W // impossible 2 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer1 i).1) 1) = true} :=
    #[⟨f2b0, f2b0ok⟩, ⟨f2b1, f2b1ok⟩, ⟨f2b2, f2b2ok⟩, ⟨f2b3, f2b3ok⟩, ⟨f2b4, f2b4ok⟩, ⟨f2b5, f2b5ok⟩, ⟨f2b6, f2b6ok⟩, ⟨f2b7, f2b7ok⟩, ⟨f2b8, f2b8ok⟩, ⟨f2b9, f2b9ok⟩, ⟨f2b10, f2b10ok⟩, ⟨f2b11, f2b11ok⟩, ⟨f2b12, f2b12ok⟩, ⟨f2b13, f2b13ok⟩, ⟨f2b14, f2b14ok⟩]
  pick alphabet layer1 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f3b0 : Array Row := #[
  ([0,39,378,396],[454,157,159]),
  ([0,49,378,392],[455,222,224]),
  ([0,71,392,396],[458,302,309]),
  ([1,39,378,396],[454,157,159]),
  ([1,49,378,392],[222,224]),
  ([1,71,392,396],[302,309]),
  ([2,39,378,396],[157,159]),
  ([2,49,378,392],[455,222,224]),
  ([2,71,392,396],[302,309]),
  ([4,39,378,396],[157,159]),
  ([4,49,378,392],[222,224]),
  ([4,71,392,396],[458,302,309]),
  ([5,39,378,396],[454,157,159]),
  ([5,49,378,392],[222,224]),
  ([5,71,392,396],[302,309]),
  ([8,39,378,396],[157,159]),
  ([8,49,378,392],[455,222,224]),
  ([8,71,392,396],[302,309]),
  ([14,19,28,131],[81,36,23,14,1,0]),
  ([14,28,67,92],[269,77,71,12,9,1]),
  ([14,28,162,371],[433]),
  ([14,28,182,378],[447,93]),
  ([14,39,44,131],[154,141,2]),
  ([14,39,49,370],[162,1]),
  ([14,39,378,396],[454,157,159]),
  ([14,44,49,131],[219,173,7]),
  ([14,44,58,92],[255,182,174,12,8,4]),
  ([14,44,71,131],[298,180,10]),
  ([14,44,83,131],[353,181,11]),
  ([14,44,103,131],[392,185,13]),
  ([14,44,131],[409,15,186,202,5,187,21,6,16]),
  ([14,44,131,135],[403,188,17])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b0ok : f3b0.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b1 : Array Row := #[
  ([14,44,131,162],[404,192,18]),
  ([14,44,135,162],[415,193,3]),
  ([14,44,135,196],[417,201,20,3]),
  ([14,44,135,361],[418]),
  ([14,44,135,378],[419,204]),
  ([14,44,162,365],[435,189]),
  ([14,44,162,394],[440,20]),
  ([14,49,71,385],[326,0]),
  ([14,49,83,131],[354,215,3]),
  ([14,49,83,348],[356,4]),
  ([14,49,83,364],[357,214,5]),
  ([14,49,131,189],[405,226,19,3]),
  ([14,49,131,257],[410,227]),
  ([14,49,131,293],[412,229]),
  ([14,49,378,392],[457,222,224]),
  ([14,71,135,341],[337,8]),
  ([14,71,182,327],[316,9]),
  ([14,71,347,394],[]),
  ([14,71,392,396],[458,302,309]),
  ([14,83,92,289],[358]),
  ([14,83,131,260],[357,241]),
  ([14,83,131,396],[361,19]),
  ([14,92,182,293],[448,380]),
  ([14,103,135,288],[12]),
  ([14,103,293,394],[]),
  ([14,135,162,247],[434,14]),
  ([14,135,162,256],[435,238,15]),
  ([15,44,135,162],[193]),
  ([17,39,378,396],[454,157,159]),
  ([17,44,71,131],[3,22]),
  ([17,49,71,385],[329]),
  ([17,49,131,293],[414])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b1ok : f3b1.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b2 : Array Row := #[
  ([17,49,378,392],[222,224]),
  ([17,71,392,396],[302,309]),
  ([19,28,65,92],[258,77,70,34,31,23]),
  ([19,28,162,365],[434]),
  ([19,28,173,378],[442,92]),
  ([19,35,39,131],[154,103,28]),
  ([19,35,49,131],[219,105,29]),
  ([19,35,58,92],[255,114,106,34,30,25]),
  ([19,35,71,131],[298,112,32]),
  ([19,35,86,131],[364,113,33]),
  ([19,35,103,131],[392,117,35]),
  ([19,35,131],[409,37,118,134,26,119,43,27,38]),
  ([19,35,131,135],[403,120,39]),
  ([19,35,131,162],[404,124,40]),
  ([19,35,135,162],[415,125,24]),
  ([19,35,135,196],[417,133,42,24]),
  ([19,35,135,361],[418]),
  ([19,35,135,378],[419,136]),
  ([19,35,162,371],[436,121]),
  ([19,35,162,390],[439,42]),
  ([19,39,49,364],[227,23]),
  ([19,39,71,385],[324,0]),
  ([19,39,86,131],[365,150,24]),
  ([19,39,86,348],[367,25]),
  ([19,39,86,370],[368,149,26]),
  ([19,39,131,192],[406,161,41,24]),
  ([19,39,131,260],[410,162]),
  ([19,39,131,293],[411,164]),
  ([19,39,378,396],[456,157,159]),
  ([19,49,378,392],[455,222,224]),
  ([19,71,135,334],[335,30]),
  ([19,71,173,327],[314,31])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b2ok : f3b2.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b3 : Array Row := #[
  ([19,71,340,390],[]),
  ([19,71,392,396],[458,302,309]),
  ([19,86,92,285],[369]),
  ([19,86,131,257],[368,240]),
  ([19,86,131,392],[372,41]),
  ([19,92,173,293],[443,378]),
  ([19,103,135,284],[34]),
  ([19,103,293,390],[]),
  ([19,135,162,238],[433,36]),
  ([19,135,162,256],[436,238,37]),
  ([20,35,135,162],[125]),
  ([22,35,71,131],[24,44]),
  ([22,39,71,385],[328]),
  ([22,39,131,293],[413]),
  ([22,39,378,396],[157,159]),
  ([22,49,378,392],[455,222,224]),
  ([22,71,392,396],[302,309]),
  ([24,28,39,131],[154,66,50]),
  ([24,28,49,131],[219,67,52]),
  ([24,28,56,131],[249,68,53]),
  ([24,28,58,92],[255,77,69,56,54,46]),
  ([24,28,71,131],[298,76,55]),
  ([24,28,103,131],[392,80,57]),
  ([24,28,131],[409,58,82,98,47,83,63,48,59]),
  ([24,28,131,135],[403,84,60]),
  ([24,28,131,162],[404,88,61]),
  ([24,28,135,162],[415,89,45]),
  ([24,28,135,196],[417,97,62,45]),
  ([24,28,135,361],[418]),
  ([24,28,135,378],[419,99]),
  ([24,28,162,377],[437,85]),
  ([24,28,162,386],[438,62])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b3ok : f3b3.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b4 : Array Row := #[
  ([24,35,135,162],[415,126,49]),
  ([24,39,49,131],[143,45]),
  ([24,39,49,348],[46]),
  ([24,39,49,376],[228,163,142,47]),
  ([24,39,86,131],[365,151,49]),
  ([24,39,131,260],[410,163]),
  ([24,39,131,396],[168,64]),
  ([24,44,135,162],[415,194,51]),
  ([24,49,83,131],[354,216,51]),
  ([24,49,131,257],[410,228]),
  ([24,49,131,392],[233,64]),
  ([24,71,135,327],[334,54]),
  ([24,71,331,386],[]),
  ([24,103,135,283],[56]),
  ([24,103,293,386],[]),
  ([24,135,162,256],[437,238,58]),
  ([25,28,135,162],[89]),
  ([26,39,49,131],[]),
  ([27,28,71,131],[45,65]),
  ([28,39,69,92],[153,146,66]),
  ([28,39,71,370],[164,1]),
  ([28,39,153,182],[160,86]),
  ([28,39,162,377],[85]),
  ([28,39,182,378],[96]),
  ([28,39,195,378],[86]),
  ([28,39,371,378],[]),
  ([28,39,378,396],[454,157,159]),
  ([28,49,69,92],[218,211,67]),
  ([28,49,71,364],[229,23]),
  ([28,49,153,173],[225,86]),
  ([28,49,162,377],[85]),
  ([28,49,173,378],[96])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b4ok : f3b4.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b5 : Array Row := #[
  ([28,49,195,378],[86]),
  ([28,49,365,378],[]),
  ([28,49,378,392],[455,222,224]),
  ([28,56,69,92],[248,242,68]),
  ([28,56,71,131],[250,244,45]),
  ([28,56,71,348],[252,46]),
  ([28,56,71,385],[253,243,48]),
  ([28,56,131,293],[253,247]),
  ([28,56,131,378],[254,94]),
  ([28,56,135,153],[251,86]),
  ([28,56,135,378],[96]),
  ([28,56,162,377],[85]),
  ([28,56,173,378],[96]),
  ([28,56,182,378],[96]),
  ([28,56,195,378],[86]),
  ([28,56,351,378],[]),
  ([28,56,378,386],[]),
  ([28,69,71,92],[292,278,76]),
  ([28,69,92],[384,78,279,286,74,280,98,75,79]),
  ([28,69,92,103],[374,281,80]),
  ([28,69,92,135],[375,282,84]),
  ([28,69,92,173],[376,283,90]),
  ([28,69,92,182],[377,284,91]),
  ([28,69,92,195],[382,285,95]),
  ([28,69,97,135],[389,72]),
  ([28,69,99,135],[390,72]),
  ([28,69,101,135],[391,72]),
  ([28,69,103,135],[393,72]),
  ([28,69,103,377],[396,100]),
  ([28,69,103,386],[397,287]),
  ([28,69,135,162],[416,89,73]),
  ([28,69,135,331],[420,287])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b5ok : f3b5.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b6 : Array Row := #[
  ([28,69,135,384],[425,100]),
  ([28,71,88,92],[373,291,72]),
  ([28,71,92,188],[378,314,92,72]),
  ([28,71,92,191],[380,316,93,72]),
  ([28,71,92,195],[383,319,96,72]),
  ([28,71,92,296],[385,332]),
  ([28,71,92,298],[386,333]),
  ([28,71,92,377],[334,99]),
  ([28,71,96,195],[388,320,96]),
  ([28,71,103,152],[85]),
  ([28,71,103,377],[89]),
  ([28,71,131,194],[407,318,94,73]),
  ([28,71,131,195],[408,323,96,73]),
  ([28,71,131,257],[411,324]),
  ([28,71,131,260],[412,326]),
  ([28,71,131,263],[413,328]),
  ([28,71,131,264],[414,329]),
  ([28,71,135,161],[87]),
  ([28,71,135,325],[69]),
  ([28,71,143,182],[426,313]),
  ([28,71,148,173],[427,307]),
  ([28,71,162,377],[85]),
  ([28,71,173,319],[443,70]),
  ([28,71,182,313],[448,71]),
  ([28,71,195,327],[451,293,74]),
  ([28,71,195,378],[452,86]),
  ([28,71,326,377],[]),
  ([28,71,331,377],[]),
  ([28,71,392,396],[463,302,309]),
  ([28,92,195,293],[451,347]),
  ([28,92,195,378],[453,86]),
  ([28,103,135,273],[77])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b6ok : f3b6.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b7 : Array Row := #[
  ([28,103,135,292],[420,397,346,78]),
  ([28,103,162,377],[85]),
  ([28,103,195,378],[86]),
  ([28,103,274,377],[]),
  ([28,103,293,377],[]),
  ([28,127,135,378],[96]),
  ([28,135,162,231],[81]),
  ([28,135,162,256],[438,417,238,82]),
  ([28,135,162,377],[85]),
  ([28,135,195,378],[86]),
  ([28,135,257,378],[]),
  ([28,135,260,378],[]),
  ([28,156,162,195],[86,85,87]),
  ([28,162,377],[97,85,85]),
  ([28,173,182,378],[96]),
  ([28,173,195,378],[86]),
  ([28,173,250,378],[]),
  ([28,173,343,378],[]),
  ([28,182,195,378],[86]),
  ([28,182,241,378],[]),
  ([28,182,336,378],[]),
  ([28,195,378],[86,86]),
  ([29,49,69,92],[72,101]),
  ([29,49,173,378],[]),
  ([29,49,195,378],[96]),
  ([30,39,69,92],[72,102]),
  ([30,39,182,378],[]),
  ([30,39,195,378],[96]),
  ([31,39,182,378],[]),
  ([31,49,173,378],[]),
  ([33,39,182,378],[]),
  ([33,49,173,378],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b7ok : f3b7.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b8 : Array Row := #[
  ([35,39,67,92],[153,145,103]),
  ([35,39,162,371],[121]),
  ([35,39,182,378],[132,123]),
  ([35,44,135,162],[415,195,127,104]),
  ([35,49,67,92],[218,210,105]),
  ([35,49,71,131],[213,24]),
  ([35,49,71,348],[25]),
  ([35,49,71,389],[327,230,212,27]),
  ([35,49,83,131],[354,217,104]),
  ([35,49,131,293],[412,230]),
  ([35,49,131,378],[234,137]),
  ([35,49,135,153],[123]),
  ([35,49,135,378],[129]),
  ([35,49,135,381],[130]),
  ([35,49,162,371],[121]),
  ([35,49,173,378],[132]),
  ([35,49,182,378],[123]),
  ([35,49,351,378],[]),
  ([35,49,378,390],[]),
  ([35,56,71,131],[250,245,49]),
  ([35,56,135,378],[132]),
  ([35,67,71,92],[292,267,112]),
  ([35,67,86,92],[362,268,113]),
  ([35,67,92],[384,115,270,276,109,271,134,110,116]),
  ([35,67,92,103],[374,272,117]),
  ([35,67,92,135],[375,273,120]),
  ([35,67,92,182],[377,274,128]),
  ([35,67,99,135],[390,107]),
  ([35,67,103,135],[393,107]),
  ([35,67,103,371],[395,135]),
  ([35,67,103,390],[398,277]),
  ([35,67,135,162],[416,125,108])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b8ok : f3b8.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b9 : Array Row := #[
  ([35,67,135,340],[421,277]),
  ([35,67,135,375],[424,135]),
  ([35,69,103,135],[393,111]),
  ([35,71,79,92],[290,107]),
  ([35,71,92,182],[310,129,107]),
  ([35,71,92,191],[380,317,131,111]),
  ([35,71,92,195],[383,321,132,111]),
  ([35,71,92,289],[331]),
  ([35,71,92,371],[335,136]),
  ([35,71,96,182],[129]),
  ([35,71,97,182],[311,130]),
  ([35,71,103,147],[121]),
  ([35,71,103,371],[125]),
  ([35,71,103,377],[126]),
  ([35,71,103,394],[127]),
  ([35,71,131,182],[312,129,108]),
  ([35,71,131,260],[412,327]),
  ([35,71,131,396],[339,137]),
  ([35,71,135,148],[122]),
  ([35,71,135,319],[106]),
  ([35,71,162,371],[121]),
  ([35,71,182,334],[449,317,294,109]),
  ([35,71,182,378],[123]),
  ([35,71,323,371],[]),
  ([35,71,340,371],[]),
  ([35,86,162,371],[121]),
  ([35,86,182,378],[123]),
  ([35,92,182,293],[449,380]),
  ([35,92,182,378],[450,123]),
  ([35,103,135,272],[114]),
  ([35,103,135,292],[421,398,346,115]),
  ([35,103,162,371],[121])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b9ok : f3b9.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b10 : Array Row := #[
  ([35,103,182,378],[123]),
  ([35,103,274,371],[]),
  ([35,103,293,371],[]),
  ([35,135,162,256],[439,417,238,118]),
  ([35,135,162,371],[121]),
  ([35,135,182,378],[123]),
  ([35,135,260,378],[]),
  ([35,135,343,378],[]),
  ([35,156,162,182],[123,121,122]),
  ([35,162,371],[133,121,121]),
  ([35,182,378],[131,123,123]),
  ([36,49,71,131],[]),
  ([36,49,135,153],[]),
  ([36,49,135,378],[]),
  ([36,49,182,378],[]),
  ([37,49,71,131],[]),
  ([37,49,131,378],[235,140]),
  ([37,49,135,153],[138]),
  ([37,49,135,378],[139]),
  ([37,71,92,182],[311,139]),
  ([37,71,131,182],[313,139]),
  ([37,71,131,396],[340,140]),
  ([37,156,162,182],[138]),
  ([38,49,71,131],[]),
  ([39,44,65,92],[153,144,141]),
  ([39,44,71,131],[3,148]),
  ([39,44,71,348],[4]),
  ([39,44,71,393],[325,6,165,147]),
  ([39,44,86,131],[365,104,152]),
  ([39,44,131,293],[411,165]),
  ([39,44,131,378],[205,169]),
  ([39,44,135,153],[191])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b10ok : f3b10.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b11 : Array Row := #[
  ([39,44,135,378],[197]),
  ([39,44,135,382],[198]),
  ([39,44,162,365],[189]),
  ([39,44,173,378],[191]),
  ([39,44,182,378],[200]),
  ([39,44,351,378],[]),
  ([39,44,378,394],[]),
  ([39,45,71,131],[]),
  ([39,45,135,153],[]),
  ([39,45,135,378],[]),
  ([39,45,173,378],[]),
  ([39,47,71,131],[]),
  ([39,47,131,378],[208,170]),
  ([39,47,135,153],[206]),
  ([39,47,135,378],[207]),
  ([39,48,71,131],[]),
  ([39,49,56,376],[68,142]),
  ([39,49,58,325],[69]),
  ([39,49,65,319],[70]),
  ([39,49,67,313],[71]),
  ([39,49,69,92],[72,143]),
  ([39,49,69,131],[73,143]),
  ([39,49,69,376],[75,231,166,142]),
  ([39,49,71,131],[]),
  ([39,49,71,141],[214]),
  ([39,49,71,146],[149]),
  ([39,49,71,166],[243]),
  ([39,49,71,348],[]),
  ([39,49,71,364],[215]),
  ([39,49,71,370],[150]),
  ([39,49,71,376],[76,216,151,142]),
  ([39,49,71,385],[244])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b11ok : f3b11.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b12 : Array Row := #[
  ([39,49,71,389],[245,217,212,28]),
  ([39,49,71,393],[246,7,152,147]),
  ([39,49,81,131],[247]),
  ([39,49,83,364],[214,141]),
  ([39,49,86,370],[105,149]),
  ([39,49,92,273],[77]),
  ([39,49,92,376],[79,232,167,142]),
  ([39,49,103,376],[80,142]),
  ([39,49,131,153],[222,157]),
  ([39,49,131,231],[81]),
  ([39,49,131,274],[]),
  ([39,49,131,293],[250]),
  ([39,49,131,376],[83,233,168,142]),
  ([39,49,131,378],[236,171]),
  ([39,49,132,153],[222]),
  ([39,49,132,378],[236]),
  ([39,49,133,153],[157]),
  ([39,49,133,378],[171]),
  ([39,49,135,153],[]),
  ([39,49,135,376],[84,142]),
  ([39,49,135,378],[]),
  ([39,49,135,399],[251,225,160]),
  ([39,49,137,378],[]),
  ([39,49,138,378],[]),
  ([39,49,141,153],[222,220,158]),
  ([39,49,141,378],[236,172]),
  ([39,49,142,153],[]),
  ([39,49,142,378],[]),
  ([39,49,142,381],[]),
  ([39,49,143,153],[222]),
  ([39,49,143,378],[236]),
  ([39,49,146,153],[223,157,155])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b12ok : f3b12.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b13 : Array Row := #[
  ([39,49,146,378],[237,171]),
  ([39,49,147,153],[]),
  ([39,49,147,378],[]),
  ([39,49,147,382],[]),
  ([39,49,148,153],[157]),
  ([39,49,148,378],[171]),
  ([39,49,152,162],[85,142]),
  ([39,49,153,173],[]),
  ([39,49,153,182],[]),
  ([39,49,153,195],[86,142]),
  ([39,49,153,348],[]),
  ([39,49,153,351],[]),
  ([39,49,153,355],[]),
  ([39,49,153,358],[]),
  ([39,49,153,365],[]),
  ([39,49,153,368],[]),
  ([39,49,153,371],[]),
  ([39,49,153,374],[]),
  ([39,49,153,386],[]),
  ([39,49,153,392],[221]),
  ([39,49,153,396],[156]),
  ([39,49,156,161],[87,142]),
  ([39,49,162,376],[88,142]),
  ([39,49,162,377],[89]),
  ([39,49,167,378],[]),
  ([39,49,172,378],[236,221]),
  ([39,49,173,376],[90,102,142]),
  ([39,49,173,378],[]),
  ([39,49,175,378],[]),
  ([39,49,181,378],[171,156]),
  ([39,49,182,376],[91,101,142]),
  ([39,49,182,378],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b13ok : f3b13.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b14 : Array Row := #[
  ([39,49,184,378],[]),
  ([39,49,188,378],[92]),
  ([39,49,191,378],[93]),
  ([39,49,194,378],[94]),
  ([39,49,195,376],[95,142]),
  ([39,49,195,378],[96]),
  ([39,49,274,348],[]),
  ([39,49,274,364],[]),
  ([39,49,274,370],[]),
  ([39,49,293,348],[252]),
  ([39,49,293,385],[253]),
  ([39,49,348,378],[]),
  ([39,49,349,378],[]),
  ([39,49,350,378],[]),
  ([39,49,351,378],[]),
  ([39,49,354,378],[]),
  ([39,49,355,378],[]),
  ([39,49,357,378],[]),
  ([39,49,358,378],[]),
  ([39,49,360,378],[]),
  ([39,49,364,378],[]),
  ([39,49,365,378],[]),
  ([39,49,365,381],[]),
  ([39,49,367,378],[]),
  ([39,49,368,378],[]),
  ([39,49,370,378],[]),
  ([39,49,371,378],[]),
  ([39,49,371,382],[]),
  ([39,49,373,378],[]),
  ([39,49,374,378],[]),
  ([39,49,376],[98,66,67,142,142]),
  ([39,49,377,378],[99])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b14ok : f3b14.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b15 : Array Row := #[
  ([39,49,377,384],[100]),
  ([39,49,378,385],[254]),
  ([39,49,378,386],[]),
  ([39,49,378,387],[]),
  ([39,49,378,388],[]),
  ([39,49,378,390],[]),
  ([39,49,378,392],[222,224]),
  ([39,49,378,394],[]),
  ([39,49,378,396],[157,159]),
  ([39,55,71,131],[241]),
  ([39,55,135,378],[]),
  ([39,56,71,385],[243,50]),
  ([39,56,131,293],[247]),
  ([39,56,378,396],[157,159]),
  ([39,58,71,341],[330,8]),
  ([39,58,86,319],[369,106]),
  ([39,58,123,378],[402,171]),
  ([39,58,153,343],[428]),
  ([39,58,343,378],[459]),
  ([39,58,378,396],[460,157,159]),
  ([39,59,71,341],[330]),
  ([39,59,343,378],[459]),
  ([39,60,343,378],[]),
  ([39,65,343,378],[459]),
  ([39,67,71,327],[332,9]),
  ([39,67,86,92],[363,107,150]),
  ([39,67,86,131],[366,108,150]),
  ([39,67,86,370],[370,110,149]),
  ([39,67,92,192],[381,275,107,161]),
  ([39,67,92,260],[162]),
  ([39,67,92,293],[385,164]),
  ([39,67,343,378],[464])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b15ok : f3b15.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b16 : Array Row := #[
  ([39,69,86,92],[363,111,151]),
  ([39,69,92,298],[387,166]),
  ([39,69,92,343],[288,167]),
  ([39,71,79,92],[]),
  ([39,71,79,131],[]),
  ([39,71,79,348],[]),
  ([39,71,83,393],[11,147]),
  ([39,71,85,92],[350]),
  ([39,71,86,370],[112,149]),
  ([39,71,92,181],[308,159]),
  ([39,71,92,288],[12]),
  ([39,71,92,289],[]),
  ([39,71,92,298],[352]),
  ([39,71,92,396],[336,171]),
  ([39,71,93,396],[336]),
  ([39,71,96,396],[171]),
  ([39,71,97,396],[336]),
  ([39,71,103,393],[13,147]),
  ([39,71,113,182],[293,160]),
  ([39,71,122,135],[296]),
  ([39,71,123,131],[297]),
  ([39,71,123,348],[]),
  ([39,71,124,394],[]),
  ([39,71,131,181],[309,159]),
  ([39,71,131,247],[14]),
  ([39,71,131,249],[]),
  ([39,71,131,250],[]),
  ([39,71,131,260],[354]),
  ([39,71,131,289],[]),
  ([39,71,131,298],[355]),
  ([39,71,131,343],[338]),
  ([39,71,131,393],[16,341,169,147])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b16ok : f3b16.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b17 : Array Row := #[
  ([39,71,131,395],[342,170]),
  ([39,71,131,396],[343,171]),
  ([39,71,132,343],[338]),
  ([39,71,132,396],[343]),
  ([39,71,135,180],[303]),
  ([39,71,135,341],[304]),
  ([39,71,135,342],[305]),
  ([39,71,135,393],[17,306,147]),
  ([39,71,135,395],[307]),
  ([39,71,143,343],[338]),
  ([39,71,143,396],[343]),
  ([39,71,153,396],[171,156]),
  ([39,71,162,393],[18,22,147]),
  ([39,71,172,396],[343,300]),
  ([39,71,173,341],[296,144]),
  ([39,71,179,347],[]),
  ([39,71,181,378],[156]),
  ([39,71,181,392],[300]),
  ([39,71,182,327],[319]),
  ([39,71,182,328],[320]),
  ([39,71,182,329],[]),
  ([39,71,182,334],[321,294,145]),
  ([39,71,182,341],[322]),
  ([39,71,182,385],[323]),
  ([39,71,189,396],[19]),
  ([39,71,195,327],[293,146]),
  ([39,71,196,394],[20]),
  ([39,71,250,348],[]),
  ([39,71,250,370],[]),
  ([39,71,250,385],[]),
  ([39,71,260,348],[356]),
  ([39,71,260,364],[357])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b17ok : f3b17.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b18 : Array Row := #[
  ([39,71,289,300],[]),
  ([39,71,289,313],[358]),
  ([39,71,289,319],[]),
  ([39,71,289,327],[]),
  ([39,71,289,348],[]),
  ([39,71,289,370],[]),
  ([39,71,298,364],[359]),
  ([39,71,327,371],[]),
  ([39,71,331,394],[]),
  ([39,71,336,396],[295,308]),
  ([39,71,341,351],[]),
  ([39,71,341,394],[]),
  ([39,71,343,348],[]),
  ([39,71,343,349],[]),
  ([39,71,343,364],[360]),
  ([39,71,343,370],[]),
  ([39,71,343,392],[297,301]),
  ([39,71,347,394],[]),
  ([39,71,348,396],[]),
  ([39,71,349,396],[]),
  ([39,71,352,396],[]),
  ([39,71,354,396],[]),
  ([39,71,364,396],[361]),
  ([39,71,367,396],[]),
  ([39,71,370,396],[]),
  ([39,71,378,396],[157,159]),
  ([39,71,385,396],[]),
  ([39,71,392,396],[302,309]),
  ([39,71,393],[21,2,10,147,147]),
  ([39,78,86,92],[363]),
  ([39,79,92,274],[]),
  ([39,79,92,378],[345,171])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b18ok : f3b18.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b19 : Array Row := #[
  ([39,79,135,378],[]),
  ([39,79,182,378],[]),
  ([39,81,92,182],[347,160]),
  ([39,81,103,371],[]),
  ([39,81,103,394],[]),
  ([39,83,92,298],[350]),
  ([39,83,131,260],[241]),
  ([39,83,378,396],[157,159]),
  ([39,86,92,272],[114]),
  ([39,86,92,296],[349]),
  ([39,86,92,370],[116,371,161,149]),
  ([39,86,103,370],[117,149]),
  ([39,86,131,257],[240]),
  ([39,86,131,370],[119,372,161,149]),
  ([39,86,135,370],[120,149]),
  ([39,86,147,162],[121,149]),
  ([39,86,148,156],[122,149]),
  ([39,86,153,182],[123,149]),
  ([39,86,162,370],[124,149]),
  ([39,86,162,371],[125]),
  ([39,86,162,377],[126]),
  ([39,86,162,394],[127]),
  ([39,86,182,370],[128,149]),
  ([39,86,182,378],[129]),
  ([39,86,182,381],[130]),
  ([39,86,195,378],[132]),
  ([39,86,370],[134,103,113,149,149]),
  ([39,86,371,375],[135]),
  ([39,86,371,378],[136]),
  ([39,86,378,396],[137,157,159]),
  ([39,92,153,289],[429]),
  ([39,92,153,396],[430,171,156])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b19ok : f3b19.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b20 : Array Row := #[
  ([39,92,182,293],[383]),
  ([39,92,195,293],[347]),
  ([39,92,274,289],[]),
  ([39,92,274,298],[]),
  ([39,92,289,293],[]),
  ([39,92,289,378],[461]),
  ([39,92,293,371],[]),
  ([39,92,293,394],[]),
  ([39,92,298,378],[465]),
  ([39,92,378,396],[466,157,159]),
  ([39,96,182,293],[388]),
  ([39,97,182,293],[]),
  ([39,103,135,292],[346,153]),
  ([39,103,147,293],[]),
  ([39,103,153,396],[156]),
  ([39,103,179,293],[]),
  ([39,103,181,378],[156]),
  ([39,103,293,371],[]),
  ([39,103,293,377],[]),
  ([39,103,293,394],[]),
  ([39,103,299,371],[]),
  ([39,103,378,396],[157,159]),
  ([39,120,378,396],[157,159]),
  ([39,123,135,153],[]),
  ([39,123,135,378],[]),
  ([39,123,173,378],[]),
  ([39,123,182,378],[]),
  ([39,123,351,378],[]),
  ([39,125,153,182],[]),
  ([39,125,182,378],[]),
  ([39,125,378,396],[157,159]),
  ([39,131,153,343],[431])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b20ok : f3b20.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b21 : Array Row := #[
  ([39,131,153,396],[432,171,156]),
  ([39,131,181,378],[446,171,156]),
  ([39,131,182,293],[408]),
  ([39,131,250,274],[]),
  ([39,131,250,293],[]),
  ([39,131,250,378],[455]),
  ([39,131,260,274],[]),
  ([39,131,260,378],[457]),
  ([39,131,274,289],[]),
  ([39,131,274,396],[458]),
  ([39,131,289,378],[462]),
  ([39,131,293,396],[463]),
  ([39,131,343,378],[467]),
  ([39,131,378,396],[468,157,159]),
  ([39,135,148,293],[427]),
  ([39,135,153,250],[]),
  ([39,135,153,260],[]),
  ([39,135,153,289],[]),
  ([39,135,153,343],[]),
  ([39,135,153,396],[156]),
  ([39,135,162,256],[238,154]),
  ([39,135,181,378],[156]),
  ([39,135,247,378],[442]),
  ([39,135,250,378],[]),
  ([39,135,260,378],[]),
  ([39,135,260,381],[]),
  ([39,135,289,378],[]),
  ([39,135,293,319],[443]),
  ([39,135,293,341],[444]),
  ([39,135,298,378],[]),
  ([39,135,298,381],[]),
  ([39,135,341,378],[445])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b21ok : f3b21.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b22 : Array Row := #[
  ([39,135,343,378],[]),
  ([39,135,378,396],[157,159]),
  ([39,140,378,396],[157,159]),
  ([39,153,156,396],[156]),
  ([39,153,162,396],[156]),
  ([39,153,173,343],[]),
  ([39,153,182,192],[123,155,156]),
  ([39,153,182,198],[138,156]),
  ([39,153,182,343],[]),
  ([39,153,343,351],[]),
  ([39,153,378,396],[159,156]),
  ([39,153,396],[156,156]),
  ([39,156,162,181],[156]),
  ([39,156,162,396],[157]),
  ([39,156,182,196],[]),
  ([39,156,378,396],[157,159]),
  ([39,162,181,378],[156]),
  ([39,162,260,371],[]),
  ([39,162,260,377],[]),
  ([39,162,293,371],[]),
  ([39,162,293,394],[]),
  ([39,162,378,396],[157,159]),
  ([39,162,380,396],[]),
  ([39,165,378,396],[157,159]),
  ([39,173,250,378],[]),
  ([39,173,260,378],[]),
  ([39,173,289,378],[]),
  ([39,173,298,378],[]),
  ([39,173,343,378],[]),
  ([39,173,378,396],[157,159]),
  ([39,181,378],[156,156]),
  ([39,181,378,396],[157,156])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b22ok : f3b22.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b23 : Array Row := #[
  ([39,182,192,378],[129,159]),
  ([39,182,198,378],[139,159]),
  ([39,182,250,378],[]),
  ([39,182,252,378],[]),
  ([39,182,253,378],[]),
  ([39,182,260,378],[]),
  ([39,182,289,378],[]),
  ([39,182,293,327],[451]),
  ([39,182,293,378],[452]),
  ([39,182,327,378],[453]),
  ([39,182,331,378],[]),
  ([39,182,343,378],[]),
  ([39,182,345,378],[]),
  ([39,182,378,396],[157,159]),
  ([39,195,343,378],[]),
  ([39,197,378,396],[157,159]),
  ([39,198,378,396],[140,157,159]),
  ([39,250,351,378],[]),
  ([39,250,358,378],[]),
  ([39,250,371,378],[]),
  ([39,250,378,386],[]),
  ([39,260,351,378],[]),
  ([39,260,365,378],[]),
  ([39,274,289,348],[]),
  ([39,274,343,348],[]),
  ([39,285,343,378],[344,402,428]),
  ([39,289,336,378],[345,401,429]),
  ([39,289,343,378],[]),
  ([39,289,348,378],[]),
  ([39,289,351,378],[]),
  ([39,293,323,371],[]),
  ([39,293,331,371],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b23ok : f3b23.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b24 : Array Row := #[
  ([39,293,347,394],[]),
  ([39,343,348,378],[]),
  ([39,343,351,378],[]),
  ([39,343,355,378],[]),
  ([39,343,358,378],[]),
  ([39,343,365,378],[]),
  ([39,343,371,378],[]),
  ([39,343,378,386],[]),
  ([39,351,378,396],[157,159]),
  ([39,361,378,396],[157,159]),
  ([39,378,392,396],[432,441,446,157,159]),
  ([39,378,396],[157,159,157,159]),
  ([44,49,65,92],[218,209,173]),
  ([44,49,162,365],[189]),
  ([44,49,173,378],[200,191]),
  ([44,56,71,131],[250,246,51]),
  ([44,56,135,378],[200]),
  ([44,65,71,92],[292,256,180]),
  ([44,65,83,92],[351,257,181]),
  ([44,65,92],[384,183,259,265,177,260,202,178,184]),
  ([44,65,92,103],[374,261,185]),
  ([44,65,92,135],[375,262,188]),
  ([44,65,92,173],[376,263,196]),
  ([44,65,97,135],[389,175]),
  ([44,65,103,135],[393,175]),
  ([44,65,103,365],[394,203]),
  ([44,65,103,394],[399,266]),
  ([44,65,135,162],[416,193,176]),
  ([44,65,135,347],[422,266]),
  ([44,65,135,369],[423,203]),
  ([44,69,103,135],[393,179]),
  ([44,71,77,92],[289,175])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b24ok : f3b24.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b25 : Array Row := #[
  ([44,71,92,173],[304,197,175]),
  ([44,71,92,188],[378,315,199,179]),
  ([44,71,92,195],[383,322,200,179]),
  ([44,71,92,285],[330]),
  ([44,71,92,365],[337,204]),
  ([44,71,96,173],[197]),
  ([44,71,99,173],[305,198]),
  ([44,71,103,142],[189]),
  ([44,71,103,365],[193]),
  ([44,71,103,377],[194]),
  ([44,71,103,390],[195]),
  ([44,71,131,173],[306,197,176]),
  ([44,71,131,257],[411,325]),
  ([44,71,131,392],[341,205]),
  ([44,71,135,143],[190]),
  ([44,71,135,313],[174]),
  ([44,71,162,365],[189]),
  ([44,71,173,341],[444,315,296,177]),
  ([44,71,173,378],[191]),
  ([44,71,317,365],[]),
  ([44,71,347,365],[]),
  ([44,83,162,365],[189]),
  ([44,83,173,378],[191]),
  ([44,92,173,293],[444,378]),
  ([44,92,173,378],[445,191]),
  ([44,103,135,271],[182]),
  ([44,103,135,292],[422,399,346,183]),
  ([44,103,162,365],[189]),
  ([44,103,173,378],[191]),
  ([44,103,274,365],[]),
  ([44,103,293,365],[]),
  ([44,135,162,256],[440,417,238,186])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b25ok : f3b25.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b26 : Array Row := #[
  ([44,135,162,365],[189]),
  ([44,135,173,378],[191]),
  ([44,135,257,378],[]),
  ([44,135,336,378],[]),
  ([44,156,162,173],[191,189,190]),
  ([44,162,365],[201,189,189]),
  ([44,173,378],[199,191,191]),
  ([47,71,92,173],[305,207]),
  ([47,71,131,173],[307,207]),
  ([47,71,131,392],[342,208]),
  ([47,156,162,173],[206]),
  ([49,54,71,131],[240]),
  ([49,54,135,378],[]),
  ([49,56,71,385],[243,52]),
  ([49,56,131,293],[247]),
  ([49,56,378,392],[222,224]),
  ([49,58,71,334],[331,30]),
  ([49,58,83,313],[358,174]),
  ([49,58,118,378],[401,236]),
  ([49,58,153,336],[429]),
  ([49,58,336,378],[461]),
  ([49,58,378,392],[462,222,224]),
  ([49,59,336,378],[]),
  ([49,60,71,334],[331]),
  ([49,60,336,378],[461]),
  ([49,65,71,327],[333,31]),
  ([49,65,83,92],[352,175,215]),
  ([49,65,83,131],[355,176,215]),
  ([49,65,83,364],[359,178,214]),
  ([49,65,92,189],[379,264,175,226]),
  ([49,65,92,257],[227]),
  ([49,65,92,293],[386,229])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b26ok : f3b26.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b27 : Array Row := #[
  ([49,65,336,378],[465]),
  ([49,67,336,378],[461]),
  ([49,69,83,92],[352,179,216]),
  ([49,69,92,296],[387,231]),
  ([49,69,92,336],[288,232]),
  ([49,71,77,92],[]),
  ([49,71,77,131],[]),
  ([49,71,77,348],[]),
  ([49,71,82,92],[349]),
  ([49,71,83,364],[180,214]),
  ([49,71,86,389],[33,212]),
  ([49,71,92,172],[301,224]),
  ([49,71,92,284],[34]),
  ([49,71,92,285],[]),
  ([49,71,92,296],[363]),
  ([49,71,92,392],[338,236]),
  ([49,71,94,392],[338]),
  ([49,71,96,392],[236]),
  ([49,71,99,392],[338]),
  ([49,71,103,389],[35,212]),
  ([49,71,113,173],[293,225]),
  ([49,71,117,135],[294]),
  ([49,71,118,131],[295]),
  ([49,71,118,348],[]),
  ([49,71,119,390],[]),
  ([49,71,131,172],[302,224]),
  ([49,71,131,238],[36]),
  ([49,71,131,240],[]),
  ([49,71,131,241],[]),
  ([49,71,131,257],[365]),
  ([49,71,131,285],[]),
  ([49,71,131,296],[366])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b27ok : f3b27.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b28 : Array Row := #[
  ([49,71,131,336],[336]),
  ([49,71,131,389],[38,339,234,212]),
  ([49,71,131,391],[340,235]),
  ([49,71,131,392],[343,236]),
  ([49,71,133,336],[336]),
  ([49,71,133,392],[343]),
  ([49,71,135,171],[299]),
  ([49,71,135,334],[310]),
  ([49,71,135,335],[311]),
  ([49,71,135,389],[39,312,212]),
  ([49,71,135,391],[313]),
  ([49,71,148,336],[336]),
  ([49,71,148,392],[343]),
  ([49,71,153,392],[236,221]),
  ([49,71,162,389],[40,44,212]),
  ([49,71,170,340],[]),
  ([49,71,172,378],[221]),
  ([49,71,172,396],[300]),
  ([49,71,173,327],[319]),
  ([49,71,173,328],[320]),
  ([49,71,173,330],[]),
  ([49,71,173,334],[321]),
  ([49,71,173,341],[322,296,209]),
  ([49,71,173,385],[323]),
  ([49,71,181,392],[343,300]),
  ([49,71,182,334],[294,210]),
  ([49,71,192,392],[41]),
  ([49,71,195,327],[293,211]),
  ([49,71,196,390],[42]),
  ([49,71,241,348],[]),
  ([49,71,241,364],[]),
  ([49,71,241,385],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b28ok : f3b28.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b29 : Array Row := #[
  ([49,71,257,348],[367]),
  ([49,71,257,370],[368]),
  ([49,71,285,300],[]),
  ([49,71,285,313],[]),
  ([49,71,285,319],[369]),
  ([49,71,285,327],[]),
  ([49,71,285,348],[]),
  ([49,71,285,364],[]),
  ([49,71,296,370],[370]),
  ([49,71,327,365],[]),
  ([49,71,331,390],[]),
  ([49,71,334,351],[]),
  ([49,71,334,390],[]),
  ([49,71,336,348],[]),
  ([49,71,336,350],[]),
  ([49,71,336,364],[]),
  ([49,71,336,370],[371]),
  ([49,71,336,396],[295,308]),
  ([49,71,340,390],[]),
  ([49,71,343,392],[297,301]),
  ([49,71,348,392],[]),
  ([49,71,350,392],[]),
  ([49,71,352,392],[]),
  ([49,71,357,392],[]),
  ([49,71,364,392],[]),
  ([49,71,370,392],[372]),
  ([49,71,373,392],[]),
  ([49,71,378,392],[222,224]),
  ([49,71,385,392],[]),
  ([49,71,389],[43,29,32,212,212]),
  ([49,71,392,396],[302,309]),
  ([49,76,83,92],[352])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b29ok : f3b29.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b30 : Array Row := #[
  ([49,77,92,274],[]),
  ([49,77,92,378],[344,236]),
  ([49,77,135,378],[]),
  ([49,77,173,378],[]),
  ([49,81,92,173],[347,225]),
  ([49,81,103,365],[]),
  ([49,81,103,390],[]),
  ([49,83,92,271],[182]),
  ([49,83,92,298],[350]),
  ([49,83,92,364],[184,360,226,214]),
  ([49,83,103,364],[185,214]),
  ([49,83,131,260],[241]),
  ([49,83,131,364],[187,361,226,214]),
  ([49,83,135,364],[188,214]),
  ([49,83,142,162],[189,214]),
  ([49,83,143,156],[190,214]),
  ([49,83,153,173],[191,214]),
  ([49,83,162,364],[192,214]),
  ([49,83,162,365],[193]),
  ([49,83,162,377],[194]),
  ([49,83,162,390],[195]),
  ([49,83,173,364],[196,214]),
  ([49,83,173,378],[197]),
  ([49,83,173,382],[198]),
  ([49,83,195,378],[200]),
  ([49,83,364],[202,173,181,214,214]),
  ([49,83,365,369],[203]),
  ([49,83,365,378],[204]),
  ([49,83,378,392],[205,222,224]),
  ([49,86,92,296],[349]),
  ([49,86,131,257],[240]),
  ([49,86,378,392],[222,224])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b30ok : f3b30.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b31 : Array Row := #[
  ([49,92,153,285],[428]),
  ([49,92,153,392],[431,236,221]),
  ([49,92,173,293],[383]),
  ([49,92,195,293],[347]),
  ([49,92,274,285],[]),
  ([49,92,274,296],[]),
  ([49,92,285,293],[]),
  ([49,92,285,378],[459]),
  ([49,92,293,365],[]),
  ([49,92,293,390],[]),
  ([49,92,296,378],[464]),
  ([49,92,378,392],[467,222,224]),
  ([49,96,173,293],[388]),
  ([49,99,173,293],[]),
  ([49,103,135,292],[346,218]),
  ([49,103,142,293],[]),
  ([49,103,153,392],[221]),
  ([49,103,170,293],[]),
  ([49,103,172,378],[221]),
  ([49,103,293,365],[]),
  ([49,103,293,377],[]),
  ([49,103,293,390],[]),
  ([49,103,297,365],[]),
  ([49,103,378,392],[222,224]),
  ([49,118,135,153],[]),
  ([49,118,135,378],[]),
  ([49,118,173,378],[]),
  ([49,118,182,378],[]),
  ([49,118,351,378],[]),
  ([49,120,153,173],[]),
  ([49,120,173,378],[]),
  ([49,120,378,392],[222,224])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b31ok : f3b31.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b32 : Array Row := #[
  ([49,125,378,392],[222,224]),
  ([49,131,153,336],[430]),
  ([49,131,153,392],[432,236,221]),
  ([49,131,172,378],[441,236,221]),
  ([49,131,173,293],[408]),
  ([49,131,241,274],[]),
  ([49,131,241,293],[]),
  ([49,131,241,378],[454]),
  ([49,131,257,274],[]),
  ([49,131,257,378],[456]),
  ([49,131,274,285],[]),
  ([49,131,274,392],[458]),
  ([49,131,285,378],[460]),
  ([49,131,293,392],[463]),
  ([49,131,336,378],[466]),
  ([49,131,378,392],[468,222,224]),
  ([49,135,143,293],[426]),
  ([49,135,153,241],[]),
  ([49,135,153,257],[]),
  ([49,135,153,285],[]),
  ([49,135,153,336],[]),
  ([49,135,153,392],[221]),
  ([49,135,162,256],[238,219]),
  ([49,135,172,378],[221]),
  ([49,135,238,378],[447]),
  ([49,135,241,378],[]),
  ([49,135,257,378],[]),
  ([49,135,257,382],[]),
  ([49,135,285,378],[]),
  ([49,135,293,313],[448]),
  ([49,135,293,334],[449]),
  ([49,135,296,378],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b32ok : f3b32.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b33 : Array Row := #[
  ([49,135,296,382],[]),
  ([49,135,334,378],[450]),
  ([49,135,336,378],[]),
  ([49,135,378,392],[222,224]),
  ([49,140,378,392],[222,224]),
  ([49,153,156,392],[221]),
  ([49,153,162,392],[221]),
  ([49,153,173,189],[191,220,221]),
  ([49,153,173,197],[206,221]),
  ([49,153,173,336],[]),
  ([49,153,182,336],[]),
  ([49,153,336,351],[]),
  ([49,153,378,392],[224,221]),
  ([49,153,392],[221,221]),
  ([49,156,162,172],[221]),
  ([49,156,162,392],[222]),
  ([49,156,173,196],[]),
  ([49,156,378,392],[222,224]),
  ([49,162,172,378],[221]),
  ([49,162,257,365],[]),
  ([49,162,257,377],[]),
  ([49,162,293,365],[]),
  ([49,162,293,390],[]),
  ([49,162,378,392],[222,224]),
  ([49,162,379,392],[]),
  ([49,165,378,392],[222,224]),
  ([49,172,378],[221,221]),
  ([49,172,378,392],[222,221]),
  ([49,173,189,378],[197,224]),
  ([49,173,197,378],[207,224]),
  ([49,173,241,378],[]),
  ([49,173,243,378],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b33ok : f3b33.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b34 : Array Row := #[
  ([49,173,244,378],[]),
  ([49,173,257,378],[]),
  ([49,173,285,378],[]),
  ([49,173,293,327],[451]),
  ([49,173,293,378],[452]),
  ([49,173,327,378],[453]),
  ([49,173,331,378],[]),
  ([49,173,336,378],[]),
  ([49,173,338,378],[]),
  ([49,173,378,392],[222,224]),
  ([49,182,241,378],[]),
  ([49,182,257,378],[]),
  ([49,182,285,378],[]),
  ([49,182,296,378],[]),
  ([49,182,336,378],[]),
  ([49,182,378,392],[222,224]),
  ([49,195,336,378],[]),
  ([49,197,378,392],[208,222,224]),
  ([49,198,378,392],[222,224]),
  ([49,241,351,378],[]),
  ([49,241,355,378],[]),
  ([49,241,365,378],[]),
  ([49,241,378,386],[]),
  ([49,257,351,378],[]),
  ([49,257,371,378],[]),
  ([49,274,285,348],[]),
  ([49,274,336,348],[]),
  ([49,285,336,378],[]),
  ([49,285,343,378],[344,402,428]),
  ([49,285,348,378],[]),
  ([49,285,351,378],[]),
  ([49,289,336,378],[345,401,429])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b34ok : f3b34.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b35 : Array Row := #[
  ([49,293,317,365],[]),
  ([49,293,331,365],[]),
  ([49,293,340,390],[]),
  ([49,336,348,378],[]),
  ([49,336,351,378],[]),
  ([49,336,355,378],[]),
  ([49,336,358,378],[]),
  ([49,336,365,378],[]),
  ([49,336,371,378],[]),
  ([49,336,378,386],[]),
  ([49,351,378,392],[222,224]),
  ([49,361,378,392],[222,224]),
  ([49,378,392],[222,224,222,224]),
  ([49,378,392,396],[432,441,446,222,224]),
  ([53,71,103,135],[238]),
  ([53,81,103,135],[348,239]),
  ([53,103,135,293],[400]),
  ([54,81,103,135],[]),
  ([54,86,135,162],[238,240]),
  ([54,103,135,293],[]),
  ([55,81,103,135],[]),
  ([55,83,135,162],[238,241]),
  ([55,103,135,293],[]),
  ([56,58,71,327],[291,54]),
  ([56,58,92,293],[373,252]),
  ([56,71,92,283],[56]),
  ([56,71,103,385],[57,243]),
  ([56,71,113,135],[293,251]),
  ([56,71,116,386],[]),
  ([56,71,131,293],[247]),
  ([56,71,131,385],[59,318,254,243]),
  ([56,71,135,328],[320])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b35ok : f3b35.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b36 : Array Row := #[
  ([56,71,135,334],[321]),
  ([56,71,135,341],[322]),
  ([56,71,135,385],[60,323,243]),
  ([56,71,162,385],[61,65,243]),
  ([56,71,167,331],[]),
  ([56,71,173,327],[319]),
  ([56,71,182,327],[319]),
  ([56,71,195,327],[293,242]),
  ([56,71,196,386],[62]),
  ([56,71,327,351],[]),
  ([56,71,327,386],[]),
  ([56,71,331,386],[]),
  ([56,71,340,390],[]),
  ([56,71,347,394],[]),
  ([56,71,385],[63,53,55,243,243]),
  ([56,71,392,396],[64,302,309]),
  ([56,81,92,135],[347,251]),
  ([56,81,103,135],[]),
  ([56,81,103,386],[]),
  ([56,81,135,162],[238,247]),
  ([56,81,135,196],[239,247]),
  ([56,81,135,331],[]),
  ([56,83,86,131],[240,241,247]),
  ([56,92,135,293],[383]),
  ([56,92,173,293],[383]),
  ([56,92,182,293],[383]),
  ([56,92,195,293],[347]),
  ([56,92,293,351],[]),
  ([56,92,293,386],[]),
  ([56,96,135,293],[388]),
  ([56,97,135,293],[]),
  ([56,99,135,293],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b36ok : f3b36.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b37 : Array Row := #[
  ([56,101,135,293],[]),
  ([56,103,131,293],[247]),
  ([56,103,135,292],[346,248]),
  ([56,103,135,293],[]),
  ([56,103,167,293],[]),
  ([56,103,293,351],[]),
  ([56,103,293,365],[]),
  ([56,103,293,371],[]),
  ([56,103,293,377],[]),
  ([56,103,293,386],[]),
  ([56,103,293,390],[]),
  ([56,103,293,394],[]),
  ([56,116,135,293],[]),
  ([56,131,135,293],[408,247]),
  ([56,131,162,293],[247]),
  ([56,131,293],[407,247,247]),
  ([56,135,162,256],[238,249]),
  ([56,135,162,293],[250]),
  ([56,135,196,293],[250]),
  ([56,135,293,309],[]),
  ([56,135,293,317],[]),
  ([56,135,293,323],[]),
  ([56,135,293,326],[]),
  ([56,135,293,327],[451]),
  ([56,135,293,331],[]),
  ([56,135,293,340],[]),
  ([56,135,293,347],[]),
  ([56,135,293,361],[]),
  ([56,135,293,378],[452]),
  ([56,135,327,378],[453]),
  ([56,162,293,386],[]),
  ([56,293,331,386],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b37ok : f3b37.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b38 : Array Row := #[
  ([58,71,118,343],[338]),
  ([58,71,123,336],[336]),
  ([58,71,336,343],[]),
  ([58,71,392,396],[458,302,309]),
  ([58,83,92,260],[356]),
  ([58,86,92,257],[367]),
  ([58,103,135,256],[418,255]),
  ([58,274,336,343],[]),
  ([58,285,343,378],[344,402,428]),
  ([58,289,336,378],[345,401,429]),
  ([58,336,343,378],[]),
  ([59,71,336,343],[]),
  ([60,71,336,343],[]),
  ([65,71,336,343],[]),
  ([65,83,92,298],[359,350]),
  ([65,83,92,343],[360,264]),
  ([65,103,135,247],[258]),
  ([65,103,135,292],[423,394,346,259]),
  ([67,71,336,343],[]),
  ([67,86,92,296],[370,349]),
  ([67,86,92,336],[371,275]),
  ([67,103,135,238],[269]),
  ([67,103,135,292],[424,395,346,270]),
  ([69,103,135,292],[425,396,346,279]),
  ([71,77,92,289],[]),
  ([71,77,92,343],[344,338]),
  ([71,79,92,285],[]),
  ([71,79,92,336],[345,336]),
  ([71,83,92,298],[350]),
  ([71,83,131,260],[241]),
  ([71,83,173,341],[257,289,296]),
  ([71,83,392,396],[302,309])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b38ok : f3b38.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b39 : Array Row := #[
  ([71,86,92,296],[349]),
  ([71,86,131,257],[240]),
  ([71,86,182,334],[268,290,294]),
  ([71,86,392,396],[302,309]),
  ([71,92,118,289],[401]),
  ([71,92,123,285],[402]),
  ([71,92,135,256],[419,255]),
  ([71,92,173,247],[442,258]),
  ([71,92,173,341],[445,260,296]),
  ([71,92,182,238],[447,269]),
  ([71,92,182,334],[450,271,294]),
  ([71,92,195,293],[452,347]),
  ([71,92,195,327],[453,280,293]),
  ([71,92,241,289],[]),
  ([71,92,250,285],[]),
  ([71,92,257,289],[]),
  ([71,92,260,285],[]),
  ([71,92,285,289],[]),
  ([71,92,285,298],[]),
  ([71,92,285,343],[459]),
  ([71,92,289,296],[]),
  ([71,92,289,336],[461]),
  ([71,92,296,343],[464]),
  ([71,92,298,336],[465]),
  ([71,92,336,396],[466,295,308]),
  ([71,92,343,392],[467,297,301]),
  ([71,92,392,396],[468,302,309]),
  ([71,103,135,256],[415]),
  ([71,103,135,292],[416,346,292]),
  ([71,103,172,396],[300]),
  ([71,103,173,341],[261,296]),
  ([71,103,181,392],[300])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b39ok : f3b39.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b40 : Array Row := #[
  ([71,103,182,334],[272,294]),
  ([71,103,195,327],[281,293]),
  ([71,103,238,371],[433]),
  ([71,103,247,365],[434]),
  ([71,103,256,365],[435]),
  ([71,103,256,371],[436]),
  ([71,103,256,377],[437]),
  ([71,103,256,386],[438]),
  ([71,103,256,390],[439]),
  ([71,103,256,394],[440]),
  ([71,103,336,396],[295,308]),
  ([71,103,343,392],[297,301]),
  ([71,103,392,396],[302,309]),
  ([71,116,173,182],[]),
  ([71,118,123,135],[]),
  ([71,118,125,182],[]),
  ([71,118,135,343],[]),
  ([71,118,173,343],[]),
  ([71,118,182,343],[]),
  ([71,118,343,351],[]),
  ([71,120,123,173],[]),
  ([71,120,173,343],[]),
  ([71,120,173,396],[295]),
  ([71,120,392,396],[302,309]),
  ([71,123,135,336],[]),
  ([71,123,173,336],[]),
  ([71,123,182,336],[]),
  ([71,123,336,351],[]),
  ([71,125,182,336],[]),
  ([71,125,182,392],[297]),
  ([71,125,392,396],[302,309]),
  ([71,127,135,327],[319])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b40ok : f3b40.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b41 : Array Row := #[
  ([71,131,172,396],[441,343,300]),
  ([71,131,181,392],[446,343,300]),
  ([71,131,241,250],[]),
  ([71,131,241,260],[]),
  ([71,131,241,396],[454]),
  ([71,131,250,257],[]),
  ([71,131,250,392],[455]),
  ([71,131,257,396],[456]),
  ([71,131,260,392],[457]),
  ([71,131,285,289],[]),
  ([71,131,285,396],[460]),
  ([71,131,289,392],[462]),
  ([71,131,336,343],[]),
  ([71,131,336,396],[466,295,308]),
  ([71,131,343,392],[467,297,301]),
  ([71,131,392,396],[468,302,309]),
  ([71,135,162,256],[238,298]),
  ([71,135,172,396],[300]),
  ([71,135,173,341],[262,296]),
  ([71,135,181,392],[300]),
  ([71,135,182,334],[273,294]),
  ([71,135,195,327],[282,293]),
  ([71,135,256,317],[]),
  ([71,135,256,323],[]),
  ([71,135,256,326],[]),
  ([71,135,256,331],[]),
  ([71,135,256,340],[]),
  ([71,135,256,347],[]),
  ([71,135,257,327],[]),
  ([71,135,257,341],[]),
  ([71,135,260,327],[]),
  ([71,135,260,334],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b41ok : f3b41.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b42 : Array Row := #[
  ([71,135,334,343],[]),
  ([71,135,336,341],[]),
  ([71,135,336,343],[]),
  ([71,135,336,396],[295,308]),
  ([71,135,343,392],[297,301]),
  ([71,135,392,396],[302,309]),
  ([71,140,392,396],[302,309]),
  ([71,156,392,396],[302,309]),
  ([71,162,172,396],[300]),
  ([71,162,181,392],[300]),
  ([71,162,336,396],[295,308]),
  ([71,162,343,392],[297,301]),
  ([71,162,392,396],[302,309]),
  ([71,165,392,396],[302,309]),
  ([71,172,392,396],[309,300]),
  ([71,172,396],[300,300]),
  ([71,173,182,196],[299,303]),
  ([71,173,182,327],[319]),
  ([71,173,182,329],[]),
  ([71,173,182,330],[]),
  ([71,173,182,331],[]),
  ([71,173,182,340],[]),
  ([71,173,182,347],[]),
  ([71,173,189,343],[264,301]),
  ([71,173,195,327],[283,293]),
  ([71,173,197,343],[301]),
  ([71,173,197,396],[302]),
  ([71,173,250,327],[]),
  ([71,173,327,343],[]),
  ([71,173,331,343],[]),
  ([71,173,336,343],[]),
  ([71,173,339,343],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b42ok : f3b42.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b43 : Array Row := #[
  ([71,173,341],[265,256,263,296,296]),
  ([71,173,347,394],[266]),
  ([71,173,392,396],[302,309]),
  ([71,181,392],[300,300]),
  ([71,181,392,396],[302,300]),
  ([71,182,192,336],[275,308]),
  ([71,182,195,327],[284,293]),
  ([71,182,198,336],[308]),
  ([71,182,198,392],[309]),
  ([71,182,241,327],[]),
  ([71,182,327,336],[]),
  ([71,182,331,336],[]),
  ([71,182,334],[276,267,274,294,294]),
  ([71,182,336,343],[]),
  ([71,182,336,346],[]),
  ([71,182,340,390],[277]),
  ([71,182,392,396],[302,309]),
  ([71,195,327],[286,278,285,293,293]),
  ([71,195,331,386],[287]),
  ([71,195,336,343],[288]),
  ([71,197,392,396],[302,309]),
  ([71,198,392,396],[302,309]),
  ([71,257,331,386],[]),
  ([71,257,347,394],[]),
  ([71,260,331,386],[]),
  ([71,260,340,390],[]),
  ([71,285,289,348],[]),
  ([71,285,336,343],[]),
  ([71,285,343,348],[]),
  ([71,285,343,378],[344,402,428]),
  ([71,289,336,343],[]),
  ([71,289,336,348],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b43ok : f3b43.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b44 : Array Row := #[
  ([71,289,336,378],[345,401,429]),
  ([71,336,343,348],[]),
  ([71,336,343,351],[]),
  ([71,336,343,355],[]),
  ([71,336,343,358],[]),
  ([71,336,343,365],[]),
  ([71,336,343,371],[]),
  ([71,336,343,386],[]),
  ([71,336,396],[295,308,295,308]),
  ([71,343,392],[297,301,297,301]),
  ([71,351,392,396],[302,309]),
  ([71,361,392,396],[302,309]),
  ([71,378,392,396],[432,441,446,302,309]),
  ([71,392,396],[302,309,302,309]),
  ([81,103,135,195],[346,347]),
  ([81,103,135,257],[]),
  ([81,103,135,260],[]),
  ([81,103,173,182],[]),
  ([82,86,103,135],[346,349]),
  ([83,85,103,135],[346,350]),
  ([83,86,92,195],[347,349,350]),
  ([83,92,103,298],[350]),
  ([83,92,135,298],[350]),
  ([83,92,173,298],[350]),
  ([83,92,298],[379,350,350]),
  ([83,97,135,298],[352]),
  ([83,103,131,260],[241]),
  ([83,103,135,292],[346,351]),
  ([83,103,135,298],[352]),
  ([83,103,298,365],[]),
  ([83,131,135,260],[241]),
  ([83,131,162,260],[241])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b44ok : f3b44.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b45 : Array Row := #[
  ([83,131,260],[405,241,241]),
  ([83,135,162,256],[238,353]),
  ([83,135,162,260],[354]),
  ([83,135,162,298],[355]),
  ([83,135,260,361],[]),
  ([83,135,260,378],[]),
  ([83,135,298,369],[]),
  ([83,162,260,365],[]),
  ([83,173,343,378],[344]),
  ([86,92,103,296],[349]),
  ([86,92,135,296],[349]),
  ([86,92,182,296],[349]),
  ([86,92,296],[381,349,349]),
  ([86,99,135,296],[363]),
  ([86,103,131,257],[240]),
  ([86,103,135,292],[346,362]),
  ([86,103,135,296],[363]),
  ([86,103,296,371],[]),
  ([86,131,135,257],[240]),
  ([86,131,162,257],[240]),
  ([86,131,257],[406,240,240]),
  ([86,135,162,256],[238,364]),
  ([86,135,162,257],[365]),
  ([86,135,162,296],[366]),
  ([86,135,257,361],[]),
  ([86,135,257,378],[]),
  ([86,135,296,375],[]),
  ([86,162,257,371],[]),
  ([86,182,336,378],[345]),
  ([88,103,135,293],[373]),
  ([92,103,195,293],[347]),
  ([92,127,135,293],[383])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b45ok : f3b45.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b46 : Array Row := #[
  ([92,135,195,293],[347]),
  ([92,135,257,293],[]),
  ([92,135,260,293],[]),
  ([92,173,182,293],[383]),
  ([92,173,195,293],[347]),
  ([92,173,250,293],[]),
  ([92,173,293,343],[]),
  ([92,182,195,293],[347]),
  ([92,182,241,293],[]),
  ([92,182,293,336],[]),
  ([92,195,293],[347,347]),
  ([92,274,285,289],[]),
  ([92,274,285,343],[]),
  ([92,274,289,336],[]),
  ([92,285,289,378],[]),
  ([92,285,343,378],[344,402,428]),
  ([92,289,336,378],[345,401,429]),
  ([97,135,195,293],[383]),
  ([97,173,182,293],[]),
  ([99,135,195,293],[383]),
  ([99,173,182,293],[]),
  ([101,135,195,293],[383]),
  ([103,127,135,293],[]),
  ([103,135,162,256],[238,392]),
  ([103,135,173,292],[376,389,346]),
  ([103,135,182,292],[377,390,346]),
  ([103,135,188,293],[378]),
  ([103,135,191,293],[380]),
  ([103,135,195,292],[382,391,346]),
  ([103,135,195,293],[383]),
  ([103,135,256,274],[]),
  ([103,135,256,293],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b46ok : f3b46.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b47 : Array Row := #[
  ([103,135,257,293],[]),
  ([103,135,257,299],[]),
  ([103,135,258,293],[]),
  ([103,135,260,293],[]),
  ([103,135,260,297],[]),
  ([103,135,261,293],[]),
  ([103,135,263,293],[]),
  ([103,135,264,293],[]),
  ([103,135,292],[384,374,375,346,346]),
  ([103,135,293,296],[385]),
  ([103,135,293,298],[386]),
  ([103,135,296,298],[387]),
  ([103,156,195,293],[388]),
  ([103,173,182,293],[]),
  ([103,173,293,343],[]),
  ([103,173,293,371],[]),
  ([103,173,293,394],[]),
  ([103,182,293,336],[]),
  ([103,182,293,365],[]),
  ([103,182,293,390],[]),
  ([103,195,293,386],[]),
  ([103,241,293,371],[]),
  ([103,250,293,365],[]),
  ([103,257,293,371],[]),
  ([103,257,293,386],[]),
  ([103,257,293,394],[]),
  ([103,260,293,365],[]),
  ([103,260,293,386],[]),
  ([103,260,293,390],[]),
  ([103,285,343,378],[344,402,428]),
  ([103,289,336,378],[345,401,429]),
  ([103,378,392,396],[432,441,446])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b47ok : f3b47.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b48 : Array Row := #[
  ([118,135,343,378],[]),
  ([120,173,343,378],[]),
  ([123,135,336,378],[]),
  ([125,182,336,378],[]),
  ([131,378,392,396],[432,441,446]),
  ([135,153,336,343],[]),
  ([135,162,195,293],[408]),
  ([135,162,256],[409,403,404,238,238]),
  ([135,162,257,260],[410]),
  ([135,162,257,293],[411]),
  ([135,162,260,293],[412]),
  ([135,162,263,293],[413]),
  ([135,162,264,293],[414]),
  ([135,195,293,331],[]),
  ([135,241,250,378],[]),
  ([135,241,260,378],[]),
  ([135,241,343,378],[]),
  ([135,250,257,378],[]),
  ([135,250,336,378],[]),
  ([135,257,293,323],[]),
  ([135,257,293,331],[]),
  ([135,257,293,347],[]),
  ([135,257,343,378],[]),
  ([135,260,293,317],[]),
  ([135,260,293,331],[]),
  ([135,260,293,340],[]),
  ([135,260,336,378],[]),
  ([135,274,336,343],[]),
  ([135,285,289,378],[]),
  ([135,285,343,378],[344,402,428]),
  ([135,289,336,378],[345,401,429]),
  ([135,293,336,343],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b48ok : f3b48.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def f3b49 : Array Row := #[
  ([135,336,343,378],[]),
  ([135,378,392,396],[432,441,446]),
  ([156,162,392,396],[432]),
  ([162,173,182,293],[426,427]),
  ([162,378,392,396],[432,441,446]),
  ([173,182,293,331],[]),
  ([173,336,343,378],[]),
  ([182,336,343,378],[]),
  ([285,343,378],[344,402,344,428,402,428]),
  ([289,336,378],[345,401,345,429,401,429]),
  ([336,343,351,378],[]),
  ([378,392,396],[432,441,432,446,441,446])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f3b49ok : f3b49.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true := by decide +kernel

private def layer3 (i : ℕ) : {s : List W // impossible 3 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer2 i).1) 2) = true} :=
    #[⟨f3b0, f3b0ok⟩, ⟨f3b1, f3b1ok⟩, ⟨f3b2, f3b2ok⟩, ⟨f3b3, f3b3ok⟩, ⟨f3b4, f3b4ok⟩, ⟨f3b5, f3b5ok⟩, ⟨f3b6, f3b6ok⟩, ⟨f3b7, f3b7ok⟩, ⟨f3b8, f3b8ok⟩, ⟨f3b9, f3b9ok⟩, ⟨f3b10, f3b10ok⟩, ⟨f3b11, f3b11ok⟩, ⟨f3b12, f3b12ok⟩, ⟨f3b13, f3b13ok⟩, ⟨f3b14, f3b14ok⟩, ⟨f3b15, f3b15ok⟩, ⟨f3b16, f3b16ok⟩, ⟨f3b17, f3b17ok⟩, ⟨f3b18, f3b18ok⟩, ⟨f3b19, f3b19ok⟩, ⟨f3b20, f3b20ok⟩, ⟨f3b21, f3b21ok⟩, ⟨f3b22, f3b22ok⟩, ⟨f3b23, f3b23ok⟩, ⟨f3b24, f3b24ok⟩, ⟨f3b25, f3b25ok⟩, ⟨f3b26, f3b26ok⟩, ⟨f3b27, f3b27ok⟩, ⟨f3b28, f3b28ok⟩, ⟨f3b29, f3b29ok⟩, ⟨f3b30, f3b30ok⟩, ⟨f3b31, f3b31ok⟩, ⟨f3b32, f3b32ok⟩, ⟨f3b33, f3b33ok⟩, ⟨f3b34, f3b34ok⟩, ⟨f3b35, f3b35ok⟩, ⟨f3b36, f3b36ok⟩, ⟨f3b37, f3b37ok⟩, ⟨f3b38, f3b38ok⟩, ⟨f3b39, f3b39ok⟩, ⟨f3b40, f3b40ok⟩, ⟨f3b41, f3b41ok⟩, ⟨f3b42, f3b42ok⟩, ⟨f3b43, f3b43ok⟩, ⟨f3b44, f3b44ok⟩, ⟨f3b45, f3b45ok⟩, ⟨f3b46, f3b46ok⟩, ⟨f3b47, f3b47ok⟩, ⟨f3b48, f3b48ok⟩, ⟨f3b49, f3b49ok⟩]
  pick alphabet layer2 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f4b0 : Array Row := #[
  ([0,39,49,71,131],[892,538,394,379]),
  ([0,39,49,71,348],[925,571,454,375]),
  ([0,39,49,131,274],[1029,675,454,375]),
  ([0,39,49,131,378],[1031,677,459,392,1,0]),
  ([0,39,49,135,153],[1041,687,427,404]),
  ([0,39,49,135,378],[1049,695,462,402]),
  ([0,39,49,173,378],[1086,728,423]),
  ([0,39,49,182,378],[1098,738,424]),
  ([0,39,49,351,378],[1107,753,404,427]),
  ([0,39,71,92,289],[1261,642,576,515]),
  ([0,39,71,131,250],[1314,675,571,375]),
  ([0,39,71,131,396],[1316,681,594,535,2,0]),
  ([0,39,135,250,378],[1550,753,404,687]),
  ([0,39,135,343,378],[1552,770,664,690]),
  ([0,49,71,92,285],[1262,996,930,869]),
  ([0,49,71,131,241],[1314,1029,925,375]),
  ([0,49,71,131,392],[1318,1035,948,889,2,1]),
  ([0,49,135,241,378],[1550,1107,404,1041]),
  ([0,49,135,336,378],[1554,1124,1017,1044]),
  ([0,56,103,135,293],[1203,1189,1169]),
  ([0,71,135,336,343],[1563,1410,1296,1304]),
  ([1,39,49,71,348],[925,375]),
  ([1,39,49,131,378],[1031,460,392,4,3]),
  ([1,39,49,135,153],[1041,427]),
  ([1,39,49,135,378],[1049,462,402]),
  ([1,39,49,173,378],[1086,423]),
  ([1,39,49,182,378],[1098,424]),
  ([1,39,49,351,378],[1107,404,427]),
  ([1,39,71,92,289],[1261,515]),
  ([1,39,71,131,396],[1316,595,535,5,3]),
  ([1,39,135,343,378],[1552,770,664,690]),
  ([1,49,71,92,285],[869])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b0ok : f4b0.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b1 : Array Row := #[
  ([1,49,71,131,241],[375]),
  ([1,49,71,131,392],[889,5,4]),
  ([1,49,135,241,378],[1107,404,1041]),
  ([1,49,135,336,378],[1124,1017,1044]),
  ([1,56,103,135,293],[1189,1169]),
  ([1,71,135,336,343],[1410,1296,1304]),
  ([2,39,49,71,348],[571,375]),
  ([2,39,49,131,378],[677,461,392,7,6]),
  ([2,39,49,135,153],[687,427]),
  ([2,39,49,135,378],[695,462,402]),
  ([2,39,49,173,378],[728,423]),
  ([2,39,49,182,378],[738,424]),
  ([2,39,49,351,378],[753,404,427]),
  ([2,39,71,92,289],[515]),
  ([2,39,71,131,250],[375]),
  ([2,39,71,131,396],[535,8,6]),
  ([2,39,135,250,378],[753,404,687]),
  ([2,39,135,343,378],[770,664,690]),
  ([2,49,71,92,285],[1262,869]),
  ([2,49,71,131,392],[1318,949,889,8,7]),
  ([2,49,135,336,378],[1554,1124,1017,1044]),
  ([2,56,103,135,293],[1189,1169]),
  ([2,71,135,336,343],[1410,1296,1304]),
  ([3,39,49,71,131],[]),
  ([3,39,49,135,378],[462,402]),
  ([3,56,103,135,293],[1189,1169]),
  ([4,39,49,71,348],[454,375]),
  ([4,39,49,131,274],[375]),
  ([4,39,49,131,378],[392,10,9]),
  ([4,39,49,135,153],[404]),
  ([4,39,49,135,378],[402]),
  ([4,39,49,173,378],[1087,423])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b1ok : f4b1.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b2 : Array Row := #[
  ([4,39,49,182,378],[739,424]),
  ([4,39,49,351,378],[404,427]),
  ([4,39,71,92,289],[642,515]),
  ([4,39,71,131,396],[681,596,535,11,9]),
  ([4,39,135,343,378],[664,690]),
  ([4,49,71,92,285],[996,869]),
  ([4,49,71,131,392],[1035,950,889,11,10]),
  ([4,49,135,336,378],[1017,1044]),
  ([4,56,103,135,293],[1203,1169]),
  ([4,71,135,336,343],[1563,1296,1304]),
  ([5,39,49,71,131],[892]),
  ([5,39,49,71,348],[925,375]),
  ([5,39,49,131,378],[1031,463,392,13,12]),
  ([5,39,49,135,153],[1041,428]),
  ([5,39,49,135,378],[1049,464,402]),
  ([5,39,49,173,378],[1086,423]),
  ([5,39,49,182,378],[1098,740,448,424]),
  ([5,39,49,351,378],[1107,404,427]),
  ([5,39,49,355,378],[1108,406,428]),
  ([5,39,71,92,289],[1261,515]),
  ([5,39,71,131,396],[1316,597,535,14,12]),
  ([5,39,135,343,378],[1552,771,664,690]),
  ([5,49,71,92,285],[869]),
  ([5,49,71,131,241],[375]),
  ([5,49,71,131,392],[889,14,13]),
  ([5,49,135,241,378],[1108,404,1041]),
  ([5,49,135,336,378],[1125,1017,1044]),
  ([5,56,103,135,293],[1203,1169]),
  ([5,71,135,336,343],[1411,1296,1304]),
  ([6,39,49,71,131],[892]),
  ([6,39,49,135,378],[1049,464,402]),
  ([7,39,49,71,131],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b2ok : f4b2.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b3 : Array Row := #[
  ([7,39,49,135,378],[402]),
  ([8,39,49,71,131],[538]),
  ([8,39,49,71,348],[571,375]),
  ([8,39,49,131,378],[677,465,392,16,15]),
  ([8,39,49,135,153],[687,429]),
  ([8,39,49,135,378],[695,466,402]),
  ([8,39,49,173,378],[1088,728,444,423]),
  ([8,39,49,182,378],[738,424]),
  ([8,39,49,351,378],[753,404,427]),
  ([8,39,49,358,378],[754,407,429]),
  ([8,39,71,92,289],[515]),
  ([8,39,71,131,250],[375]),
  ([8,39,71,131,396],[535,17,15]),
  ([8,39,135,250,378],[754,404,687]),
  ([8,39,135,343,378],[772,664,690]),
  ([8,49,71,92,285],[1262,869]),
  ([8,49,71,131,392],[1318,951,889,17,16]),
  ([8,49,135,336,378],[1554,1126,1017,1044]),
  ([8,56,103,135,293],[1203,1169]),
  ([8,71,135,336,343],[1412,1296,1304]),
  ([9,39,49,71,131],[538]),
  ([9,39,49,135,378],[695,466,402]),
  ([10,39,49,71,131],[]),
  ([10,39,49,135,378],[402]),
  ([11,39,49,71,131],[]),
  ([11,39,49,135,378],[467,402]),
  ([11,56,103,135,293],[1203,1169]),
  ([14,19,28,135,162],[230,104,67,57,20,18]),
  ([14,19,39,49,131],[393,90,84,44,23,18]),
  ([14,28,49,71,131],[890,206,156,45,39,18]),
  ([14,28,49,135,378],[1048,235,161,21]),
  ([14,28,67,103,135],[1237,223,55,19])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b3ok : f4b3.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b4 : Array Row := #[
  ([14,28,71,92,182],[1257,215,195,54,48,21,19]),
  ([14,28,71,103,371],[1282,20]),
  ([14,39,44,135,162],[692,354,22]),
  ([14,39,49,67,92],[509,389,371,19,23]),
  ([14,39,49,71,131],[892,539,394,380,40]),
  ([14,39,49,71,348],[925,574,454,375,41]),
  ([14,39,49,71,364],[926,575,455,376,42]),
  ([14,39,49,83,131],[614,387,22]),
  ([14,39,49,131,274],[1029,678,455,375]),
  ([14,39,49,131,378],[1031,679,468,392,46,24]),
  ([14,39,49,135,153],[1041,688,430,404]),
  ([14,39,49,135,378],[1049,696,469,402]),
  ([14,39,49,135,381],[697,470]),
  ([14,39,49,162,371],[721,20]),
  ([14,39,49,173,378],[1086,729,423]),
  ([14,39,49,182,378],[1098,741,450,424,21]),
  ([14,39,49,351,378],[1107,757,404,427]),
  ([14,39,49,365,378],[1109,758,411,430]),
  ([14,39,71,92,289],[1261,642,577,515,51]),
  ([14,39,71,131,260],[1315,678,575,489,52]),
  ([14,39,71,131,396],[1316,681,598,535,53,50,24]),
  ([14,39,135,260,378],[1551,758,490,688]),
  ([14,39,135,343,378],[1552,773,664,690]),
  ([14,44,49,135,162],[1046,781,25]),
  ([14,44,58,103,135],[1222,825,55,35,26]),
  ([14,44,71,92,135],[1254,815,804,47,36,26]),
  ([14,44,71,103,365],[1284,829,819,807,37]),
  ([14,44,71,103,394],[1289,56,49,38]),
  ([14,44,71,135,162],[1328,816,27]),
  ([14,44,71,135,317],[1334,819]),
  ([14,44,71,135,347],[1339,820,49]),
  ([14,44,83,135,162],[1441,821,28])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b4ok : f4b4.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b5 : Array Row := #[
  ([14,44,103,135,162],[1495,827,29]),
  ([14,44,103,135,274],[1502,829]),
  ([14,44,103,135,293],[1503,830,56]),
  ([14,44,135,162],[1543,58,831,837,37,832,38,34,30,31,32]),
  ([14,49,58,83,92],[1220,967,849,51,26,41]),
  ([14,49,71,83,131],[1245,873,27]),
  ([14,49,71,92,285],[1264,996,931,869]),
  ([14,49,71,131,241],[1315,1029,926,375]),
  ([14,49,71,131,392],[1320,1035,952,889,50,46]),
  ([14,49,71,135,327],[1342,937,48]),
  ([14,49,71,331,386],[1400]),
  ([14,49,81,103,135],[1424,965]),
  ([14,49,83,103,131],[1434,970,29]),
  ([14,49,83,131],[1440,52,971,985,42,972,30,25,28,53,43]),
  ([14,49,83,131,135],[1438,973,31]),
  ([14,49,83,131,162],[1439,977,32]),
  ([14,49,83,135,162],[1442,978,33,40]),
  ([14,49,83,135,361],[1444,35]),
  ([14,49,83,135,378],[1445,987,36]),
  ([14,49,83,162,365],[1447,974,37]),
  ([14,49,92,135,293],[1474,1053,1000,54]),
  ([14,49,103,135,293],[1507,1011]),
  ([14,49,103,135,297],[1508,1014]),
  ([14,49,103,293,365],[1530,1120,965,1007]),
  ([14,49,103,293,386],[1531]),
  ([14,49,135,162,257],[1544,1075,44]),
  ([14,49,135,162,293],[1546,1077,45]),
  ([14,49,135,241,378],[1551,1109,404,1041]),
  ([14,49,135,293,317],[1559,1120]),
  ([14,49,135,293,331],[1560,1121]),
  ([14,49,135,336,378],[1562,1127,1017,1044]),
  ([14,56,103,135,293],[1204,1190,1169])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b5ok : f4b5.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b6 : Array Row := #[
  ([14,71,103,135,247],[1283,57]),
  ([14,71,103,135,256],[1502,1334,1284,1134,58]),
  ([14,71,135,336,343],[1563,1413,1296,1304]),
  ([14,83,103,135,289],[51]),
  ([14,83,135,162,260],[1447,1141,52]),
  ([14,103,135,182,293],[1522,1499,54]),
  ([14,103,135,250,293],[1526]),
  ([14,103,135,260,293],[1559,1530,1142,1424]),
  ([15,39,49,71,131],[892]),
  ([15,39,49,135,153],[1041,430]),
  ([15,39,49,135,378],[1049,469,402]),
  ([15,44,71,103,135],[808,59]),
  ([15,49,83,135,162],[978,59]),
  ([15,49,103,135,293],[1509,1011]),
  ([16,39,49,71,131],[394]),
  ([16,39,49,135,378],[402]),
  ([17,28,49,71,131],[891,208,63,62]),
  ([17,39,49,71,131],[892]),
  ([17,39,49,131,378],[1031,471,392,64,60]),
  ([17,39,49,135,153],[1041,431]),
  ([17,39,49,135,378],[1049,472,402]),
  ([17,39,71,131,396],[1316,599,535,65,60]),
  ([17,44,71,103,135],[]),
  ([17,44,71,135,162],[33,61]),
  ([17,49,71,83,131],[40,61]),
  ([17,49,71,131,241],[375]),
  ([17,49,71,131,392],[889,65,64]),
  ([17,49,103,135,293],[1511]),
  ([17,49,135,162,293],[1548,63]),
  ([18,39,49,71,131],[892]),
  ([19,28,39,71,131],[536,205,148,91,85,18]),
  ([19,28,39,135,378],[694,234,153,68])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b6ok : f4b6.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b7 : Array Row := #[
  ([19,28,65,103,135],[1232,223,102,66]),
  ([19,28,71,92,173],[1255,214,194,101,95,68,66]),
  ([19,28,71,103,365],[1283,67]),
  ([19,35,39,135,162],[692,257,69]),
  ([19,35,49,135,162],[1046,270,70]),
  ([19,35,58,103,135],[1222,317,102,80,71]),
  ([19,35,71,92,135],[1254,307,296,94,81,71]),
  ([19,35,71,103,371],[1285,321,311,299,82]),
  ([19,35,71,103,390],[1288,103,96,83]),
  ([19,35,71,135,162],[1328,308,72]),
  ([19,35,71,135,323],[1335,311]),
  ([19,35,71,135,340],[1338,312,96]),
  ([19,35,86,135,162],[1461,313,73]),
  ([19,35,103,135,162],[1495,319,74]),
  ([19,35,103,135,274],[1502,321]),
  ([19,35,103,135,293],[1503,322,103]),
  ([19,35,135,162],[1543,105,323,329,82,324,83,79,75,76,77]),
  ([19,39,49,65,92],[862,389,370,66,84]),
  ([19,39,49,71,131],[893,538,394,381,86]),
  ([19,39,49,71,348],[928,571,454,375,87]),
  ([19,39,49,71,370],[929,572,456,377,88]),
  ([19,39,49,86,131],[990,388,70]),
  ([19,39,49,131,274],[1032,675,456,375]),
  ([19,39,49,131,378],[1033,677,473,392,93,92]),
  ([19,39,49,135,153],[1042,687,432,404]),
  ([19,39,49,135,378],[1050,695,474,402]),
  ([19,39,49,135,382],[1051,475]),
  ([19,39,49,162,365],[1075,67]),
  ([19,39,49,173,378],[1089,728,449,423,68]),
  ([19,39,49,182,378],[1099,738,424]),
  ([19,39,49,351,378],[1111,753,404,427]),
  ([19,39,49,371,378],[1112,755,418,432])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b7ok : f4b7.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b8 : Array Row := #[
  ([19,39,58,86,92],[1221,616,495,98,71,87]),
  ([19,39,71,86,131],[1249,520,72]),
  ([19,39,71,92,289],[1263,642,578,515]),
  ([19,39,71,131,250],[1317,675,572,375]),
  ([19,39,71,131,396],[1319,681,600,535,97,92]),
  ([19,39,71,135,327],[1340,583,95]),
  ([19,39,71,331,386],[1398]),
  ([19,39,81,103,135],[1423,611]),
  ([19,39,86,103,131],[1454,619,74]),
  ([19,39,86,131],[1460,99,620,634,88,621,75,69,73,100,89]),
  ([19,39,86,131,135],[1458,622,76]),
  ([19,39,86,131,162],[1459,626,77]),
  ([19,39,86,135,162],[1462,627,78,86]),
  ([19,39,86,135,361],[1464,80]),
  ([19,39,86,135,378],[1465,636,81]),
  ([19,39,86,162,371],[1467,623,82]),
  ([19,39,92,135,293],[1473,699,646,101]),
  ([19,39,103,135,293],[1504,657]),
  ([19,39,103,135,299],[1505,660]),
  ([19,39,103,293,371],[1527,766,611,653]),
  ([19,39,103,293,386],[1528]),
  ([19,39,135,162,260],[1544,721,90]),
  ([19,39,135,162,293],[1545,723,91]),
  ([19,39,135,250,378],[1553,755,404,687]),
  ([19,39,135,293,323],[1555,766]),
  ([19,39,135,293,331],[1556,767]),
  ([19,39,135,343,378],[1558,774,664,690]),
  ([19,49,71,92,285],[1262,996,932,869,98]),
  ([19,49,71,131,257],[1317,1032,929,843,99]),
  ([19,49,71,131,392],[1318,1035,953,889,100,97,93]),
  ([19,49,135,257,378],[1553,1112,844,1042]),
  ([19,49,135,336,378],[1554,1128,1017,1044])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b8ok : f4b8.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b9 : Array Row := #[
  ([19,56,103,135,293],[1205,1191,1169]),
  ([19,71,103,135,238],[1282,104]),
  ([19,71,103,135,256],[1502,1335,1285,1134,105]),
  ([19,71,135,336,343],[1563,1414,1296,1304]),
  ([19,86,103,135,285],[98]),
  ([19,86,135,162,257],[1467,1138,99]),
  ([19,103,135,173,293],[1519,1498,101]),
  ([19,103,135,241,293],[1525]),
  ([19,103,135,257,293],[1555,1527,1139,1423]),
  ([20,35,71,103,135],[300,106]),
  ([20,39,49,71,131],[538]),
  ([20,39,49,135,153],[687,432]),
  ([20,39,49,135,378],[695,474,402]),
  ([20,39,86,135,162],[627,106]),
  ([20,39,103,135,293],[1506,657]),
  ([21,39,49,71,131],[394]),
  ([21,39,49,135,378],[402]),
  ([22,28,39,71,131],[537,207,109,108]),
  ([22,35,71,103,135],[]),
  ([22,35,71,135,162],[78,107]),
  ([22,39,49,71,131],[538]),
  ([22,39,49,131,378],[677,476,392,111,110]),
  ([22,39,49,135,153],[687,433]),
  ([22,39,49,135,378],[695,477,402]),
  ([22,39,71,86,131],[86,107]),
  ([22,39,71,131,250],[375]),
  ([22,39,71,131,396],[535,112,110]),
  ([22,39,103,135,293],[1510]),
  ([22,39,135,162,293],[1547,109]),
  ([22,49,71,131,392],[1318,954,889,112,111]),
  ([23,39,49,71,131],[538]),
  ([24,28,39,135,162],[692,150,113])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b9ok : f4b9.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b10 : Array Row := #[
  ([24,28,49,135,162],[1046,158,114]),
  ([24,28,56,135,162],[1200,171,115]),
  ([24,28,58,103,135],[1222,223,141,124,116]),
  ([24,28,71,92,135],[1254,210,199,139,125,116]),
  ([24,28,71,103,377],[1286,227,218,201,126]),
  ([24,28,71,103,386],[1287,142,140,127]),
  ([24,28,71,135,162],[1328,213,117]),
  ([24,28,71,135,326],[1336,218]),
  ([24,28,71,135,331],[1337,219,140]),
  ([24,28,103,135,162],[1495,225,118]),
  ([24,28,103,135,274],[1502,227]),
  ([24,28,103,135,293],[1503,228,142]),
  ([24,28,135,162],[1543,143,231,237,126,232,127,123,119,120,121]),
  ([24,35,71,103,135],[1275,301,128]),
  ([24,39,49,56,131],[368,115]),
  ([24,39,49,58,92],[389,369,116,130]),
  ([24,39,49,71,131],[893,539,394,382,117,136,132]),
  ([24,39,49,103,131],[391,118]),
  ([24,39,49,131],[137,133,478,131,396,119,113,114,138,134]),
  ([24,39,49,131,135],[403,120]),
  ([24,39,49,131,162],[438,121]),
  ([24,39,49,135,162],[439,122,129]),
  ([24,39,49,135,361],[124]),
  ([24,39,49,135,378],[1050,696,479,402,125]),
  ([24,39,49,162,377],[1076,722,422,126]),
  ([24,39,86,135,162],[1462,628,128,132]),
  ([24,39,103,135,293],[1504,658]),
  ([24,39,135,162,260],[1544,722,133]),
  ([24,44,71,103,135],[1275,809,135]),
  ([24,49,83,135,162],[1442,979,135,136]),
  ([24,49,103,135,293],[1507,1012]),
  ([24,49,135,162,257],[1544,1076,137])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b10ok : f4b10.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b11 : Array Row := #[
  ([24,56,103,135,293],[1206,1192,1169]),
  ([24,71,103,135,256],[1502,1336,1286,1134,143]),
  ([25,28,71,103,135],[202,144]),
  ([25,39,49,135,162],[439,144]),
  ([26,39,49,135,162],[145]),
  ([27,28,71,103,135],[]),
  ([27,28,71,135,162],[122,146]),
  ([27,39,49,71,131],[129,146]),
  ([28,39,49,71,131],[892,538,395,383,164]),
  ([28,39,49,71,348],[925,571,457,375,165]),
  ([28,39,49,71,385],[927,573,458,378,166]),
  ([28,39,49,131,293],[1030,676,458,386,167]),
  ([28,39,49,131,378],[1031,677,481,392,168,162,154]),
  ([28,39,49,135,153],[1041,687,434,405,169,157,149]),
  ([28,39,49,135,378],[1049,695,482,402,170,159,151]),
  ([28,39,49,173,378],[1086,728,423,172,157,152]),
  ([28,39,49,182,378],[1098,738,424,173,160,149]),
  ([28,39,49,351,378],[1107,753,404,427,175]),
  ([28,39,49,378,386],[1110,756,434,440,176]),
  ([28,39,56,71,131],[492,491,113]),
  ([28,39,56,135,378],[172,169,152]),
  ([28,39,67,71,92],[522,510,504,197,19,148]),
  ([28,39,69,103,135],[652,147]),
  ([28,39,71,92,182],[640,562,196,151]),
  ([28,39,71,92,195],[641,569,152,147]),
  ([28,39,71,92,289],[1261,644,579,515]),
  ([28,39,71,92,371],[646,583,153]),
  ([28,39,71,96,182],[650,563,200,151]),
  ([28,39,71,97,182],[651,564]),
  ([28,39,71,103,147],[653]),
  ([28,39,71,103,371],[657]),
  ([28,39,71,103,377],[658,201,150])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b11ok : f4b11.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b12 : Array Row := #[
  ([28,39,71,103,394],[659,584]),
  ([28,39,71,131,182],[674,567,204,151]),
  ([28,39,71,131,250],[1314,676,573,375]),
  ([28,39,71,131,396],[1316,683,602,535,220,154]),
  ([28,39,71,135,148],[686,552,212]),
  ([28,39,71,135,319],[699,214]),
  ([28,39,71,162,371],[723,20]),
  ([28,39,71,182,327],[1385,743,530,216]),
  ([28,39,71,182,378],[744,21,217,149]),
  ([28,39,71,323,371],[766]),
  ([28,39,71,331,371],[767]),
  ([28,39,92,182,293],[1480,743,610,221]),
  ([28,39,92,182,378],[745,244,222,149]),
  ([28,39,103,182,378],[746,226,149]),
  ([28,39,103,274,371],[]),
  ([28,39,103,293,371],[1525,767,611,653]),
  ([28,39,135,182,378],[238,233,149]),
  ([28,39,135,250,378],[1550,756,404,687,240]),
  ([28,39,135,343,378],[1552,775,664,690,241]),
  ([28,39,156,162,182],[718,236,149]),
  ([28,39,182,378],[243,149,245,152,242,149,149]),
  ([28,49,56,71,131],[846,845,114]),
  ([28,49,56,135,378],[173,169,160]),
  ([28,49,65,71,92],[876,863,857,198,66,156]),
  ([28,49,69,103,135],[1006,155]),
  ([28,49,71,92,173],[994,914,196,159]),
  ([28,49,71,92,195],[995,923,160,155]),
  ([28,49,71,92,285],[1262,998,933,869]),
  ([28,49,71,92,365],[1000,937,161]),
  ([28,49,71,96,173],[1004,915,200,159]),
  ([28,49,71,99,173],[1005,916]),
  ([28,49,71,103,142],[1007])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b12ok : f4b12.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b13 : Array Row := #[
  ([28,49,71,103,365],[1011]),
  ([28,49,71,103,377],[1012,201,158]),
  ([28,49,71,103,390],[1013,938]),
  ([28,49,71,131,173],[1028,919,204,159]),
  ([28,49,71,131,241],[1314,1030,927,375]),
  ([28,49,71,131,392],[1318,1037,956,889,220,162]),
  ([28,49,71,135,143],[1040,906,211]),
  ([28,49,71,135,313],[1053,215]),
  ([28,49,71,162,365],[1077,67]),
  ([28,49,71,173,327],[1371,1091,884,216]),
  ([28,49,71,173,378],[1092,68,217,157]),
  ([28,49,71,317,365],[1120]),
  ([28,49,71,331,365],[1121]),
  ([28,49,92,173,293],[1477,1091,964,221]),
  ([28,49,92,173,378],[1093,241,222,157]),
  ([28,49,103,173,378],[1094,226,157]),
  ([28,49,103,274,365],[]),
  ([28,49,103,293,365],[1526,1121,965,1007]),
  ([28,49,135,173,378],[238,233,157]),
  ([28,49,135,241,378],[1550,1110,404,1041,243]),
  ([28,49,135,336,378],[1554,1129,1017,1044,244]),
  ([28,49,156,162,173],[1072,236,157]),
  ([28,49,173,378],[240,157,245,160,239,157,157]),
  ([28,54,71,103,135],[1139]),
  ([28,55,71,103,135],[1142]),
  ([28,56,58,71,92],[1145,1144,1143,193,116,165]),
  ([28,56,69,103,135],[1186,163]),
  ([28,56,71,92,173],[1176,1157,196,172]),
  ([28,56,71,92,182],[1177,1158,196,173]),
  ([28,56,71,92,195],[1178,1159,174,163]),
  ([28,56,71,92,351],[1179,1161,175]),
  ([28,56,71,92,386],[1180,1162,176])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b13ok : f4b13.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b14 : Array Row := #[
  ([28,56,71,96,135],[1181,1151,200,170]),
  ([28,56,71,97,135],[1182]),
  ([28,56,71,99,135],[1183]),
  ([28,56,71,101,135],[1184]),
  ([28,56,71,103,131],[1185,1146,118]),
  ([28,56,71,103,135],[1187]),
  ([28,56,71,103,167],[1188,1156]),
  ([28,56,71,103,351],[1189]),
  ([28,56,71,103,365],[1190]),
  ([28,56,71,103,371],[1191]),
  ([28,56,71,103,377],[1192,201,171]),
  ([28,56,71,103,386],[1193,1163]),
  ([28,56,71,116,135],[1196,1148]),
  ([28,56,71,131],[1199,167,1149,1166,166,1150,119,115,117,203,168]),
  ([28,56,71,131,135],[1197,1154,120,204,170]),
  ([28,56,71,131,162],[1198,1155,121,146]),
  ([28,56,71,135,196],[1202,1160,123,164]),
  ([28,56,71,135,309],[1203]),
  ([28,56,71,135,317],[1204]),
  ([28,56,71,135,323],[1205]),
  ([28,56,71,135,326],[1206]),
  ([28,56,71,135,327],[1207,1162,1147,216]),
  ([28,56,71,135,331],[1208,1163]),
  ([28,56,71,135,361],[1211,124]),
  ([28,56,71,135,378],[1212,125,217,169]),
  ([28,56,71,162,386],[1214,1160,127]),
  ([28,56,71,331,386],[1215,1148,1156]),
  ([28,56,81,103,135],[1187,1173,1170]),
  ([28,56,92,135,293],[1207,1180,1168,221]),
  ([28,56,92,135,378],[1213,229,222,175,169]),
  ([28,56,103,135,274],[]),
  ([28,56,103,135,293],[1208,1193,1169])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b14ok : f4b14.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b15 : Array Row := #[
  ([28,56,103,135,378],[226,169]),
  ([28,56,103,293,386],[1215,1170,1188]),
  ([28,56,135,156,162],[236,144,169]),
  ([28,56,135,162,293],[1214,1202,1171,167]),
  ([28,56,135,293,331],[1215,1173,1196]),
  ([28,56,135,378],[176,169,245,174,233,169,169]),
  ([28,69,71,103,135],[1276,202,190,177]),
  ([28,69,103,135],[1512,224,1239,191,189,192,188,178,179,180]),
  ([28,69,103,135,173],[1496,181,184]),
  ([28,69,103,135,182],[1497,182,185]),
  ([28,69,103,135,195],[1500,183,186]),
  ([28,71,88,103,135],[1469,187,193]),
  ([28,71,92,103,195],[1470,1281,226,179]),
  ([28,71,92,127,135],[1471,1311,229,196]),
  ([28,71,92,135,195],[1472,1333,233,180]),
  ([28,71,92,135,257],[1473,1340,234]),
  ([28,71,92,135,260],[1474,1342,235]),
  ([28,71,92,173,182],[1475,1361,238,196]),
  ([28,71,92,173,195],[1476,1368,239,181]),
  ([28,71,92,173,250],[1477,1371,240]),
  ([28,71,92,173,343],[1478,1372,241]),
  ([28,71,92,182,195],[1479,1382,242,182]),
  ([28,71,92,182,241],[1480,1385,243]),
  ([28,71,92,182,336],[1481,1386,244]),
  ([28,71,92,195],[1482,221,1259,1393,216,1260,245,217,222,178,177,183]),
  ([28,71,97,135,195],[1489,184,196]),
  ([28,71,97,173,182],[1490,1362]),
  ([28,71,99,135,195],[1491,185,196]),
  ([28,71,99,173,182],[1492,1363]),
  ([28,71,101,135,195],[1493,186,196]),
  ([28,71,103,127,135],[1494]),
  ([28,71,103,135,188],[1498,187,194])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b15ok : f4b15.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b16 : Array Row := #[
  ([28,71,103,135,191],[1499,187,195]),
  ([28,71,103,135,195],[1501,187,196]),
  ([28,71,103,135,231],[230]),
  ([28,71,103,135,256],[1503,1337,1287,1134,231]),
  ([28,71,103,135,257],[1504]),
  ([28,71,103,135,258],[1506]),
  ([28,71,103,135,260],[1507]),
  ([28,71,103,135,261],[1509]),
  ([28,71,103,135,263],[1510]),
  ([28,71,103,135,264],[1511]),
  ([28,71,103,135,296],[1513,197]),
  ([28,71,103,135,298],[1514,198]),
  ([28,71,103,135,377],[232,199,201]),
  ([28,71,103,156,195],[1516,236,200,201]),
  ([28,71,103,173,182],[1517,1364]),
  ([28,71,103,173,343],[1518,1373]),
  ([28,71,103,173,371],[1519]),
  ([28,71,103,182,336],[1521,1387]),
  ([28,71,103,182,365],[1522]),
  ([28,71,103,195,386],[1524,1394,189]),
  ([28,71,103,241,371],[1525]),
  ([28,71,103,250,365],[1526]),
  ([28,71,103,257,371],[1527]),
  ([28,71,103,257,386],[1528,1398]),
  ([28,71,103,260,365],[1530]),
  ([28,71,103,260,386],[1531,1400]),
  ([28,71,103,377],[228,219,201,237,213,225,201,201]),
  ([28,71,135,162,195],[1542,236,190,204,209]),
  ([28,71,135,162,257],[1545,205]),
  ([28,71,135,162,260],[1546,206]),
  ([28,71,135,162,263],[1547,207]),
  ([28,71,135,162,264],[1548,208])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b16ok : f4b16.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b17 : Array Row := #[
  ([28,71,135,195,331],[1549,1394,191]),
  ([28,71,135,257,323],[1555]),
  ([28,71,135,257,331],[1556,1398]),
  ([28,71,135,260,317],[1559]),
  ([28,71,135,260,331],[1560,1400]),
  ([28,71,135,336,343],[1567,1415,1296,1304]),
  ([28,71,162,173,182],[1571,1360,211,212]),
  ([28,71,173,182,331],[1573,1293]),
  ([28,103,135,195,293],[1549,1524,1422,221]),
  ([28,103,135,257,274],[]),
  ([28,103,135,257,293],[1556,1528,1139,1423]),
  ([28,103,135,260,274],[]),
  ([28,103,135,260,293],[1560,1531,1142,1424]),
  ([28,103,173,182,293],[1573,1425]),
  ([29,39,49,71,131],[892]),
  ([29,39,49,135,378],[1049,482,402,247]),
  ([29,39,49,182,378],[1098,151,424,248]),
  ([29,49,69,103,135],[187,246]),
  ([29,49,71,92,173],[247]),
  ([29,49,71,92,195],[196,248,246]),
  ([29,49,71,99,173],[]),
  ([29,49,71,103,365],[]),
  ([29,71,103,135,260],[]),
  ([30,39,49,71,131],[538]),
  ([30,39,49,135,378],[695,482,402,250]),
  ([30,39,49,173,378],[159,728,423,251]),
  ([30,39,69,103,135],[187,249]),
  ([30,39,71,92,182],[250]),
  ([30,39,71,92,195],[196,251,249]),
  ([30,39,71,97,182],[]),
  ([30,39,71,103,371],[]),
  ([30,71,103,135,257],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b17ok : f4b17.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b18 : Array Row := #[
  ([31,39,49,71,131],[892]),
  ([31,39,49,135,378],[1049,483,402,253,252]),
  ([31,39,71,92,182],[564,252]),
  ([31,49,71,92,173],[253]),
  ([31,49,71,103,365],[1014]),
  ([31,71,103,135,260],[1508]),
  ([31,71,103,173,182],[1364]),
  ([33,39,49,71,131],[538]),
  ([33,39,49,135,378],[695,484,402,255,254]),
  ([33,39,71,92,182],[254]),
  ([33,39,71,103,371],[660]),
  ([33,49,71,92,173],[916,255]),
  ([33,71,103,135,257],[1505]),
  ([33,71,103,173,182],[1364]),
  ([35,39,49,71,131],[892,539,395,384,275,264,69]),
  ([35,39,49,135,378],[1049,696,485,402,276,271,267,258]),
  ([35,39,67,103,135],[652,256]),
  ([35,39,71,92,182],[640,565,294,258,256]),
  ([35,39,71,103,371],[657,299,257]),
  ([35,44,71,103,135],[1275,810,302,259]),
  ([35,49,58,71,92],[876,848,295,71,262]),
  ([35,49,60,71,92],[855,295]),
  ([35,49,67,103,135],[1006,260]),
  ([35,49,71,86,131],[874,73]),
  ([35,49,71,92,135],[903,292,268]),
  ([35,49,71,92,173],[994,917,294,271]),
  ([35,49,71,92,182],[921,272,260]),
  ([35,49,71,92,351],[939,273]),
  ([35,49,71,92,390],[1001,940,274]),
  ([35,49,71,96,135],[297,268]),
  ([35,49,71,97,135],[904,298,269]),
  ([35,49,71,99,135],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b18ok : f4b18.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b19 : Array Row := #[
  ([35,49,71,100,135],[]),
  ([35,49,71,103,131],[883,74]),
  ([35,49,71,103,133],[]),
  ([35,49,71,103,135],[]),
  ([35,49,71,103,170],[1009,911]),
  ([35,49,71,103,351],[]),
  ([35,49,71,103,365],[1011]),
  ([35,49,71,103,371],[299,270]),
  ([35,49,71,103,386],[]),
  ([35,49,71,103,390],[1013,946]),
  ([35,49,71,119,135],[888]),
  ([35,49,71,131],[304,265,957,263,897,75,70,72,305,266]),
  ([35,49,71,131,135],[905,76,303,268]),
  ([35,49,71,131,162],[910,77,107]),
  ([35,49,71,135,196],[924,79,261]),
  ([35,49,71,135,309],[]),
  ([35,49,71,135,317],[]),
  ([35,49,71,135,323],[]),
  ([35,49,71,135,331],[938]),
  ([35,49,71,135,334],[1343,1054,940,885,309]),
  ([35,49,71,135,340],[946]),
  ([35,49,71,135,361],[80]),
  ([35,49,71,135,378],[81,310,267]),
  ([35,49,71,162,390],[1078,924,83]),
  ([35,49,71,340,390],[1401,1122,888,911]),
  ([35,49,81,103,135],[1424,966]),
  ([35,49,83,135,162],[1442,980,259,264]),
  ([35,49,86,135,378],[314,267]),
  ([35,49,92,135,293],[1474,1054,1001,315]),
  ([35,49,92,135,378],[1057,327,316,273,267]),
  ([35,49,103,135,274],[]),
  ([35,49,103,135,278],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b19ok : f4b19.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b20 : Array Row := #[
  ([35,49,103,135,293],[1507,1013]),
  ([35,49,103,135,378],[320,267]),
  ([35,49,103,293,390],[1532,1122,966,1009]),
  ([35,49,135,156,162],[328,106,267]),
  ([35,49,135,162,293],[1546,1078,265]),
  ([35,49,135,293,340],[1561,1122]),
  ([35,49,135,378],[326,274,267,330,272,325,267,267]),
  ([35,55,71,103,135],[1142]),
  ([35,56,71,92,135],[1175,1152,294,276]),
  ([35,56,71,103,135],[1187]),
  ([35,56,71,103,390],[1194,1164]),
  ([35,56,71,135,162],[1201,128,275]),
  ([35,56,71,135,340],[1209,1164]),
  ([35,56,103,135,293],[1209,1194,1169]),
  ([35,67,71,103,135],[1276,300,287,277]),
  ([35,67,86,103,135],[1455,278]),
  ([35,67,103,135],[1512,318,1238,288,286,289,285,279,280,281]),
  ([35,67,103,135,182],[1497,282,283]),
  ([35,71,79,103,135],[284,291]),
  ([35,71,86,92,182],[1250,314,278,291]),
  ([35,71,86,103,371],[313,299]),
  ([35,71,92,103,182],[1280,320,280]),
  ([35,71,92,135,182],[1332,325,281]),
  ([35,71,92,135,260],[1474,1343,326]),
  ([35,71,92,135,343],[1344,327]),
  ([35,71,92,182],[315,1388,309,1258,293,330,310,316,279,277,282]),
  ([35,71,99,135,182],[283,292]),
  ([35,71,103,135,191],[1499,290,293]),
  ([35,71,103,135,195],[1501,290,294]),
  ([35,71,103,135,250],[]),
  ([35,71,103,135,251],[]),
  ([35,71,103,135,253],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b20ok : f4b20.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b21 : Array Row := #[
  ([35,71,103,135,256],[1503,1338,1288,1134,323]),
  ([35,71,103,135,257],[1504]),
  ([35,71,103,135,260],[1507]),
  ([35,71,103,135,289],[295]),
  ([35,71,103,135,343],[]),
  ([35,71,103,135,371],[324,296,299]),
  ([35,71,103,156,182],[328,297,299]),
  ([35,71,103,173,182],[1517,1365,298]),
  ([35,71,103,182,390],[1523,1391,286]),
  ([35,71,103,260,390],[1532,1401]),
  ([35,71,103,371],[322,312,299,329,308,319,299,299]),
  ([35,71,135,162,182],[328,287,303,306]),
  ([35,71,135,162,260],[1546,304]),
  ([35,71,135,182,340],[1391,288]),
  ([35,71,135,260,340],[1561,1401]),
  ([35,103,135,182,293],[1523,1499,315]),
  ([35,103,135,260,293],[1561,1532,1142,1424]),
  ([36,49,71,92,135],[333]),
  ([36,49,71,92,182],[334]),
  ([36,49,71,96,135],[333]),
  ([36,49,71,99,135],[]),
  ([36,49,71,100,135],[]),
  ([36,49,71,103,135],[]),
  ([36,49,71,103,390],[]),
  ([36,49,71,135,162],[331]),
  ([36,49,135,156,162],[332]),
  ([37,39,49,71,131],[892]),
  ([37,49,71,92,135],[904,339,338]),
  ([37,49,71,103,131],[]),
  ([37,49,71,103,133],[]),
  ([37,49,71,103,135],[]),
  ([37,49,71,131],[898,341,336])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b21ok : f4b21.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b22 : Array Row := #[
  ([37,49,71,131,135],[906,340,338]),
  ([37,49,71,131,162],[]),
  ([37,49,71,131,198],[]),
  ([37,49,71,133,162],[335]),
  ([37,49,71,135,162],[335]),
  ([37,49,71,135,196],[335]),
  ([37,49,71,135,340],[]),
  ([37,49,135,156,162],[342,337]),
  ([37,71,103,135,182],[339]),
  ([37,71,135,162,182],[342,340]),
  ([38,49,71,103,135],[]),
  ([38,49,71,135,162],[343]),
  ([39,44,49,71,131],[893,783,25,538,395,385,348]),
  ([39,44,49,135,378],[1050,784,782,695,487,402,356,351]),
  ([39,44,58,71,92],[803,26,522,494,346]),
  ([39,44,59,71,92],[803,500]),
  ([39,44,65,103,135],[652,344]),
  ([39,44,71,83,131],[28,518]),
  ([39,44,71,92,135],[800,549,352]),
  ([39,44,71,92,173],[558,355,344]),
  ([39,44,71,92,182],[802,640,566,356]),
  ([39,44,71,92,351],[586,357]),
  ([39,44,71,92,394],[647,587,358]),
  ([39,44,71,96,135],[805,352]),
  ([39,44,71,97,135],[]),
  ([39,44,71,98,135],[]),
  ([39,44,71,99,135],[806,550,353]),
  ([39,44,71,103,131],[29,529]),
  ([39,44,71,103,132],[]),
  ([39,44,71,103,135],[]),
  ([39,44,71,103,179],[655,559]),
  ([39,44,71,103,351],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b22ok : f4b22.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b23 : Array Row := #[
  ([39,44,71,103,365],[807,354]),
  ([39,44,71,103,371],[657]),
  ([39,44,71,103,386],[]),
  ([39,44,71,103,394],[659,593]),
  ([39,44,71,124,135],[534]),
  ([39,44,71,131],[812,30,22,27,813,349,604,347,543,350]),
  ([39,44,71,131,135],[31,811,551,352]),
  ([39,44,71,131,162],[32,61,556]),
  ([39,44,71,135,196],[34,570,345]),
  ([39,44,71,135,309],[]),
  ([39,44,71,135,317],[]),
  ([39,44,71,135,323],[]),
  ([39,44,71,135,331],[584]),
  ([39,44,71,135,341],[1341,817,700,587,531]),
  ([39,44,71,135,347],[593]),
  ([39,44,71,135,361],[35]),
  ([39,44,71,135,378],[36,818,351]),
  ([39,44,71,162,394],[38,724,570]),
  ([39,44,71,347,394],[1399,768,534,559]),
  ([39,44,81,103,135],[1423,612]),
  ([39,44,83,135,378],[822,351]),
  ([39,44,86,135,162],[1462,259,629,348]),
  ([39,44,92,135,293],[1473,823,700,647]),
  ([39,44,92,135,378],[835,824,703,357,351]),
  ([39,44,103,135,274],[]),
  ([39,44,103,135,280],[]),
  ([39,44,103,135,293],[1504,659]),
  ([39,44,103,135,378],[828,351]),
  ([39,44,103,293,394],[1529,768,612,655]),
  ([39,44,135,156,162],[836,59,351]),
  ([39,44,135,162,293],[1545,724,349]),
  ([39,44,135,293,347],[1557,768])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b23ok : f4b23.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b24 : Array Row := #[
  ([39,44,135,378],[834,838,355,833,351,358,351,351]),
  ([39,45,71,92,135],[361]),
  ([39,45,71,92,173],[362]),
  ([39,45,71,96,135],[361]),
  ([39,45,71,97,135],[]),
  ([39,45,71,98,135],[]),
  ([39,45,71,103,135],[]),
  ([39,45,71,103,394],[]),
  ([39,45,71,135,162],[359]),
  ([39,45,135,156,162],[360]),
  ([39,47,49,71,131],[538]),
  ([39,47,71,92,135],[839,550,366]),
  ([39,47,71,103,131],[]),
  ([39,47,71,103,132],[]),
  ([39,47,71,103,135],[]),
  ([39,47,71,131],[841,544,364]),
  ([39,47,71,131,135],[840,552,366]),
  ([39,47,71,131,162],[]),
  ([39,47,71,131,197],[]),
  ([39,47,71,132,162],[363]),
  ([39,47,71,135,162],[363]),
  ([39,47,71,135,196],[363]),
  ([39,47,71,135,347],[]),
  ([39,47,135,156,162],[842,365]),
  ([39,48,71,103,135],[]),
  ([39,48,71,135,162],[367]),
  ([39,49,56,69,92],[163,368]),
  ([39,49,56,71,348],[165,130,375]),
  ([39,49,56,131,378],[168,847,493,451,392]),
  ([39,49,56,135,153],[169,425]),
  ([39,49,56,135,378],[170,453,402]),
  ([39,49,56,162,377],[171,422])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b24ok : f4b24.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b25 : Array Row := #[
  ([39,49,56,173,378],[172,453,423]),
  ([39,49,56,182,378],[173,453,424]),
  ([39,49,56,195,378],[174,425]),
  ([39,49,56,351,378],[175,404,427]),
  ([39,49,58,71,92],[877,523,379]),
  ([39,49,58,71,131],[894,540,394,379]),
  ([39,49,58,71,300],[930,576]),
  ([39,49,58,71,313],[931,849,577]),
  ([39,49,58,71,319],[932,578,495]),
  ([39,49,58,71,327],[1143,933,579]),
  ([39,49,58,71,348],[934,580,454,375]),
  ([39,49,58,92,153],[992,851,638,497,426]),
  ([39,49,58,92,274],[996,642,454]),
  ([39,49,58,92,293],[1144,998,644,457]),
  ([39,49,58,92,378],[999,852,645,498,459]),
  ([39,49,58,131,274],[1034,680,454,375]),
  ([39,49,58,131,378],[1036,853,682,499,459,392]),
  ([39,49,58,135,153],[1043,689,427,404]),
  ([39,49,58,135,378],[1052,698,462,402]),
  ([39,49,58,173,378],[1090,730,423]),
  ([39,49,58,182,378],[1100,742,424]),
  ([39,49,58,274,348],[1113,759,379,394]),
  ([39,49,58,336,378],[1115,850,851,762]),
  ([39,49,58,343,378],[1116,763,496,497]),
  ([39,49,58,348,378],[1117,764,397,426]),
  ([39,49,58,351,378],[1118,765,404,427]),
  ([39,49,59,71,131],[894]),
  ([39,49,59,92,378],[999,854,501,460]),
  ([39,49,59,135,378],[1052,462,402]),
  ([39,49,60,71,131],[540]),
  ([39,49,60,92,378],[856,645,502,461]),
  ([39,49,60,135,378],[698,462,402])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b25ok : f4b25.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b26 : Array Row := #[
  ([39,49,61,71,92],[]),
  ([39,49,62,71,131],[394]),
  ([39,49,62,135,378],[402]),
  ([39,49,65,71,92],[877,858,524,380]),
  ([39,49,65,71,131],[894,859,541,394,380]),
  ([39,49,65,71,364],[935,860,582,455,376]),
  ([39,49,65,83,92],[613,344,387]),
  ([39,49,65,92,274],[996,643,455]),
  ([39,49,65,92,378],[999,864,648,503,468]),
  ([39,49,65,135,378],[1052,701,469,402]),
  ([39,49,65,135,381],[702,470]),
  ([39,49,65,173,378],[1090,731,423]),
  ([39,49,67,71,92],[878,523,505,381]),
  ([39,49,67,71,131],[895,540,506,394,381]),
  ([39,49,67,71,370],[936,581,507,456,377]),
  ([39,49,67,86,92],[989,260,388]),
  ([39,49,67,92,274],[997,642,456]),
  ([39,49,67,92,378],[1002,865,645,511,473]),
  ([39,49,67,135,378],[1055,698,474,402]),
  ([39,49,67,135,382],[1056,475]),
  ([39,49,67,182,378],[1101,742,424]),
  ([39,49,69,71,92],[177,878,866,524,512,382]),
  ([39,49,69,92],[178,147,155,867,868,513,514,478,374,390]),
  ([39,49,69,92,103],[179,391]),
  ([39,49,69,92,135],[180,403]),
  ([39,49,69,92,173],[181,249,442]),
  ([39,49,69,92,182],[182,246,446]),
  ([39,49,69,92,195],[183,452]),
  ([39,49,69,97,135],[184,372]),
  ([39,49,69,99,135],[185,372]),
  ([39,49,69,101,135],[186,372]),
  ([39,49,69,103,135],[187,372])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b26ok : f4b26.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b27 : Array Row := #[
  ([39,49,69,103,377],[188,480]),
  ([39,49,69,135,162],[190,439,373]),
  ([39,49,69,135,384],[192,480]),
  ([39,49,70,103,135],[]),
  ([39,49,71,74,131],[]),
  ([39,49,71,75,131],[]),
  ([39,49,71,76,92],[959,524]),
  ([39,49,71,77,92],[877]),
  ([39,49,71,78,92],[878,605]),
  ([39,49,71,79,92],[523]),
  ([39,49,71,83,348],[41,346,375]),
  ([39,49,71,86,348],[262,87,375]),
  ([39,49,71,88,92],[193,372]),
  ([39,49,71,91,131],[]),
  ([39,49,71,92,131],[896,879,542,525,397,379]),
  ([39,49,71,92,132],[879,546,399]),
  ([39,49,71,92,133],[900,525,401]),
  ([39,49,71,92,135],[404]),
  ([39,49,71,92,137],[406]),
  ([39,49,71,92,138],[407]),
  ([39,49,71,92,142],[411]),
  ([39,49,71,92,143],[879,553,414]),
  ([39,49,71,92,147],[418]),
  ([39,49,71,92,148],[907,525,421]),
  ([39,49,71,92,167],[440]),
  ([39,49,71,92,173],[443]),
  ([39,49,71,92,175],[444]),
  ([39,49,71,92,182],[447]),
  ([39,49,71,92,184],[448]),
  ([39,49,71,92,188],[194,449,372]),
  ([39,49,71,92,191],[195,450,372]),
  ([39,49,71,92,195],[196,453,372])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b27ok : f4b27.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b28 : Array Row := #[
  ([39,49,71,92,265],[]),
  ([39,49,71,92,266],[]),
  ([39,49,71,92,267],[]),
  ([39,49,71,92,269],[]),
  ([39,49,71,92,270],[]),
  ([39,49,71,92,271],[967]),
  ([39,49,71,92,272],[616]),
  ([39,49,71,92,283],[1145]),
  ([39,49,71,92,285],[869]),
  ([39,49,71,92,286],[]),
  ([39,49,71,92,289],[515]),
  ([39,49,71,92,290],[]),
  ([39,49,71,92,296],[197,872,617]),
  ([39,49,71,92,298],[198,968,519]),
  ([39,49,71,92,348],[941,588,459,375]),
  ([39,49,71,92,349],[589,460]),
  ([39,49,71,92,350],[942,461]),
  ([39,49,71,92,351],[462]),
  ([39,49,71,92,355],[464]),
  ([39,49,71,92,358],[466]),
  ([39,49,71,92,360],[467]),
  ([39,49,71,92,364],[969,943,590,468,376]),
  ([39,49,71,92,365],[469]),
  ([39,49,71,92,368],[472]),
  ([39,49,71,92,370],[944,618,591,473,377]),
  ([39,49,71,92,371],[474]),
  ([39,49,71,92,374],[477]),
  ([39,49,71,92,377],[199,479]),
  ([39,49,71,92,386],[482]),
  ([39,49,71,92,387],[483]),
  ([39,49,71,92,388],[484]),
  ([39,49,71,92,390],[485])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b28ok : f4b28.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b29 : Array Row := #[
  ([39,49,71,92,392],[875,592,486]),
  ([39,49,71,92,394],[487]),
  ([39,49,71,92,396],[945,521,488]),
  ([39,49,71,93,131],[896,526]),
  ([39,49,71,94,131],[880,542]),
  ([39,49,71,96,131],[881,527,397]),
  ([39,49,71,96,135],[404]),
  ([39,49,71,96,142],[411]),
  ([39,49,71,96,147],[418]),
  ([39,49,71,96,195],[200,453]),
  ([39,49,71,96,351],[462]),
  ([39,49,71,96,355],[464]),
  ([39,49,71,96,358],[466]),
  ([39,49,71,96,365],[469]),
  ([39,49,71,96,371],[474]),
  ([39,49,71,96,386],[482]),
  ([39,49,71,97,131],[896,528]),
  ([39,49,71,97,135],[]),
  ([39,49,71,97,142],[412]),
  ([39,49,71,97,167],[]),
  ([39,49,71,97,351],[]),
  ([39,49,71,97,358],[]),
  ([39,49,71,97,365],[470]),
  ([39,49,71,97,371],[]),
  ([39,49,71,97,386],[]),
  ([39,49,71,98,135],[]),
  ([39,49,71,98,182],[]),
  ([39,49,71,99,131],[882,542]),
  ([39,49,71,99,135],[]),
  ([39,49,71,99,147],[419]),
  ([39,49,71,99,167],[]),
  ([39,49,71,99,351],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b29ok : f4b29.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b30 : Array Row := #[
  ([39,49,71,99,355],[]),
  ([39,49,71,99,365],[]),
  ([39,49,71,99,371],[475]),
  ([39,49,71,99,386],[]),
  ([39,49,71,100,135],[]),
  ([39,49,71,100,173],[]),
  ([39,49,71,101,135],[]),
  ([39,49,71,102,135],[]),
  ([39,49,71,103,131],[]),
  ([39,49,71,103,132],[]),
  ([39,49,71,103,133],[]),
  ([39,49,71,103,134],[]),
  ([39,49,71,103,135],[]),
  ([39,49,71,103,142],[]),
  ([39,49,71,103,147],[]),
  ([39,49,71,103,152],[201,422]),
  ([39,49,71,103,167],[]),
  ([39,49,71,103,170],[]),
  ([39,49,71,103,179],[]),
  ([39,49,71,103,348],[375]),
  ([39,49,71,103,349],[]),
  ([39,49,71,103,350],[]),
  ([39,49,71,103,351],[]),
  ([39,49,71,103,364],[970,376]),
  ([39,49,71,103,365],[]),
  ([39,49,71,103,370],[619,377]),
  ([39,49,71,103,371],[]),
  ([39,49,71,103,377],[202,439]),
  ([39,49,71,103,385],[1146,378]),
  ([39,49,71,103,386],[]),
  ([39,49,71,103,390],[]),
  ([39,49,71,103,394],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b30ok : f4b30.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b31 : Array Row := #[
  ([39,49,71,106,135],[404]),
  ([39,49,71,108,131],[]),
  ([39,49,71,108,135],[]),
  ([39,49,71,108,365],[]),
  ([39,49,71,109,135],[404]),
  ([39,49,71,111,131],[]),
  ([39,49,71,111,135],[]),
  ([39,49,71,111,371],[]),
  ([39,49,71,112,135],[]),
  ([39,49,71,113,135],[1147,884,530,405]),
  ([39,49,71,116,135],[]),
  ([39,49,71,116,386],[1148]),
  ([39,49,71,119,135],[]),
  ([39,49,71,120,133],[]),
  ([39,49,71,120,348],[375]),
  ([39,49,71,124,135],[]),
  ([39,49,71,125,132],[]),
  ([39,49,71,125,348],[375]),
  ([39,49,71,130,131],[145]),
  ([39,49,71,131],[899,545,397]),
  ([39,49,71,131,132],[899,547,399]),
  ([39,49,71,131,133],[901,545,401]),
  ([39,49,71,131,135],[404]),
  ([39,49,71,131,139],[]),
  ([39,49,71,131,140],[]),
  ([39,49,71,131,143],[899,554,414]),
  ([39,49,71,131,148],[908,545,421]),
  ([39,49,71,131,153],[909,555,397]),
  ([39,49,71,131,156],[]),
  ([39,49,71,131,162],[]),
  ([39,49,71,131,163],[]),
  ([39,49,71,131,164],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b31ok : f4b31.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b32 : Array Row := #[
  ([39,49,71,131,165],[]),
  ([39,49,71,131,172],[899,557,441]),
  ([39,49,71,131,173],[443]),
  ([39,49,71,131,176],[]),
  ([39,49,71,131,177],[]),
  ([39,49,71,131,181],[920,545,445]),
  ([39,49,71,131,182],[447]),
  ([39,49,71,131,185],[]),
  ([39,49,71,131,186],[]),
  ([39,49,71,131,189],[43,568,345]),
  ([39,49,71,131,190],[359]),
  ([39,49,71,131,192],[922,261,89]),
  ([39,49,71,131,193],[331]),
  ([39,49,71,131,194],[203,451,373]),
  ([39,49,71,131,195],[204,453,373]),
  ([39,49,71,131,196],[335,363]),
  ([39,49,71,131,197],[363]),
  ([39,49,71,131,198],[335]),
  ([39,49,71,131,200],[]),
  ([39,49,71,131,201],[367]),
  ([39,49,71,131,202],[343]),
  ([39,49,71,131,241],[]),
  ([39,49,71,131,242],[]),
  ([39,49,71,131,243],[]),
  ([39,49,71,131,244],[]),
  ([39,49,71,131,250],[]),
  ([39,49,71,131,251],[]),
  ([39,49,71,131,252],[]),
  ([39,49,71,131,253],[]),
  ([39,49,71,131,257],[205,44,843,620]),
  ([39,49,71,131,260],[206,971,90,489]),
  ([39,49,71,131,263],[207])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b32ok : f4b32.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b33 : Array Row := #[
  ([39,49,71,131,264],[208]),
  ([39,49,71,131,274],[]),
  ([39,49,71,131,275],[]),
  ([39,49,71,131,276],[]),
  ([39,49,71,131,278],[]),
  ([39,49,71,131,280],[]),
  ([39,49,71,131,285],[870]),
  ([39,49,71,131,289],[516]),
  ([39,49,71,131,293],[1149,45,91,386]),
  ([39,49,71,131,309],[]),
  ([39,49,71,131,310],[]),
  ([39,49,71,131,311],[]),
  ([39,49,71,131,317],[]),
  ([39,49,71,131,323],[]),
  ([39,49,71,131,331],[]),
  ([39,49,71,131,336],[886,585]),
  ([39,49,71,131,343],[947,532]),
  ([39,49,71,131,348],[948,594,459]),
  ([39,49,71,131,349],[595,460]),
  ([39,49,71,131,350],[949,461]),
  ([39,49,71,131,351],[462]),
  ([39,49,71,131,352],[950,596]),
  ([39,49,71,131,353],[]),
  ([39,49,71,131,354],[597,463]),
  ([39,49,71,131,355],[464]),
  ([39,49,71,131,357],[951,465]),
  ([39,49,71,131,358],[466]),
  ([39,49,71,131,361],[]),
  ([39,49,71,131,364],[972,952,598,468,376]),
  ([39,49,71,131,365],[469]),
  ([39,49,71,131,367],[599,471]),
  ([39,49,71,131,368],[472])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b33ok : f4b33.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b34 : Array Row := #[
  ([39,49,71,131,370],[953,621,600,473,377]),
  ([39,49,71,131,371],[474]),
  ([39,49,71,131,373],[954,476]),
  ([39,49,71,131,374],[477]),
  ([39,49,71,131,378],[955,601,392]),
  ([39,49,71,131,385],[1150,956,602,481,378]),
  ([39,49,71,131,386],[482]),
  ([39,49,71,131,392],[889,603,486]),
  ([39,49,71,131,396],[958,535,488]),
  ([39,49,71,132,162],[375]),
  ([39,49,71,132,198],[375]),
  ([39,49,71,133,162],[375]),
  ([39,49,71,133,197],[375]),
  ([39,49,71,134,162],[375]),
  ([39,49,71,135,139],[375]),
  ([39,49,71,135,144],[375]),
  ([39,49,71,135,149],[375]),
  ([39,49,71,135,153],[404,375]),
  ([39,49,71,135,157],[375]),
  ([39,49,71,135,159],[375]),
  ([39,49,71,135,161],[209,437,375]),
  ([39,49,71,135,162],[375]),
  ([39,49,71,135,196],[375]),
  ([39,49,71,135,300],[]),
  ([39,49,71,135,303],[]),
  ([39,49,71,135,304],[]),
  ([39,49,71,135,305],[]),
  ([39,49,71,135,306],[]),
  ([39,49,71,135,307],[]),
  ([39,49,71,135,308],[]),
  ([39,49,71,135,309],[]),
  ([39,49,71,135,314],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b34ok : f4b34.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b35 : Array Row := #[
  ([39,49,71,135,315],[]),
  ([39,49,71,135,316],[]),
  ([39,49,71,135,317],[]),
  ([39,49,71,135,320],[]),
  ([39,49,71,135,321],[]),
  ([39,49,71,135,322],[]),
  ([39,49,71,135,323],[]),
  ([39,49,71,135,325],[210,369]),
  ([39,49,71,135,326],[]),
  ([39,49,71,135,328],[1151,915,563]),
  ([39,49,71,135,329],[564]),
  ([39,49,71,135,330],[916]),
  ([39,49,71,135,331],[]),
  ([39,49,71,135,334],[1152,917,885,565]),
  ([39,49,71,135,340],[]),
  ([39,49,71,135,341],[1153,918,566,531]),
  ([39,49,71,135,347],[]),
  ([39,49,71,135,348],[375]),
  ([39,49,71,135,352],[]),
  ([39,49,71,135,354],[]),
  ([39,49,71,135,357],[]),
  ([39,49,71,135,361],[]),
  ([39,49,71,135,364],[973,376]),
  ([39,49,71,135,367],[]),
  ([39,49,71,135,369],[]),
  ([39,49,71,135,370],[622,377]),
  ([39,49,71,135,373],[]),
  ([39,49,71,135,375],[]),
  ([39,49,71,135,378],[402]),
  ([39,49,71,135,381],[]),
  ([39,49,71,135,382],[]),
  ([39,49,71,135,383],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b35ok : f4b35.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b36 : Array Row := #[
  ([39,49,71,135,384],[]),
  ([39,49,71,135,385],[1154,919,567,378]),
  ([39,49,71,139,351],[]),
  ([39,49,71,140,348],[375]),
  ([39,49,71,142,162],[974,376]),
  ([39,49,71,142,317],[]),
  ([39,49,71,143,156],[975,376]),
  ([39,49,71,143,182],[211,375]),
  ([39,49,71,147,162],[623,377]),
  ([39,49,71,147,323],[]),
  ([39,49,71,148,156],[624,377]),
  ([39,49,71,148,173],[212,375]),
  ([39,49,71,153,173],[976,443,376]),
  ([39,49,71,153,182],[625,447,377]),
  ([39,49,71,153,351],[462,402]),
  ([39,49,71,156,348],[375]),
  ([39,49,71,162,167],[375]),
  ([39,49,71,162,348],[375]),
  ([39,49,71,162,349],[]),
  ([39,49,71,162,350],[]),
  ([39,49,71,162,351],[]),
  ([39,49,71,162,364],[977,376]),
  ([39,49,71,162,365],[978]),
  ([39,49,71,162,370],[626,377]),
  ([39,49,71,162,371],[627]),
  ([39,49,71,162,377],[213,979,628,422]),
  ([39,49,71,162,385],[1155,62,108,378]),
  ([39,49,71,162,386],[]),
  ([39,49,71,162,390],[980]),
  ([39,49,71,162,394],[629]),
  ([39,49,71,167,331],[1156]),
  ([39,49,71,173,300],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b36ok : f4b36.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b37 : Array Row := #[
  ([39,49,71,173,303],[]),
  ([39,49,71,173,306],[]),
  ([39,49,71,173,313],[]),
  ([39,49,71,173,319],[214,370]),
  ([39,49,71,173,327],[1157,884,569]),
  ([39,49,71,173,348],[375]),
  ([39,49,71,173,364],[981,376]),
  ([39,49,71,173,378],[982,423]),
  ([39,49,71,173,382],[983]),
  ([39,49,71,182,300],[]),
  ([39,49,71,182,303],[]),
  ([39,49,71,182,304],[]),
  ([39,49,71,182,313],[215,371]),
  ([39,49,71,182,319],[]),
  ([39,49,71,182,327],[1158,923,530]),
  ([39,49,71,182,348],[375]),
  ([39,49,71,182,370],[630,377]),
  ([39,49,71,182,378],[631,424]),
  ([39,49,71,182,381],[632]),
  ([39,49,71,195,378],[217,984,633,425]),
  ([39,49,71,196,386],[1160]),
  ([39,49,71,274,348],[394,375]),
  ([39,49,71,285,348],[871,894,375]),
  ([39,49,71,289,348],[517,540,375]),
  ([39,49,71,300,351],[]),
  ([39,49,71,303,351],[]),
  ([39,49,71,304,351],[]),
  ([39,49,71,306,351],[]),
  ([39,49,71,309,348],[375]),
  ([39,49,71,309,351],[]),
  ([39,49,71,309,365],[]),
  ([39,49,71,309,371],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b37ok : f4b37.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b38 : Array Row := #[
  ([39,49,71,309,386],[]),
  ([39,49,71,313,351],[]),
  ([39,49,71,313,365],[]),
  ([39,49,71,317,351],[]),
  ([39,49,71,317,365],[]),
  ([39,49,71,317,371],[]),
  ([39,49,71,317,386],[]),
  ([39,49,71,319,351],[]),
  ([39,49,71,319,371],[]),
  ([39,49,71,323,351],[]),
  ([39,49,71,323,365],[]),
  ([39,49,71,323,371],[]),
  ([39,49,71,323,386],[]),
  ([39,49,71,326,377],[218]),
  ([39,49,71,327,351],[1161]),
  ([39,49,71,327,386],[1162]),
  ([39,49,71,331,351],[]),
  ([39,49,71,331,365],[]),
  ([39,49,71,331,371],[]),
  ([39,49,71,331,386],[1163]),
  ([39,49,71,336,348],[887,896,375]),
  ([39,49,71,340,390],[1164,888,911]),
  ([39,49,71,343,348],[533,542,375]),
  ([39,49,71,347,394],[1165,534,559]),
  ([39,49,71,348],[375,375,375]),
  ([39,49,71,348,351],[375]),
  ([39,49,71,348,361],[375]),
  ([39,49,71,348,378],[397,426,375]),
  ([39,49,71,351,361],[]),
  ([39,49,71,351,378],[404,427]),
  ([39,49,71,355,378],[406,428]),
  ([39,49,71,358,378],[407,429])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b38ok : f4b38.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b39 : Array Row := #[
  ([39,49,71,361,365],[]),
  ([39,49,71,361,371],[]),
  ([39,49,71,361,386],[]),
  ([39,49,71,364],[156,985,387,873,376,84,376,376]),
  ([39,49,71,365,369],[986]),
  ([39,49,71,365,378],[987,411,430]),
  ([39,49,71,370],[148,23,377,634,388,520,377,377]),
  ([39,49,71,371,375],[635]),
  ([39,49,71,371,378],[636,418,432]),
  ([39,49,71,378,386],[434,440]),
  ([39,49,71,378,392],[46,988,909,912,435,441]),
  ([39,49,71,378,396],[92,637,555,560,436,445]),
  ([39,49,71,385],[1166,491,845,39,378,85,378,378]),
  ([39,49,71,392,396],[220,1167,913,920,557,561]),
  ([39,49,72,135,162],[]),
  ([39,49,73,135,162],[]),
  ([39,49,81,92,135],[1168,964,610,405]),
  ([39,49,81,103,135],[1169]),
  ([39,49,81,103,386],[1170]),
  ([39,49,81,135,162],[1171,386]),
  ([39,49,81,135,196],[1172,386]),
  ([39,49,81,135,331],[1173]),
  ([39,49,83,86,131],[1174,264,348,386]),
  ([39,49,83,131,378],[988,350,615,392]),
  ([39,49,83,135,153],[976,351]),
  ([39,49,83,135,378],[982,352,402]),
  ([39,49,83,135,382],[983,353]),
  ([39,49,83,162,365],[974,354]),
  ([39,49,83,173,378],[976,355,423]),
  ([39,49,83,182,378],[984,356,424]),
  ([39,49,83,351,378],[357,404,427]),
  ([39,49,86,131,378],[266,991,637,392])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b39ok : f4b39.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b40 : Array Row := #[
  ([39,49,86,135,153],[267,625]),
  ([39,49,86,135,378],[268,631,402]),
  ([39,49,86,135,381],[269,632]),
  ([39,49,86,162,371],[270,623]),
  ([39,49,86,173,378],[271,633,423]),
  ([39,49,86,182,378],[272,625,424]),
  ([39,49,86,351,378],[273,404,427]),
  ([39,49,91,135,378],[402]),
  ([39,49,92,131,153],[1025,993,671,639,426,397]),
  ([39,49,92,131,378],[1038,1003,684,649,459,392]),
  ([39,49,92,135,153],[1044,690,427,404]),
  ([39,49,92,135,274],[]),
  ([39,49,92,135,293],[1175,994,640]),
  ([39,49,92,135,378],[1058,704,462,402]),
  ([39,49,92,153,173],[1065,709,443]),
  ([39,49,92,153,182],[1066,712,447]),
  ([39,49,92,153,351],[1067,713,462,402]),
  ([39,49,92,173,274],[]),
  ([39,49,92,173,293],[1176,964,641]),
  ([39,49,92,173,378],[1095,732,423]),
  ([39,49,92,182,274],[]),
  ([39,49,92,182,293],[1177,995,610]),
  ([39,49,92,182,378],[1102,747,424]),
  ([39,49,92,195,378],[222,1104,750,425]),
  ([39,49,92,274,285],[877,960]),
  ([39,49,92,274,289],[523,606]),
  ([39,49,92,274,348],[1114,760,379,394]),
  ([39,49,92,274,351],[]),
  ([39,49,92,274,365],[]),
  ([39,49,92,274,371],[]),
  ([39,49,92,285,378],[1115,961,992,761]),
  ([39,49,92,289,378],[1119,763,607,638])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b40ok : f4b40.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b41 : Array Row := #[
  ([39,49,92,293,351],[1179]),
  ([39,49,92,293,386],[1180]),
  ([39,49,92,348,378],[1123,769,397,426]),
  ([39,49,92,351,378],[1124,770,404,427]),
  ([39,49,92,355,378],[1125,771,406,428]),
  ([39,49,92,358,378],[1126,772,407,429]),
  ([39,49,92,365,378],[1127,773,411,430]),
  ([39,49,92,371,378],[1128,774,418,432]),
  ([39,49,92,378,386],[1129,775,434,440]),
  ([39,49,93,135,378],[1058,462,402]),
  ([39,49,94,135,378],[704,462,402]),
  ([39,49,96,135,153],[404]),
  ([39,49,96,135,274],[]),
  ([39,49,96,135,293],[1181,1004,650]),
  ([39,49,96,135,378],[402]),
  ([39,49,96,173,378],[1096,423]),
  ([39,49,96,182,378],[748,424]),
  ([39,49,97,135,274],[]),
  ([39,49,97,135,293],[1182,651]),
  ([39,49,97,135,378],[1058,464,402]),
  ([39,49,97,173,378],[1095,423]),
  ([39,49,99,135,274],[]),
  ([39,49,99,135,293],[1183,1005]),
  ([39,49,99,135,378],[704,466,402]),
  ([39,49,99,182,378],[747,424]),
  ([39,49,103,131,153],[1008,654]),
  ([39,49,103,131,274],[375]),
  ([39,49,103,131,293],[1185,386]),
  ([39,49,103,131,378],[1015,661,392]),
  ([39,49,103,135,153],[]),
  ([39,49,103,135,273],[223,389]),
  ([39,49,103,135,274],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b41ok : f4b41.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b42 : Array Row := #[
  ([39,49,103,135,293],[1187]),
  ([39,49,103,135,378],[402]),
  ([39,49,103,142,274],[]),
  ([39,49,103,147,274],[]),
  ([39,49,103,153,173],[1021]),
  ([39,49,103,153,182],[668]),
  ([39,49,103,153,351],[402]),
  ([39,49,103,162,377],[225,422]),
  ([39,49,103,167,293],[1188]),
  ([39,49,103,173,378],[1022,423]),
  ([39,49,103,182,378],[669,424]),
  ([39,49,103,195,378],[226,425]),
  ([39,49,103,274,348],[379,394]),
  ([39,49,103,274,351],[]),
  ([39,49,103,274,365],[]),
  ([39,49,103,274,371],[]),
  ([39,49,103,274,377],[227]),
  ([39,49,103,274,386],[]),
  ([39,49,103,278,365],[]),
  ([39,49,103,280,371],[]),
  ([39,49,103,293,351],[1189]),
  ([39,49,103,293,365],[1190,965,1007]),
  ([39,49,103,293,371],[1191,611,653]),
  ([39,49,103,293,386],[1193]),
  ([39,49,103,293,390],[1194,966,1009]),
  ([39,49,103,293,394],[1195,612,655]),
  ([39,49,103,348,378],[397,426]),
  ([39,49,103,351,378],[404,427]),
  ([39,49,103,355,378],[406,428]),
  ([39,49,103,358,378],[407,429]),
  ([39,49,103,365,378],[411,430]),
  ([39,49,103,371,378],[418,432])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b42ok : f4b42.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b43 : Array Row := #[
  ([39,49,103,378,386],[434,440]),
  ([39,49,103,378,392],[13,1023,1008,1010,435,441]),
  ([39,49,103,378,396],[15,670,654,656,436,445]),
  ([39,49,108,135,274],[]),
  ([39,49,111,135,274],[]),
  ([39,49,116,135,293],[1196]),
  ([39,49,118,135,378],[1058,1018,1016,443,402]),
  ([39,49,120,131,378],[1023,662,392]),
  ([39,49,120,135,153],[1021]),
  ([39,49,120,135,378],[1022,402]),
  ([39,49,120,173,378],[1021,423]),
  ([39,49,120,182,378],[254,424]),
  ([39,49,120,351,378],[404,427]),
  ([39,49,123,135,378],[704,666,663,447,402]),
  ([39,49,125,131,378],[1024,670,392]),
  ([39,49,125,135,153],[668]),
  ([39,49,125,135,378],[669,402]),
  ([39,49,125,173,378],[253,423]),
  ([39,49,125,182,378],[668,424]),
  ([39,49,125,351,378],[404,427]),
  ([39,49,127,135,378],[229,453,402]),
  ([39,49,130,135,378],[402]),
  ([39,49,131,135,153],[1045,691,427,404]),
  ([39,49,131,135,274],[375]),
  ([39,49,131,135,293],[1197,1028,674,386]),
  ([39,49,131,135,378],[1059,705,462,402,392]),
  ([39,49,131,140,378],[1060,706,392]),
  ([39,49,131,153],[1069,435,1026,715,436,672,397]),
  ([39,49,131,153,156],[1061,707]),
  ([39,49,131,153,162],[1062,708]),
  ([39,49,131,153,378],[1068,714]),
  ([39,49,131,156,162],[1071,717,392])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b43ok : f4b43.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b44 : Array Row := #[
  ([39,49,131,156,378],[1073,719,392]),
  ([39,49,131,162,274],[375]),
  ([39,49,131,162,275],[]),
  ([39,49,131,162,276],[]),
  ([39,49,131,162,293],[1198,63,109,386]),
  ([39,49,131,162,378],[1079,725,392]),
  ([39,49,131,165,378],[1081,727,392]),
  ([39,49,131,173,378],[1097,733,423,392]),
  ([39,49,131,182,378],[1103,749,424,392]),
  ([39,49,131,197,378],[1105,751,364,392]),
  ([39,49,131,198,378],[1106,336,752,392]),
  ([39,49,131,274],[1035,375,681,375,375]),
  ([39,49,131,293],[1199,492,846,1037,386,683,386,386]),
  ([39,49,131,351,378],[1130,776,404,427,392]),
  ([39,49,131,361,378],[1131,777,392]),
  ([39,49,131,378],[1132,486,1039,392,779,488,685,392,392]),
  ([39,49,131,378,392],[1,1026,1027,778,435,441,392]),
  ([39,49,131,378,396],[1133,0,672,673,436,445,392]),
  ([39,49,132,156,162],[1071,398]),
  ([39,49,132,162,379],[1080]),
  ([39,49,133,156,162],[717,400]),
  ([39,49,133,162,380],[726]),
  ([39,49,135,139,274],[394]),
  ([39,49,135,140,153],[]),
  ([39,49,135,140,378],[402]),
  ([39,49,135,153],[423,424,392]),
  ([39,49,135,153,156],[]),
  ([39,49,135,153,162],[392]),
  ([39,49,135,153,165],[]),
  ([39,49,135,153,173],[]),
  ([39,49,135,153,182],[]),
  ([39,49,135,153,189],[1063,351,398])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b44ok : f4b44.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b45 : Array Row := #[
  ([39,49,135,153,190],[360]),
  ([39,49,135,153,192],[267,710,400]),
  ([39,49,135,153,193],[332]),
  ([39,49,135,153,197],[1064,365,398]),
  ([39,49,135,153,198],[337,711,400]),
  ([39,49,135,153,309],[]),
  ([39,49,135,153,336],[1065,1016]),
  ([39,49,135,153,343],[712,663]),
  ([39,49,135,153,351],[]),
  ([39,49,135,153,378],[397]),
  ([39,49,135,154,162],[402]),
  ([39,49,135,155,162],[402]),
  ([39,49,135,156,157],[402]),
  ([39,49,135,156,159],[402]),
  ([39,49,135,156,162],[402]),
  ([39,49,135,156,196],[1072,718,402]),
  ([39,49,135,156,378],[402]),
  ([39,49,135,156,381],[]),
  ([39,49,135,156,382],[]),
  ([39,49,135,162,187],[402]),
  ([39,49,135,162,231],[230,393]),
  ([39,49,135,162,274],[394]),
  ([39,49,135,162,275],[]),
  ([39,49,135,162,276],[]),
  ([39,49,135,162,277],[]),
  ([39,49,135,162,293],[1201,395]),
  ([39,49,135,162,294],[]),
  ([39,49,135,162,295],[]),
  ([39,49,135,162,377],[232,422]),
  ([39,49,135,162,378],[397,402]),
  ([39,49,135,162,379],[]),
  ([39,49,135,162,380],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b45ok : f4b45.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b46 : Array Row := #[
  ([39,49,135,165,378],[402]),
  ([39,49,135,173,378],[423,402]),
  ([39,49,135,177,378],[402]),
  ([39,49,135,182,378],[424,402]),
  ([39,49,135,186,378],[402]),
  ([39,49,135,189,378],[1084,352,399,402]),
  ([39,49,135,190,378],[361,402]),
  ([39,49,135,192,378],[268,736,401,402]),
  ([39,49,135,193,378],[333,402]),
  ([39,49,135,195,378],[233,425,402]),
  ([39,49,135,196,293],[1202,395]),
  ([39,49,135,197,378],[1085,366,399,402]),
  ([39,49,135,198,378],[338,737,401,402]),
  ([39,49,135,241,378],[1086,1041,402]),
  ([39,49,135,242,378],[402]),
  ([39,49,135,243,378],[1087,402]),
  ([39,49,135,244,378],[1088,402]),
  ([39,49,135,250,378],[738,687,402]),
  ([39,49,135,251,378],[402]),
  ([39,49,135,252,378],[739,402]),
  ([39,49,135,253,378],[740,402]),
  ([39,49,135,257,378],[234,1089,844,1042,402]),
  ([39,49,135,260,378],[235,741,490,688,402]),
  ([39,49,135,274,300],[]),
  ([39,49,135,274,303],[]),
  ([39,49,135,274,309],[]),
  ([39,49,135,274,313],[]),
  ([39,49,135,274,317],[]),
  ([39,49,135,274,319],[]),
  ([39,49,135,274,323],[]),
  ([39,49,135,274,326],[]),
  ([39,49,135,274,331],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b46ok : f4b46.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b47 : Array Row := #[
  ([39,49,135,274,348],[379,394]),
  ([39,49,135,274,361],[]),
  ([39,49,135,274,369],[]),
  ([39,49,135,274,375],[]),
  ([39,49,135,274,378],[402]),
  ([39,49,135,275,378],[402]),
  ([39,49,135,276,378],[402]),
  ([39,49,135,278,378],[402]),
  ([39,49,135,280,378],[402]),
  ([39,49,135,285,378],[1090,962,1043,402]),
  ([39,49,135,289,378],[742,608,689,402]),
  ([39,49,135,293,309],[1203]),
  ([39,49,135,293,317],[1204]),
  ([39,49,135,293,323],[1205]),
  ([39,49,135,293,327],[1207,1091,743]),
  ([39,49,135,293,331],[1208]),
  ([39,49,135,293,340],[1209]),
  ([39,49,135,293,347],[1210]),
  ([39,49,135,293,361],[1211]),
  ([39,49,135,293,378],[1212,1092,744,402]),
  ([39,49,135,300,378],[402]),
  ([39,49,135,301,378],[402]),
  ([39,49,135,302,378],[402]),
  ([39,49,135,303,378],[402]),
  ([39,49,135,304,378],[402]),
  ([39,49,135,306,378],[402]),
  ([39,49,135,309,378],[402]),
  ([39,49,135,310,378],[402]),
  ([39,49,135,311,378],[402]),
  ([39,49,135,313,378],[402]),
  ([39,49,135,317,378],[402]),
  ([39,49,135,319,378],[402])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b47ok : f4b47.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b48 : Array Row := #[
  ([39,49,135,323,378],[402]),
  ([39,49,135,327,378],[1213,1093,745,402]),
  ([39,49,135,331,378],[1094,746,402]),
  ([39,49,135,336,378],[1095,1017,1044,402]),
  ([39,49,135,338,378],[1096,402]),
  ([39,49,135,343,378],[747,664,690,402]),
  ([39,49,135,345,378],[748,402]),
  ([39,49,135,348,378],[397,426,402]),
  ([39,49,135,351,378],[427,402]),
  ([39,49,135,353,378],[402]),
  ([39,49,135,355,378],[406,428,402]),
  ([39,49,135,358,378],[407,429,402]),
  ([39,49,135,361,378],[402]),
  ([39,49,135,365,378],[411,430,402]),
  ([39,49,135,371,378],[418,432,402]),
  ([39,49,135,378],[443,402,447,402,402]),
  ([39,49,135,378,386],[434,440,402]),
  ([39,49,135,378,392],[4,1097,1045,1047,435,441,402]),
  ([39,49,135,378,396],[6,749,691,693,436,445,402]),
  ([39,49,140,173,378],[406,423]),
  ([39,49,140,182,378],[407,424]),
  ([39,49,140,351,378],[404,427]),
  ([39,49,142,156,162],[410]),
  ([39,49,143,156,162],[1071,413]),
  ([39,49,147,156,162],[417]),
  ([39,49,148,156,162],[717,420]),
  ([39,49,153,156,173],[410]),
  ([39,49,153,156,182],[417]),
  ([39,49,153,162,173],[1064,413]),
  ([39,49,153,162,182],[711,420]),
  ([39,49,153,173],[157,1063,425,408]),
  ([39,49,153,173,378],[1084,409])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b48ok : f4b48.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b49 : Array Row := #[
  ([39,49,153,182],[149,425,710,415]),
  ([39,49,153,182,378],[736,416]),
  ([39,49,153,351],[402,402,402]),
  ([39,49,153,351,378],[404,402]),
  ([39,49,156,162,195],[236,425,422,437]),
  ([39,49,156,162,351],[427]),
  ([39,49,156,162,355],[428]),
  ([39,49,156,162,358],[429]),
  ([39,49,156,162,365],[430]),
  ([39,49,156,162,368],[431]),
  ([39,49,156,162,371],[432]),
  ([39,49,156,162,374],[433]),
  ([39,49,156,162,386],[434]),
  ([39,49,156,162,392],[1070,435]),
  ([39,49,156,162,396],[716,436]),
  ([39,49,156,173,378],[411,423]),
  ([39,49,156,173,381],[412]),
  ([39,49,156,182,378],[418,424]),
  ([39,49,156,182,382],[419]),
  ([39,49,156,351,378],[404,427]),
  ([39,49,162,173,378],[1085,414,423]),
  ([39,49,162,182,378],[737,421,424]),
  ([39,49,162,274,351],[]),
  ([39,49,162,274,365],[]),
  ([39,49,162,274,371],[]),
  ([39,49,162,275,351],[]),
  ([39,49,162,276,351],[]),
  ([39,49,162,293,386],[1214]),
  ([39,49,162,351,378],[404,427]),
  ([39,49,162,377],[237,150,158,422,422,422]),
  ([39,49,162,378,392],[64,1105,1062,1074,435,441]),
  ([39,49,162,378,396],[110,752,708,720,436,445])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b49ok : f4b49.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b50 : Array Row := #[
  ([39,49,173,177,378],[423]),
  ([39,49,173,182,378],[238,247,250,440,453,424,423]),
  ([39,49,173,190,378],[362,423]),
  ([39,49,173,195,378],[239,251,425,423]),
  ([39,49,173,309,378],[423]),
  ([39,49,173,336,378],[1018,1065,423]),
  ([39,49,173,343,378],[241,750,665,709,423]),
  ([39,49,173,351,378],[404,427,423]),
  ([39,49,173,378],[159,423,453,423,423]),
  ([39,49,182,186,378],[424]),
  ([39,49,182,193,378],[334,424]),
  ([39,49,182,195,378],[242,248,425,424]),
  ([39,49,182,309,378],[424]),
  ([39,49,182,336,378],[244,1104,1019,1066,424]),
  ([39,49,182,343,378],[666,712,424]),
  ([39,49,182,351,378],[404,427,424]),
  ([39,49,182,378],[151,453,424,424,424]),
  ([39,49,195,378],[245,152,160,425,425,425]),
  ([39,49,274,317,365],[]),
  ([39,49,274,323,371],[]),
  ([39,49,274,348],[379,394,379,394,379,394]),
  ([39,49,274,351,361],[]),
  ([39,49,293,331,386],[1215]),
  ([39,49,309,351,378],[404,427]),
  ([39,49,336,351,378],[1020,1058,1067,404,427]),
  ([39,49,343,351,378],[667,704,713,404,427]),
  ([39,49,348,378],[397,426,397,426,397,426]),
  ([39,49,351,378],[404,427,404,427,404,427]),
  ([39,49,355,378],[406,428,406,428,406,428]),
  ([39,49,358,378],[407,429,407,429,407,429]),
  ([39,49,365,378],[161,411,430,411,430,411,430]),
  ([39,49,371,378],[153,418,432,418,432,418,432])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b50ok : f4b50.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b51 : Array Row := #[
  ([39,49,378,386],[434,440,434,440,434,440]),
  ([39,49,378,392],[162,847,1069,435,1068,1082,441,1083,435,441,435,441]),
  ([39,49,378,396],[154,493,436,445,715,436,714,734,445,735,436,445]),
  ([39,55,71,92,135],[490]),
  ([39,55,71,103,135],[]),
  ([39,55,71,103,365],[]),
  ([39,55,71,135,162],[1141,489]),
  ([39,55,71,135,317],[]),
  ([39,55,103,135,274],[]),
  ([39,56,71,86,131],[1174,275,132,489]),
  ([39,56,71,92,289],[515]),
  ([39,56,71,131,396],[1167,134,535,493]),
  ([39,56,71,135,327],[1157,1147,569]),
  ([39,56,71,331,386],[1148,1156]),
  ([39,56,81,103,135],[]),
  ([39,56,86,135,378],[276,490,633]),
  ([39,56,92,135,293],[1176,1168,641]),
  ([39,56,103,135,293],[1169]),
  ([39,56,103,293,386],[1170,1188]),
  ([39,56,135,162,293],[1171,492]),
  ([39,56,135,293,331],[1173,1196]),
  ([39,56,135,343,378],[750,664,690]),
  ([39,58,71,79,92],[1242,606,523,517]),
  ([39,58,71,92,123],[1253,1217,533,525,496]),
  ([39,58,71,92,250],[1262,571]),
  ([39,58,71,92,260],[1264,1220,574]),
  ([39,58,71,92,289],[1265,642,580,515]),
  ([39,58,71,92,343],[1267,1218,588,498]),
  ([39,58,71,131,289],[1321,680,580,516]),
  ([39,58,71,131,396],[1322,1219,681,594,535,499]),
  ([39,58,71,289,348],[1402,759,517,540]),
  ([39,58,71,336,343],[1403,1216,1217])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b51ok : f4b51.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b52 : Array Row := #[
  ([39,58,71,343,348],[1404,760,533,542]),
  ([39,58,71,343,378],[1405,496,497]),
  ([39,58,92,274,289],[1483,759,523,606]),
  ([39,58,92,274,343],[1484,1223,760]),
  ([39,58,92,289,378],[1486,1225,764,607,638]),
  ([39,58,92,343,378],[1487,1226,769,496,497]),
  ([39,58,103,343,378],[1533,496,497]),
  ([39,58,135,289,378],[1564,765,608,689]),
  ([39,58,135,343,378],[1565,770,664,690,496,497]),
  ([39,58,343,378],[1576,761,1224,496,497,496,497,496,497]),
  ([39,59,71,92,343],[1267,1227,589,501]),
  ([39,60,71,92,289],[515]),
  ([39,60,71,92,343],[1228,502]),
  ([39,65,71,92,298],[1266,1230,643,582,519]),
  ([39,65,71,92,343],[1267,1231,1229,590,503]),
  ([39,67,71,86,92],[1248,277,520]),
  ([39,67,71,92,289],[1268,642,581,515]),
  ([39,67,71,92,343],[1270,1234,591,511]),
  ([39,67,86,92],[1452,617,1235,279,256,278,1236,634,507,618,508]),
  ([39,67,86,92,103],[1449,280,619]),
  ([39,67,86,92,135],[1450,281,622]),
  ([39,67,86,92,182],[1451,282,630]),
  ([39,67,86,99,135],[1453,283,505]),
  ([39,67,86,103,135],[1456,284,505]),
  ([39,67,86,103,371],[1457,285,635]),
  ([39,67,86,135,162],[1463,287,627,506]),
  ([39,67,86,135,375],[1466,289,635]),
  ([39,67,103,135,260],[509]),
  ([39,67,103,135,293],[1513,657,510]),
  ([39,69,86,103,135],[1456,290,512]),
  ([39,69,103,135,298],[1515,513]),
  ([39,71,79,86,92],[291,505])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b52ok : f4b52.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b53 : Array Row := #[
  ([39,71,79,92],[1243,607,525]),
  ([39,71,79,92,103],[]),
  ([39,71,79,92,135],[608]),
  ([39,71,79,92,182],[609]),
  ([39,71,79,92,289],[]),
  ([39,71,79,99,135],[515]),
  ([39,71,79,103,135],[515]),
  ([39,71,79,103,351],[]),
  ([39,71,79,135,162],[516]),
  ([39,71,79,135,361],[]),
  ([39,71,83,92,289],[51,515]),
  ([39,71,83,131,396],[53,1247,615,568,535]),
  ([39,71,83,135,341],[1246,500,531]),
  ([39,71,83,347,394],[534,559]),
  ([39,71,85,103,135],[1427,519]),
  ([39,71,86,92,182],[292,631,505,515]),
  ([39,71,86,92,195],[1428,294,633,512,519]),
  ([39,71,86,92,289],[295,515]),
  ([39,71,86,92,371],[296,636]),
  ([39,71,86,96,182],[297,631]),
  ([39,71,86,97,182],[298,632]),
  ([39,71,86,103,147],[299,623]),
  ([39,71,86,103,371],[300,627]),
  ([39,71,86,103,377],[301,628]),
  ([39,71,86,103,394],[302,629]),
  ([39,71,86,131,182],[303,631,506,516]),
  ([39,71,86,131,396],[305,1251,637,535]),
  ([39,71,86,135,148],[306,624]),
  ([39,71,86,135,319],[307,495]),
  ([39,71,86,162,371],[308,623]),
  ([39,71,86,182,378],[310,625]),
  ([39,71,86,323,371],[311])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b53ok : f4b53.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b54 : Array Row := #[
  ([39,71,92,103,289],[515]),
  ([39,71,92,103,298],[1429,519]),
  ([39,71,92,103,396],[1290,661,521]),
  ([39,71,92,120,289],[515]),
  ([39,71,92,123,135],[1304,664]),
  ([39,71,92,123,173],[1305,665]),
  ([39,71,92,123,182],[1306,666]),
  ([39,71,92,123,351],[1307,667]),
  ([39,71,92,125,182],[1308,669]),
  ([39,71,92,125,289],[515]),
  ([39,71,92,131,343],[1324,1273,684,588,532]),
  ([39,71,92,131,396],[1325,1274,685,649,594,535,521]),
  ([39,71,92,135,247],[1255,694]),
  ([39,71,92,135,250],[695]),
  ([39,71,92,135,260],[696]),
  ([39,71,92,135,289],[698,515]),
  ([39,71,92,135,298],[1430,701,519]),
  ([39,71,92,135,341],[1345,1256,703,586,531]),
  ([39,71,92,135,343],[1346,704]),
  ([39,71,92,135,396],[1347,705,521]),
  ([39,71,92,140,289],[515]),
  ([39,71,92,156,289],[515]),
  ([39,71,92,162,289],[515]),
  ([39,71,92,162,396],[1354,725,521]),
  ([39,71,92,173,250],[728]),
  ([39,71,92,173,260],[729]),
  ([39,71,92,173,289],[730,515]),
  ([39,71,92,173,298],[1431,731,519]),
  ([39,71,92,173,343],[1374,732]),
  ([39,71,92,182,192],[1381,292,736,508,521]),
  ([39,71,92,182,198],[1383,339,737,521]),
  ([39,71,92,182,250],[738])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b54ok : f4b54.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b55 : Array Row := #[
  ([39,71,92,182,252],[739]),
  ([39,71,92,182,253],[740]),
  ([39,71,92,182,260],[741,509]),
  ([39,71,92,182,289],[742,515]),
  ([39,71,92,182,293],[54,1259,744,510,610]),
  ([39,71,92,182,327],[1386,1260,745,530]),
  ([39,71,92,182,331],[1387,746]),
  ([39,71,92,182,343],[1389,747]),
  ([39,71,92,195,343],[1395,750,514]),
  ([39,71,92,250,351],[753]),
  ([39,71,92,250,358],[754]),
  ([39,71,92,250,371],[755]),
  ([39,71,92,250,386],[756]),
  ([39,71,92,260,351],[757]),
  ([39,71,92,260,365],[758]),
  ([39,71,92,274,289],[606,515]),
  ([39,71,92,285,289],[1240,1242,515]),
  ([39,71,92,285,343],[1403,1241,1253,761]),
  ([39,71,92,289],[1269,515,645,515,515]),
  ([39,71,92,289,309],[515]),
  ([39,71,92,289,336],[1243,1252,762,515]),
  ([39,71,92,289,343],[1406,763,515]),
  ([39,71,92,289,348],[1407,764,517,540,515]),
  ([39,71,92,289,351],[765,515]),
  ([39,71,92,289,361],[515]),
  ([39,71,92,289,378],[1408,607,638,515]),
  ([39,71,92,298],[1432,613,1244,1271,519,648,519,519]),
  ([39,71,92,343,348],[1409,769,533,542]),
  ([39,71,92,343,351],[1410,770]),
  ([39,71,92,343,355],[1411,771]),
  ([39,71,92,343,358],[1412,772]),
  ([39,71,92,343,365],[1413,773])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b55ok : f4b55.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b56 : Array Row := #[
  ([39,71,92,343,371],[1414,774]),
  ([39,71,92,343,386],[1415,775]),
  ([39,71,92,396],[1416,585,1272,521,779,601,649,521,521]),
  ([39,71,93,103,289],[523]),
  ([39,71,93,125,182],[1308]),
  ([39,71,93,135,343],[1346]),
  ([39,71,94,103,289],[523]),
  ([39,71,96,125,182],[669]),
  ([39,71,96,135,250],[695]),
  ([39,71,96,135,260],[696]),
  ([39,71,96,135,289],[698,523]),
  ([39,71,96,135,343],[704]),
  ([39,71,96,182,345],[748]),
  ([39,71,97,125,182],[1308]),
  ([39,71,97,135,250],[]),
  ([39,71,97,135,260],[697]),
  ([39,71,97,135,289],[523]),
  ([39,71,97,135,298],[1433,702,524]),
  ([39,71,97,135,343],[1346]),
  ([39,71,97,173,343],[1374]),
  ([39,71,97,182,346],[1390]),
  ([39,71,99,123,135],[]),
  ([39,71,99,135,250],[]),
  ([39,71,99,135,260],[]),
  ([39,71,99,135,289],[523]),
  ([39,71,99,135,343],[]),
  ([39,71,99,173,343],[1375]),
  ([39,71,103,114,182],[]),
  ([39,71,103,123,135],[]),
  ([39,71,103,123,173],[1300]),
  ([39,71,103,123,351],[]),
  ([39,71,103,125,394],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b56ok : f4b56.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b57 : Array Row := #[
  ([39,71,103,131,181],[1279,656,521]),
  ([39,71,103,131,250],[375]),
  ([39,71,103,131,260],[1434,489]),
  ([39,71,103,131,289],[523,516]),
  ([39,71,103,131,343],[1291,532]),
  ([39,71,103,131,396],[1292,661,525,535]),
  ([39,71,103,133,396],[525]),
  ([39,71,103,135,181],[521]),
  ([39,71,103,135,247],[]),
  ([39,71,103,135,248],[]),
  ([39,71,103,135,249],[]),
  ([39,71,103,135,250],[]),
  ([39,71,103,135,256],[1134,692]),
  ([39,71,103,135,260],[]),
  ([39,71,103,135,288],[55,522]),
  ([39,71,103,135,289],[523]),
  ([39,71,103,135,298],[1436,524]),
  ([39,71,103,135,341],[1278,531]),
  ([39,71,103,135,343],[]),
  ([39,71,103,135,396],[525]),
  ([39,71,103,142,260],[]),
  ([39,71,103,147,250],[]),
  ([39,71,103,156,396],[717,527]),
  ([39,71,103,167,250],[]),
  ([39,71,103,173,343],[1301]),
  ([39,71,103,173,396],[1302,528]),
  ([39,71,103,182,327],[1281,530]),
  ([39,71,103,247,371],[]),
  ([39,71,103,247,386],[]),
  ([39,71,103,250,351],[]),
  ([39,71,103,250,365],[]),
  ([39,71,103,250,371],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b57ok : f4b57.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b58 : Array Row := #[
  ([39,71,103,250,386],[]),
  ([39,71,103,250,394],[]),
  ([39,71,103,252,371],[]),
  ([39,71,103,253,386],[]),
  ([39,71,103,260,351],[]),
  ([39,71,103,260,365],[]),
  ([39,71,103,260,371],[721]),
  ([39,71,103,260,377],[722]),
  ([39,71,103,260,386],[]),
  ([39,71,103,260,390],[]),
  ([39,71,103,289,348],[517,540]),
  ([39,71,103,289,351],[]),
  ([39,71,103,289,365],[]),
  ([39,71,103,289,371],[]),
  ([39,71,103,289,386],[]),
  ([39,71,103,293,371],[723,611,653]),
  ([39,71,103,293,394],[56,724,612,655]),
  ([39,71,103,298,365],[1437]),
  ([39,71,103,343,348],[533,542]),
  ([39,71,103,343,351],[]),
  ([39,71,103,343,355],[]),
  ([39,71,103,343,365],[]),
  ([39,71,103,343,371],[]),
  ([39,71,103,343,386],[]),
  ([39,71,103,347,394],[534,559]),
  ([39,71,103,351,396],[]),
  ([39,71,103,378,396],[9,725,654,656,555,560]),
  ([39,71,103,392,396],[14,1303,1277,1279,557,561]),
  ([39,71,108,135,260],[]),
  ([39,71,111,135,250],[]),
  ([39,71,116,135,182],[1293]),
  ([39,71,116,135,250],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b58ok : f4b58.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b59 : Array Row := #[
  ([39,71,118,135,343],[1346,1297,1294]),
  ([39,71,120,123,135],[1300]),
  ([39,71,120,131,396],[1303,662,525,535]),
  ([39,71,120,135,343],[1301]),
  ([39,71,120,135,396],[1302,526]),
  ([39,71,120,173,343],[1300]),
  ([39,71,120,343,351],[]),
  ([39,71,123,135,162],[532]),
  ([39,71,123,135,309],[]),
  ([39,71,123,135,336],[1305,1294]),
  ([39,71,123,135,378],[496,663]),
  ([39,71,125,131,182],[1309,669,532]),
  ([39,71,125,131,396],[1310,670,525,535]),
  ([39,71,125,182,336],[1295]),
  ([39,71,125,182,378],[737,668]),
  ([39,71,131,135,181],[1331,693]),
  ([39,71,131,135,250],[695,375]),
  ([39,71,131,135,260],[1438,696,489]),
  ([39,71,131,135,289],[698,516]),
  ([39,71,131,135,343],[1348,704,532]),
  ([39,71,131,135,396],[1349,705,535]),
  ([39,71,131,140,396],[1350,706,535]),
  ([39,71,131,156,396],[1351,719,535]),
  ([39,71,131,162,181],[1353,720]),
  ([39,71,131,162,250],[375]),
  ([39,71,131,162,260],[1439,489]),
  ([39,71,131,162,289],[516]),
  ([39,71,131,162,343],[1355,532]),
  ([39,71,131,162,396],[1356,725,535]),
  ([39,71,131,165,396],[1357,727,535]),
  ([39,71,131,173,396],[1378,733,535]),
  ([39,71,131,181],[1379,561,1313,734,560,673,545])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b59ok : f4b59.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b60 : Array Row := #[
  ([39,71,131,181,396],[1380,735]),
  ([39,71,131,182,198],[1384,340,737,535]),
  ([39,71,131,182,396],[1392,749,535]),
  ([39,71,131,197,396],[1396,751,535]),
  ([39,71,131,198,396],[1397,341,752,535]),
  ([39,71,131,250],[1318,375,677,375,375]),
  ([39,71,131,260],[1440,614,1245,1320,489,679,489,489]),
  ([39,71,131,289],[1323,516,682,516,516]),
  ([39,71,131,343],[1417,592,1326,532,684,532,532]),
  ([39,71,131,351,396],[1418,776,535]),
  ([39,71,131,361,396],[1419,777,535]),
  ([39,71,131,378,396],[1420,499,672,673,555,560,535]),
  ([39,71,131,392,396],[2,1312,1313,778,557,561,535]),
  ([39,71,131,396],[1421,603,1327,535,779,601,685,535,535]),
  ([39,71,133,162,396],[726,545]),
  ([39,71,135,139,289],[540]),
  ([39,71,135,148,396],[545]),
  ([39,71,135,153,343],[497,704,663,542]),
  ([39,71,135,162,181],[716,535]),
  ([39,71,135,162,247],[57,536]),
  ([39,71,135,162,249],[537]),
  ([39,71,135,162,250],[538]),
  ([39,71,135,162,260],[1442,539]),
  ([39,71,135,162,289],[540]),
  ([39,71,135,162,298],[1443,541]),
  ([39,71,135,162,343],[542]),
  ([39,71,135,162,396],[717,545]),
  ([39,71,135,182,196],[1360,718,548]),
  ([39,71,135,182,327],[1361,1333,530]),
  ([39,71,135,182,330],[1363]),
  ([39,71,135,182,331],[1364]),
  ([39,71,135,182,340],[1365])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b60ok : f4b60.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b61 : Array Row := #[
  ([39,71,135,182,347],[1366]),
  ([39,71,135,189,343],[1367,546]),
  ([39,71,135,196,250],[538]),
  ([39,71,135,197,343],[1369,546]),
  ([39,71,135,197,396],[1370,547]),
  ([39,71,135,247,323],[]),
  ([39,71,135,247,331],[]),
  ([39,71,135,250,300],[]),
  ([39,71,135,250,306],[]),
  ([39,71,135,250,309],[]),
  ([39,71,135,250,317],[]),
  ([39,71,135,250,319],[]),
  ([39,71,135,250,323],[]),
  ([39,71,135,250,327],[1371]),
  ([39,71,135,250,331],[]),
  ([39,71,135,250,347],[]),
  ([39,71,135,250,361],[]),
  ([39,71,135,250,378],[404,687]),
  ([39,71,135,251,331],[]),
  ([39,71,135,260,309],[]),
  ([39,71,135,260,313],[]),
  ([39,71,135,260,317],[]),
  ([39,71,135,260,323],[]),
  ([39,71,135,260,326],[]),
  ([39,71,135,260,331],[]),
  ([39,71,135,260,340],[]),
  ([39,71,135,260,361],[1444]),
  ([39,71,135,260,378],[1445,490,688]),
  ([39,71,135,289,309],[]),
  ([39,71,135,289,317],[]),
  ([39,71,135,289,323],[]),
  ([39,71,135,289,331],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b61ok : f4b61.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b62 : Array Row := #[
  ([39,71,135,289,348],[517,540]),
  ([39,71,135,289,361],[]),
  ([39,71,135,289,375],[]),
  ([39,71,135,289,378],[608,689]),
  ([39,71,135,298,369],[1446]),
  ([39,71,135,300,343],[]),
  ([39,71,135,301,343],[]),
  ([39,71,135,303,343],[]),
  ([39,71,135,304,343],[]),
  ([39,71,135,306,343],[]),
  ([39,71,135,309,343],[]),
  ([39,71,135,310,343],[]),
  ([39,71,135,313,343],[]),
  ([39,71,135,317,343],[]),
  ([39,71,135,319,343],[]),
  ([39,71,135,323,343],[]),
  ([39,71,135,327,343],[1372]),
  ([39,71,135,331,343],[1373]),
  ([39,71,135,336,343],[1374,1296,1304]),
  ([39,71,135,339,343],[1375]),
  ([39,71,135,341],[47,1376,558,1330,531,494,531,531]),
  ([39,71,135,343,348],[533,542]),
  ([39,71,135,343,361],[]),
  ([39,71,135,343,378],[498,664,690]),
  ([39,71,135,343,382],[]),
  ([39,71,135,347,394],[1377,534,559]),
  ([39,71,135,361,396],[]),
  ([39,71,135,378,396],[499,719,691,693,555,560]),
  ([39,71,135,392,396],[5,1378,1329,1331,557,561]),
  ([39,71,156,162,396],[716,555]),
  ([39,71,156,182,331],[]),
  ([39,71,162,173,343],[1369,553])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b62ok : f4b62.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b63 : Array Row := #[
  ([39,71,162,173,396],[1370,554]),
  ([39,71,162,250,351],[]),
  ([39,71,162,250,371],[]),
  ([39,71,162,250,386],[]),
  ([39,71,162,260,365],[1447]),
  ([39,71,162,289,351],[]),
  ([39,71,162,343,351],[]),
  ([39,71,162,351,396],[]),
  ([39,71,162,378,396],[708,720,555,560]),
  ([39,71,162,392,396],[65,1396,1352,1353,557,561]),
  ([39,71,173,182,331],[1293]),
  ([39,71,173,309,343],[]),
  ([39,71,173,336,343],[1297,1305]),
  ([39,71,173,343,378],[1448,503,665,709]),
  ([39,71,182,327],[48,1393,569,1382,530,504,530,530]),
  ([39,71,182,331,386],[1394]),
  ([39,71,182,336,343],[1395,1298,1306]),
  ([39,71,182,343,378],[511,666,712]),
  ([39,71,250,323,371],[]),
  ([39,71,250,331,386],[]),
  ([39,71,260,317,365],[]),
  ([39,71,289,348],[517,540,517,540,517,540]),
  ([39,71,289,351,361],[]),
  ([39,71,309,343,351],[]),
  ([39,71,336,343,351],[1299,1307,1346]),
  ([39,71,343,348],[533,542,533,542,533,542]),
  ([39,71,343,351,378],[667,704,713]),
  ([39,71,347,394],[49,534,559,534,559,534,559]),
  ([39,71,378,396],[24,615,555,560,715,555,714,734,560,735,555,560]),
  ([39,71,392,396],[50,1247,1359,557,1358,1379,561,1380,557,561,557,561]),
  ([39,78,86,103,135],[1456,605]),
  ([39,79,103,135,274],[606])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b63ok : f4b63.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b64 : Array Row := #[
  ([39,81,103,135,182],[1425,1422,610]),
  ([39,81,103,135,250],[]),
  ([39,83,86,92,182],[1428,610,605]),
  ([39,83,86,103,371],[611]),
  ([39,83,86,103,394],[612]),
  ([39,83,103,135,298],[1427,613]),
  ([39,83,103,293,394],[612,655]),
  ([39,83,135,162,260],[1141,614]),
  ([39,83,135,343,378],[1448,501,664,690]),
  ([39,86,92,182,378],[316,1468,736,607,625]),
  ([39,86,103,135,272],[317,616]),
  ([39,86,103,135,296],[1426,617]),
  ([39,86,103,162,371],[319,623]),
  ([39,86,103,182,378],[320,737,625]),
  ([39,86,103,274,371],[321]),
  ([39,86,135,162,257],[1138,620]),
  ([39,86,135,162,371],[324,623]),
  ([39,86,135,182,378],[325,608,625]),
  ([39,86,135,343,378],[327,502,664,690]),
  ([39,86,156,162,182],[328,625,623,624]),
  ([39,86,162,371],[329,257,313,623,623,623]),
  ([39,86,182,378],[330,258,314,633,625,609,625,625]),
  ([39,92,103,182,293],[1521,1470,610]),
  ([39,92,103,274,289],[523,606]),
  ([39,92,103,289,378],[1534,607,638]),
  ([39,92,123,135,378],[1538,704,667,663]),
  ([39,92,125,182,378],[1539,668]),
  ([39,92,135,153,343],[1541,713,704,663]),
  ([39,92,135,182,293],[1475,1472,610]),
  ([39,92,135,250,274],[]),
  ([39,92,135,250,293],[1477]),
  ([39,92,135,250,378],[1554,753,404,687])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b64ok : f4b64.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b65 : Array Row := #[
  ([39,92,135,260,274],[]),
  ([39,92,135,260,378],[1562,757,490,688]),
  ([39,92,135,274,289],[523,606]),
  ([39,92,135,274,343],[1563]),
  ([39,92,135,289,378],[1566,765,608,689,607,638]),
  ([39,92,135,293,343],[1567,1478]),
  ([39,92,135,343,378],[1568,770,664,690]),
  ([39,92,173,343,378],[1574,665,709]),
  ([39,92,182,293],[1481,1482,641,1479,610,610,610]),
  ([39,92,182,343,378],[1575,666,712]),
  ([39,92,274,289],[1485,523,606,523,606,523,606]),
  ([39,92,289,378],[1577,762,1488,607,638,607,638,607,638]),
  ([39,92,343,351,378],[1578,667,704,713]),
  ([39,99,135,182,293],[1492,1491,640]),
  ([39,103,123,135,378],[663]),
  ([39,103,125,182,378],[668]),
  ([39,103,131,378,396],[1535,649,777,672,673,654,656]),
  ([39,103,135,153,343],[663]),
  ([39,103,135,182,293],[1517,1501,640]),
  ([39,103,135,195,293],[1422,641]),
  ([39,103,135,247,274],[]),
  ([39,103,135,247,293],[]),
  ([39,103,135,250,274],[]),
  ([39,103,135,250,293],[]),
  ([39,103,135,250,378],[404,687]),
  ([39,103,135,251,293],[]),
  ([39,103,135,253,293],[]),
  ([39,103,135,257,293],[1139,1423]),
  ([39,103,135,260,274],[]),
  ([39,103,135,260,278],[]),
  ([39,103,135,260,293],[1142,1424]),
  ([39,103,135,260,378],[490,688])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b65ok : f4b65.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b66 : Array Row := #[
  ([39,103,135,274,289],[642]),
  ([39,103,135,274,298],[643]),
  ([39,103,135,274,343],[]),
  ([39,103,135,289,293],[644]),
  ([39,103,135,289,378],[645,608,689]),
  ([39,103,135,293,343],[1518]),
  ([39,103,135,293,371],[1519,646,611,653]),
  ([39,103,135,293,394],[1520,647,612,655]),
  ([39,103,135,343,378],[664,690]),
  ([39,103,135,378,396],[649,706,691,693,654,656]),
  ([39,103,156,162,396],[716,654]),
  ([39,103,156,182,293],[1516,650,653]),
  ([39,103,162,378,396],[708,720,654,656]),
  ([39,103,173,182,293],[1425,651]),
  ([39,103,173,343,378],[1537,665,709]),
  ([39,103,182,293,386],[1524]),
  ([39,103,182,343,378],[666,712]),
  ([39,103,250,274,371],[]),
  ([39,103,250,293,386],[]),
  ([39,103,260,274,365],[]),
  ([39,103,274,289,351],[]),
  ([39,103,293,371],[611,653,611,653,611,653]),
  ([39,103,293,394],[612,655,612,655,612,655]),
  ([39,103,343,351,378],[667,704,713]),
  ([39,103,378,396],[12,662,654,656,715,654,714,734,656,735,654,656]),
  ([39,120,135,343,378],[1537,664,690]),
  ([39,123,135,343,378],[747,690,663]),
  ([39,123,135,378],[665,663,666,663,663]),
  ([39,125,135,182,378],[664,668]),
  ([39,125,135,343,378],[664,690]),
  ([39,125,156,162,182],[668]),
  ([39,125,182,378],[252,668,666,668,668])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b66ok : f4b66.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b67 : Array Row := #[
  ([39,131,135,378,396],[1569,776,691,693,672,673]),
  ([39,131,156,162,396],[1570,716,672]),
  ([39,131,162,378,396],[1572,708,720,672,673]),
  ([39,131,378,396],[0,1579,778,1540,672,673,715,672,714,734,673,735,672,673]),
  ([39,135,140,343,378],[664,690]),
  ([39,135,153,343],[709,663,671,663,663]),
  ([39,135,153,343,378],[684,664,663]),
  ([39,135,156,162,250],[687]),
  ([39,135,156,162,260],[688]),
  ([39,135,156,162,289],[689]),
  ([39,135,156,162,343],[690]),
  ([39,135,156,162,396],[716,691]),
  ([39,135,156,343,378],[664,690]),
  ([39,135,162,182,293],[1571,1542,674,686]),
  ([39,135,162,250,274],[675]),
  ([39,135,162,250,276],[]),
  ([39,135,162,250,293],[676]),
  ([39,135,162,260,274],[678]),
  ([39,135,162,274,289],[680]),
  ([39,135,162,343,378],[684,664,690]),
  ([39,135,162,378,396],[685,727,708,720,691,693]),
  ([39,135,173,343,378],[665,709,664,690]),
  ([39,135,182,293,331],[1573,1549]),
  ([39,135,182,343,378],[666,712,664,690]),
  ([39,135,250,274,323],[]),
  ([39,135,250,293,331],[]),
  ([39,135,250,378],[728,404,687,404,687,404,687]),
  ([39,135,260,274,317],[]),
  ([39,135,260,378],[729,490,688,490,688,490,688]),
  ([39,135,274,289,361],[]),
  ([39,135,289,378],[730,608,689,608,689,608,689]),
  ([39,135,309,343,378],[664,690])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b67ok : f4b67.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b68 : Array Row := #[
  ([39,135,336,343,378],[1574,1536,1538,1541,664,690]),
  ([39,135,343,351,378],[667,713,664,690]),
  ([39,135,343,378],[732,664,690,664,690,664,690]),
  ([39,135,378,396],[3,733,691,693,715,691,714,734,693,735,691,693]),
  ([39,156,162,182,198],[342,711,716]),
  ([39,156,162,396],[716,715,707,708,716,716]),
  ([39,162,378,396],[60,751,708,720,715,708,714,734,720,735,708,720]),
  ([39,173,343,378],[665,709,665,709,665,709]),
  ([39,182,343,378],[750,666,712,666,712,666,712]),
  ([39,343,351,378],[667,704,713,667,704,667,713,704,713]),
  ([39,378,396],[715,714,734,735,715,714,734,735]),
  ([44,49,65,103,135],[1006,780]),
  ([44,49,71,92,173],[994,918,802,782,780]),
  ([44,49,71,103,365],[1011,807,781]),
  ([44,54,71,103,135],[1139]),
  ([44,56,71,92,135],[1175,1153,802,784]),
  ([44,56,71,103,135],[1187]),
  ([44,56,71,103,394],[1195,1165]),
  ([44,56,71,135,162],[1201,135,783]),
  ([44,56,71,135,347],[1210,1165]),
  ([44,56,103,135,293],[1210,1195,1169]),
  ([44,65,71,103,135],[1276,808,795,785]),
  ([44,65,83,103,135],[1435,786]),
  ([44,65,103,135],[1512,826,1233,796,794,797,793,787,788,789]),
  ([44,65,103,135,173],[1496,790,791]),
  ([44,71,77,103,135],[792,799]),
  ([44,71,83,92,173],[1246,822,786,799]),
  ([44,71,83,103,365],[821,807]),
  ([44,71,92,103,173],[1278,828,788]),
  ([44,71,92,135,173],[1330,833,789]),
  ([44,71,92,135,257],[1473,1341,834]),
  ([44,71,92,135,336],[1345,835])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b68ok : f4b68.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b69 : Array Row := #[
  ([44,71,92,173],[823,1376,817,1256,801,838,818,824,787,785,790]),
  ([44,71,97,135,173],[791,800]),
  ([44,71,103,135,188],[1498,798,801]),
  ([44,71,103,135,195],[1501,798,802]),
  ([44,71,103,135,241],[]),
  ([44,71,103,135,242],[]),
  ([44,71,103,135,244],[]),
  ([44,71,103,135,256],[1503,1339,1289,1134,831]),
  ([44,71,103,135,257],[1504]),
  ([44,71,103,135,260],[1507]),
  ([44,71,103,135,285],[803]),
  ([44,71,103,135,336],[]),
  ([44,71,103,135,365],[832,804,807]),
  ([44,71,103,156,173],[836,805,807]),
  ([44,71,103,173,182],[1517,1366,806]),
  ([44,71,103,173,394],[1520,1377,794]),
  ([44,71,103,257,394],[1529,1399]),
  ([44,71,103,365],[830,820,807,837,816,827,807,807]),
  ([44,71,135,162,173],[836,795,811,814]),
  ([44,71,135,162,257],[1545,812]),
  ([44,71,135,173,347],[1377,796]),
  ([44,71,135,257,347],[1557,1399]),
  ([44,103,135,173,293],[1520,1498,823]),
  ([44,103,135,257,293],[1557,1529,1139,1423]),
  ([47,71,103,135,173],[839]),
  ([47,71,135,162,173],[842,840]),
  ([49,54,71,92,135],[844]),
  ([49,54,71,103,135],[]),
  ([49,54,71,103,371],[]),
  ([49,54,71,135,162],[1138,843]),
  ([49,54,71,135,323],[]),
  ([49,54,103,135,274],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b69ok : f4b69.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b70 : Array Row := #[
  ([49,56,71,83,131],[1174,783,136,843]),
  ([49,56,71,92,285],[869]),
  ([49,56,71,131,392],[1167,138,889,847]),
  ([49,56,71,135,327],[1158,1147,923]),
  ([49,56,71,331,386],[1148,1156]),
  ([49,56,81,103,135],[]),
  ([49,56,83,135,378],[784,844,984]),
  ([49,56,92,135,293],[1177,1168,995]),
  ([49,56,103,135,293],[1169]),
  ([49,56,103,293,386],[1170,1188]),
  ([49,56,135,162,293],[1171,846]),
  ([49,56,135,293,331],[1173,1196]),
  ([49,56,135,336,378],[1104,1017,1044]),
  ([49,58,71,77,92],[1240,960,877,871]),
  ([49,58,71,92,118],[1252,1216,887,879,850]),
  ([49,58,71,92,241],[1261,925]),
  ([49,58,71,92,257],[1263,1221,928]),
  ([49,58,71,92,285],[1265,996,934,869]),
  ([49,58,71,92,336],[1269,1218,941,852]),
  ([49,58,71,131,285],[1321,1034,934,870]),
  ([49,58,71,131,392],[1323,1219,1035,948,889,853]),
  ([49,58,71,285,348],[1402,1113,871,894]),
  ([49,58,71,336,343],[1406,1216,1217]),
  ([49,58,71,336,348],[1407,1114,887,896]),
  ([49,58,71,336,378],[1408,850,851]),
  ([49,58,92,274,285],[1483,1113,877,960]),
  ([49,58,92,274,336],[1485,1223,1114]),
  ([49,58,92,285,378],[1486,1224,1117,961,992]),
  ([49,58,92,336,378],[1488,1226,1123,850,851]),
  ([49,58,103,336,378],[1534,850,851]),
  ([49,58,135,285,378],[1564,1118,962,1043]),
  ([49,58,135,336,378],[1566,1124,1017,1044,850,851])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b70ok : f4b70.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b71 : Array Row := #[
  ([49,58,336,378],[1577,1119,1225,850,851,850,851,850,851]),
  ([49,59,71,92,285],[869]),
  ([49,59,71,92,336],[1227,854]),
  ([49,60,71,92,336],[1269,1228,942,856]),
  ([49,65,71,83,92],[1244,785,873]),
  ([49,65,71,92,285],[1266,996,935,869]),
  ([49,65,71,92,336],[1271,1229,943,864]),
  ([49,65,83,92],[1432,968,1230,787,780,786,1231,985,860,969,861]),
  ([49,65,83,92,103],[1429,788,970]),
  ([49,65,83,92,135],[1430,789,973]),
  ([49,65,83,92,173],[1431,790,981]),
  ([49,65,83,97,135],[1433,791,858]),
  ([49,65,83,103,135],[1436,792,858]),
  ([49,65,83,103,365],[1437,793,986]),
  ([49,65,83,135,162],[1443,795,978,859]),
  ([49,65,83,135,369],[1446,797,986]),
  ([49,65,103,135,257],[862]),
  ([49,65,103,135,293],[1514,1011,863]),
  ([49,67,71,92,296],[1268,1235,997,936,872]),
  ([49,67,71,92,336],[1269,1236,1234,944,865]),
  ([49,69,83,103,135],[1436,798,866]),
  ([49,69,103,135,296],[1515,867]),
  ([49,71,77,83,92],[799,858]),
  ([49,71,77,92],[1241,961,879]),
  ([49,71,77,92,103],[]),
  ([49,71,77,92,135],[962]),
  ([49,71,77,92,173],[963]),
  ([49,71,77,92,285],[]),
  ([49,71,77,97,135],[869]),
  ([49,71,77,103,135],[869]),
  ([49,71,77,103,351],[]),
  ([49,71,77,135,162],[870])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b71ok : f4b71.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b72 : Array Row := #[
  ([49,71,77,135,361],[]),
  ([49,71,82,103,135],[1426,872]),
  ([49,71,83,92,173],[800,982,858,869]),
  ([49,71,83,92,195],[1428,802,984,866,872]),
  ([49,71,83,92,285],[803,869]),
  ([49,71,83,92,365],[804,987]),
  ([49,71,83,96,173],[805,982]),
  ([49,71,83,99,173],[806,983]),
  ([49,71,83,103,142],[807,974]),
  ([49,71,83,103,365],[808,978]),
  ([49,71,83,103,377],[809,979]),
  ([49,71,83,103,390],[810,980]),
  ([49,71,83,131,173],[811,982,859,870]),
  ([49,71,83,131,392],[813,1247,988,889]),
  ([49,71,83,135,143],[814,975]),
  ([49,71,83,135,313],[815,849]),
  ([49,71,83,162,365],[816,974]),
  ([49,71,83,173,378],[818,976]),
  ([49,71,83,317,365],[819]),
  ([49,71,86,92,285],[98,869]),
  ([49,71,86,131,392],[100,1251,991,922,889]),
  ([49,71,86,135,334],[1250,855,885]),
  ([49,71,86,340,390],[888,911]),
  ([49,71,92,103,285],[869]),
  ([49,71,92,103,296],[1449,872]),
  ([49,71,92,103,392],[1291,1015,875]),
  ([49,71,92,118,135],[1296,1017]),
  ([49,71,92,118,173],[1297,1018]),
  ([49,71,92,118,182],[1298,1019]),
  ([49,71,92,118,351],[1299,1020]),
  ([49,71,92,120,173],[1301,1022]),
  ([49,71,92,120,285],[869])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b72ok : f4b72.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b73 : Array Row := #[
  ([49,71,92,125,285],[869]),
  ([49,71,92,131,336],[1324,1272,1038,941,886]),
  ([49,71,92,131,392],[1326,1274,1039,1003,948,889,875]),
  ([49,71,92,135,238],[1257,1048]),
  ([49,71,92,135,241],[1049]),
  ([49,71,92,135,257],[1050]),
  ([49,71,92,135,285],[1052,869]),
  ([49,71,92,135,296],[1450,1055,872]),
  ([49,71,92,135,334],[1344,1258,1057,939,885]),
  ([49,71,92,135,336],[1346,1058]),
  ([49,71,92,135,392],[1348,1059,875]),
  ([49,71,92,140,285],[869]),
  ([49,71,92,156,285],[869]),
  ([49,71,92,162,285],[869]),
  ([49,71,92,162,392],[1355,1079,875]),
  ([49,71,92,173,189],[1367,800,1084,861,875]),
  ([49,71,92,173,197],[1369,839,1085,875]),
  ([49,71,92,173,241],[1086]),
  ([49,71,92,173,243],[1087]),
  ([49,71,92,173,244],[1088]),
  ([49,71,92,173,257],[1089,862]),
  ([49,71,92,173,285],[1090,869]),
  ([49,71,92,173,293],[101,1259,1092,863,964]),
  ([49,71,92,173,327],[1372,1260,1093,884]),
  ([49,71,92,173,331],[1373,1094]),
  ([49,71,92,173,336],[1374,1095]),
  ([49,71,92,182,241],[1098]),
  ([49,71,92,182,257],[1099]),
  ([49,71,92,182,285],[1100,869]),
  ([49,71,92,182,296],[1451,1101,872]),
  ([49,71,92,182,336],[1389,1102]),
  ([49,71,92,195,336],[1395,1104,868])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b73ok : f4b73.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b74 : Array Row := #[
  ([49,71,92,241,351],[1107]),
  ([49,71,92,241,355],[1108]),
  ([49,71,92,241,365],[1109]),
  ([49,71,92,241,386],[1110]),
  ([49,71,92,257,351],[1111]),
  ([49,71,92,257,371],[1112]),
  ([49,71,92,274,285],[960,869]),
  ([49,71,92,285],[1267,869,999,869,869]),
  ([49,71,92,285,289],[1240,1242,869]),
  ([49,71,92,285,309],[869]),
  ([49,71,92,285,336],[1403,1115,869]),
  ([49,71,92,285,343],[1241,1253,1116,869]),
  ([49,71,92,285,348],[1404,1117,871,894,869]),
  ([49,71,92,285,351],[1118,869]),
  ([49,71,92,285,361],[869]),
  ([49,71,92,285,378],[1405,961,992,869]),
  ([49,71,92,289,336],[1406,1243,1252,1119]),
  ([49,71,92,296],[1452,989,1248,1270,872,1002,872,872]),
  ([49,71,92,336,348],[1409,1123,887,896]),
  ([49,71,92,336,351],[1410,1124]),
  ([49,71,92,336,355],[1411,1125]),
  ([49,71,92,336,358],[1412,1126]),
  ([49,71,92,336,365],[1413,1127]),
  ([49,71,92,336,371],[1414,1128]),
  ([49,71,92,336,386],[1415,1129]),
  ([49,71,92,392],[1417,947,1273,875,1132,955,1003,875,875]),
  ([49,71,93,103,285],[877]),
  ([49,71,94,103,285],[877]),
  ([49,71,94,120,173],[1301]),
  ([49,71,94,135,336],[1346]),
  ([49,71,96,120,173],[1022]),
  ([49,71,96,135,241],[1049])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b74ok : f4b74.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b75 : Array Row := #[
  ([49,71,96,135,257],[1050]),
  ([49,71,96,135,285],[1052,877]),
  ([49,71,96,135,336],[1058]),
  ([49,71,96,173,338],[1096]),
  ([49,71,97,118,135],[]),
  ([49,71,97,135,241],[]),
  ([49,71,97,135,257],[]),
  ([49,71,97,135,285],[877]),
  ([49,71,97,135,336],[]),
  ([49,71,97,182,336],[1390]),
  ([49,71,99,120,173],[1301]),
  ([49,71,99,135,241],[]),
  ([49,71,99,135,257],[1051]),
  ([49,71,99,135,285],[877]),
  ([49,71,99,135,296],[1453,1056,878]),
  ([49,71,99,135,336],[1346]),
  ([49,71,99,173,339],[1375]),
  ([49,71,99,182,336],[1389]),
  ([49,71,103,115,173],[]),
  ([49,71,103,118,135],[]),
  ([49,71,103,118,182],[1295]),
  ([49,71,103,118,351],[]),
  ([49,71,103,120,390],[]),
  ([49,71,103,131,172],[1277,1010,875]),
  ([49,71,103,131,241],[375]),
  ([49,71,103,131,257],[1454,843]),
  ([49,71,103,131,285],[877,870]),
  ([49,71,103,131,336],[1290,886]),
  ([49,71,103,131,392],[1292,1015,879,889]),
  ([49,71,103,132,392],[879]),
  ([49,71,103,135,172],[875]),
  ([49,71,103,135,238],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b75ok : f4b75.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b76 : Array Row := #[
  ([49,71,103,135,239],[]),
  ([49,71,103,135,240],[]),
  ([49,71,103,135,241],[]),
  ([49,71,103,135,256],[1134,1046]),
  ([49,71,103,135,257],[]),
  ([49,71,103,135,284],[102,876]),
  ([49,71,103,135,285],[877]),
  ([49,71,103,135,296],[1456,878]),
  ([49,71,103,135,334],[1280,885]),
  ([49,71,103,135,336],[]),
  ([49,71,103,135,392],[879]),
  ([49,71,103,142,241],[]),
  ([49,71,103,147,257],[]),
  ([49,71,103,156,392],[1071,881]),
  ([49,71,103,167,241],[]),
  ([49,71,103,173,327],[1281,884]),
  ([49,71,103,182,336],[1308]),
  ([49,71,103,182,392],[1309,882]),
  ([49,71,103,238,365],[]),
  ([49,71,103,238,386],[]),
  ([49,71,103,241,351],[]),
  ([49,71,103,241,365],[]),
  ([49,71,103,241,371],[]),
  ([49,71,103,241,386],[]),
  ([49,71,103,241,390],[]),
  ([49,71,103,243,365],[]),
  ([49,71,103,244,386],[]),
  ([49,71,103,257,351],[]),
  ([49,71,103,257,365],[1075]),
  ([49,71,103,257,371],[]),
  ([49,71,103,257,377],[1076]),
  ([49,71,103,257,386],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b76ok : f4b76.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b77 : Array Row := #[
  ([49,71,103,257,394],[]),
  ([49,71,103,285,348],[871,894]),
  ([49,71,103,285,351],[]),
  ([49,71,103,285,365],[]),
  ([49,71,103,285,371],[]),
  ([49,71,103,285,386],[]),
  ([49,71,103,293,365],[1077,965,1007]),
  ([49,71,103,293,390],[103,1078,966,1009]),
  ([49,71,103,296,371],[1457]),
  ([49,71,103,336,348],[887,896]),
  ([49,71,103,336,351],[]),
  ([49,71,103,336,358],[]),
  ([49,71,103,336,365],[]),
  ([49,71,103,336,371],[]),
  ([49,71,103,336,386],[]),
  ([49,71,103,340,390],[888,911]),
  ([49,71,103,351,392],[]),
  ([49,71,103,378,392],[10,1079,1008,1010,909,912]),
  ([49,71,103,392,396],[17,1310,1277,1279,913,920]),
  ([49,71,108,135,241],[]),
  ([49,71,111,135,257],[]),
  ([49,71,116,135,173],[1293]),
  ([49,71,116,135,241],[]),
  ([49,71,118,125,135],[1295]),
  ([49,71,118,135,162],[886]),
  ([49,71,118,135,309],[]),
  ([49,71,118,135,343],[1298,1294]),
  ([49,71,118,135,378],[850,1016]),
  ([49,71,120,131,173],[1302,1022,886]),
  ([49,71,120,131,392],[1303,1023,879,889]),
  ([49,71,120,173,343],[1300]),
  ([49,71,120,173,378],[1085,1021])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b77ok : f4b77.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b78 : Array Row := #[
  ([49,71,123,135,336],[1346,1306,1294]),
  ([49,71,125,131,392],[1310,1024,879,889]),
  ([49,71,125,135,336],[1308]),
  ([49,71,125,135,392],[1309,880]),
  ([49,71,125,182,336],[1295]),
  ([49,71,125,336,351],[]),
  ([49,71,131,135,172],[1329,1047]),
  ([49,71,131,135,241],[1049,375]),
  ([49,71,131,135,257],[1458,1050,843]),
  ([49,71,131,135,285],[1052,870]),
  ([49,71,131,135,336],[1347,1058,886]),
  ([49,71,131,135,392],[1349,1059,889]),
  ([49,71,131,140,392],[1350,1060,889]),
  ([49,71,131,156,392],[1351,1073,889]),
  ([49,71,131,162,172],[1352,1074]),
  ([49,71,131,162,241],[375]),
  ([49,71,131,162,257],[1459,843]),
  ([49,71,131,162,285],[870]),
  ([49,71,131,162,336],[1354,886]),
  ([49,71,131,162,392],[1356,1079,889]),
  ([49,71,131,165,392],[1357,1081,889]),
  ([49,71,131,172],[1359,913,1312,1082,912,1027,899]),
  ([49,71,131,172,392],[1358,1083]),
  ([49,71,131,173,197],[1370,840,1085,889]),
  ([49,71,131,173,392],[1378,1097,889]),
  ([49,71,131,182,392],[1392,1103,889]),
  ([49,71,131,197,392],[1396,841,1105,889]),
  ([49,71,131,198,392],[1397,1106,889]),
  ([49,71,131,241],[1316,375,1031,375,375]),
  ([49,71,131,257],[1460,990,1249,1319,843,1033,843,843]),
  ([49,71,131,285],[1322,870,1036,870,870]),
  ([49,71,131,336],[1416,945,1325,886,1038,886,886])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b78ok : f4b78.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b79 : Array Row := #[
  ([49,71,131,351,392],[1418,1130,889]),
  ([49,71,131,361,392],[1419,1131,889]),
  ([49,71,131,378,392],[1420,853,1026,1027,909,912,889]),
  ([49,71,131,392],[1421,958,1327,889,1132,955,1039,889,889]),
  ([49,71,131,392,396],[2,1312,1313,1133,913,920,889]),
  ([49,71,132,162,392],[1080,899]),
  ([49,71,135,139,285],[894]),
  ([49,71,135,143,392],[899]),
  ([49,71,135,153,336],[851,1058,1016,896]),
  ([49,71,135,162,172],[1070,889]),
  ([49,71,135,162,238],[104,890]),
  ([49,71,135,162,240],[891]),
  ([49,71,135,162,241],[892]),
  ([49,71,135,162,257],[1462,893]),
  ([49,71,135,162,285],[894]),
  ([49,71,135,162,296],[1463,895]),
  ([49,71,135,162,336],[896]),
  ([49,71,135,162,392],[1071,899]),
  ([49,71,135,173,196],[1360,1072,902]),
  ([49,71,135,173,327],[1361,1333,884]),
  ([49,71,135,173,329],[1362]),
  ([49,71,135,173,331],[1364]),
  ([49,71,135,173,340],[1365]),
  ([49,71,135,173,347],[1366]),
  ([49,71,135,192,336],[1381,900]),
  ([49,71,135,196,241],[892]),
  ([49,71,135,198,336],[1383,900]),
  ([49,71,135,198,392],[1384,901]),
  ([49,71,135,238,317],[]),
  ([49,71,135,238,331],[]),
  ([49,71,135,241,300],[]),
  ([49,71,135,241,304],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b79ok : f4b79.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b80 : Array Row := #[
  ([49,71,135,241,309],[]),
  ([49,71,135,241,313],[]),
  ([49,71,135,241,317],[]),
  ([49,71,135,241,323],[]),
  ([49,71,135,241,327],[1385]),
  ([49,71,135,241,331],[]),
  ([49,71,135,241,340],[]),
  ([49,71,135,241,361],[]),
  ([49,71,135,241,378],[404,1041]),
  ([49,71,135,242,331],[]),
  ([49,71,135,257,309],[]),
  ([49,71,135,257,317],[]),
  ([49,71,135,257,319],[]),
  ([49,71,135,257,323],[]),
  ([49,71,135,257,326],[]),
  ([49,71,135,257,331],[]),
  ([49,71,135,257,347],[]),
  ([49,71,135,257,361],[1464]),
  ([49,71,135,257,378],[1465,844,1042]),
  ([49,71,135,285,309],[]),
  ([49,71,135,285,317],[]),
  ([49,71,135,285,323],[]),
  ([49,71,135,285,331],[]),
  ([49,71,135,285,348],[871,894]),
  ([49,71,135,285,361],[]),
  ([49,71,135,285,369],[]),
  ([49,71,135,285,378],[962,1043]),
  ([49,71,135,296,375],[1466]),
  ([49,71,135,300,336],[]),
  ([49,71,135,302,336],[]),
  ([49,71,135,303,336],[]),
  ([49,71,135,304,336],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b80ok : f4b80.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b81 : Array Row := #[
  ([49,71,135,306,336],[]),
  ([49,71,135,309,336],[]),
  ([49,71,135,311,336],[]),
  ([49,71,135,313,336],[]),
  ([49,71,135,317,336],[]),
  ([49,71,135,319,336],[]),
  ([49,71,135,323,336],[]),
  ([49,71,135,327,336],[1386]),
  ([49,71,135,331,336],[1387]),
  ([49,71,135,334],[94,1388,921,1332,885,848,885,885]),
  ([49,71,135,336,343],[1389,1296,1304]),
  ([49,71,135,336,346],[1390]),
  ([49,71,135,336,348],[887,896]),
  ([49,71,135,336,361],[]),
  ([49,71,135,336,378],[852,1017,1044]),
  ([49,71,135,336,381],[]),
  ([49,71,135,340,390],[1391,888,911]),
  ([49,71,135,361,392],[]),
  ([49,71,135,378,392],[853,1073,1045,1047,909,912]),
  ([49,71,135,392,396],[8,1392,1329,1331,913,920]),
  ([49,71,156,162,392],[1070,909]),
  ([49,71,156,173,331],[]),
  ([49,71,162,182,336],[1383,907]),
  ([49,71,162,182,392],[1384,908]),
  ([49,71,162,241,351],[]),
  ([49,71,162,241,365],[]),
  ([49,71,162,241,386],[]),
  ([49,71,162,257,371],[1467]),
  ([49,71,162,285,351],[]),
  ([49,71,162,336,351],[]),
  ([49,71,162,351,392],[]),
  ([49,71,162,378,392],[1062,1074,909,912])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b81ok : f4b81.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b82 : Array Row := #[
  ([49,71,162,392,396],[112,1397,1352,1353,913,920]),
  ([49,71,173,182,331],[1293]),
  ([49,71,173,327],[95,1393,923,1368,884,857,884,884]),
  ([49,71,173,331,386],[1394]),
  ([49,71,173,336,343],[1395,1297,1305]),
  ([49,71,173,336,378],[864,1018,1065]),
  ([49,71,182,309,336],[]),
  ([49,71,182,336,343],[1298,1306]),
  ([49,71,182,336,378],[1468,865,1019,1066]),
  ([49,71,241,317,365],[]),
  ([49,71,241,331,386],[]),
  ([49,71,257,323,371],[]),
  ([49,71,285,348],[871,894,871,894,871,894]),
  ([49,71,285,351,361],[]),
  ([49,71,309,336,351],[]),
  ([49,71,336,343,351],[1299,1307,1346]),
  ([49,71,336,348],[887,896,887,896,887,896]),
  ([49,71,336,351,378],[1020,1058,1067]),
  ([49,71,340,390],[96,888,911,888,911,888,911]),
  ([49,71,378,392],[93,991,909,912,1069,909,1068,1082,912,1083,909,912]),
  ([49,71,392,396],[97,1251,1359,913,1358,1379,920,1380,913,920,913,920]),
  ([49,76,83,103,135],[1436,959]),
  ([49,77,103,135,274],[960]),
  ([49,81,103,135,173],[1425,1422,964]),
  ([49,81,103,135,241],[]),
  ([49,83,86,92,173],[1428,964,959]),
  ([49,83,86,103,365],[965]),
  ([49,83,86,103,390],[966]),
  ([49,83,92,173,378],[824,1448,1084,961,976]),
  ([49,83,103,135,271],[825,967]),
  ([49,83,103,135,298],[1427,968]),
  ([49,83,103,162,365],[827,974])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b82ok : f4b82.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b83 : Array Row := #[
  ([49,83,103,173,378],[828,1085,976]),
  ([49,83,103,274,365],[829]),
  ([49,83,135,162,260],[1141,971]),
  ([49,83,135,162,365],[832,974]),
  ([49,83,135,173,378],[833,962,976]),
  ([49,83,135,336,378],[835,854,1017,1044]),
  ([49,83,156,162,173],[836,976,974,975]),
  ([49,83,162,365],[837,781,821,974,974,974]),
  ([49,83,173,378],[838,782,822,984,976,963,976,976]),
  ([49,86,103,135,296],[1426,989]),
  ([49,86,103,293,390],[966,1009]),
  ([49,86,135,162,257],[1138,990]),
  ([49,86,135,336,378],[1468,856,1017,1044]),
  ([49,92,103,173,293],[1518,1470,964]),
  ([49,92,103,274,285],[877,960]),
  ([49,92,103,285,378],[1533,961,992]),
  ([49,92,118,135,378],[1536,1058,1020,1016]),
  ([49,92,120,173,378],[1537,1021]),
  ([49,92,135,153,336],[1541,1067,1058,1016]),
  ([49,92,135,173,293],[1475,1472,964]),
  ([49,92,135,241,274],[]),
  ([49,92,135,241,293],[1480]),
  ([49,92,135,241,378],[1552,1107,404,1041]),
  ([49,92,135,257,274],[]),
  ([49,92,135,257,378],[1558,1111,844,1042]),
  ([49,92,135,274,285],[877,960]),
  ([49,92,135,274,336],[1563]),
  ([49,92,135,285,378],[1565,1118,962,1043,961,992]),
  ([49,92,135,293,336],[1567,1481]),
  ([49,92,135,336,378],[1568,1124,1017,1044]),
  ([49,92,173,293],[1478,1482,995,1476,964,964,964]),
  ([49,92,173,336,378],[1574,1018,1065])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b83ok : f4b83.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b84 : Array Row := #[
  ([49,92,182,336,378],[1575,1019,1066]),
  ([49,92,274,285],[1484,877,960,877,960,877,960]),
  ([49,92,285,378],[1576,1116,1487,961,992,961,992,961,992]),
  ([49,92,336,351,378],[1578,1020,1058,1067]),
  ([49,97,135,173,293],[1490,1489,994]),
  ([49,103,118,135,378],[1016]),
  ([49,103,120,173,378],[1021]),
  ([49,103,131,378,392],[1535,1003,1131,1026,1027,1008,1010]),
  ([49,103,135,153,336],[1016]),
  ([49,103,135,173,293],[1517,1501,994]),
  ([49,103,135,195,293],[1422,995]),
  ([49,103,135,238,274],[]),
  ([49,103,135,238,293],[]),
  ([49,103,135,241,274],[]),
  ([49,103,135,241,293],[]),
  ([49,103,135,241,378],[404,1041]),
  ([49,103,135,242,293],[]),
  ([49,103,135,244,293],[]),
  ([49,103,135,257,274],[]),
  ([49,103,135,257,280],[]),
  ([49,103,135,257,293],[1139,1423]),
  ([49,103,135,257,378],[844,1042]),
  ([49,103,135,260,293],[1142,1424]),
  ([49,103,135,274,285],[996]),
  ([49,103,135,274,296],[997]),
  ([49,103,135,274,336],[]),
  ([49,103,135,285,293],[998]),
  ([49,103,135,285,378],[999,962,1043]),
  ([49,103,135,293,336],[1521]),
  ([49,103,135,293,365],[1522,1000,965,1007]),
  ([49,103,135,293,390],[1523,1001,966,1009]),
  ([49,103,135,336,378],[1017,1044])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b84ok : f4b84.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b85 : Array Row := #[
  ([49,103,135,378,392],[1003,1060,1045,1047,1008,1010]),
  ([49,103,156,162,392],[1070,1008]),
  ([49,103,156,173,293],[1516,1004,1007]),
  ([49,103,162,378,392],[1062,1074,1008,1010]),
  ([49,103,173,182,293],[1425,1005]),
  ([49,103,173,293,386],[1524]),
  ([49,103,173,336,378],[1018,1065]),
  ([49,103,182,336,378],[1539,1019,1066]),
  ([49,103,241,274,365],[]),
  ([49,103,241,293,386],[]),
  ([49,103,257,274,371],[]),
  ([49,103,274,285,351],[]),
  ([49,103,293,365],[965,1007,965,1007,965,1007]),
  ([49,103,293,390],[966,1009,966,1009,966,1009]),
  ([49,103,336,351,378],[1020,1058,1067]),
  ([49,103,378,392],[16,1024,1008,1010,1069,1008,1068,1082,1010,1083,1008,1010]),
  ([49,118,135,336,378],[1095,1044,1016]),
  ([49,118,135,378],[1019,1016,1018,1016,1016]),
  ([49,120,135,173,378],[1017,1021]),
  ([49,120,135,336,378],[1017,1044]),
  ([49,120,156,162,173],[1021]),
  ([49,120,173,378],[255,1021,1018,1021,1021]),
  ([49,125,135,336,378],[1539,1017,1044]),
  ([49,131,135,378,392],[1569,1130,1045,1047,1026,1027]),
  ([49,131,156,162,392],[1570,1070,1026]),
  ([49,131,162,378,392],[1572,1062,1074,1026,1027]),
  ([49,131,378,392],[1,1579,1133,1540,1026,1027,1069,1026,1068,1082,1027,1083,1026,1027]),
  ([49,135,140,336,378],[1017,1044]),
  ([49,135,153,336],[1066,1016,1025,1016,1016]),
  ([49,135,153,336,378],[1038,1017,1016]),
  ([49,135,156,162,241],[1041]),
  ([49,135,156,162,257],[1042])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b85ok : f4b85.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b86 : Array Row := #[
  ([49,135,156,162,285],[1043]),
  ([49,135,156,162,336],[1044]),
  ([49,135,156,162,392],[1070,1045]),
  ([49,135,156,336,378],[1017,1044]),
  ([49,135,162,173,293],[1571,1542,1028,1040]),
  ([49,135,162,241,274],[1029]),
  ([49,135,162,241,275],[]),
  ([49,135,162,241,293],[1030]),
  ([49,135,162,257,274],[1032]),
  ([49,135,162,274,285],[1034]),
  ([49,135,162,336,378],[1038,1017,1044]),
  ([49,135,162,378,392],[1039,1081,1062,1074,1045,1047]),
  ([49,135,173,293,331],[1573,1549]),
  ([49,135,173,336,378],[1018,1065,1017,1044]),
  ([49,135,182,336,378],[1019,1066,1017,1044]),
  ([49,135,241,274,317],[]),
  ([49,135,241,293,331],[]),
  ([49,135,241,378],[1098,404,1041,404,1041,404,1041]),
  ([49,135,257,274,323],[]),
  ([49,135,257,378],[1099,844,1042,844,1042,844,1042]),
  ([49,135,274,285,361],[]),
  ([49,135,285,378],[1100,962,1043,962,1043,962,1043]),
  ([49,135,309,336,378],[1017,1044]),
  ([49,135,336,343,378],[1575,1536,1538,1541,1017,1044]),
  ([49,135,336,351,378],[1020,1067,1017,1044]),
  ([49,135,336,378],[1102,1017,1044,1017,1044,1017,1044]),
  ([49,135,378,392],[7,1103,1045,1047,1069,1045,1068,1082,1047,1083,1045,1047]),
  ([49,156,162,173,197],[842,1064,1070]),
  ([49,156,162,392],[1070,1069,1061,1062,1070,1070]),
  ([49,162,378,392],[111,1106,1062,1074,1069,1062,1068,1082,1074,1083,1062,1074]),
  ([49,173,336,378],[1104,1018,1065,1018,1065,1018,1065]),
  ([49,182,336,378],[1019,1066,1019,1066,1019,1066])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b86ok : f4b86.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b87 : Array Row := #[
  ([49,336,351,378],[1020,1058,1067,1020,1058,1020,1067,1058,1067]),
  ([49,378,392],[1069,1068,1082,1083,1069,1068,1082,1083]),
  ([54,71,86,103,135],[1134,1138]),
  ([54,71,103,135,250],[]),
  ([54,83,86,103,135],[1137]),
  ([55,71,83,103,135],[1134,1141]),
  ([55,71,103,135,241],[]),
  ([55,83,86,103,135],[1140]),
  ([56,58,103,135,293],[1469,1211,1189,1169,1144]),
  ([56,71,81,103,135],[1134,1187,1171]),
  ([56,71,92,135,293],[1259,1212,1144,1168]),
  ([56,71,92,135,327],[1311,1260,1213,1161,1147]),
  ([56,71,103,135,232],[]),
  ([56,71,103,135,235],[]),
  ([56,71,103,135,238],[]),
  ([56,71,103,135,247],[]),
  ([56,71,103,135,256],[1134,1200]),
  ([56,71,103,135,283],[141,1145]),
  ([56,71,103,135,293],[1201,1169]),
  ([56,71,103,135,327],[1281,1147]),
  ([56,71,103,293,386],[142,1214,1170,1188]),
  ([56,71,103,331,386],[1148,1156]),
  ([56,71,135,162,293],[1171,1149]),
  ([56,71,135,293,331],[1173,1196]),
  ([56,71,135,327],[139,1393,1159,1333,1147,1143,1147,1147]),
  ([56,71,135,331,386],[1394,1148,1156]),
  ([56,71,135,336,343],[1395,1296,1304]),
  ([56,71,331,386],[140,1148,1156,1148,1156,1148,1156]),
  ([56,81,83,103,135],[1137]),
  ([56,81,86,103,135],[1140]),
  ([56,81,103,135],[1135,1422,1172,1168]),
  ([56,81,103,135,293],[1136,1202])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b87ok : f4b87.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b88 : Array Row := #[
  ([56,83,86,92,135],[1428,1168]),
  ([56,83,86,135,162],[1138,1141,1171,1174]),
  ([56,83,103,135,293],[1139,1169]),
  ([56,86,103,135,293],[1142,1169]),
  ([56,91,103,135,293],[1169]),
  ([56,92,103,135,293],[1494,1470,1203,1189,1169,1168]),
  ([56,92,135,293],[1471,1482,1178,1472,1168,1179,1168,1168]),
  ([56,103,120,135,293],[1169]),
  ([56,103,125,135,293],[1169]),
  ([56,103,130,135,293],[1169]),
  ([56,103,135,140,293],[1169]),
  ([56,103,135,156,293],[1516,1181,1169]),
  ([56,103,135,162,293],[1171,1185,1169]),
  ([56,103,135,173,293],[1501,1176,1182,1169]),
  ([56,103,135,182,293],[1501,1177,1183,1169]),
  ([56,103,135,195,293],[1422,1178,1184,1169]),
  ([56,103,135,241,293],[1169]),
  ([56,103,135,250,293],[1169]),
  ([56,103,135,293],[1501,1169,1175,1169,1169]),
  ([56,103,135,293,331],[1173,1196,1169]),
  ([56,103,135,293,386],[1524,1180,1170,1188,1169]),
  ([56,103,293,386],[1170,1188,1170,1188,1170,1188]),
  ([56,135,162,293],[1542,1171,1199,1197,1198,1171,1171]),
  ([56,135,293,331],[1549,1173,1196,1173,1196,1173,1196]),
  ([58,71,92,285,289],[1483,1402,1240,1242]),
  ([58,71,92,285,343],[1484,1404,1241,1253,1224]),
  ([58,71,92,289,336],[1485,1407,1243,1252,1225]),
  ([58,71,92,336,343],[1409,1226,1216,1217]),
  ([58,71,103,336,343],[1216,1217]),
  ([58,71,135,336,343],[1563,1410,1296,1304,1216,1217]),
  ([58,71,336,343],[1223,1216,1217,1216,1217,1216,1217]),
  ([58,83,103,135,260],[1444,1220])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b88ok : f4b88.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b89 : Array Row := #[
  ([58,86,103,135,257],[1464,1221]),
  ([65,83,103,135,298],[1446,1437,1427,1230]),
  ([67,86,103,135,296],[1466,1457,1426,1235]),
  ([71,77,103,135,289],[1240]),
  ([71,79,103,135,285],[1242]),
  ([71,83,92,135,260],[1445,1220]),
  ([71,83,92,173,343],[1448,1231,1367,1241]),
  ([71,83,103,135,256],[1441,1134]),
  ([71,83,103,135,260],[1442]),
  ([71,83,103,135,298],[1443,1427,1244]),
  ([71,83,103,173,343],[1369]),
  ([71,83,103,260,365],[1447]),
  ([71,83,135,162,260],[1141,1245]),
  ([71,83,135,260,317],[]),
  ([71,83,135,336,343],[1227,1296,1304]),
  ([71,86,92,135,257],[1465,1221]),
  ([71,86,92,182,336],[1468,1236,1381,1243]),
  ([71,86,103,135,256],[1461,1134]),
  ([71,86,103,135,257],[1462]),
  ([71,86,103,135,296],[1463,1426,1248]),
  ([71,86,103,182,336],[1383]),
  ([71,86,103,257,371],[1467]),
  ([71,86,135,162,257],[1138,1249]),
  ([71,86,135,257,323],[]),
  ([71,86,135,336,343],[1228,1296,1304]),
  ([71,92,103,285,289],[1240,1242]),
  ([71,92,103,285,343],[1533,1241,1253]),
  ([71,92,103,289,336],[1534,1243,1252]),
  ([71,92,118,135,343],[1536,1346,1299,1294]),
  ([71,92,120,173,343],[1537,1300]),
  ([71,92,123,135,336],[1538,1346,1307,1294]),
  ([71,92,125,182,336],[1539,1295])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b89ok : f4b89.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b90 : Array Row := #[
  ([71,92,135,241,250],[1550]),
  ([71,92,135,241,260],[1551]),
  ([71,92,135,241,343],[1552]),
  ([71,92,135,250,257],[1553]),
  ([71,92,135,250,336],[1554]),
  ([71,92,135,257,343],[1558]),
  ([71,92,135,260,336],[1562]),
  ([71,92,135,285,289],[1564,1240,1242]),
  ([71,92,135,285,343],[1565,1241,1253]),
  ([71,92,135,289,336],[1566,1243,1252]),
  ([71,92,135,336,343],[1568,1410,1296,1304]),
  ([71,92,173,336,343],[1574,1297,1305]),
  ([71,92,182,336,343],[1575,1298,1306]),
  ([71,92,285,289],[1486,1240,1242,1240,1242,1240,1242]),
  ([71,92,285,343],[1576,1405,1487,1241,1253,1241,1253,1241,1253]),
  ([71,92,289,336],[1577,1408,1488,1243,1252,1243,1252,1243,1252]),
  ([71,92,336,343,351],[1578,1299,1307,1346]),
  ([71,103,118,135,343],[1294]),
  ([71,103,120,173,343],[1300]),
  ([71,103,123,135,336],[1294]),
  ([71,103,125,182,336],[1295]),
  ([71,103,131,392,396],[1535,1274,1419,1312,1313,1277,1279]),
  ([71,103,135,173,247],[1232,1255]),
  ([71,103,135,182,238],[1237,1257]),
  ([71,103,135,195,293],[1542,1516,1422,1259]),
  ([71,103,135,238,250],[]),
  ([71,103,135,238,260],[]),
  ([71,103,135,241,247],[]),
  ([71,103,135,241,250],[]),
  ([71,103,135,241,260],[]),
  ([71,103,135,241,289],[1261]),
  ([71,103,135,241,343],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b90ok : f4b90.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b91 : Array Row := #[
  ([71,103,135,243,260],[]),
  ([71,103,135,247,257],[]),
  ([71,103,135,250,257],[]),
  ([71,103,135,250,285],[1262]),
  ([71,103,135,250,336],[]),
  ([71,103,135,252,257],[]),
  ([71,103,135,256],[1543,1328,1495,1222,1134,1254,1134,1134]),
  ([71,103,135,257,260],[1544]),
  ([71,103,135,257,289],[1263]),
  ([71,103,135,257,293],[1545,1139,1423]),
  ([71,103,135,257,343],[]),
  ([71,103,135,260,285],[1264]),
  ([71,103,135,260,293],[1546,1142,1424]),
  ([71,103,135,260,336],[]),
  ([71,103,135,285,289],[1265]),
  ([71,103,135,285,298],[1266]),
  ([71,103,135,285,343],[1267]),
  ([71,103,135,289,296],[1268]),
  ([71,103,135,289,336],[1269]),
  ([71,103,135,336,343],[1296,1304]),
  ([71,103,135,392,396],[1274,1350,1329,1331,1277,1279]),
  ([71,103,162,392,396],[1352,1353,1277,1279]),
  ([71,103,173,182,293],[1571,1425]),
  ([71,103,173,182,331],[1293]),
  ([71,103,173,336,343],[1297,1305]),
  ([71,103,182,336,343],[1298,1306]),
  ([71,103,241,250,386],[]),
  ([71,103,241,260,365],[]),
  ([71,103,250,257,371],[]),
  ([71,103,285,289,351],[]),
  ([71,103,336,343,351],[1299,1307,1346]),
  ([71,103,392,396],[11,1356,1277,1279,1359,1277,1358,1379,1279,1380,1277,1279])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b91ok : f4b91.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b92 : Array Row := #[
  ([71,118,135,336,343],[1374,1304,1294]),
  ([71,118,135,343],[1216,1294,1297,1294,1294]),
  ([71,120,125,173,182],[1293,1295,1300]),
  ([71,120,135,173,343],[1296,1300]),
  ([71,120,135,336,343],[1296,1304]),
  ([71,120,173,343],[1369,1300,1297,1300,1300]),
  ([71,123,135,336],[1217,1294,1306,1294,1294]),
  ([71,123,135,336,343],[1389,1296,1294]),
  ([71,125,135,182,336],[1304,1295]),
  ([71,125,135,336,343],[1296,1304]),
  ([71,125,182,336],[1383,1295,1306,1295,1295]),
  ([71,131,135,392,396],[1569,1418,1329,1331,1312,1313]),
  ([71,131,162,392,396],[1572,1352,1353,1312,1313]),
  ([71,131,392,396],[1219,1579,1420,1540,1312,1313,1359,1312,1358,1379,1313,1380,1312,1313]),
  ([71,135,140,336,343],[1296,1304]),
  ([71,135,156,336,343],[1296,1304]),
  ([71,135,162,241,250],[1314]),
  ([71,135,162,241,260],[1315]),
  ([71,135,162,250,257],[1317]),
  ([71,135,162,285,289],[1321]),
  ([71,135,162,336,343],[1324,1296,1304]),
  ([71,135,162,392,396],[1570,1327,1357,1352,1353,1329,1331]),
  ([71,135,173,182,331],[1293]),
  ([71,135,173,250,331],[]),
  ([71,135,173,336,343],[1297,1305,1296,1304]),
  ([71,135,182,241,331],[]),
  ([71,135,182,336,343],[1298,1306,1296,1304]),
  ([71,135,241,250,331],[]),
  ([71,135,241,260,317],[]),
  ([71,135,250,257,323],[]),
  ([71,135,285,289,361],[]),
  ([71,135,309,336,343],[1296,1304])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b92ok : f4b92.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b93 : Array Row := #[
  ([71,135,336,343],[1218,1296,1304,1296,1304,1296,1304]),
  ([71,135,336,343,351],[1299,1307,1296,1304]),
  ([71,135,336,343,378],[1226,1536,1538,1541,1296,1304]),
  ([71,135,392,396],[1219,1351,1329,1331,1359,1329,1358,1379,1331,1380,1329,1331]),
  ([71,162,392,396],[1352,1353,1359,1352,1358,1379,1353,1380,1352,1353]),
  ([71,173,182,331],[1293,1293,1293]),
  ([71,173,336,343],[1229,1297,1305,1297,1305,1297,1305]),
  ([71,182,336,343],[1234,1298,1306,1298,1306,1298,1306]),
  ([71,336,343,351],[1299,1307,1346,1299,1307,1299,1346,1307,1346]),
  ([71,392,396],[1359,1358,1379,1380,1359,1358,1379,1380]),
  ([83,86,103,135,195],[1422,1426,1427,1428]),
  ([83,86,103,135,257],[1423]),
  ([83,86,103,135,260],[1424]),
  ([83,86,103,173,182],[1425]),
  ([83,103,135,162,260],[1141,1434]),
  ([83,103,135,173,298],[1431,1433,1427]),
  ([83,103,135,257,293],[1139,1423]),
  ([83,103,135,260,274],[]),
  ([83,103,135,298],[1427,1432,1429,1430,1427,1427]),
  ([83,135,162,260],[1141,1440,1438,1439,1141,1141]),
  ([86,103,135,162,257],[1138,1454]),
  ([86,103,135,182,296],[1451,1453,1426]),
  ([86,103,135,257,274],[]),
  ([86,103,135,260,293],[1142,1424]),
  ([86,103,135,296],[1426,1452,1449,1450,1426,1426]),
  ([86,135,162,257],[1138,1460,1458,1459,1138,1138]),
  ([92,135,336,343,378],[1578,1536,1538,1541]),
  ([103,135,173,182,293],[1475,1425,1501]),
  ([103,135,173,195,293],[1476,1489,1422]),
  ([103,135,173,250,293],[1477]),
  ([103,135,182,195,293],[1479,1491,1422]),
  ([103,135,182,241,293],[1480])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b93ok : f4b93.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def f4b94 : Array Row := #[
  ([103,135,195,293],[1482,1470,1472,1493,1422,1422,1422]),
  ([103,135,241,250,293],[]),
  ([103,135,241,260,274],[]),
  ([103,135,250,257,274],[]),
  ([103,135,257,293],[1473,1139,1423,1139,1423,1139,1423]),
  ([103,135,260,293],[1474,1142,1424,1142,1424,1142,1424]),
  ([103,135,274,285,289],[1483]),
  ([103,135,336,343,378],[1536,1538,1541]),
  ([103,173,182,293],[1490,1492,1425,1425,1425]),
  ([135,336,343,378],[1536,1538,1541,1536,1538,1536,1541,1538,1541])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f4b94ok : f4b94.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true := by decide +kernel

private def layer4 (i : ℕ) : {s : List W // impossible 4 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer3 i).1) 3) = true} :=
    #[⟨f4b0, f4b0ok⟩, ⟨f4b1, f4b1ok⟩, ⟨f4b2, f4b2ok⟩, ⟨f4b3, f4b3ok⟩, ⟨f4b4, f4b4ok⟩, ⟨f4b5, f4b5ok⟩, ⟨f4b6, f4b6ok⟩, ⟨f4b7, f4b7ok⟩, ⟨f4b8, f4b8ok⟩, ⟨f4b9, f4b9ok⟩, ⟨f4b10, f4b10ok⟩, ⟨f4b11, f4b11ok⟩, ⟨f4b12, f4b12ok⟩, ⟨f4b13, f4b13ok⟩, ⟨f4b14, f4b14ok⟩, ⟨f4b15, f4b15ok⟩, ⟨f4b16, f4b16ok⟩, ⟨f4b17, f4b17ok⟩, ⟨f4b18, f4b18ok⟩, ⟨f4b19, f4b19ok⟩, ⟨f4b20, f4b20ok⟩, ⟨f4b21, f4b21ok⟩, ⟨f4b22, f4b22ok⟩, ⟨f4b23, f4b23ok⟩, ⟨f4b24, f4b24ok⟩, ⟨f4b25, f4b25ok⟩, ⟨f4b26, f4b26ok⟩, ⟨f4b27, f4b27ok⟩, ⟨f4b28, f4b28ok⟩, ⟨f4b29, f4b29ok⟩, ⟨f4b30, f4b30ok⟩, ⟨f4b31, f4b31ok⟩, ⟨f4b32, f4b32ok⟩, ⟨f4b33, f4b33ok⟩, ⟨f4b34, f4b34ok⟩, ⟨f4b35, f4b35ok⟩, ⟨f4b36, f4b36ok⟩, ⟨f4b37, f4b37ok⟩, ⟨f4b38, f4b38ok⟩, ⟨f4b39, f4b39ok⟩, ⟨f4b40, f4b40ok⟩, ⟨f4b41, f4b41ok⟩, ⟨f4b42, f4b42ok⟩, ⟨f4b43, f4b43ok⟩, ⟨f4b44, f4b44ok⟩, ⟨f4b45, f4b45ok⟩, ⟨f4b46, f4b46ok⟩, ⟨f4b47, f4b47ok⟩, ⟨f4b48, f4b48ok⟩, ⟨f4b49, f4b49ok⟩, ⟨f4b50, f4b50ok⟩, ⟨f4b51, f4b51ok⟩, ⟨f4b52, f4b52ok⟩, ⟨f4b53, f4b53ok⟩, ⟨f4b54, f4b54ok⟩, ⟨f4b55, f4b55ok⟩, ⟨f4b56, f4b56ok⟩, ⟨f4b57, f4b57ok⟩, ⟨f4b58, f4b58ok⟩, ⟨f4b59, f4b59ok⟩, ⟨f4b60, f4b60ok⟩, ⟨f4b61, f4b61ok⟩, ⟨f4b62, f4b62ok⟩, ⟨f4b63, f4b63ok⟩, ⟨f4b64, f4b64ok⟩, ⟨f4b65, f4b65ok⟩, ⟨f4b66, f4b66ok⟩, ⟨f4b67, f4b67ok⟩, ⟨f4b68, f4b68ok⟩, ⟨f4b69, f4b69ok⟩, ⟨f4b70, f4b70ok⟩, ⟨f4b71, f4b71ok⟩, ⟨f4b72, f4b72ok⟩, ⟨f4b73, f4b73ok⟩, ⟨f4b74, f4b74ok⟩, ⟨f4b75, f4b75ok⟩, ⟨f4b76, f4b76ok⟩, ⟨f4b77, f4b77ok⟩, ⟨f4b78, f4b78ok⟩, ⟨f4b79, f4b79ok⟩, ⟨f4b80, f4b80ok⟩, ⟨f4b81, f4b81ok⟩, ⟨f4b82, f4b82ok⟩, ⟨f4b83, f4b83ok⟩, ⟨f4b84, f4b84ok⟩, ⟨f4b85, f4b85ok⟩, ⟨f4b86, f4b86ok⟩, ⟨f4b87, f4b87ok⟩, ⟨f4b88, f4b88ok⟩, ⟨f4b89, f4b89ok⟩, ⟨f4b90, f4b90ok⟩, ⟨f4b91, f4b91ok⟩, ⟨f4b92, f4b92ok⟩, ⟨f4b93, f4b93ok⟩, ⟨f4b94, f4b94ok⟩]
  pick alphabet layer3 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f5b0 : Array Row := #[
  ([0,28,56,71,103,135],[2796,478,465,455,19]),
  ([0,35,49,71,103,135],[2431,669,638,623,613]),
  ([0,39,44,71,103,135],[2212,1832,760,745,735]),
  ([0,39,49,58,71,92],[2255,1656,896,812,806,14,9,1]),
  ([0,39,49,71,92,135],[2340,1741,1291,1111,913,5]),
  ([0,39,49,71,92,173],[2353,1752,1297,1183,6]),
  ([0,39,49,71,92,182],[2362,1759,1300,1193,7]),
  ([0,39,49,71,92,351],[2368,1769,1307,1208,881,8]),
  ([0,39,49,71,96,135],[2399,1800,1324,1112,938,5]),
  ([0,39,49,71,97,135],[2405,1806,1329,1113,948]),
  ([0,39,49,71,99,135],[2411,1814,1333,1115,959]),
  ([0,39,49,71,103,131],[2424,1825,1338,1065,979]),
  ([0,39,49,71,103,135],[2434,1835,1343,1118,982]),
  ([0,39,49,71,103,351],[2452,1853,1357,1213,972]),
  ([0,39,49,71,103,365],[2453,1854,1358,1214,973]),
  ([0,39,49,71,103,371],[2454,1855,1359,1215,974]),
  ([0,39,49,71,103,386],[2455,1856,1361,1216,976]),
  ([0,39,49,71,131],[2524,15,1045,1925,10,1049,1419,2,1057,1240,1,1073,16,11,3]),
  ([0,39,49,71,131,135],[2503,1904,1399,1137,1076,5]),
  ([0,39,49,71,131,162],[2511,1912,1409,1169]),
  ([0,39,49,71,135,162],[2540,1941,1461,1172,0]),
  ([0,39,49,71,135,300],[2558,1959,1495,1208,881]),
  ([0,39,49,71,135,309],[2560,1961,1497,1213,972]),
  ([0,39,49,71,135,317],[2562,1962,1499,1219,994]),
  ([0,39,49,71,135,323],[2563,1964,1501,1225,998]),
  ([0,39,49,71,135,331],[2565,1966,1503,1232,1002]),
  ([0,39,49,71,135,361],[2567,1968,1505,1244,1102]),
  ([0,39,49,71,135,378],[2568,1969,1508,1245,1105,4]),
  ([0,39,49,92,135,274],[2676,2077,1495,1307,881]),
  ([0,39,49,92,135,378],[2678,2079,1524,1315,1290,18,13,8,4]),
  ([0,39,49,103,135,274],[2701,2102,1497,1357,972]),
  ([0,39,49,103,135,293],[2702,2103,1515,1364,1265,19])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b0ok : f5b0.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b1 : Array Row := #[
  ([0,39,49,103,135,378],[2703,2104,1530,1371,1341,4]),
  ([0,39,49,135,378],[2769,17,1485,2170,12,1489,1627,8,1544,1433,4,1449,6,4,7,4,4]),
  ([0,39,71,92,135,250],[2880,2077,1959,1769,881,12]),
  ([0,39,71,92,135,343],[2882,2083,1989,1788,1732,20,13]),
  ([0,39,71,103,135,250],[2908,2102,1961,1853,972]),
  ([0,39,71,103,135,260],[2909,2108,1971,1860,1636]),
  ([0,39,71,103,135,289],[2910,2112,1980,1867,1702,9]),
  ([0,39,71,103,135,343],[2911,2114,1994,1875,1820]),
  ([0,49,71,92,135,241],[2880,2676,2558,2368,881,17]),
  ([0,49,71,92,135,336],[2884,2682,2588,2387,2330,20,18]),
  ([0,49,71,103,135,241],[2908,2701,2560,2452,972]),
  ([0,49,71,103,135,257],[2914,2706,2570,2459,2235]),
  ([0,49,71,103,135,285],[2915,2711,2579,2466,2301,14]),
  ([0,49,71,103,135,336],[2916,2713,2593,2474,2419]),
  ([1,28,56,71,103,135],[455,36]),
  ([1,35,49,71,103,135],[2432,670,613]),
  ([1,39,44,71,103,135],[2212,735]),
  ([1,39,49,58,71,92],[2255,897,31,28,21]),
  ([1,39,49,71,92,173],[2353,25]),
  ([1,39,49,71,92,182],[2362,26]),
  ([1,39,49,71,92,351],[2368,881,27]),
  ([1,39,49,71,96,135],[2399,938,24]),
  ([1,39,49,71,97,135],[2405,948]),
  ([1,39,49,71,99,135],[2411,959]),
  ([1,39,49,71,103,131],[2424,0,1066,980]),
  ([1,39,49,71,103,135],[2434,982]),
  ([1,39,49,71,103,351],[2452,972]),
  ([1,39,49,71,103,365],[2453,973]),
  ([1,39,49,71,103,371],[2454,974]),
  ([1,39,49,71,103,386],[2455,976]),
  ([1,39,49,71,131],[2524,32,1045,0,1050,0,1058,0,1074,33,29,22]),
  ([1,39,49,71,131,135],[2503,1076,24])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b1ok : f5b1.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b2 : Array Row := #[
  ([1,39,49,71,131,162],[2511,1410,1170,0,1022]),
  ([1,39,49,71,135,309],[2560,1213,972]),
  ([1,39,49,71,135,317],[2562,1219,994]),
  ([1,39,49,71,135,323],[2563,1225,998]),
  ([1,39,49,71,135,331],[2565,1970,1232,1002]),
  ([1,39,49,71,135,361],[2567,1244,1102]),
  ([1,39,49,71,135,378],[2568,5,1509,1245,1105,23]),
  ([1,39,49,71,162,351],[2616,1593,1109]),
  ([1,39,49,92,135,378],[2678,5,1525,1315,1290,35,30,27,23]),
  ([1,39,49,103,135,274],[2701,1357,972]),
  ([1,39,49,103,135,293],[2702,2105,1364,1265,36]),
  ([1,39,49,103,135,378],[2703,5,1531,1371,1341,23]),
  ([1,39,49,135,156,162],[2750,1573,23]),
  ([1,39,49,135,162,275],[2758,1593,1262]),
  ([1,39,49,135,378],[2769,34,1485,5,1490,1627,27,1544,1433,23,1449,25,23,26,23,23]),
  ([1,39,71,92,135,343],[2882,1990,1788,1732,37,30]),
  ([1,39,71,103,135,250],[2908,1853,972]),
  ([1,39,71,103,135,260],[2909,1860,1636]),
  ([1,39,71,103,135,289],[2910,1867,1702,28]),
  ([1,39,71,103,135,343],[2911,1995,1875,1820]),
  ([1,49,71,92,135,241],[2368,881,34]),
  ([1,49,71,92,135,336],[2387,2330,37,35]),
  ([1,49,71,103,135,241],[2452,972]),
  ([1,49,71,103,135,257],[2459,2235]),
  ([1,49,71,103,135,285],[2466,2301,31]),
  ([1,49,71,103,135,336],[2474,2419]),
  ([1,49,71,103,241,351],[982,2434]),
  ([1,49,71,135,162,241],[2758,2616,1109,32]),
  ([2,28,56,71,103,135],[455,53]),
  ([2,35,49,71,103,135],[669,613]),
  ([2,39,44,71,103,135],[2213,1833,735]),
  ([2,39,49,58,71,92],[1656,898,50,45,38])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b2ok : f5b2.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b3 : Array Row := #[
  ([2,39,49,71,92,173],[1752,42]),
  ([2,39,49,71,92,182],[1759,43]),
  ([2,39,49,71,92,351],[1769,881,44]),
  ([2,39,49,71,96,135],[1800,938,41]),
  ([2,39,49,71,97,135],[1806,948]),
  ([2,39,49,71,99,135],[1814,959]),
  ([2,39,49,71,103,131],[1825,0,1067,981]),
  ([2,39,49,71,103,135],[1835,982]),
  ([2,39,49,71,103,351],[1853,972]),
  ([2,39,49,71,103,365],[1854,973]),
  ([2,39,49,71,103,371],[1855,974]),
  ([2,39,49,71,103,386],[1856,976]),
  ([2,39,49,71,131],[0,1046,1925,46,1049,0,1059,0,1075,51,47,39]),
  ([2,39,49,71,131,135],[1904,1076,41]),
  ([2,39,49,71,131,162],[1912,1411,1171,0,1023]),
  ([2,39,49,71,135,309],[1961,1213,972]),
  ([2,39,49,71,135,317],[1962,1219,994]),
  ([2,39,49,71,135,323],[1964,1225,998]),
  ([2,39,49,71,135,331],[2569,1966,1232,1002]),
  ([2,39,49,71,135,361],[1968,1244,1102]),
  ([2,39,49,71,135,378],[1969,5,1510,1245,1105,40]),
  ([2,39,49,71,162,351],[2017,1594,1109]),
  ([2,39,49,92,135,378],[2079,5,1526,1315,1290,52,49,44,40]),
  ([2,39,49,103,135,274],[2102,1357,972]),
  ([2,39,49,103,135,293],[2704,2103,1364,1265,53]),
  ([2,39,49,103,135,378],[2104,5,1532,1371,1341,40]),
  ([2,39,49,135,156,162],[2151,1573,40]),
  ([2,39,49,135,162,276],[2159,1594,1263]),
  ([2,39,49,135,378],[5,1486,2170,48,1489,1627,44,1544,1433,40,1449,42,40,43,40,40]),
  ([2,39,71,92,135,250],[1769,881,48]),
  ([2,39,71,92,135,343],[1788,1732,54,49]),
  ([2,39,71,103,135,250],[1853,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b3ok : f5b3.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b4 : Array Row := #[
  ([2,39,71,103,135,260],[1860,1636]),
  ([2,39,71,103,135,289],[1867,1702,45]),
  ([2,39,71,103,135,343],[1875,1820]),
  ([2,39,71,103,250,351],[982,1835]),
  ([2,39,71,135,162,250],[2159,2017,1109,46]),
  ([2,49,71,92,135,336],[2884,2589,2387,2330,54,52]),
  ([2,49,71,103,135,241],[2908,2452,972]),
  ([2,49,71,103,135,257],[2914,2459,2235]),
  ([2,49,71,103,135,285],[2915,2466,2301,50]),
  ([2,49,71,103,135,336],[2916,2594,2474,2419]),
  ([3,28,56,71,103,135],[455,57]),
  ([3,39,49,71,92,135],[913,56]),
  ([3,39,49,71,103,351],[972]),
  ([3,39,49,71,135,162],[1464,1172,55]),
  ([4,28,56,71,103,135],[2797,478,465,72]),
  ([4,35,49,71,103,135],[638,623]),
  ([4,39,44,71,103,135],[760,745]),
  ([4,39,49,58,71,92],[812,69,66,58]),
  ([4,39,49,71,92,173],[2354,1297,1184,63]),
  ([4,39,49,71,92,182],[1760,1300,1194,64]),
  ([4,39,49,71,92,351],[1307,1209,881,65]),
  ([4,39,49,71,96,135],[1324,1112,62]),
  ([4,39,49,71,97,135],[1329,1114]),
  ([4,39,49,71,99,135],[1333,1116]),
  ([4,39,49,71,103,131],[1338,1065]),
  ([4,39,49,71,103,135],[1343,1118]),
  ([4,39,49,71,103,351],[1357,1213,972]),
  ([4,39,49,71,103,365],[2457,1358,1214,973]),
  ([4,39,49,71,103,371],[1858,1359,1215,974]),
  ([4,39,49,71,103,386],[1361,1216,976]),
  ([4,39,49,71,131],[0,1047,0,1051,1419,59,1057,0,1077,70,67,60]),
  ([4,39,49,71,131,135],[1399,1138,0,1078,62])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b4ok : f5b4.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b5 : Array Row := #[
  ([4,39,49,71,131,162],[1409]),
  ([4,39,49,71,135,303],[1496,934]),
  ([4,39,49,71,135,309],[1497,972]),
  ([4,39,49,71,135,317],[1499,994]),
  ([4,39,49,71,135,323],[1501,998]),
  ([4,39,49,71,135,331],[1503,1002]),
  ([4,39,49,71,135,361],[1505,1102]),
  ([4,39,49,71,135,378],[1508,1105,61]),
  ([4,39,49,92,135,274],[1496,881]),
  ([4,39,49,92,135,378],[5,1527,1290,71,68,65,61]),
  ([4,39,49,103,135,274],[1497,972]),
  ([4,39,49,103,135,293],[1515,1265,72]),
  ([4,39,49,103,135,378],[1530,1341,61]),
  ([4,39,49,135,156,162],[61]),
  ([4,39,49,135,162,274],[1109,59]),
  ([4,39,49,135,274,309],[1118,1343]),
  ([4,39,49,135,378],[5,1487,5,1491,5,1545,1433,61,1449,63,61,64,61,61]),
  ([4,39,71,92,135,343],[2083,1991,1732,73,68]),
  ([4,39,71,103,135,250],[2102,1961,972]),
  ([4,39,71,103,135,260],[2912,2108,1971,1636]),
  ([4,39,71,103,135,289],[2112,1980,1702,66]),
  ([4,39,71,103,135,343],[2114,1994,1820]),
  ([4,49,71,92,135,336],[2682,2590,2330,73,71]),
  ([4,49,71,103,135,241],[2701,2560,972]),
  ([4,49,71,103,135,257],[2917,2706,2570,2235]),
  ([4,49,71,103,135,285],[2711,2579,2301,69]),
  ([4,49,71,103,135,336],[2713,2593,2419]),
  ([5,28,56,71,103,135],[465,91]),
  ([5,35,49,71,103,135],[2433,671,639,623]),
  ([5,39,44,71,103,135],[2212,745]),
  ([5,39,49,58,71,92],[2255,899,86,83,75]),
  ([5,39,49,71,92,173],[2353,79])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b5ok : f5b5.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b6 : Array Row := #[
  ([5,39,49,71,92,182],[2362,1761,1195,892,80]),
  ([5,39,49,71,92,351],[2368,1210,881,81]),
  ([5,39,49,71,92,355],[2369,882,82]),
  ([5,39,49,71,96,135],[2399,1114,939,78]),
  ([5,39,49,71,97,135],[2405,1113]),
  ([5,39,49,71,99,135],[2411,1117,960]),
  ([5,39,49,71,103,131],[2424,1065]),
  ([5,39,49,71,103,135],[2434,1118]),
  ([5,39,49,71,103,351],[2452,1213,972]),
  ([5,39,49,71,103,365],[2453,1362,1214,973]),
  ([5,39,49,71,103,371],[2454,1215,974]),
  ([5,39,49,71,103,386],[2455,1859,1216,976]),
  ([5,39,49,71,131],[2524,87,1045,0,1052,0,1060,0,1079,88,84,76]),
  ([5,39,49,71,131,135],[2503,1139,0,1080,78]),
  ([5,39,49,71,131,162],[2511]),
  ([5,39,49,71,135,162],[2540,74]),
  ([5,39,49,71,135,304],[2559,945]),
  ([5,39,49,71,135,309],[2560,972]),
  ([5,39,49,71,135,317],[2562,994]),
  ([5,39,49,71,135,323],[2563,998]),
  ([5,39,49,71,135,331],[2565,1002]),
  ([5,39,49,71,135,361],[2567,1102]),
  ([5,39,49,71,135,378],[2568,5,1511,1246,1105,77]),
  ([5,39,49,92,135,378],[2678,5,1528,1316,1290,90,85,81,77]),
  ([5,39,49,103,135,274],[2701,1497,972]),
  ([5,39,49,103,135,293],[2702,2106,1515,1265,91]),
  ([5,39,49,103,135,378],[2703,1530,1372,1341,77]),
  ([5,39,49,135,156,162],[2750,1574,77]),
  ([5,39,49,135,378],[2769,89,1485,5,1492,5,1628,82,1546,1433,77,1449,79,77,80,77,77]),
  ([5,39,71,92,135,343],[2882,1992,1789,1732,92,85]),
  ([5,39,71,103,135,250],[2908,1961,972]),
  ([5,39,71,103,135,260],[2909,2109,1971,1636])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b6ok : f5b6.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b7 : Array Row := #[
  ([5,39,71,103,135,289],[2910,1980,1702,83]),
  ([5,39,71,103,135,343],[2911,1994,1876,1820]),
  ([5,49,71,92,135,241],[2559,2369,881,89]),
  ([5,49,71,92,135,336],[2591,2388,2330,92,90]),
  ([5,49,71,103,135,241],[2560,972]),
  ([5,49,71,103,135,257],[2570,2235]),
  ([5,49,71,103,135,285],[2579,2301,86]),
  ([5,49,71,103,135,336],[2593,2419]),
  ([5,49,71,135,162,241],[1109,87]),
  ([5,49,71,135,241,309],[1118,2434]),
  ([6,39,49,71,92,135],[2340,914,94]),
  ([6,39,49,71,135,162],[2540,93]),
  ([6,49,71,103,135,241],[972]),
  ([7,39,44,71,103,135],[745]),
  ([7,39,49,71,92,135],[1114,96]),
  ([7,39,49,71,135,162],[95]),
  ([7,39,49,71,135,309],[972]),
  ([8,28,56,71,103,135],[465,114]),
  ([8,35,49,71,103,135],[669,623]),
  ([8,39,44,71,103,135],[2214,1834,761,745]),
  ([8,39,49,58,71,92],[1656,900,111,106,98]),
  ([8,39,49,71,92,173],[2355,1752,1185,890,102]),
  ([8,39,49,71,92,182],[1759,103]),
  ([8,39,49,71,92,351],[1769,1211,881,104]),
  ([8,39,49,71,92,358],[1770,883,105]),
  ([8,39,49,71,96,135],[1800,1116,940,101]),
  ([8,39,49,71,97,135],[1806,1117,949]),
  ([8,39,49,71,99,135],[1814,1115]),
  ([8,39,49,71,103,131],[1825,1065]),
  ([8,39,49,71,103,135],[1835,1118]),
  ([8,39,49,71,103,351],[1853,1213,972]),
  ([8,39,49,71,103,365],[1854,1214,973])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b7ok : f5b7.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b8 : Array Row := #[
  ([8,39,49,71,103,371],[1855,1363,1215,974]),
  ([8,39,49,71,103,386],[2458,1856,1216,976]),
  ([8,39,49,71,131],[0,1048,1925,107,1049,0,1061,0,1081,112,108,99]),
  ([8,39,49,71,131,135],[1904,1140,0,1082,101]),
  ([8,39,49,71,131,162],[1912]),
  ([8,39,49,71,135,162],[1941,97]),
  ([8,39,49,71,135,306],[1960,956]),
  ([8,39,49,71,135,309],[1961,972]),
  ([8,39,49,71,135,317],[1962,994]),
  ([8,39,49,71,135,323],[1964,998]),
  ([8,39,49,71,135,331],[1966,1002]),
  ([8,39,49,71,135,361],[1968,1102]),
  ([8,39,49,71,135,378],[1969,5,1512,1247,1105,100]),
  ([8,39,49,92,135,378],[2079,5,1529,1317,1290,113,110,104,100]),
  ([8,39,49,103,135,274],[2102,1497,972]),
  ([8,39,49,103,135,293],[2705,2103,1515,1265,114]),
  ([8,39,49,103,135,378],[2104,1530,1373,1341,100]),
  ([8,39,49,135,156,162],[2151,1575,100]),
  ([8,39,49,135,378],[5,1488,2170,109,1489,5,1629,105,1547,1433,100,1449,102,100,103,100,100]),
  ([8,39,71,92,135,250],[1960,1770,881,109]),
  ([8,39,71,92,135,343],[1993,1790,1732,115,110]),
  ([8,39,71,103,135,250],[1961,972]),
  ([8,39,71,103,135,260],[1971,1636]),
  ([8,39,71,103,135,289],[1980,1702,106]),
  ([8,39,71,103,135,343],[1994,1820]),
  ([8,39,71,135,162,250],[1109,107]),
  ([8,39,71,135,250,309],[1118,1835]),
  ([8,49,71,92,135,336],[2884,2592,2389,2330,115,113]),
  ([8,49,71,103,135,241],[2908,2560,972]),
  ([8,49,71,103,135,257],[2914,2707,2570,2235]),
  ([8,49,71,103,135,285],[2915,2579,2301,111]),
  ([8,49,71,103,135,336],[2916,2593,2475,2419])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b8ok : f5b8.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b9 : Array Row := #[
  ([9,39,49,71,92,135],[1741,915,117]),
  ([9,39,49,71,135,162],[1941,116]),
  ([9,39,71,103,135,250],[972]),
  ([10,35,49,71,103,135],[623]),
  ([10,39,49,71,92,135],[1116,119]),
  ([10,39,49,71,135,162],[118]),
  ([10,39,49,71,135,309],[972]),
  ([11,28,56,71,103,135],[465,122]),
  ([11,39,49,71,92,135],[1117,916,121]),
  ([11,39,49,71,135,162],[120]),
  ([11,39,49,71,135,309],[972]),
  ([12,39,49,71,103,135],[]),
  ([13,39,49,71,103,135],[1118]),
  ([14,19,28,71,103,135],[514,289,226,192,129,123]),
  ([14,19,39,49,135,162],[1460,277,251,185,141,123,124]),
  ([14,28,49,71,92,135],[2339,496,423,412,180,169,128,126]),
  ([14,28,49,71,103,365],[2450,536,432,427,415,183]),
  ([14,28,49,71,103,386],[2451,537,184,170]),
  ([14,28,49,71,135,162],[2538,541,424,186,123,125]),
  ([14,28,49,71,135,317],[2556,547,427,188]),
  ([14,28,49,71,135,331],[2557,548,428,189,170]),
  ([14,28,49,103,135,274],[2699,555,432]),
  ([14,28,49,103,135,293],[2700,556,433,198,189,184,171]),
  ([14,28,56,71,103,135],[2798,478,466,456,191]),
  ([14,28,71,103,135,182],[2903,530,512,197,127,128]),
  ([14,28,71,103,135,250],[2905,533,198]),
  ([14,28,71,103,135,260],[2906,555,547,536,440,199]),
  ([14,29,49,71,103,135],[2432,566,565]),
  ([14,31,49,71,103,135],[2433,581,580,182]),
  ([14,35,49,71,103,135],[2431,674,638,624,614,181]),
  ([14,39,44,71,103,135],[2212,1836,760,746,736,130]),
  ([14,39,49,58,71,92],[2255,1657,901,812,807,166,164,146,133])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b9ok : f5b9.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b10 : Array Row := #[
  ([14,39,49,67,103,135],[1691,1342,127,131]),
  ([14,39,49,71,92,173],[2353,1753,1297,1186,142]),
  ([14,39,49,71,92,182],[2362,1762,1300,1196,894,128,143,131]),
  ([14,39,49,71,92,351],[2368,1773,1307,1217,881,144]),
  ([14,39,49,71,92,365],[2370,1774,1308,1218,884,145]),
  ([14,39,49,71,96,135],[2399,1801,1324,1119,941,139]),
  ([14,39,49,71,97,135],[2405,1807,1329,1120,950,140]),
  ([14,39,49,71,99,135],[2411,1815,1333,1121,961]),
  ([14,39,49,71,103,131],[2424,1826,1338,0,1068,983,172]),
  ([14,39,49,71,103,135],[2434,1837,1343,1122,984]),
  ([14,39,49,71,103,142],[2443,1844,1346,1157,984]),
  ([14,39,49,71,103,351],[2452,1860,1357,1219,972]),
  ([14,39,49,71,103,365],[2453,1861,1358,1220,973]),
  ([14,39,49,71,103,371],[2454,1862,1359,1221,974,129,141]),
  ([14,39,49,71,103,386],[2455,1864,1361,1222,976]),
  ([14,39,49,71,108,135],[2483,1884,1379,1122,995]),
  ([14,39,49,71,131],[2524,167,1045,0,1926,147,1054,1419,136,1057,0,1251,134,1084,125,173,135,165,168,124,148,137]),
  ([14,39,49,71,131,135],[2503,1905,1399,1142,0,1085,174,139]),
  ([14,39,49,71,131,162],[2511,1913,1409,1173,175]),
  ([14,39,49,71,135,162],[2540,1942,1461,1174,176,132]),
  ([14,39,49,71,135,309],[2560,1971,1497,1214,972]),
  ([14,39,49,71,135,313],[2561,1972,1498,1218,992]),
  ([14,39,49,71,135,317],[2562,1973,1499,1220,994]),
  ([14,39,49,71,135,323],[2563,1974,1501,1226,998]),
  ([14,39,49,71,135,331],[2565,1976,1503,1233,1002]),
  ([14,39,49,71,135,361],[2567,1978,1505,1248,1102,177]),
  ([14,39,49,71,135,378],[2568,1979,1508,1253,1105,178,138]),
  ([14,39,49,71,162,365],[2617,2020,1591,1156,179]),
  ([14,39,49,71,317,365],[2633,2036,1618,995,1157]),
  ([14,39,49,83,135,162],[2055,1275,130,135]),
  ([14,39,49,92,135,274],[2676,2080,1498,1308,881]),
  ([14,39,49,92,135,378],[2678,2081,5,1533,1318,1290,190,150,144,138])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b10ok : f5b10.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b11 : Array Row := #[
  ([14,39,49,103,135,274],[2701,2108,1499,1358,972]),
  ([14,39,49,103,135,278],[2109,1362]),
  ([14,39,49,103,135,293],[2702,2110,1516,1365,1265,191,171]),
  ([14,39,49,103,135,378],[2703,2111,5,1534,1374,1341,138]),
  ([14,39,49,103,274,365],[2728,2131,1618,984,1346]),
  ([14,39,49,135,156,162],[2750,2152,1576,138]),
  ([14,39,49,135,162,274],[2757,2161,1591,1109,136]),
  ([14,39,49,135,274,317],[2767,2171,1618,1122,1379]),
  ([14,39,49,135,378],[2769,187,1485,5,2172,149,1494,5,1630,145,1549,1433,138,1449,126,142,138,143,138,138]),
  ([14,39,55,71,103,135],[2790,1837,1640,1639,1637]),
  ([14,39,71,92,135,260],[2881,2080,1972,1774,1635,149]),
  ([14,39,71,92,135,343],[2882,2083,1996,1791,1732,194,150]),
  ([14,39,71,103,135,250],[2908,2102,1962,1854,972]),
  ([14,39,71,103,135,260],[2909,2108,1973,1861,1636]),
  ([14,39,71,103,135,289],[2910,2112,1981,1868,1702,195,146]),
  ([14,39,71,103,135,343],[2911,2114,1997,1877,1820]),
  ([14,39,71,103,260,365],[2939,2131,2036,1637,1844]),
  ([14,39,71,135,162,260],[2961,2161,2020,1638,196,147]),
  ([14,39,71,135,260,317],[2972,2171,2036,1639,1884]),
  ([14,39,103,135,260,274],[3010,2171,2131,1640,1837]),
  ([14,44,49,71,103,135],[2435,2217,2189,181,151]),
  ([14,44,71,83,103,135],[2855,2203,159]),
  ([14,44,71,103,135],[2918,193,2215,161,157,2225,154,2220,162,158,155,163,156,160,152,153]),
  ([14,49,58,83,103,135],[2847,2653,195,152,177,164]),
  ([14,49,71,83,92,135],[2853,2319,2309,153,178,164]),
  ([14,49,71,83,103,365],[2859,2657,2322,2312,154,179]),
  ([14,49,71,83,135,162],[2860,2320,156,165]),
  ([14,49,71,83,135,317],[2861,2322,157]),
  ([14,49,71,92,135,241],[2881,2676,2561,2370,881,187]),
  ([14,49,71,92,135,336],[2886,2682,2595,2390,2330,194,190]),
  ([14,49,71,103,135,238],[2906,2699,2556,2450,611]),
  ([14,49,71,103,135,241],[2909,2701,2562,2453,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b11ok : f5b11.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b12 : Array Row := #[
  ([14,49,71,103,135,243],[2912,2457]),
  ([14,49,71,103,135,257],[2919,2706,2571,2460,2235,185]),
  ([14,49,71,103,135,285],[2923,2711,2580,2467,2301,166]),
  ([14,49,71,103,135,293],[2924,2470,186,171]),
  ([14,49,71,103,135,336],[2925,2713,2596,2476,2419]),
  ([14,49,71,103,241,365],[2939,2728,2633,984,2443]),
  ([14,49,71,135,162,241],[2961,2757,2617,1109,167]),
  ([14,49,71,135,241,317],[2972,2767,2633,1122,2483]),
  ([14,49,83,86,103,135],[2988,2650,171]),
  ([14,49,83,103,135,162],[2990,2655,160,172]),
  ([14,49,83,103,135,274],[2993,2657,161]),
  ([14,49,83,135,162],[2995,196,2658,2663,179,2659,163,151,159,173,174,175]),
  ([14,49,103,135,241,274],[3010,2767,2728,1343,2434]),
  ([14,49,103,135,293],[3013,199,2710,188,2732,183,2717,171,197,171,180,171,171]),
  ([14,71,83,103,135,260],[2993,2861,2859,2789,196]),
  ([14,71,103,135,241,260],[3010,2972,2939,1837,2790]),
  ([15,28,49,71,103,135],[2432,519,416,205]),
  ([15,39,49,71,92,135],[2340,918,202]),
  ([15,39,49,71,96,135],[2399,941,202]),
  ([15,39,49,71,103,365],[2453,973]),
  ([15,39,49,71,135,162],[2540,1462,1174,204,200]),
  ([15,39,49,135,156,162],[2750,1576,201]),
  ([15,49,71,83,103,135],[2313,203,204]),
  ([15,49,71,103,135,241],[2453,972]),
  ([16,39,49,71,92,135],[1291,1119,207]),
  ([16,39,49,71,135,162],[1461,206]),
  ([16,39,49,71,135,317],[1499,994]),
  ([16,39,49,103,135,274],[1499,972]),
  ([17,28,49,71,103,135],[2433,521,219]),
  ([17,28,49,71,135,162],[2539,543,220,208]),
  ([17,39,49,71,92,135],[2340,1120,919,212]),
  ([17,39,49,71,103,131],[2424,74,1068])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b12ok : f5b12.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b13 : Array Row := #[
  ([17,39,49,71,131],[2524,217,1045,0,1056,132,1060,0,1086,208,216,218,213,210]),
  ([17,39,49,71,131,135],[2503,1143,0,1087,212]),
  ([17,39,49,71,131,162],[2511]),
  ([17,39,49,71,135,162],[2540,209]),
  ([17,39,49,71,135,317],[2562,994]),
  ([17,39,49,135,156,162],[2750,1577,211]),
  ([17,49,71,83,103,135],[214]),
  ([17,49,71,83,135,162],[176,215,216]),
  ([17,49,71,103,135,241],[2562,972]),
  ([17,49,71,135,162,241],[1109,217]),
  ([18,39,49,71,103,135],[2434]),
  ([18,39,49,71,135,162],[2540,221]),
  ([19,28,39,71,92,135],[1740,495,389,378,272,261,225,223]),
  ([19,28,39,71,103,371],[1851,534,398,393,381,275]),
  ([19,28,39,71,103,386],[1852,535,276,262]),
  ([19,28,39,71,135,162],[1939,540,390,278,123,222]),
  ([19,28,39,71,135,323],[1957,545,393,280]),
  ([19,28,39,71,135,331],[1958,546,394,281,262]),
  ([19,28,39,103,135,274],[2100,553,398]),
  ([19,28,39,103,135,293],[2101,554,399,295,281,276,263]),
  ([19,28,56,71,103,135],[2799,478,467,457,288]),
  ([19,28,71,103,135,173],[2902,528,511,294,224,225]),
  ([19,28,71,103,135,241],[2907,532,295]),
  ([19,28,71,103,135,257],[2913,553,545,534,439,296]),
  ([19,30,39,71,103,135],[1833,575,574]),
  ([19,33,39,71,103,135],[1834,588,586,274]),
  ([19,35,39,71,103,135],[1836,673,594,273,227]),
  ([19,35,49,71,103,135],[2435,669,638,625,615,228]),
  ([19,35,71,86,103,135],[2865,660,236]),
  ([19,35,71,103,135],[2918,290,672,238,234,682,231,677,239,235,232,240,233,237,229,230]),
  ([19,39,44,71,103,135],[2216,1832,760,747,737,273]),
  ([19,39,49,58,71,92],[2256,1656,902,812,808,283,258,256,243])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b13ok : f5b13.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b14 : Array Row := #[
  ([19,39,49,65,103,135],[2288,1342,224,241]),
  ([19,39,49,71,92,173],[2356,1752,1297,1187,893,225,252,241]),
  ([19,39,49,71,92,182],[2363,1759,1300,1197,253]),
  ([19,39,49,71,92,351],[2372,1769,1307,1223,881,254]),
  ([19,39,49,71,92,371],[2373,1771,1309,1224,886,255]),
  ([19,39,49,71,96,135],[2400,1800,1324,1123,942,249]),
  ([19,39,49,71,97,135],[2406,1806,1329,1124,951]),
  ([19,39,49,71,99,135],[2412,1814,1333,1125,962,250]),
  ([19,39,49,71,103,131],[2425,1825,1338,0,1069,985,264]),
  ([19,39,49,71,103,135],[2436,1835,1343,1126,986]),
  ([19,39,49,71,103,147],[2444,1845,1347,1161,986]),
  ([19,39,49,71,103,351],[2459,1853,1357,1225,972]),
  ([19,39,49,71,103,365],[2460,1854,1358,1226,973,226,251]),
  ([19,39,49,71,103,371],[2461,1855,1359,1227,974]),
  ([19,39,49,71,103,386],[2463,1856,1361,1228,976]),
  ([19,39,49,71,111,135],[2484,1885,1380,1126,999]),
  ([19,39,49,71,131],[0,2525,284,1053,1925,259,1049,1419,246,1057,0,1254,244,1088,222,124,285,265,245,257,260,247]),
  ([19,39,49,71,131,135],[2504,1904,1399,1145,0,1089,266,249]),
  ([19,39,49,71,131,162],[2512,1912,1409,1175,267]),
  ([19,39,49,71,135,162],[2541,1941,1461,1176,268,242]),
  ([19,39,49,71,135,309],[2570,1961,1497,1215,972]),
  ([19,39,49,71,135,317],[2571,1962,1499,1221,994]),
  ([19,39,49,71,135,319],[2572,1963,1500,1224,996]),
  ([19,39,49,71,135,323],[2573,1964,1501,1227,998]),
  ([19,39,49,71,135,331],[2575,1966,1503,1234,1002]),
  ([19,39,49,71,135,361],[2577,1968,1505,1249,1102,269]),
  ([19,39,49,71,135,378],[2578,1969,1508,1256,1105,270,248]),
  ([19,39,49,71,162,371],[2619,2018,1592,1160,271]),
  ([19,39,49,71,323,371],[2635,2034,1619,999,1161]),
  ([19,39,49,86,135,162],[2667,1283,228,245]),
  ([19,39,49,92,135,274],[2679,2077,1500,1309,881]),
  ([19,39,49,92,135,378],[2680,2079,5,1535,1319,1290,287,282,254,248])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b14ok : f5b14.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b15 : Array Row := #[
  ([19,39,49,103,135,274],[2706,2102,1501,1359,972]),
  ([19,39,49,103,135,280],[2707,1363]),
  ([19,39,49,103,135,293],[2708,2103,1517,1366,1265,288,263]),
  ([19,39,49,103,135,378],[2709,2104,5,1536,1375,1341,248]),
  ([19,39,49,103,274,371],[2730,2129,1619,986,1347]),
  ([19,39,49,135,156,162],[2751,2151,1578,248]),
  ([19,39,49,135,162,274],[2760,2158,1592,1109,246]),
  ([19,39,49,135,274,323],[2770,2168,1619,1126,1380]),
  ([19,39,49,135,378],[5,2771,286,1493,2170,279,1489,5,1631,255,1550,1433,248,1449,223,252,248,253,248,248]),
  ([19,39,58,86,103,135],[2848,2058,292,229,269,256]),
  ([19,39,71,86,92,135],[2863,1724,1714,230,270,256]),
  ([19,39,71,86,103,371],[2869,2062,1727,1717,231,271]),
  ([19,39,71,86,135,162],[2870,1725,233,257]),
  ([19,39,71,86,135,323],[2871,1727,234]),
  ([19,39,71,92,135,250],[2883,2077,1963,1771,881,279]),
  ([19,39,71,92,135,343],[2885,2083,1998,1792,1732,291,282]),
  ([19,39,71,103,135,247],[2913,2100,1957,1851,733]),
  ([19,39,71,103,135,250],[2914,2102,1964,1855,972]),
  ([19,39,71,103,135,252],[2917,1858]),
  ([19,39,71,103,135,260],[2919,2108,1974,1862,1636,277]),
  ([19,39,71,103,135,289],[2920,2112,1982,1869,1702,258]),
  ([19,39,71,103,135,293],[2921,1871,278,263]),
  ([19,39,71,103,135,343],[2922,2114,1999,1878,1820]),
  ([19,39,71,103,250,371],[2940,2129,2034,986,1845]),
  ([19,39,71,135,162,250],[2962,2158,2018,1109,259]),
  ([19,39,71,135,250,323],[2973,2168,2034,1126,1885]),
  ([19,39,83,86,103,135],[2987,2051,263]),
  ([19,39,86,103,135,162],[2996,2060,237,264]),
  ([19,39,86,103,135,274],[2998,2062,238]),
  ([19,39,86,135,162],[3001,293,2063,2068,271,2064,240,227,236,265,266,267]),
  ([19,39,103,135,250,274],[3011,2168,2129,1343,1835]),
  ([19,39,103,135,293],[3012,296,2107,280,2133,275,2118,263,294,263,272,263,263])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b15ok : f5b15.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b16 : Array Row := #[
  ([19,49,54,71,103,135],[2787,2436,2239,2238,2236]),
  ([19,49,71,92,135,257],[2883,2679,2572,2373,2234,286]),
  ([19,49,71,92,135,336],[2884,2682,2597,2391,2330,291,287]),
  ([19,49,71,103,135,241],[2908,2701,2563,2454,972]),
  ([19,49,71,103,135,257],[2914,2706,2573,2461,2235]),
  ([19,49,71,103,135,285],[2915,2711,2581,2468,2301,292,283]),
  ([19,49,71,103,135,336],[2916,2713,2598,2477,2419]),
  ([19,49,71,103,257,371],[2940,2730,2635,2236,2444]),
  ([19,49,71,135,162,257],[2962,2760,2619,2237,293,284]),
  ([19,49,71,135,257,323],[2973,2770,2635,2238,2484]),
  ([19,49,103,135,257,274],[3011,2770,2730,2239,2436]),
  ([19,71,86,103,135,257],[2998,2871,2869,2786,293]),
  ([19,71,103,135,250,257],[3011,2973,2940,2436,2787]),
  ([20,28,39,71,103,135],[1833,517,382,302]),
  ([20,39,49,71,92,135],[1741,921,300]),
  ([20,39,49,71,96,135],[1800,942,300]),
  ([20,39,49,71,103,371],[1855,974]),
  ([20,39,49,71,135,162],[1941,1463,1176,301,298]),
  ([20,39,49,135,156,162],[2151,1578,299]),
  ([20,39,71,86,103,135],[1718,297,301]),
  ([20,39,71,103,135,250],[1855,972]),
  ([21,39,49,71,92,135],[1291,1123,304]),
  ([21,39,49,71,135,162],[1461,303]),
  ([21,39,49,71,135,323],[1501,998]),
  ([21,39,49,103,135,274],[1501,972]),
  ([22,28,39,71,103,135],[1834,520,315]),
  ([22,28,39,71,135,162],[1940,542,316,305]),
  ([22,39,49,71,92,135],[1741,1125,922,311]),
  ([22,39,49,71,103,131],[1825,97,1069]),
  ([22,39,49,71,131],[0,1055,1925,313,1049,242,1061,0,1090,305,317,312,314,309]),
  ([22,39,49,71,131,135],[1904,1146,0,1091,311]),
  ([22,39,49,71,131,162],[1912])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b16ok : f5b16.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b17 : Array Row := #[
  ([22,39,49,71,135,162],[1941,308]),
  ([22,39,49,71,135,323],[1964,998]),
  ([22,39,49,135,156,162],[2151,1579,310]),
  ([22,39,71,86,103,135],[306]),
  ([22,39,71,86,135,162],[268,307,312]),
  ([22,39,71,103,135,250],[1964,972]),
  ([22,39,71,135,162,250],[1109,313]),
  ([23,39,49,71,103,135],[1835]),
  ([23,39,49,71,135,162],[1941,318]),
  ([24,28,39,71,103,135],[1836,516,383,346,319]),
  ([24,28,49,71,103,135],[2435,518,417,350,320]),
  ([24,28,56,71,103,135],[2800,478,468,458,352,321]),
  ([24,28,71,103,135],[2918,353,515,330,327,538,324,524,331,328,325,332,326,329,322,323]),
  ([24,39,49,56,135,162],[799,321,334]),
  ([24,39,49,58,103,135],[1342,322,342,335]),
  ([24,39,49,71,92,135],[2341,1742,1291,1127,923,323,343,335]),
  ([24,39,49,71,103,377],[2462,1863,1360,1229,975,324,344]),
  ([24,39,49,71,135,162],[2541,1942,1461,1177,326,349,345,336]),
  ([24,39,49,71,135,326],[2574,1975,1502,1229,1000,327]),
  ([24,39,49,103,135,162],[1351,329,337]),
  ([24,39,49,103,135,274],[2706,2108,1502,1360,972,330]),
  ([24,39,49,135,162],[351,347,1597,344,1468,332,319,320,338,339,340]),
  ([24,39,71,86,103,135],[2866,1719,333,345]),
  ([24,39,71,103,135,260],[2919,2108,1975,1863,1636,347]),
  ([24,49,71,83,103,135],[2856,2314,348,349]),
  ([24,49,71,103,135,257],[2919,2706,2574,2462,2235,351]),
  ([25,39,49,71,103,135],[987,354,355]),
  ([26,39,49,71,103,135],[1343,1128,356]),
  ([27,39,49,71,103,135],[1128,357]),
  ([27,39,49,71,135,162],[341,358,359]),
  ([28,35,49,71,103,135],[2431,669,640,626,616,518,418]),
  ([28,39,44,71,103,135],[2212,1832,762,748,738,516,384])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b17ok : f5b17.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b18 : Array Row := #[
  ([28,39,49,58,71,92],[2255,1656,903,813,809,441,411,377,361]),
  ([28,39,49,71,92,173],[2353,1752,1298,1188,443,376,367]),
  ([28,39,49,71,92,182],[2362,1759,1301,1198,444,410,368]),
  ([28,39,49,71,92,351],[2368,1769,1312,1230,881,446,369]),
  ([28,39,49,71,92,386],[2371,1772,1313,1231,888,447,370]),
  ([28,39,49,71,96,135],[2399,1800,1325,1129,943,448,413,379,366]),
  ([28,39,49,71,97,135],[2405,1806,1330,1130,952,449,380]),
  ([28,39,49,71,99,135],[2411,1814,1334,1131,963,450,414]),
  ([28,39,49,71,103,131],[2424,1825,1339,0,1070,988,452]),
  ([28,39,49,71,103,135],[2434,1835,1344,1132,989,453]),
  ([28,39,49,71,103,167],[2446,1847,1352,1182,989,454]),
  ([28,39,49,71,103,351],[2452,1853,1364,1232,972,455]),
  ([28,39,49,71,103,365],[2453,1854,1365,1233,973,456,415]),
  ([28,39,49,71,103,371],[2454,1855,1366,1234,974,457,381]),
  ([28,39,49,71,103,386],[2455,1856,1367,1235,976,459]),
  ([28,39,49,71,116,135],[2486,1887,1381,1132,1003,460]),
  ([28,39,49,71,131],[2524,420,1045,1925,386,1049,0,1420,363,1064,0,1260,362,1093,461,371,405,125,421,222,387,364]),
  ([28,39,49,71,131,135],[2503,1904,1400,1153,0,1094,462,419,385,366]),
  ([28,39,49,71,131,162],[2511,1912,1412,1178,0,1039,463,208,305]),
  ([28,39,49,71,135,196],[2553,1954,1482,1204,464,360]),
  ([28,39,49,71,135,309],[2560,1961,1515,1216,972,465]),
  ([28,39,49,71,135,317],[2562,1962,1516,1222,994,466]),
  ([28,39,49,71,135,323],[2563,1964,1517,1228,998,467]),
  ([28,39,49,71,135,327],[2564,1965,1518,1231,1001,469,425,391]),
  ([28,39,49,71,135,331],[2565,1966,1519,1235,1002,470]),
  ([28,39,49,71,135,361],[2567,1968,1522,1250,1102,471]),
  ([28,39,49,71,135,378],[2568,1969,5,1523,1257,1105,472,126,426,223,392,365]),
  ([28,39,49,71,162,386],[2618,2019,1595,1204,1168,473]),
  ([28,39,49,71,331,386],[2634,2035,1622,1003,1182,474]),
  ([28,39,49,81,103,135],[2648,2049,1344,1269,1266,475]),
  ([28,39,49,92,135,293],[2677,2078,1518,1313,1264,476,429,395]),
  ([28,39,49,92,135,378],[2678,2079,5,1537,1320,1290,477,436,430,402,396,369,365])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b18ok : f5b18.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b19 : Array Row := #[
  ([28,39,49,103,135,274],[2701,2102,1503,1361,972,478]),
  ([28,39,49,103,135,293],[2702,2103,1519,1367,1265,479]),
  ([28,39,49,103,135,378],[2703,2104,5,1538,1376,1341,480,431,397,365]),
  ([28,39,49,103,293,386],[2729,2130,1622,1266,1352,481]),
  ([28,39,49,135,156,162],[2750,2151,1580,1459,1455,482,437,403,365]),
  ([28,39,49,135,162,293],[2759,2160,1595,1482,1267,483,363]),
  ([28,39,49,135,293,331],[2768,2169,1622,1269,1381,484]),
  ([28,39,49,135,378],[2769,435,1485,2170,401,1489,5,1632,370,1552,1433,365,1449,485,372,406,438,367,434,365,404,368,400,365,365]),
  ([28,39,56,71,92,135],[1648,1644,443,376,372]),
  ([28,39,56,71,103,386],[1650,1645,454]),
  ([28,39,56,71,135,162],[1651,319,371]),
  ([28,39,56,71,135,331],[1652,1645,460]),
  ([28,39,56,103,135,293],[2832,1652,1650,1646,475]),
  ([28,39,67,71,103,135],[1838,1692,522,127,382,373]),
  ([28,39,71,92,103,182],[2070,1850,1766,529,492,397]),
  ([28,39,71,92,135,182],[2076,1948,497,494,400]),
  ([28,39,71,92,135,250],[2880,2078,1965,1772,881,499,401]),
  ([28,39,71,92,135,343],[2882,2085,2000,1793,1732,549,500,402]),
  ([28,39,71,92,182],[502,2088,395,1764,2030,391,1765,128,503,504,376,501,404,392,396,373]),
  ([28,39,71,99,135,182],[2093,1949,508,507,375]),
  ([28,39,71,103,135,182],[2098,1950,526,513,375]),
  ([28,39,71,103,135,195],[2099,374,376]),
  ([28,39,71,103,135,247],[2907,2101,1958,1852,733]),
  ([28,39,71,103,135,250],[2908,2103,1966,1856,972]),
  ([28,39,71,103,135,251],[2105,1970]),
  ([28,39,71,103,135,253],[2106,1859]),
  ([28,39,71,103,135,257],[2107,439]),
  ([28,39,71,103,135,260],[2909,2110,1976,1864,1636,440]),
  ([28,39,71,103,135,289],[2910,2115,1983,1870,1702,377]),
  ([28,39,71,103,135,343],[2911,2117,2001,1879,1820,527]),
  ([28,39,71,103,135,371],[2118,528,378,381]),
  ([28,39,71,103,156,182],[2123,2014,525,403,379,381])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b19ok : f5b19.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b20 : Array Row := #[
  ([28,39,71,103,173,182],[2125,2026,380]),
  ([28,39,71,103,182,386],[2127,2031,531]),
  ([28,39,71,103,250,386],[2938,2130,2035,989,1847]),
  ([28,39,71,103,371],[532,2133,399,1871,394,381,129,381,390,381,381]),
  ([28,39,71,135,162,182],[2157,1947,550,539,403,385,388]),
  ([28,39,71,135,162,250],[2960,2160,2019,1954,1109,386]),
  ([28,39,71,135,182,331],[2969,2166,2031,1886,551,544]),
  ([28,39,71,135,250,331],[2971,2169,2035,1132,1887]),
  ([28,39,103,135,182,293],[3007,2166,2127,2048,557,552,395]),
  ([28,39,103,135,250,293],[3009,2169,2130,1344,2049]),
  ([28,49,56,71,92,135],[2247,2243,444,410,406]),
  ([28,49,56,71,103,386],[2249,2244,454]),
  ([28,49,56,71,135,162],[2250,320,405]),
  ([28,49,56,71,135,331],[2251,2244,460]),
  ([28,49,56,103,135,293],[2833,2251,2249,2245,475]),
  ([28,49,65,71,103,135],[2437,2289,523,224,416,407]),
  ([28,49,71,92,103,173],[2669,2447,2360,527,492,431]),
  ([28,49,71,92,135,173],[2675,2547,497,494,434]),
  ([28,49,71,92,135,241],[2880,2677,2564,2371,881,502,435]),
  ([28,49,71,92,135,336],[2884,2684,2599,2392,2330,549,503,436]),
  ([28,49,71,92,173],[499,2686,429,2358,2626,425,2359,225,500,504,410,498,438,426,430,407]),
  ([28,49,71,97,135,173],[2692,2548,506,505,409]),
  ([28,49,71,103,135,173],[2697,2549,526,513,409]),
  ([28,49,71,103,135,195],[2698,408,410]),
  ([28,49,71,103,135,238],[2905,2700,2557,2451,611]),
  ([28,49,71,103,135,241],[2908,2702,2565,2455,972]),
  ([28,49,71,103,135,242],[2704,2569]),
  ([28,49,71,103,135,244],[2705,2458]),
  ([28,49,71,103,135,257],[2914,2708,2575,2463,2235,439]),
  ([28,49,71,103,135,260],[2710,440]),
  ([28,49,71,103,135,285],[2915,2714,2582,2469,2301,411]),
  ([28,49,71,103,135,336],[2916,2716,2600,2478,2419,529])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b20ok : f5b20.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b21 : Array Row := #[
  ([28,49,71,103,135,365],[2717,530,412,415]),
  ([28,49,71,103,156,173],[2722,2613,525,437,413,415]),
  ([28,49,71,103,173,182],[2724,2625,414]),
  ([28,49,71,103,173,386],[2725,2627,531]),
  ([28,49,71,103,241,386],[2938,2729,2634,989,2446]),
  ([28,49,71,103,365],[533,2732,433,2470,428,415,226,415,424,415,415]),
  ([28,49,71,135,162,173],[2756,2546,550,539,437,419,422]),
  ([28,49,71,135,162,241],[2960,2759,2618,2553,1109,420]),
  ([28,49,71,135,173,331],[2967,2764,2627,2485,551,544]),
  ([28,49,71,135,241,331],[2971,2768,2634,1132,2486]),
  ([28,49,103,135,173,293],[3005,2764,2725,2647,557,552,429]),
  ([28,49,103,135,241,293],[3009,2768,2729,1344,2648]),
  ([28,56,58,71,103,135],[2801,2792,491,322,478,471,455,441]),
  ([28,56,71,83,103,135],[2818,439]),
  ([28,56,71,86,103,135],[2819,440]),
  ([28,56,71,91,103,135],[2820]),
  ([28,56,71,92,103,135],[2821,2803,510,492,480,465,455]),
  ([28,56,71,92,135],[2822,476,2794,2808,469,2795,447,323,493,504,445,494,485,472,477,441,446]),
  ([28,56,71,103,120,135],[2823]),
  ([28,56,71,103,125,135],[2824]),
  ([28,56,71,103,130,135],[2825]),
  ([28,56,71,103,135,140],[2826]),
  ([28,56,71,103,135,156],[2827,525,354,482,448]),
  ([28,56,71,103,135,162],[2828,329,357,452]),
  ([28,56,71,103,135,173],[2829,513,443,449]),
  ([28,56,71,103,135,182],[2830,513,444,450]),
  ([28,56,71,103,135,195],[2831,442,445,451]),
  ([28,56,71,103,135,241],[2832]),
  ([28,56,71,103,135,250],[2833]),
  ([28,56,71,103,135,293],[19,2807,2804,2793,331,483,475]),
  ([28,56,71,103,135,331],[2835,2805,460]),
  ([28,56,71,103,135,386],[2836,2809,531,447,454])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b21ok : f5b21.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b22 : Array Row := #[
  ([28,56,71,103,386],[2837,481,2804,2811,474,2805,454,325,454,473,454,454]),
  ([28,56,71,135,162],[2838,483,2806,473,464,332,321,326,539,358,482,461,462,463]),
  ([28,56,71,135,331],[2839,484,2807,2811,474,2809,460,328,544,460,460,460]),
  ([28,56,103,135,293],[19,2839,484,2835,19,2837,481,2836,2814,475,2815,552,475,476,475,475]),
  ([28,71,103,135,173,182],[3003,2966,497,513]),
  ([28,71,103,135,173,195],[3004,488,498,505]),
  ([28,71,103,135,173,250],[3005,2967,499]),
  ([28,71,103,135,182,195],[3006,489,501,507]),
  ([28,71,103,135,182,241],[3007,2969,502]),
  ([28,71,103,135,195],[3008,552,2904,544,531,539,525,487,486,490,504,492,494,509]),
  ([28,71,103,135,241,250],[3009,2971,2938,1835,2434]),
  ([28,71,103,135,257],[3012,554,2921,546,535,439,540,439,495,439,439]),
  ([28,71,103,135,260],[3013,556,2924,548,537,440,541,440,496,440,440]),
  ([28,71,103,173,182],[3016,557,2934,2981,551,2935,550,506,508]),
  ([29,39,49,71,92,135],[2340,924,562,559]),
  ([29,39,49,71,92,182],[2362,375,563,560]),
  ([29,39,49,71,99,135],[2411,963,564]),
  ([29,39,49,71,103,386],[2455,976]),
  ([29,39,49,71,135,162],[2540,1466,1179,558]),
  ([29,49,56,71,103,135],[453]),
  ([29,49,71,103,135,173],[562]),
  ([29,49,71,103,135,195],[513,561,563]),
  ([29,49,71,103,135,241],[2455,972]),
  ([29,49,71,103,173,182],[526,564]),
  ([30,39,49,71,92,135],[1741,924,571,568]),
  ([30,39,49,71,92,173],[409,1752,572,569]),
  ([30,39,49,71,97,135],[1806,952,573]),
  ([30,39,49,71,103,386],[1856,976]),
  ([30,39,49,71,135,162],[1941,1467,1179,567]),
  ([30,39,56,71,103,135],[453]),
  ([30,39,71,103,135,182],[571]),
  ([30,39,71,103,135,195],[513,570,572])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b22ok : f5b22.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b23 : Array Row := #[
  ([30,39,71,103,135,250],[1856,972]),
  ([30,39,71,103,173,182],[526,573]),
  ([31,39,49,71,92,135],[2340,1130,925,579,578,577]),
  ([31,39,49,71,135,162],[2540,1110,576]),
  ([31,39,49,71,135,331],[2565,1002]),
  ([31,39,71,103,135,182],[1950,582,578]),
  ([31,49,56,71,103,135],[453]),
  ([31,49,71,103,135,173],[2549,582,579]),
  ([31,49,71,103,135,241],[2565,972]),
  ([32,39,49,71,103,135],[2434]),
  ([33,39,49,71,92,135],[1741,1131,926,587,585,584]),
  ([33,39,49,71,135,162],[1941,1110,583]),
  ([33,39,49,71,135,331],[1966,1002]),
  ([33,39,56,71,103,135],[453]),
  ([33,39,71,103,135,182],[1950,589,585]),
  ([33,39,71,103,135,250],[1966,972]),
  ([33,49,71,103,135,173],[2549,589,587]),
  ([34,39,49,71,103,135],[1835]),
  ([35,39,49,71,92,135],[2340,1742,1292,1133,927,648,601,593,591]),
  ([35,39,49,71,103,390],[2456,1865,1368,1237,977,650,612]),
  ([35,39,49,71,135,162],[2540,1942,1465,1180,1110,651,634,227,590]),
  ([35,39,49,71,135,340],[2566,1977,1520,1237,1004,652,618]),
  ([35,39,49,103,135,293],[2702,2110,1520,1368,1265,653,633]),
  ([35,39,56,71,103,135],[1649]),
  ([35,39,71,103,135,182],[2098,1951,679,668,592,593]),
  ([35,39,71,103,135,260],[2909,2110,1977,1865,1636,647]),
  ([35,49,56,71,103,135],[453,2248]),
  ([35,49,58,71,103,135],[2437,675,229,638,629,613,596]),
  ([35,49,60,71,103,135],[675,613,597]),
  ([35,49,71,83,103,135],[2856,2315,595,634]),
  ([35,49,71,86,92,135],[2325,659,635,597]),
  ([35,49,71,86,103,135],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b23ok : f5b23.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b24 : Array Row := #[
  ([35,49,71,86,103,390],[2666,2326,612]),
  ([35,49,71,86,135,162],[236,599]),
  ([35,49,71,86,135,340],[2326,618]),
  ([35,49,71,91,103,135],[]),
  ([35,49,71,92,103,135],[2440,676,661,641,623,613]),
  ([35,49,71,92,135],[663,636,2601,627,2344,604,230,664,665,602,662,646,630,637,596,603]),
  ([35,49,71,103,120,135],[2422]),
  ([35,49,71,103,125,135],[]),
  ([35,49,71,103,135,140],[]),
  ([35,49,71,103,135,156],[678,297,643,605]),
  ([35,49,71,103,135,162],[237,306,609]),
  ([35,49,71,103,135,173],[2697,2550,679,668,601,606]),
  ([35,49,71,103,135,182],[598,602,607]),
  ([35,49,71,103,135,193],[608]),
  ([35,49,71,103,135,198],[610]),
  ([35,49,71,103,135,241],[2909,2702,2566,2456,972]),
  ([35,49,71,103,135,260],[518,2710,647]),
  ([35,49,71,103,135,293],[2924,181,2471,239,644,633]),
  ([35,49,71,103,135,340],[2479,618]),
  ([35,49,71,103,135,390],[2718,2608,680,604,612]),
  ([35,49,71,103,390],[418,681,2733,642,2471,2642,632,2479,612,232,612,631,612,612]),
  ([35,49,71,135,162],[684,644,631,622,240,228,233,683,307,643,619,620,621]),
  ([35,49,71,135,340],[686,645,2642,632,2608,618,235,685,618,618,618]),
  ([35,49,83,86,103,135],[2988,2651,633]),
  ([35,49,86,103,135,293],[2999,2666,633]),
  ([35,49,103,135,293],[3013,688,2710,645,2733,642,2718,633,687,633,636,633,633]),
  ([35,56,71,86,103,135],[2819,647]),
  ([35,56,71,103,135],[2834,653,2802,652,650,333,668,651,648]),
  ([35,71,86,103,135,182],[655,658,659]),
  ([35,71,86,103,135,260],[2999,647]),
  ([35,71,103,135,182],[687,685,680,667,683,678,656,654,657,665,661,662,666]),
  ([35,71,103,135,260],[3013,688,2924,686,681,647,684,647,663,647,647])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b24ok : f5b24.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b25 : Array Row := #[
  ([36,39,49,71,103,135],[2434,990]),
  ([36,49,71,86,103,135],[611]),
  ([36,49,71,103,135],[695,696,689]),
  ([36,49,71,103,135,156],[697,691]),
  ([36,49,71,103,135,182],[690,692]),
  ([36,49,71,103,135,193],[693]),
  ([37,39,49,71,103,135],[2434,1134]),
  ([37,39,49,71,135,162],[2540,1110,698]),
  ([37,49,71,86,103,135],[611]),
  ([37,49,71,103,125,135],[]),
  ([37,49,71,103,135],[710,712,708,699]),
  ([37,49,71,103,135,162],[700]),
  ([37,49,71,103,135,198],[701]),
  ([37,49,71,135,162],[709,713,711,703,704,705]),
  ([37,49,71,135,162,198],[706,707]),
  ([39,40,49,71,103,135],[]),
  ([39,41,49,71,103,135],[]),
  ([39,42,49,71,103,135],[611,1134]),
  ([39,43,49,71,103,135],[]),
  ([39,44,49,71,92,135],[2341,2191,2188,1741,1292,1135,929,724,717]),
  ([39,44,49,71,103,394],[2464,2193,1857,1369,1239,978,734]),
  ([39,44,49,71,135,162],[2541,2194,151,1941,1465,1181,1110,757,716]),
  ([39,44,49,71,135,347],[2576,2195,1967,1521,1239,1007,740]),
  ([39,44,49,103,135,293],[2708,2196,2103,1521,1369,1265,755]),
  ([39,44,56,71,103,135],[453,1649]),
  ([39,44,58,71,103,135],[2218,152,1838,760,751,735,718]),
  ([39,44,59,71,103,135],[2218,735,719]),
  ([39,44,71,83,92,135],[2202,1708,756,719]),
  ([39,44,71,83,103,135],[]),
  ([39,44,71,83,103,394],[2054,1709,734]),
  ([39,44,71,83,135,162],[159,721]),
  ([39,44,71,83,135,347],[1709,740])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b25ok : f5b25.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b26 : Array Row := #[
  ([39,44,71,86,103,135],[2866,595,1720,757]),
  ([39,44,71,91,103,135],[]),
  ([39,44,71,92,103,135],[2219,2204,1841,763,745,735]),
  ([39,44,71,92,135],[2206,153,2207,2208,723,2205,758,2004,749,1745,726,768,752,759,718,725]),
  ([39,44,71,103,120,135],[]),
  ([39,44,71,103,125,135],[1823]),
  ([39,44,71,103,135,140],[]),
  ([39,44,71,103,135,156],[2221,203,765,727]),
  ([39,44,71,103,135,162],[160,214,731]),
  ([39,44,71,103,135,173],[720,723,728]),
  ([39,44,71,103,135,182],[2222,2211,2098,1952,724,730]),
  ([39,44,71,103,135,190],[729]),
  ([39,44,71,103,135,197],[732]),
  ([39,44,71,103,135,250],[2914,2103,1967,1857,972]),
  ([39,44,71,103,135,257],[516,2190,2107]),
  ([39,44,71,103,135,293],[2921,162,273,1872,766,755]),
  ([39,44,71,103,135,347],[1880,740]),
  ([39,44,71,103,135,394],[2223,2119,2009,726,734]),
  ([39,44,71,103,394],[384,2224,155,734,2134,764,1872,2043,754,1880,734,753,734,734]),
  ([39,44,71,135,162],[2227,163,130,156,2226,215,766,753,744,765,741,742,743]),
  ([39,44,71,135,347],[2229,158,2228,740,767,2043,754,2009,740,740,740]),
  ([39,44,83,86,103,135],[2987,2052,755]),
  ([39,44,83,103,135,293],[2992,2054,755]),
  ([39,44,103,135,293],[3012,2107,2231,2230,755,767,2134,764,2119,755,758,755,755]),
  ([39,45,49,71,103,135],[1835,991]),
  ([39,45,71,83,103,135],[733]),
  ([39,45,71,103,135],[775,776,769]),
  ([39,45,71,103,135,156],[777,771]),
  ([39,45,71,103,135,173],[770,772]),
  ([39,45,71,103,135,190],[773]),
  ([39,46,49,71,103,135],[733,1136]),
  ([39,47,49,71,103,135],[1835,1136])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b26ok : f5b26.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b27 : Array Row := #[
  ([39,47,49,71,135,162],[1941,1110,778]),
  ([39,47,71,83,103,135],[733]),
  ([39,47,71,103,120,135],[]),
  ([39,47,71,103,135],[2232,790,788,779]),
  ([39,47,71,103,135,162],[780]),
  ([39,47,71,103,135,197],[781]),
  ([39,47,71,135,162],[2233,789,791,783,784,785]),
  ([39,47,71,135,162,197],[786,787]),
  ([39,49,50,71,103,135],[]),
  ([39,49,51,71,103,135],[]),
  ([39,49,52,71,103,135],[]),
  ([39,49,54,71,103,135],[439,2436,733]),
  ([39,49,55,71,103,135],[440,611,1837]),
  ([39,49,56,58,71,92],[441,2241,1642,876,335,795]),
  ([39,49,56,69,103,135],[442,794]),
  ([39,49,56,71,92,173],[443,895,800]),
  ([39,49,56,71,92,182],[444,895,801]),
  ([39,49,56,71,92,195],[445,802,794]),
  ([39,49,56,71,92,351],[446,881,803]),
  ([39,49,56,71,96,135],[448,937,798]),
  ([39,49,56,71,97,135],[449]),
  ([39,49,56,71,99,135],[450]),
  ([39,49,56,71,101,135],[451]),
  ([39,49,56,71,103,131],[452,337,120,1010]),
  ([39,49,56,71,103,351],[455,972]),
  ([39,49,56,71,103,365],[456,973]),
  ([39,49,56,71,103,371],[457,974]),
  ([39,49,56,71,103,377],[458,975,799]),
  ([39,49,56,71,103,386],[459,976]),
  ([39,49,56,71,131],[461,371,405,2240,2242,1641,1643,338,334,336,877,0,1037,796]),
  ([39,49,56,71,131,135],[462,339,55,1038,798]),
  ([39,49,56,71,131,162],[463,340,359,1042])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b27ok : f5b27.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b28 : Array Row := #[
  ([39,49,56,71,135,309],[465,972]),
  ([39,49,56,71,135,317],[466,994]),
  ([39,49,56,71,135,323],[467,998]),
  ([39,49,56,71,135,326],[468,1000]),
  ([39,49,56,71,135,331],[470,1002]),
  ([39,49,56,71,135,361],[471,342,1102]),
  ([39,49,56,71,135,378],[472,2246,1647,343,1287,1203,1105,797]),
  ([39,49,56,92,135,378],[477,2252,1653,5,1396,1303,1290,803,797]),
  ([39,49,56,103,135,274],[478,972]),
  ([39,49,56,103,135,293],[479,2245,1646,1265]),
  ([39,49,56,103,135,378],[480,121,1397,1355,1341,797]),
  ([39,49,56,135,156,162],[482,1572,355,797]),
  ([39,49,56,135,378],[485,372,406,800,797,801,797,56,1617,802,1481,1433,797,1449,797]),
  ([39,49,57,71,103,135],[]),
  ([39,49,58,71,83,92],[2308,164,1706,718,874]),
  ([39,49,58,71,86,92],[2323,596,1713,256,875]),
  ([39,49,58,71,92,120],[2335,1731,1006]),
  ([39,49,58,71,92,125],[2336,1737,1009]),
  ([39,49,58,71,92,140],[2347,1748,1155]),
  ([39,49,58,71,92,156],[2348,1749,1167]),
  ([39,49,58,71,92,162],[2349,1750,1169]),
  ([39,49,58,71,92,173],[2357,1754,1297,1189,819]),
  ([39,49,58,71,92,182],[2364,1763,1300,1199,820]),
  ([39,49,58,71,92,274],[2374,1775,1205]),
  ([39,49,58,71,92,285],[14,2253,1776,1304,1206,871]),
  ([39,49,58,71,92,289],[2376,9,1654,1305,1207,873]),
  ([39,49,58,71,92,309],[2377,1779,1212]),
  ([39,49,58,71,92,336],[2378,2254,1780,1663,1236,822]),
  ([39,49,58,71,92,343],[2379,2262,1781,1655,1238,823]),
  ([39,49,58,71,92,348],[2380,2263,1782,1664,1306,1,878,824,805]),
  ([39,49,58,71,92,351],[2381,1783,1307,1241,881,825]),
  ([39,49,58,71,92,361],[2382,1784,1242])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b28ok : f5b28.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b29 : Array Row := #[
  ([39,49,58,71,92,378],[2383,2264,1785,1665,1243,811]),
  ([39,49,58,71,93,103],[2394,1795,980,804]),
  ([39,49,58,71,94,103],[2395,1798,981,804]),
  ([39,49,58,71,96,135],[2401,1802,1324,1138,938,818,804]),
  ([39,49,58,71,97,135],[2407,1808,1329,1139,948,804]),
  ([39,49,58,71,99,135],[2413,1816,1333,1140,959,804]),
  ([39,49,58,71,103,131],[2426,1827,1338,0,1083,979,804]),
  ([39,49,58,71,103,135],[2438,1839,1343,1141,982,804]),
  ([39,49,58,71,103,348],[2465,1866,1356,1,1242,968,805]),
  ([39,49,58,71,103,351],[2466,1867,1357,1244,972]),
  ([39,49,58,71,103,365],[2467,1868,1358,1248,973]),
  ([39,49,58,71,103,371],[2468,1869,1359,1249,974]),
  ([39,49,58,71,103,386],[2469,1870,1361,1250,976]),
  ([39,49,58,71,131],[0,2526,1062,2259,2260,0,1927,1063,1660,1661,1419,815,1057,1240,810,1073,816]),
  ([39,49,58,71,131,135],[2505,1906,1399,1137,1076,818]),
  ([39,49,58,71,131,162],[2513,1914,1409,1169]),
  ([39,49,58,71,135,139],[2534,1935,1430,1154,1141,805]),
  ([39,49,58,71,135,162],[2542,1943,1461,1172,805]),
  ([39,49,58,71,135,309],[2579,1980,1497,1213,972]),
  ([39,49,58,71,135,317],[2580,1981,1499,1219,994]),
  ([39,49,58,71,135,323],[2581,1982,1501,1225,998]),
  ([39,49,58,71,135,331],[2582,1983,1503,1232,1002]),
  ([39,49,58,71,135,348],[2583,1984,1504,1241,1014,805]),
  ([39,49,58,71,135,361],[2584,1985,1505,1244,1102]),
  ([39,49,58,71,135,378],[2586,1987,1508,1245,1105,817]),
  ([39,49,58,71,162,351],[2620,2021,1590,1109]),
  ([39,49,58,71,348],[1,2636,1206,2261,805,1,2037,1207,1662,805,1620,821,1205,1011,805,1073,805]),
  ([39,49,58,71,351,361],[2637,2038,1621,1141,1154]),
  ([39,49,58,92,103,274],[2670,2071,1356,804]),
  ([39,49,58,92,103,378],[2671,2269,2072,1670,1370,811]),
  ([39,49,58,92,135,274],[2681,2082,1504,1307,881,804]),
  ([39,49,58,92,135,378],[2683,2271,2084,1672,5,1543,1315,1290,825,817,811])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b29ok : f5b29.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b30 : Array Row := #[
  ([39,49,58,92,274],[2689,1304,2265,2266,804,2090,1305,1666,1667,804,1620,821,1306,804,804]),
  ([39,49,58,92,378],[2690,1310,2267,2272,822,2268,811,2091,1311,1668,1673,823,1669,811,1626,824,1314,811,811]),
  ([39,49,58,103,135,274],[2711,2112,1505,1357,972,812]),
  ([39,49,58,103,135,293],[2792,2714,2115,1522,1364,1265,813]),
  ([39,49,58,103,135,378],[2715,2116,5,1548,1371,1341,814,817]),
  ([39,49,58,103,274,351],[2731,2132,1621,982,1343]),
  ([39,49,58,135,156,162],[2752,2153,1573,817]),
  ([39,49,58,135,162,274],[2761,2162,1590,1109,815]),
  ([39,49,58,135,274,361],[2772,2173,1621,1141,1430]),
  ([39,49,58,135,378],[5,2773,1513,2270,819,817,5,2174,1514,1671,820,817,1627,825,1544,1433,817,1449,817]),
  ([39,49,59,71,83,92],[2308,719]),
  ([39,49,59,71,92],[2375,904,2273,2274,907,1674,804,911,827]),
  ([39,49,59,71,92,103],[2327,980]),
  ([39,49,59,71,92,135],[2342,913,828]),
  ([39,49,59,71,103,351],[2466,972]),
  ([39,49,59,71,135,162],[2542,1462,1172,826]),
  ([39,49,60,71,86,92],[597,1713]),
  ([39,49,60,71,92],[905,2275,1778,906,1675,1676,804,912,830]),
  ([39,49,60,71,92,103],[1728,981]),
  ([39,49,60,71,92,135],[1743,913,831]),
  ([39,49,60,71,103,351],[1867,972]),
  ([39,49,60,71,135,162],[1943,1463,1172,829]),
  ([39,49,61,71,103,135],[982,832]),
  ([39,49,62,71,92,135],[1291,1138,804,834]),
  ([39,49,62,71,135,162],[1461,833]),
  ([39,49,62,71,135,361],[1505,1102]),
  ([39,49,62,103,135,274],[1505,972]),
  ([39,49,63,71,103,135],[]),
  ([39,49,64,71,103,135],[]),
  ([39,49,65,71,92],[407,2375,904,2277,2279,838,2276,2278,1786,909,1677,241,1678,839,1251,837,917,840]),
  ([39,49,65,71,92,103],[2327,2280,1729,983]),
  ([39,49,65,71,92,135],[2342,2281,1744,1291,1142,804,918,841])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b30ok : f5b30.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b31 : Array Row := #[
  ([39,49,65,71,92,173],[2357,2282,1755,1297,1190,843]),
  ([39,49,65,71,97,135],[2407,2283,1809,1329,1143,950,842,835]),
  ([39,49,65,71,103,365],[2467,2285,1873,1358,1252,973]),
  ([39,49,65,71,135,162],[2542,2286,1944,1461,1174,836]),
  ([39,49,65,71,135,369],[2585,2287,1988,1506,1252,1103]),
  ([39,49,65,83,103,135],[2053,720,838]),
  ([39,49,65,103,135,274],[2711,2113,1506,1358,972,839]),
  ([39,49,66,71,103,135],[1343,1144]),
  ([39,49,67,71,92],[373,2385,908,2290,131,2291,1778,906,1680,1682,847,1679,1681,848,1254,846,920,849]),
  ([39,49,67,71,92,103],[2328,1728,1683,985]),
  ([39,49,67,71,92,135],[2343,1743,1684,1291,1145,804,921,850]),
  ([39,49,67,71,92,182],[2365,1763,1685,1300,1200,852]),
  ([39,49,67,71,99,135],[2414,1816,1686,1333,1146,962,851,844]),
  ([39,49,67,71,103,371],[2472,1869,1688,1359,1255,974]),
  ([39,49,67,71,135,162],[2543,1943,1689,1461,1176,845]),
  ([39,49,67,71,135,375],[2587,1986,1690,1507,1255,1104]),
  ([39,49,67,86,103,135],[2665,598,847]),
  ([39,49,67,103,135,274],[2712,2112,1507,1359,972,848]),
  ([39,49,68,71,103,135],[1343,1147]),
  ([39,49,69,71,103,135],[486,2439,2292,1840,1693,1343,1152,987,865,853]),
  ([39,49,69,103,135],[487,374,408,2293,1694,866,864,854,855,856]),
  ([39,49,69,103,135,173],[488,570,857,860]),
  ([39,49,69,103,135,182],[489,561,858,861]),
  ([39,49,69,103,135,195],[490,859,862]),
  ([39,49,71,72,103,135],[1262]),
  ([39,49,71,73,103,135],[1263]),
  ([39,49,71,74,103,135],[1109]),
  ([39,49,71,74,135,162],[868]),
  ([39,49,71,75,103,135],[1109]),
  ([39,49,71,75,135,162],[869]),
  ([39,49,71,76,103,135],[2645,611,1840,990,870]),
  ([39,49,71,77,103,135],[2438,871])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b31ok : f5b31.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b32 : Array Row := #[
  ([39,49,71,78,103,135],[2439,2046,733,991,872]),
  ([39,49,71,79,103,135],[1839,873]),
  ([39,49,71,81,103,135],[2793,171,611,263,733,1344,1267,1110]),
  ([39,49,71,83,92,173],[723,1276,838,871]),
  ([39,49,71,83,92,182],[2307,2050,724,1277,872]),
  ([39,49,71,83,92,351],[725,1278,881]),
  ([39,49,71,83,96,135],[2310,727,1273]),
  ([39,49,71,83,97,135],[728]),
  ([39,49,71,83,98,135],[729]),
  ([39,49,71,83,99,135],[2311,730,1274]),
  ([39,49,71,83,103,131],[172,731,95,1040]),
  ([39,49,71,83,103,132],[732]),
  ([39,49,71,83,103,351],[735,972]),
  ([39,49,71,83,103,365],[2312,736,1275,973]),
  ([39,49,71,83,103,371],[2051,737,974]),
  ([39,49,71,83,103,386],[738,976]),
  ([39,49,71,83,103,394],[2052,739,978]),
  ([39,49,71,83,131],[2240,173,135,165,2317,1270,741,716,721,877,1707,1271,805,1033]),
  ([39,49,71,83,131,135],[174,2316,742,1273,826,1034]),
  ([39,49,71,83,131,162],[175,216,743,868,1040]),
  ([39,49,71,83,135,309],[745,972]),
  ([39,49,71,83,135,317],[746,994]),
  ([39,49,71,83,135,323],[747,998]),
  ([39,49,71,83,135,331],[748,1002]),
  ([39,49,71,83,135,347],[750,1007]),
  ([39,49,71,83,135,361],[177,751,1102]),
  ([39,49,71,83,135,378],[178,2321,752,1272,1105]),
  ([39,49,71,84,103,135],[774]),
  ([39,49,71,86,92,173],[2649,601,1712,1284,870]),
  ([39,49,71,86,92,182],[602,1285,847,873]),
  ([39,49,71,86,92,351],[603,1286,881]),
  ([39,49,71,86,96,135],[605,1715,1281])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b32ok : f5b32.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b33 : Array Row := #[
  ([39,49,71,86,97,135],[606,1716,1282]),
  ([39,49,71,86,99,135],[607]),
  ([39,49,71,86,100,135],[608]),
  ([39,49,71,86,103,131],[609,264,118,1041]),
  ([39,49,71,86,103,133],[610]),
  ([39,49,71,86,103,351],[613,972]),
  ([39,49,71,86,103,365],[2650,614,973]),
  ([39,49,71,86,103,371],[615,1717,1283,974]),
  ([39,49,71,86,103,386],[616,976]),
  ([39,49,71,86,103,390],[2651,617,977]),
  ([39,49,71,86,131],[1641,1270,619,590,599,877,2324,265,245,257,1722,1279,805,1035]),
  ([39,49,71,86,131,135],[620,266,1721,1281,829,1036]),
  ([39,49,71,86,131,162],[621,267,312,869,1041]),
  ([39,49,71,86,135,309],[623,972]),
  ([39,49,71,86,135,317],[624,994]),
  ([39,49,71,86,135,323],[625,998]),
  ([39,49,71,86,135,331],[626,1002]),
  ([39,49,71,86,135,340],[628,1004]),
  ([39,49,71,86,135,361],[629,269,1102]),
  ([39,49,71,86,135,378],[630,270,1726,1280,1105]),
  ([39,49,71,87,103,135],[694]),
  ([39,49,71,88,103,135],[491,863,876]),
  ([39,49,71,89,103,135],[782]),
  ([39,49,71,90,103,135],[702]),
  ([39,49,71,91,92,135],[1287,832]),
  ([39,49,71,91,103,135],[]),
  ([39,49,71,91,135,162],[877]),
  ([39,49,71,92,93,135],[2345,1797,1321,913]),
  ([39,49,71,92,94,135],[2397,1746,1322,913]),
  ([39,49,71,92,96,135],[2402,1803,1326,1293,1112,938]),
  ([39,49,71,92,97,135],[2408,2345,1810,1331,1113,948,914]),
  ([39,49,71,92,97,173],[2361,1811,1332])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b33ok : f5b33.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b34 : Array Row := #[
  ([39,49,71,92,99,135],[2415,1817,1746,1335,1115,959,915]),
  ([39,49,71,92,99,182],[2417,1767,1336]),
  ([39,49,71,92,103,131],[2427,2329,1828,1730,1340,1065,979]),
  ([39,49,71,92,103,135],[2441,1842,1345,1118,982]),
  ([39,49,71,92,103,173],[2334,1848,1353]),
  ([39,49,71,92,103,182],[2448,1736,1354]),
  ([39,49,71,92,103,195],[492,1355,855]),
  ([39,49,71,92,103,285],[86,2335,2296,871]),
  ([39,49,71,92,103,289],[106,1737,1697,873]),
  ([39,49,71,92,103,348],[2473,1874,1370,1212,968,878]),
  ([39,49,71,92,103,351],[2474,1875,1371,1213,972,881]),
  ([39,49,71,92,103,355],[1876,1372,882]),
  ([39,49,71,92,103,358],[2475,1373,883]),
  ([39,49,71,92,103,365],[2476,1877,1374,1214,973,884]),
  ([39,49,71,92,103,371],[2477,1878,1375,1215,974,886]),
  ([39,49,71,92,103,386],[2478,1879,1376,1216,976,888]),
  ([39,49,71,92,118,135],[2345,2331,1888,1382,889]),
  ([39,49,71,92,120,135],[2334,1891,1385]),
  ([39,49,71,92,120,173],[1893,1386]),
  ([39,49,71,92,120,182],[585,1387]),
  ([39,49,71,92,120,351],[1894,1388,881]),
  ([39,49,71,92,123,135],[2496,1746,1734,1389,891]),
  ([39,49,71,92,125,135],[2498,1736,1392]),
  ([39,49,71,92,125,173],[579,1393]),
  ([39,49,71,92,125,182],[2500,1394]),
  ([39,49,71,92,125,351],[2501,1395,881]),
  ([39,49,71,92,127,135],[493,1396,895]),
  ([39,49,71,92,130,135],[1397]),
  ([39,49,71,92,131],[0,2527,1071,2337,2393,928,2338,0,1928,1072,1738,1794,930,1739,0,1423,1092,1289,804,1289,1240,910,1073]),
  ([39,49,71,92,131,135],[2506,2346,1907,1747,1401,1293,1137,1076,913]),
  ([39,49,71,92,131,162],[2514,2350,1915,1751,1413,1169]),
  ([39,49,71,92,135],[2345,889,1746,891,1551,1148,1293,804,913])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b34ok : f5b34.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b35 : Array Row := #[
  ([39,49,71,92,135,153],[2536,1937,4,1449,811,1293,1166,1148,878]),
  ([39,49,71,92,135,156],[1456]),
  ([39,49,71,92,135,162],[2544,1945,1469,1172,878]),
  ([39,49,71,92,135,165],[1472]),
  ([39,49,71,92,135,173],[1473]),
  ([39,49,71,92,135,177],[1474]),
  ([39,49,71,92,135,182],[1475]),
  ([39,49,71,92,135,186],[1476]),
  ([39,49,71,92,135,189],[2351,1953,722,1477,879]),
  ([39,49,71,92,135,190],[769,1478]),
  ([39,49,71,92,135,192],[2552,600,1757,1479,880]),
  ([39,49,71,92,135,193],[689,1480]),
  ([39,49,71,92,135,195],[494,1481,856]),
  ([39,49,71,92,135,197],[2352,1955,779,1483,879]),
  ([39,49,71,92,135,198],[2554,699,1758,1484,880]),
  ([39,49,71,92,135,241],[2353,1485]),
  ([39,49,71,92,135,242],[1486]),
  ([39,49,71,92,135,243],[2354,1487]),
  ([39,49,71,92,135,244],[2355,1488]),
  ([39,49,71,92,135,250],[1759,1489]),
  ([39,49,71,92,135,251],[1490]),
  ([39,49,71,92,135,252],[1760,1491]),
  ([39,49,71,92,135,253],[1761,1492]),
  ([39,49,71,92,135,257],[495,2356,2234,1493]),
  ([39,49,71,92,135,260],[496,1762,1635,1494]),
  ([39,49,71,92,135,274],[1508,812]),
  ([39,49,71,92,135,275],[1509]),
  ([39,49,71,92,135,276],[1510]),
  ([39,49,71,92,135,278],[1511]),
  ([39,49,71,92,135,280],[1512]),
  ([39,49,71,92,135,285],[31,2357,2297,1513,871]),
  ([39,49,71,92,135,289],[45,1763,1698,1514,873])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b35ok : f5b35.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b36 : Array Row := #[
  ([39,49,71,92,135,293],[2794,180,2358,272,1764,1523,813,1264]),
  ([39,49,71,92,135,300],[2588,1989,1524,1208]),
  ([39,49,71,92,135,301],[1990,1525]),
  ([39,49,71,92,135,302],[2589,1526]),
  ([39,49,71,92,135,303],[2590,1991,1527,1209,934]),
  ([39,49,71,92,135,304],[2591,1992,1528,1210,945]),
  ([39,49,71,92,135,306],[2592,1993,1529,1211,956]),
  ([39,49,71,92,135,309],[2593,1994,1530,1213,972]),
  ([39,49,71,92,135,310],[1995,1531]),
  ([39,49,71,92,135,311],[2594,1532]),
  ([39,49,71,92,135,313],[2595,1996,1533,1217,992]),
  ([39,49,71,92,135,317],[2596,1997,1534,1219,994]),
  ([39,49,71,92,135,319],[2597,1998,1535,1223,996]),
  ([39,49,71,92,135,323],[2598,1999,1536,1225,998]),
  ([39,49,71,92,135,327],[2795,2599,2359,2000,1765,1537,1230,1001]),
  ([39,49,71,92,135,331],[2600,2360,2001,1766,1538,1232,1002]),
  ([39,49,71,92,135,336],[2361,2330,2002,1539]),
  ([39,49,71,92,135,343],[2602,1767,1732,1541]),
  ([39,49,71,92,135,348],[2604,2005,1543,1241,1014,878]),
  ([39,49,71,92,135,351],[1544]),
  ([39,49,71,92,135,353],[1545]),
  ([39,49,71,92,135,355],[1546,882]),
  ([39,49,71,92,135,358],[1547,883]),
  ([39,49,71,92,135,361],[2605,2006,1548,1244,1102]),
  ([39,49,71,92,135,365],[1549,884]),
  ([39,49,71,92,135,371],[1550,886]),
  ([39,49,71,92,135,378],[2606,2007,5,814,1290,1245,1105]),
  ([39,49,71,92,135,386],[1552,888]),
  ([39,49,71,92,140,173],[1555,882]),
  ([39,49,71,92,140,182],[1556,883]),
  ([39,49,71,92,140,351],[1557,881]),
  ([39,49,71,92,156,173],[1583,884])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b36ok : f5b36.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b37 : Array Row := #[
  ([39,49,71,92,156,182],[1585,886]),
  ([39,49,71,92,156,351],[1587,881]),
  ([39,49,71,92,162,173],[2352,2015,1588,885]),
  ([39,49,71,92,162,182],[2614,1758,1589,887]),
  ([39,49,71,92,162,351],[2621,2022,1596,1109,881]),
  ([39,49,71,92,173],[409,2306,2361,1756,895,1608,1191,1299,835]),
  ([39,49,71,92,173,177],[1600]),
  ([39,49,71,92,173,182],[497,562,571,1601,888,895]),
  ([39,49,71,92,173,190],[770,1602]),
  ([39,49,71,92,173,195],[498,572,1603,857]),
  ([39,49,71,92,173,309],[2027,1604]),
  ([39,49,71,92,173,336],[2331,2028,1605]),
  ([39,49,71,92,173,343],[500,2628,1768,1733,1606]),
  ([39,49,71,92,173,351],[1607,881]),
  ([39,49,71,92,173,378],[2652,2629,2029,6,840,1294,1164]),
  ([39,49,71,92,182],[375,2366,895,1711,1767,1616,1201,1302,844]),
  ([39,49,71,92,182,186],[1609]),
  ([39,49,71,92,182,193],[690,1610]),
  ([39,49,71,92,182,195],[501,563,1611,858]),
  ([39,49,71,92,182,309],[2630,1612]),
  ([39,49,71,92,182,336],[503,2367,2332,2032,1613]),
  ([39,49,71,92,182,343],[2631,1734,1614]),
  ([39,49,71,92,182,351],[1615,881]),
  ([39,49,71,92,182,378],[2632,2057,2033,7,849,1295,1165]),
  ([39,49,71,92,195],[504,376,410,2307,2367,1712,1768,1617,1203,1303,854,853,859]),
  ([39,49,71,92,285],[411,2241,166,2308,14,2378,2295,871,2299,1777,871,1310,871,871]),
  ([39,49,71,92,289],[377,1642,2384,873,258,1713,9,1781,1696,873,1700,1311,873,873]),
  ([39,49,71,92,309,351],[2638,2039,1623,982,1118,881]),
  ([39,49,71,92,336,351],[2333,2345,2040,1624,881]),
  ([39,49,71,92,343,351],[2639,1735,1746,1625,881]),
  ([39,49,71,92,348],[1,2640,1236,2386,878,1,2041,1238,1787,878,1,1626,1243,1314,878,1011,878,1073]),
  ([39,49,71,92,351],[2387,881,1788,881,1627,1245,1315,881,881])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b37ok : f5b37.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b38 : Array Row := #[
  ([39,49,71,92,351,378],[2641,2042,8,1293,1296,1148,1166,881]),
  ([39,49,71,92,355],[2388,882,1789,882,1628,1246,1316,882,882]),
  ([39,49,71,92,358],[2389,883,1790,883,1629,1247,1317,883,883]),
  ([39,49,71,92,365],[412,2309,2390,884,1791,884,1630,1253,1318,884,884]),
  ([39,49,71,92,371],[378,2391,886,1714,1792,886,1631,1256,1319,886,886]),
  ([39,49,71,92,386],[2392,888,1793,888,1632,1257,1320,888,888]),
  ([39,49,71,93,103,173],[889]),
  ([39,49,71,93,103,182],[2448,1796,891]),
  ([39,49,71,93,103,351],[2474,913,972]),
  ([39,49,71,93,125,135],[2498,1796,881]),
  ([39,49,71,93,135,162],[2544,1470,1172,881,931]),
  ([39,49,71,94,103,173],[2396,1848,889]),
  ([39,49,71,94,103,182],[891]),
  ([39,49,71,94,103,351],[1875,913,972]),
  ([39,49,71,94,120,135],[2396,1891,881]),
  ([39,49,71,94,135,162],[1945,1471,1172,881,932]),
  ([39,49,71,95,103,135],[881,982]),
  ([39,49,71,96,103,173],[2398,1353]),
  ([39,49,71,96,103,182],[1799,1354]),
  ([39,49,71,96,120,135],[2398,1385]),
  ([39,49,71,96,125,135],[1799,1392]),
  ([39,49,71,96,135,140],[1432]),
  ([39,49,71,96,135,156],[1456]),
  ([39,49,71,96,135,162],[1469,933]),
  ([39,49,71,96,135,165],[1472]),
  ([39,49,71,96,135,173],[1473,889,881]),
  ([39,49,71,96,135,182],[1475,891,881]),
  ([39,49,71,96,135,190],[771,1478]),
  ([39,49,71,96,135,193],[691,1480]),
  ([39,49,71,96,135,309],[1530,972]),
  ([39,49,71,96,135,338],[2403,1540]),
  ([39,49,71,96,135,345],[1804,1542])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b38ok : f5b38.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b39 : Array Row := #[
  ([39,49,71,96,135,353],[1545]),
  ([39,49,71,96,135,378],[62,1323,1105]),
  ([39,49,71,96,156,173],[1583,935]),
  ([39,49,71,96,156,182],[1585,936]),
  ([39,49,71,96,173],[413,2310,2403,937,1608,1191,1327,889]),
  ([39,49,71,96,182],[379,937,1715,1804,1616,1201,1328,891]),
  ([39,49,71,97,103,182],[2448,1805]),
  ([39,49,71,97,120,135],[]),
  ([39,49,71,97,125,135],[2498,1805]),
  ([39,49,71,97,135,140],[]),
  ([39,49,71,97,135,156],[1457,881]),
  ([39,49,71,97,135,162],[2544,944]),
  ([39,49,71,97,135,173],[889]),
  ([39,49,71,97,135,177],[]),
  ([39,49,71,97,135,182],[891,881]),
  ([39,49,71,97,135,190],[772]),
  ([39,49,71,97,135,195],[505,860,895]),
  ([39,49,71,97,135,309],[2593,972]),
  ([39,49,71,97,135,336],[2404]),
  ([39,49,71,97,135,346],[2603,1812]),
  ([39,49,71,97,135,355],[914]),
  ([39,49,71,97,135,381],[2607,1106]),
  ([39,49,71,97,156,173],[1584,889,946]),
  ([39,49,71,97,173,182],[506,573,889,947]),
  ([39,49,71,97,182],[380,2409,1716,1812,1202,891]),
  ([39,49,71,98,103,135],[1118]),
  ([39,49,71,98,135],[954,1149,881]),
  ([39,49,71,98,135,156],[1457,934]),
  ([39,49,71,98,135,173],[889,945]),
  ([39,49,71,98,135,190],[773]),
  ([39,49,71,99,103,173],[2410,1848]),
  ([39,49,71,99,120,135],[2410,1891])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b39ok : f5b39.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b40 : Array Row := #[
  ([39,49,71,99,125,135],[]),
  ([39,49,71,99,135,140],[]),
  ([39,49,71,99,135,156],[1458,881]),
  ([39,49,71,99,135,162],[1945,955]),
  ([39,49,71,99,135,173],[889,881]),
  ([39,49,71,99,135,182],[891]),
  ([39,49,71,99,135,186],[]),
  ([39,49,71,99,135,193],[692]),
  ([39,49,71,99,135,195],[507,861,895]),
  ([39,49,71,99,135,309],[1994,972]),
  ([39,49,71,99,135,339],[2416,2003]),
  ([39,49,71,99,135,343],[1813]),
  ([39,49,71,99,135,358],[915]),
  ([39,49,71,99,135,382],[2008,1107]),
  ([39,49,71,99,156,182],[1586,891,957]),
  ([39,49,71,99,173],[414,2311,2416,1818,1192,889]),
  ([39,49,71,99,173,182],[508,564,891,958]),
  ([39,49,71,100,103,135],[1118]),
  ([39,49,71,100,135],[965,1150,881]),
  ([39,49,71,100,135,156],[1458,934]),
  ([39,49,71,100,135,182],[891,956]),
  ([39,49,71,100,135,193],[693]),
  ([39,49,71,101,103,135],[1118]),
  ([39,49,71,101,135],[1151,881]),
  ([39,49,71,101,135,173],[889,945]),
  ([39,49,71,101,135,182],[891,956]),
  ([39,49,71,101,135,195],[509,862,895]),
  ([39,49,71,103,104,135],[]),
  ([39,49,71,103,105,135],[]),
  ([39,49,71,103,107,135],[934]),
  ([39,49,71,103,108,135],[1122]),
  ([39,49,71,103,110,135],[934])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b40ok : f5b40.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b41 : Array Row := #[
  ([39,49,71,103,111,135],[1126]),
  ([39,49,71,103,114,135],[1819,945]),
  ([39,49,71,103,115,135],[2418,956]),
  ([39,49,71,103,116,135],[1132]),
  ([39,49,71,103,118,135],[2441,945]),
  ([39,49,71,103,120,131],[]),
  ([39,49,71,103,120,132],[]),
  ([39,49,71,103,120,351],[972]),
  ([39,49,71,103,120,365],[973]),
  ([39,49,71,103,120,371],[586,974]),
  ([39,49,71,103,120,386],[976]),
  ([39,49,71,103,121,135],[]),
  ([39,49,71,103,123,135],[1842,956]),
  ([39,49,71,103,125,131],[]),
  ([39,49,71,103,125,133],[]),
  ([39,49,71,103,125,351],[972]),
  ([39,49,71,103,125,365],[580,973]),
  ([39,49,71,103,125,371],[974]),
  ([39,49,71,103,125,386],[976]),
  ([39,49,71,103,126,135],[]),
  ([39,49,71,103,127,135],[510,966]),
  ([39,49,71,103,128,135],[782]),
  ([39,49,71,103,129,135],[702]),
  ([39,49,71,103,130,135],[]),
  ([39,49,71,103,131,140],[]),
  ([39,49,71,103,131,156],[2445,1846,1407,933,1024]),
  ([39,49,71,103,131,162],[]),
  ([39,49,71,103,131,165],[]),
  ([39,49,71,103,131,173],[2492,1849,1353,889,944,1028]),
  ([39,49,71,103,131,182],[2449,1899,1354,891,955,1032]),
  ([39,49,71,103,131,197],[780]),
  ([39,49,71,103,131,198],[700])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b41ok : f5b41.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b42 : Array Row := #[
  ([39,49,71,103,131,351],[2480,1881,1371,913,1244,1014,972]),
  ([39,49,71,103,131,361],[1015]),
  ([39,49,71,103,131,378],[2481,1882,60,1413,1337,1019]),
  ([39,49,71,103,131,392],[88,2493,2423,1883,1377,928,1025]),
  ([39,49,71,103,131,396],[2482,108,1900,1824,1378,930,1029]),
  ([39,49,71,103,132],[2429,1008,1097,879]),
  ([39,49,71,103,132,135],[2442,881,879,982]),
  ([39,49,71,103,132,162],[968]),
  ([39,49,71,103,132,197],[781]),
  ([39,49,71,103,133],[1005,1830,1099,880]),
  ([39,49,71,103,133,135],[1843,881,880,982]),
  ([39,49,71,103,133,162],[968]),
  ([39,49,71,103,133,198],[701]),
  ([39,49,71,103,135],[1109,881]),
  ([39,49,71,103,135,136],[934]),
  ([39,49,71,103,135,137],[882,945]),
  ([39,49,71,103,135,138],[883,956]),
  ([39,49,71,103,135,139],[1141,968]),
  ([39,49,71,103,135,142],[884,881,984]),
  ([39,49,71,103,135,143],[2442,885,945,1144,968]),
  ([39,49,71,103,135,145],[]),
  ([39,49,71,103,135,147],[886,881,986]),
  ([39,49,71,103,135,148],[1843,887,956,1147,968]),
  ([39,49,71,103,135,150],[]),
  ([39,49,71,103,135,153],[61,1435,1345,934,1109,968]),
  ([39,49,71,103,135,158],[953]),
  ([39,49,71,103,135,160],[964]),
  ([39,49,71,103,135,163],[969]),
  ([39,49,71,103,135,164],[970]),
  ([39,49,71,103,135,165],[]),
  ([39,49,71,103,135,167],[888,881,989]),
  ([39,49,71,103,135,168],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b42ok : f5b42.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b43 : Array Row := #[
  ([39,49,71,103,135,174],[953]),
  ([39,49,71,103,135,175],[890,966]),
  ([39,49,71,103,135,176],[969]),
  ([39,49,71,103,135,177],[]),
  ([39,49,71,103,135,183],[964]),
  ([39,49,71,103,135,184],[892,966]),
  ([39,49,71,103,135,185],[970]),
  ([39,49,71,103,135,186],[]),
  ([39,49,71,103,135,187],[694,774,1459,934]),
  ([39,49,71,103,135,188],[511,774,863,893,945]),
  ([39,49,71,103,135,189],[733,953,969]),
  ([39,49,71,103,135,190],[774,953]),
  ([39,49,71,103,135,191],[512,694,863,894,956]),
  ([39,49,71,103,135,192],[611,964,970]),
  ([39,49,71,103,135,193],[694,964]),
  ([39,49,71,103,135,195],[513,863,895,966]),
  ([39,49,71,103,135,196],[702,782,968]),
  ([39,49,71,103,135,197],[782,969]),
  ([39,49,71,103,135,198],[702,970]),
  ([39,49,71,103,135,199],[967]),
  ([39,49,71,103,135,200],[971]),
  ([39,49,71,103,135,201],[792]),
  ([39,49,71,103,135,202],[714]),
  ([39,49,71,103,135,203],[867]),
  ([39,49,71,103,135,204],[]),
  ([39,49,71,103,135,205],[]),
  ([39,49,71,103,135,206],[]),
  ([39,49,71,103,135,207],[]),
  ([39,49,71,103,135,208],[]),
  ([39,49,71,103,135,209],[]),
  ([39,49,71,103,135,210],[]),
  ([39,49,71,103,135,211],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b43ok : f5b43.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b44 : Array Row := #[
  ([39,49,71,103,135,212],[]),
  ([39,49,71,103,135,213],[]),
  ([39,49,71,103,135,214],[]),
  ([39,49,71,103,135,215],[]),
  ([39,49,71,103,135,216],[]),
  ([39,49,71,103,135,217],[]),
  ([39,49,71,103,135,218],[]),
  ([39,49,71,103,135,219],[]),
  ([39,49,71,103,135,220],[]),
  ([39,49,71,103,135,221],[]),
  ([39,49,71,103,135,222],[]),
  ([39,49,71,103,135,223],[]),
  ([39,49,71,103,135,224],[]),
  ([39,49,71,103,135,225],[]),
  ([39,49,71,103,135,226],[]),
  ([39,49,71,103,135,227],[]),
  ([39,49,71,103,135,228],[]),
  ([39,49,71,103,135,229],[]),
  ([39,49,71,103,135,230],[]),
  ([39,49,71,103,135,231],[514,1460]),
  ([39,49,71,103,135,232],[2796]),
  ([39,49,71,103,135,233],[]),
  ([39,49,71,103,135,234],[]),
  ([39,49,71,103,135,235],[2797]),
  ([39,49,71,103,135,236],[]),
  ([39,49,71,103,135,237],[]),
  ([39,49,71,103,135,238],[2798,611]),
  ([39,49,71,103,135,241],[]),
  ([39,49,71,103,135,242],[]),
  ([39,49,71,103,135,243],[]),
  ([39,49,71,103,135,244],[]),
  ([39,49,71,103,135,245],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b44ok : f5b44.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b45 : Array Row := #[
  ([39,49,71,103,135,246],[]),
  ([39,49,71,103,135,247],[2799,733]),
  ([39,49,71,103,135,250],[]),
  ([39,49,71,103,135,251],[]),
  ([39,49,71,103,135,252],[]),
  ([39,49,71,103,135,253],[]),
  ([39,49,71,103,135,254],[]),
  ([39,49,71,103,135,255],[]),
  ([39,49,71,103,135,257],[516,2235]),
  ([39,49,71,103,135,258],[517]),
  ([39,49,71,103,135,259],[]),
  ([39,49,71,103,135,260],[518,1636]),
  ([39,49,71,103,135,261],[519]),
  ([39,49,71,103,135,262],[]),
  ([39,49,71,103,135,263],[520]),
  ([39,49,71,103,135,264],[521]),
  ([39,49,71,103,135,265],[896]),
  ([39,49,71,103,135,266],[897]),
  ([39,49,71,103,135,267],[898]),
  ([39,49,71,103,135,268],[]),
  ([39,49,71,103,135,269],[899]),
  ([39,49,71,103,135,270],[900]),
  ([39,49,71,103,135,271],[2653,901]),
  ([39,49,71,103,135,272],[2058,902]),
  ([39,49,71,103,135,274],[1461]),
  ([39,49,71,103,135,275],[1462]),
  ([39,49,71,103,135,276],[1463]),
  ([39,49,71,103,135,277],[1464]),
  ([39,49,71,103,135,278],[]),
  ([39,49,71,103,135,279],[]),
  ([39,49,71,103,135,280],[]),
  ([39,49,71,103,135,281],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b45ok : f5b45.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b46 : Array Row := #[
  ([39,49,71,103,135,282],[]),
  ([39,49,71,103,135,283],[2801,903]),
  ([39,49,71,103,135,285],[2301,904]),
  ([39,49,71,103,135,286],[905]),
  ([39,49,71,103,135,287],[]),
  ([39,49,71,103,135,289],[1702,906]),
  ([39,49,71,103,135,290],[907]),
  ([39,49,71,103,135,291],[]),
  ([39,49,71,103,135,293],[2802,181,273,1465,1265]),
  ([39,49,71,103,135,294],[1466]),
  ([39,49,71,103,135,295],[1467]),
  ([39,49,71,103,135,296],[522,2305,2059,908]),
  ([39,49,71,103,135,297],[182]),
  ([39,49,71,103,135,298],[523,2654,1710,909]),
  ([39,49,71,103,135,299],[274]),
  ([39,49,71,103,135,300],[881]),
  ([39,49,71,103,135,301],[]),
  ([39,49,71,103,135,302],[]),
  ([39,49,71,103,135,303],[934]),
  ([39,49,71,103,135,304],[945]),
  ([39,49,71,103,135,306],[956]),
  ([39,49,71,103,135,309],[]),
  ([39,49,71,103,135,310],[]),
  ([39,49,71,103,135,311],[]),
  ([39,49,71,103,135,312],[]),
  ([39,49,71,103,135,313],[992]),
  ([39,49,71,103,135,317],[994]),
  ([39,49,71,103,135,318],[]),
  ([39,49,71,103,135,319],[996]),
  ([39,49,71,103,135,323],[998]),
  ([39,49,71,103,135,324],[]),
  ([39,49,71,103,135,326],[1000])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b46ok : f5b46.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b47 : Array Row := #[
  ([39,49,71,103,135,327],[2803,2447,1850,1001]),
  ([39,49,71,103,135,331],[1002]),
  ([39,49,71,103,135,332],[]),
  ([39,49,71,103,135,333],[]),
  ([39,49,71,103,135,336],[2419]),
  ([39,49,71,103,135,337],[]),
  ([39,49,71,103,135,338],[]),
  ([39,49,71,103,135,339],[]),
  ([39,49,71,103,135,340],[1004]),
  ([39,49,71,103,135,343],[1820]),
  ([39,49,71,103,135,344],[]),
  ([39,49,71,103,135,345],[]),
  ([39,49,71,103,135,346],[]),
  ([39,49,71,103,135,347],[1007]),
  ([39,49,71,103,135,348],[910,1155,1014,968]),
  ([39,49,71,103,135,351],[913]),
  ([39,49,71,103,135,353],[]),
  ([39,49,71,103,135,355],[914]),
  ([39,49,71,103,135,356],[]),
  ([39,49,71,103,135,358],[915]),
  ([39,49,71,103,135,359],[]),
  ([39,49,71,103,135,360],[916]),
  ([39,49,71,103,135,361],[1102]),
  ([39,49,71,103,135,362],[]),
  ([39,49,71,103,135,363],[]),
  ([39,49,71,103,135,365],[918,973]),
  ([39,49,71,103,135,366],[]),
  ([39,49,71,103,135,368],[919]),
  ([39,49,71,103,135,369],[1103]),
  ([39,49,71,103,135,371],[921,974]),
  ([39,49,71,103,135,372],[]),
  ([39,49,71,103,135,374],[922])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b47ok : f5b47.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b48 : Array Row := #[
  ([39,49,71,103,135,375],[1104]),
  ([39,49,71,103,135,377],[524,1468,923,975]),
  ([39,49,71,103,135,378],[62,1469,1341,1105]),
  ([39,49,71,103,135,379],[1470]),
  ([39,49,71,103,135,380],[1471]),
  ([39,49,71,103,135,381],[1106]),
  ([39,49,71,103,135,382],[1107]),
  ([39,49,71,103,135,386],[924,976]),
  ([39,49,71,103,135,387],[925]),
  ([39,49,71,103,135,388],[926]),
  ([39,49,71,103,135,390],[927,977]),
  ([39,49,71,103,135,392],[2430,928]),
  ([39,49,71,103,135,394],[929,978]),
  ([39,49,71,103,135,396],[1831,930]),
  ([39,49,71,103,140,351],[972]),
  ([39,49,71,103,140,365],[973]),
  ([39,49,71,103,140,371],[974]),
  ([39,49,71,103,140,386],[976]),
  ([39,49,71,103,142],[415,2312,1156,884]),
  ([39,49,71,103,142,156],[1558,935]),
  ([39,49,71,103,142,173],[889,946]),
  ([39,49,71,103,142,365],[918]),
  ([39,49,71,103,147],[381,1717,1160,886]),
  ([39,49,71,103,147,156],[1560,936]),
  ([39,49,71,103,147,182],[891,957]),
  ([39,49,71,103,147,371],[921]),
  ([39,49,71,103,156,195],[525,1572,937,975]),
  ([39,49,71,103,156,351],[1573,938,972]),
  ([39,49,71,103,156,355],[1574,939]),
  ([39,49,71,103,156,358],[1575,940]),
  ([39,49,71,103,156,365],[1576,941,973]),
  ([39,49,71,103,156,371],[1578,942,974])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b48ok : f5b48.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b49 : Array Row := #[
  ([39,49,71,103,156,386],[1580,943,976]),
  ([39,49,71,103,162,351],[1109,972]),
  ([39,49,71,103,162,365],[2655,1156,973]),
  ([39,49,71,103,162,371],[2060,1160,974]),
  ([39,49,71,103,162,386],[1168,976]),
  ([39,49,71,103,167],[1168,888]),
  ([39,49,71,103,167,173],[889,947]),
  ([39,49,71,103,167,182],[891,958]),
  ([39,49,71,103,167,386],[924]),
  ([39,49,71,103,173,193],[965,977]),
  ([39,49,71,103,173,343],[527,2494,1821]),
  ([39,49,71,103,173,351],[948,972]),
  ([39,49,71,103,173,353],[]),
  ([39,49,71,103,173,358],[949]),
  ([39,49,71,103,173,365],[950,973]),
  ([39,49,71,103,173,371],[528,574,951,974]),
  ([39,49,71,103,173,378],[2656,2495,63,1588,1348,1164]),
  ([39,49,71,103,173,386],[952,976]),
  ([39,49,71,103,182,190],[954,978]),
  ([39,49,71,103,182,336],[529,2420,1901]),
  ([39,49,71,103,182,351],[959,972]),
  ([39,49,71,103,182,353],[]),
  ([39,49,71,103,182,355],[960]),
  ([39,49,71,103,182,365],[530,565,961,973]),
  ([39,49,71,103,182,371],[962,974]),
  ([39,49,71,103,182,378],[2061,1902,64,1589,1349,1165]),
  ([39,49,71,103,182,386],[963,976]),
  ([39,49,71,103,241,351],[2434,972]),
  ([39,49,71,103,241,365],[2443,973]),
  ([39,49,71,103,241,386],[2446,976]),
  ([39,49,71,103,242,351],[972]),
  ([39,49,71,103,250,351],[1835,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b49ok : f5b49.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b50 : Array Row := #[
  ([39,49,71,103,250,371],[1845,974]),
  ([39,49,71,103,250,386],[1847,976]),
  ([39,49,71,103,251,351],[972]),
  ([39,49,71,103,257,371],[534,2236,2444,974]),
  ([39,49,71,103,260,365],[536,1637,1844,973]),
  ([39,49,71,103,274,351],[1590,1343,972]),
  ([39,49,71,103,274,365],[2657,1591,1346,973]),
  ([39,49,71,103,274,371],[2062,1592,1347,974]),
  ([39,49,71,103,275,351],[1593,972]),
  ([39,49,71,103,276,351],[1594,972]),
  ([39,49,71,103,285,351],[2302,2438,972]),
  ([39,49,71,103,289,351],[1703,1839,972]),
  ([39,49,71,103,293,386],[2804,184,276,1595,1266,1352,976]),
  ([39,49,71,103,309,351],[1118,972]),
  ([39,49,71,103,310,351],[972]),
  ([39,49,71,103,311,351],[972]),
  ([39,49,71,103,317,365],[995,1157,973]),
  ([39,49,71,103,323,371],[999,1161,974]),
  ([39,49,71,103,331,386],[2805,1003,1182,976]),
  ([39,49,71,103,336,351],[2421,2441,972]),
  ([39,49,71,103,343,351],[1822,1842,972]),
  ([39,49,71,103,348],[75,1006,968,98,1009,968,58,1169,968,1011,968,1073]),
  ([39,49,71,103,351],[972,972,1172,972,972]),
  ([39,49,71,103,351,361],[1141,1154,972]),
  ([39,49,71,103,351,378],[65,1596,1345,1350,1148,1166,972]),
  ([39,49,71,103,365],[416,2313,973,973,1174,973,973]),
  ([39,49,71,103,371],[382,974,1718,974,1176,974,974]),
  ([39,49,71,103,377],[538,383,417,2314,975,1719,975,1597,1177,1351,975,975]),
  ([39,49,71,103,386],[976,976,1179,976,976]),
  ([39,49,71,103,390],[418,2315,2422,977,977,1180,977,977]),
  ([39,49,71,103,394],[384,978,1720,1823,978,1181,978,978]),
  ([39,49,71,108,120,135],[])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b50ok : f5b50.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b51 : Array Row := #[
  ([39,49,71,108,135],[1109,881]),
  ([39,49,71,108,135,162],[993]),
  ([39,49,71,108,135,317],[]),
  ([39,49,71,111,125,135],[]),
  ([39,49,71,111,135],[1109,881]),
  ([39,49,71,111,135,162],[997]),
  ([39,49,71,111,135,323],[]),
  ([39,49,71,116,120,135],[]),
  ([39,49,71,116,125,135],[]),
  ([39,49,71,116,135],[2485,1886,1110,881]),
  ([39,49,71,116,135,331],[]),
  ([39,49,71,120,131],[2493,583,1010,1890,206,1040,1383,878,1027]),
  ([39,49,71,120,131,135],[2492,1892,1385,881,931,1028]),
  ([39,49,71,120,131,162],[993,1040]),
  ([39,49,71,120,135,198],[1004,1005]),
  ([39,49,71,120,135,309],[972]),
  ([39,49,71,120,135,311],[]),
  ([39,49,71,120,135,317],[994]),
  ([39,49,71,120,135,323],[998]),
  ([39,49,71,120,135,331],[1002]),
  ([39,49,71,120,135,343],[2494,1889]),
  ([39,49,71,120,135,361],[1102]),
  ([39,49,71,120,135,378],[2495,207,1483,1384,1105]),
  ([39,49,71,125,131],[576,1010,2497,1900,303,1041,1390,878,1031]),
  ([39,49,71,125,131,135],[2499,1899,1392,881,932,1032]),
  ([39,49,71,125,131,162],[997,1041]),
  ([39,49,71,125,135,197],[1007,1008]),
  ([39,49,71,125,135,309],[972]),
  ([39,49,71,125,135,310],[]),
  ([39,49,71,125,135,317],[994]),
  ([39,49,71,125,135,323],[998]),
  ([39,49,71,125,135,331],[1002])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b51ok : f5b51.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b52 : Array Row := #[
  ([39,49,71,125,135,336],[2487,1901]),
  ([39,49,71,125,135,361],[1102]),
  ([39,49,71,125,135,378],[1902,304,1484,1391,1105]),
  ([39,49,71,130,135,162],[356,1000,1010]),
  ([39,49,71,131,135,140],[1432]),
  ([39,49,71,131,135,156],[1456]),
  ([39,49,71,131,135,162],[2545,1946,1469,1407,1172,1024]),
  ([39,49,71,131,135,165],[1472]),
  ([39,49,71,131,135,173],[1473]),
  ([39,49,71,131,135,182],[1475]),
  ([39,49,71,131,135,197],[2519,1956,784,1483,1012,1043]),
  ([39,49,71,131,135,198],[2555,704,1921,1484,1013,1044]),
  ([39,49,71,131,135,351],[1544]),
  ([39,49,71,131,135,361],[2609,2010,1548,1244,1102,1015]),
  ([39,49,71,131,135,378],[2610,2011,818,816,1408,1398,1245,1105,1019]),
  ([39,49,71,131,135,392],[33,2520,2502,2012,1553,1025]),
  ([39,49,71,131,135,396],[2611,47,1922,1903,1554,1029]),
  ([39,49,71,131,140],[2508,93,1028,1909,116,1032,1402,833,1024]),
  ([39,49,71,131,140,162],[1015,1024]),
  ([39,49,71,131,156],[2509,200,1034,1910,298,1036,1408]),
  ([39,49,71,131,156,162],[2612,2013,1019,1024]),
  ([39,49,71,131,162],[2515,209,1040,1916,308,1041,1413]),
  ([39,49,71,131,162,165],[]),
  ([39,49,71,131,162,173],[2519,2016,1588,1017,1043]),
  ([39,49,71,131,162,182],[2615,1921,1589,1018,1044]),
  ([39,49,71,131,162,197],[785]),
  ([39,49,71,131,162,198],[705]),
  ([39,49,71,131,162,351],[2622,2023,1596,1109,1014]),
  ([39,49,71,131,162,361],[1015]),
  ([39,49,71,131,162,378],[2623,2024,1405,1019]),
  ([39,49,71,131,162,392],[218,2522,2510,2025,1598,1025]),
  ([39,49,71,131,162,396],[2624,314,1924,1911,1599,1029])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b52ok : f5b52.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b53 : Array Row := #[
  ([39,49,71,131,165],[2516,221,1043,1917,318,1044,1414]),
  ([39,49,71,131,173],[419,2316,2520,1918,567,1038,1608,1191,1415,836,1034]),
  ([39,49,71,131,182],[385,2521,558,1038,1721,1922,1616,1201,1416,845,1036]),
  ([39,49,71,131,197],[2522,1923,783,778,786,1042,1417]),
  ([39,49,71,131,198],[2523,703,698,706,1042,1924,1418]),
  ([39,49,71,131,351],[2528,1014,1929,1014,1627,1245,1421,1014,1014]),
  ([39,49,71,131,361],[2529,1015,1930,1015,1422,1015,1015]),
  ([39,49,71,131,378],[137,1271,2643,1258,2530,1019,247,1279,2044,1259,1931,1019,816,1403,1019,1406,1019]),
  ([39,49,71,131,392],[421,2242,168,2317,16,2517,1025,2518,2045,1261,1932,1025,1633,1258,1424,1025,1025]),
  ([39,49,71,131,396],[387,1643,2644,1261,2532,1029,260,1722,11,1919,1029,1920,1634,1259,1425,1029,1029]),
  ([39,49,71,132,135,162],[2545,1470,1426,1172,1014,1012]),
  ([39,49,71,132,162],[2533,1098,1427,1011,1012,1021]),
  ([39,49,71,132,162,197],[787,1040]),
  ([39,49,71,133,135,162],[1946,1471,1428,1172,1014,1013]),
  ([39,49,71,133,162],[1100,1934,1429,1011,1013,1021]),
  ([39,49,71,133,162,198],[707,1041]),
  ([39,49,71,135,139],[1109,1011,1014,1015]),
  ([39,49,71,135,139,140],[1016]),
  ([39,49,71,135,139,162],[1021,1015]),
  ([39,49,71,135,139,361],[1083]),
  ([39,49,71,135,140,309],[972]),
  ([39,49,71,135,140,317],[994]),
  ([39,49,71,135,140,323],[998]),
  ([39,49,71,135,140,331],[1002]),
  ([39,49,71,135,140,361],[1102]),
  ([39,49,71,135,140,378],[834,1472,1431,1105]),
  ([39,49,71,135,143],[422,2318,2535,1159,1158,1149,1011,1014,1017]),
  ([39,49,71,135,143,162],[2545,1559,1021,1017]),
  ([39,49,71,135,143,173],[1026]),
  ([39,49,71,135,148],[388,1163,1723,1936,1162,1150,1011,1014,1018]),
  ([39,49,71,135,148,162],[1946,1561,1021,1018]),
  ([39,49,71,135,148,182],[1030])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b53ok : f5b53.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b54 : Array Row := #[
  ([39,49,71,135,153],[138,1272,1164,248,1280,1165,817,1434,1551,1148,1449,1011,1014,1019]),
  ([39,49,71,135,153,156],[1456,1020]),
  ([39,49,71,135,153,162],[1469,1021,1019]),
  ([39,49,71,135,153,378],[1092]),
  ([39,49,71,135,156,309],[972]),
  ([39,49,71,135,156,317],[994]),
  ([39,49,71,135,156,323],[998]),
  ([39,49,71,135,156,331],[2613,2014,1002]),
  ([39,49,71,135,156,361],[1102]),
  ([39,49,71,135,156,378],[1434,1105]),
  ([39,49,71,135,162,163],[1022,1097]),
  ([39,49,71,135,162,164],[1023,1099]),
  ([39,49,71,135,162,165],[1024]),
  ([39,49,71,135,162,177],[1028,1103]),
  ([39,49,71,135,162,186],[1032,1104]),
  ([39,49,71,135,162,190],[776,1034,1106]),
  ([39,49,71,135,162,193],[696,1036,1107]),
  ([39,49,71,135,162,195],[539,1572,865,1038,1108]),
  ([39,49,71,135,162,196],[708,788,1039,1021]),
  ([39,49,71,135,162,197],[788,1040,1097]),
  ([39,49,71,135,162,198],[708,1041,1099]),
  ([39,49,71,135,162,200],[1042,1101]),
  ([39,49,71,135,162,201],[793,1043]),
  ([39,49,71,135,162,202],[715,1044]),
  ([39,49,71,135,162,241],[1045]),
  ([39,49,71,135,162,242],[1046]),
  ([39,49,71,135,162,243],[1047]),
  ([39,49,71,135,162,244],[1048]),
  ([39,49,71,135,162,250],[1049]),
  ([39,49,71,135,162,251],[1050]),
  ([39,49,71,135,162,252],[1051]),
  ([39,49,71,135,162,253],[1052])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b54ok : f5b54.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b55 : Array Row := #[
  ([39,49,71,135,162,257],[540,185,2237,2063,1053]),
  ([39,49,71,135,162,260],[541,2658,277,1638,1054]),
  ([39,49,71,135,162,263],[542,1055]),
  ([39,49,71,135,162,264],[543,1056]),
  ([39,49,71,135,162,274],[1057]),
  ([39,49,71,135,162,275],[1262,1058]),
  ([39,49,71,135,162,276],[1263,1059]),
  ([39,49,71,135,162,278],[1060]),
  ([39,49,71,135,162,280],[1061]),
  ([39,49,71,135,162,285],[2303,1062]),
  ([39,49,71,135,162,289],[1704,1063]),
  ([39,49,71,135,162,293],[2806,186,278,1267,1064]),
  ([39,49,71,135,162,309],[1065,972]),
  ([39,49,71,135,162,310],[1066]),
  ([39,49,71,135,162,311],[1067]),
  ([39,49,71,135,162,317],[1068,994]),
  ([39,49,71,135,162,323],[1069,998]),
  ([39,49,71,135,162,331],[1070,1002]),
  ([39,49,71,135,162,336],[2488,1071]),
  ([39,49,71,135,162,343],[1895,1072]),
  ([39,49,71,135,162,351],[1573,1076]),
  ([39,49,71,135,162,353],[1078]),
  ([39,49,71,135,162,355],[1574,1080]),
  ([39,49,71,135,162,358],[1575,1082]),
  ([39,49,71,135,162,361],[1083,1102]),
  ([39,49,71,135,162,365],[2659,1576,1085,1156]),
  ([39,49,71,135,162,368],[1577,1087]),
  ([39,49,71,135,162,371],[2064,1578,1089,1160]),
  ([39,49,71,135,162,374],[1579,1091]),
  ([39,49,71,135,162,378],[1435,1092,1105]),
  ([39,49,71,135,162,386],[1580,1094,1168]),
  ([39,49,71,135,162,392],[2537,1581,1095])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b55ok : f5b55.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b56 : Array Row := #[
  ([39,49,71,135,162,396],[1938,1582,1096]),
  ([39,49,71,135,173,309],[972]),
  ([39,49,71,135,173,317],[994]),
  ([39,49,71,135,173,323],[998]),
  ([39,49,71,135,173,331],[2485,2026,1002]),
  ([39,49,71,135,173,361],[1102]),
  ([39,49,71,135,173,369],[1103]),
  ([39,49,71,135,173,378],[2660,819,1583,841,1478,1437,1164,1105]),
  ([39,49,71,135,173,381],[1584,842,1106]),
  ([39,49,71,135,182,309],[972]),
  ([39,49,71,135,182,317],[994]),
  ([39,49,71,135,182,323],[998]),
  ([39,49,71,135,182,331],[2625,1886,1002]),
  ([39,49,71,135,182,361],[1102]),
  ([39,49,71,135,182,375],[1104]),
  ([39,49,71,135,182,378],[2065,820,1585,850,1480,1438,1165,1105]),
  ([39,49,71,135,182,382],[1586,851,1107]),
  ([39,49,71,135,196],[2546,709,1947,789,1455,1011,1014,1039]),
  ([39,49,71,135,197,198],[1098,1100,1110]),
  ([39,49,71,135,241,309],[2434,972]),
  ([39,49,71,135,241,317],[2483,994]),
  ([39,49,71,135,241,331],[2486,1002]),
  ([39,49,71,135,243,309],[972]),
  ([39,49,71,135,244,309],[972]),
  ([39,49,71,135,250,309],[1835,972]),
  ([39,49,71,135,250,323],[1885,998]),
  ([39,49,71,135,250,331],[1887,1002]),
  ([39,49,71,135,252,309],[972]),
  ([39,49,71,135,253,309],[972]),
  ([39,49,71,135,257,323],[545,2238,2484,998]),
  ([39,49,71,135,260,317],[547,1639,1884,994]),
  ([39,49,71,135,274,309],[1343,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b56ok : f5b56.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b57 : Array Row := #[
  ([39,49,71,135,274,317],[1379,994]),
  ([39,49,71,135,274,323],[1380,998]),
  ([39,49,71,135,274,361],[1430,1102]),
  ([39,49,71,135,278,309],[972]),
  ([39,49,71,135,280,309],[972]),
  ([39,49,71,135,285,361],[2304,2534,1102]),
  ([39,49,71,135,289,361],[1705,1935,1102]),
  ([39,49,71,135,293,331],[2807,189,281,1269,1381,1002]),
  ([39,49,71,135,300],[1183,881,1193,881,806,881,881]),
  ([39,49,71,135,303],[1184,934,1194,934,934,934]),
  ([39,49,71,135,304],[945,1195,945,945,945]),
  ([39,49,71,135,306],[1185,956,956,956,956]),
  ([39,49,71,135,309],[972,972,972,972]),
  ([39,49,71,135,309,336],[2441,2489,972]),
  ([39,49,71,135,309,343],[1842,1896,972]),
  ([39,49,71,135,309,351],[982,972]),
  ([39,49,71,135,309,353],[972]),
  ([39,49,71,135,309,355],[972]),
  ([39,49,71,135,309,358],[972]),
  ([39,49,71,135,309,378],[1345,1445,972,1105]),
  ([39,49,71,135,313],[423,2319,1186,992,1196,992,807,992,992]),
  ([39,49,71,135,317],[994,994,994,994]),
  ([39,49,71,135,317,365],[995,1157,994]),
  ([39,49,71,135,319],[389,1187,996,1724,1197,996,808,996,996]),
  ([39,49,71,135,323],[998,998,998,998]),
  ([39,49,71,135,323,371],[999,1161,998]),
  ([39,49,71,135,326],[1000,1000,1000,1000]),
  ([39,49,71,135,327],[2808,1644,2243,169,2626,1188,2547,1001,261,2030,1198,1948,1001,809,1001,1001]),
  ([39,49,71,135,331],[2549,1002,1950,1002,1002,1002]),
  ([39,49,71,135,331,386],[2809,2627,2031,1003,1182,1002]),
  ([39,49,71,135,336,343],[549,2810,2628,2490,2496,2032,1888,1897]),
  ([39,49,71,135,336,378],[190,2661,2629,2491,2536,822,1382,1446,1105])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b57ok : f5b57.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b58 : Array Row := #[
  ([39,49,71,135,340],[2550,1004,1951,1004,1004,1004]),
  ([39,49,71,135,343,378],[282,2066,2033,1898,1937,823,1389,1447,1105]),
  ([39,49,71,135,347],[2551,1007,1952,1007,1007,1007]),
  ([39,49,71,135,348],[21,1189,1014,38,1199,1014,810,1167,1014,1011,1014,1073]),
  ([39,49,71,135,351,361],[1154,1102]),
  ([39,49,71,135,351,378],[825,1587,1448,1166,1105]),
  ([39,49,71,135,361],[1102,1102,1102,1102]),
  ([39,49,71,135,369],[1103,1103,1103,1103]),
  ([39,49,71,135,375],[1104,1104,1104,1104]),
  ([39,49,71,135,378],[139,1273,1191,1105,249,1281,1201,1105,818,1456,1433,1105,1449,1105]),
  ([39,49,71,135,381],[140,1106,1282,1202,1106,1457,1106,1106]),
  ([39,49,71,135,382],[1274,1192,1107,250,1107,1458,1107,1107]),
  ([39,49,71,156,162,173],[2662,1164,1156,1158]),
  ([39,49,71,156,162,182],[2067,1165,1160,1162]),
  ([39,49,71,162,173,182],[550,1159,1163,1168]),
  ([39,49,71,162,351],[1109,1109,1109,1109]),
  ([39,49,71,162,365],[424,2663,1275,2320,1156,251,1156,1156,1156]),
  ([39,49,71,162,371],[390,141,1160,2068,1283,1725,1160,1160,1160]),
  ([39,49,71,162,386],[1168,1168,1168,1168]),
  ([39,49,71,173,378],[426,142,2664,1276,2321,1164,252,1284,1203,1164,843,1602,1566,1164,1567,1164]),
  ([39,49,71,182,378],[392,143,1277,1203,1165,253,2069,1285,1726,1165,852,1610,1568,1165,1569,1165]),
  ([39,49,71,309,351],[982,1118,982,1118,982,1118,982,1118]),
  ([39,49,71,317,365],[427,2322,995,1157,995,1157,995,1157,995,1157]),
  ([39,49,71,323,371],[393,999,1161,1727,999,1161,999,1161,999,1161]),
  ([39,49,71,331,386],[2811,1645,2244,170,1003,1182,262,1003,1182,1003,1182,1003,1182]),
  ([39,49,71,348],[361,795,133,874,1011,1073,243,875,1011,1073,1011,1073]),
  ([39,49,71,351,361],[1141,1154,1141,1154,1141,1154,1141,1154]),
  ([39,49,71,351,378],[144,1278,1148,1166,254,1286,1148,1166,1551,1148,1544,1570,1166,1571,1148,1166]),
  ([39,49,81,83,103,135],[2812,755]),
  ([39,49,81,86,103,135],[2813,633]),
  ([39,49,81,103,135],[2814,1646,2245,633,2647,755,2048,1268,1264]),
  ([39,49,81,103,135,293],[2815,640,762,1482])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b58ok : f5b58.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b59 : Array Row := #[
  ([39,49,83,86,92,135],[2816,2649,2050,1264]),
  ([39,49,83,86,135,162],[2817,634,757,1267,1270]),
  ([39,49,83,92,135,378],[2661,2652,759,2056,5,1477,827,1290,1278,1272]),
  ([39,49,83,103,135,274],[760,972]),
  ([39,49,83,103,135,276],[]),
  ([39,49,83,103,135,280],[761]),
  ([39,49,83,103,135,293],[2818,762,1265]),
  ([39,49,83,103,135,378],[2656,763,96,1483,1341,1272]),
  ([39,49,83,135,156,162],[2662,204,765,1262,1272]),
  ([39,49,83,135,378],[2246,2664,1276,2660,1272,768,717,756,1287,1277,1272,828,1478,1433,1272,1449,1272]),
  ([39,49,86,92,135,378],[637,2668,2066,2057,5,1479,830,1290,1286,1280]),
  ([39,49,86,103,135,274],[638,972]),
  ([39,49,86,103,135,275],[]),
  ([39,49,86,103,135,278],[639]),
  ([39,49,86,103,135,293],[2819,640,1265]),
  ([39,49,86,103,135,378],[641,2061,119,1484,1341,1280]),
  ([39,49,86,135,156,162],[643,2067,301,1263,1280]),
  ([39,49,86,135,378],[1647,646,591,635,1287,1284,1280,2069,1285,2065,1280,831,1480,1433,1280,1449,1280]),
  ([39,49,92,103,135,153],[2696,2097,1445,1350,1345]),
  ([39,49,92,103,135,274],[2713,2114,1497,1357,972,881]),
  ([39,49,92,103,135,293],[2821,2716,2669,2117,2070,1515,1364,1265,1264]),
  ([39,49,92,103,135,378],[2719,2120,1530,1371,1341,1290]),
  ([39,49,92,103,173,378],[2726,2673,2126,1604,1348,1294]),
  ([39,49,92,103,182,378],[2727,2128,2074,1612,1349,1295]),
  ([39,49,92,103,351,378],[2734,2135,1623,1345,1350,1293,1296]),
  ([39,49,92,120,135,378],[2739,2673,2137,1388,1384,1290]),
  ([39,49,92,125,135,378],[2742,2141,2074,1395,1391,1290]),
  ([39,49,92,135,140,378],[2747,2148,1557,1431,1290]),
  ([39,49,92,135,153],[4,2748,1446,2674,1294,4,2149,1447,2075,1295,1570,1296,1448,1551,1293,1449,1288]),
  ([39,49,92,135,153,378],[2749,2150,1571,1289]),
  ([39,49,92,135,156,162],[2753,2154,1573,1290]),
  ([39,49,92,135,156,378],[2755,2156,1587,1434,1290])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b59ok : f5b59.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b60 : Array Row := #[
  ([39,49,92,135,162,378],[2762,2163,1596,1435,1289,1290]),
  ([39,49,92,135,173,378],[2765,2165,1607,1437,1294,1290]),
  ([39,49,92,135,182,378],[2766,2167,1615,1438,1295,1290]),
  ([39,49,92,135,274],[2682,1297,881,2083,1300,881,1307,881,881]),
  ([39,49,92,135,293],[2822,1648,2247,2684,2686,1298,2675,1264,2085,2088,1301,2076,1264,1312,1264,1264]),
  ([39,49,92,135,309,378],[2774,2175,1623,1345,1445,1290]),
  ([39,49,92,135,336,378],[18,2687,2672,2674,2176,1624,1382,1446,1290]),
  ([39,49,92,135,343,378],[2775,13,2089,2073,2075,1625,1389,1447,1290]),
  ([39,49,92,135,351,378],[2776,2177,1448,1296,1290]),
  ([39,49,92,135,378],[5,2777,1539,2685,1299,1290,5,2178,1541,2086,1302,1290,1627,1315,1544,1433,1290,1449,1290]),
  ([39,49,92,173,378],[430,6,2782,1605,2687,1294,6,2183,1606,2087,1303,1294,1566,1294,1567,1294]),
  ([39,49,92,182,378],[396,7,2783,1613,2688,1303,1295,7,2184,1614,2089,1295,1568,1295,1569,1295]),
  ([39,49,92,351,378],[8,2784,1624,2691,1293,1296,8,2185,1625,2092,1293,1296,1551,1293,1544,1570,1296,1571,1293,1296]),
  ([39,49,96,103,135,378],[1530,1341,1323]),
  ([39,49,96,135,156,162],[1323]),
  ([39,49,96,135,156,378],[1434,1323]),
  ([39,49,96,135,378],[5,1540,1327,1323,5,1542,1328,1323,1293,1545,1433,1323,1449,1323]),
  ([39,49,103,120,135,274],[972]),
  ([39,49,103,120,135,293],[2823,1265]),
  ([39,49,103,120,135,378],[2694,1384,1341]),
  ([39,49,103,125,135,274],[972]),
  ([39,49,103,125,135,293],[2824,1265]),
  ([39,49,103,125,135,378],[2095,1391,1341]),
  ([39,49,103,131,135,378],[2720,2121,1293,1548,1289,1402,1398,1371,1341,1337]),
  ([39,49,103,131,156,162],[2721,2122,1337]),
  ([39,49,103,131,162,378],[2723,2124,1405,1337]),
  ([39,49,103,131,378],[76,1383,2735,1377,2695,1337,99,1390,2136,1378,2096,1337,1289,1422,1403,1337,1406,1337]),
  ([39,49,103,135,140,274],[972]),
  ([39,49,103,135,140,293],[2826,1265]),
  ([39,49,103,135,140,378],[1431,1341]),
  ([39,49,103,135,153],[77,1384,1348,100,1391,1349,1290,1431,1323,1435,1337]),
  ([39,49,103,135,153,156],[1454,1323,1436])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b60ok : f5b60.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b61 : Array Row := #[
  ([39,49,103,135,153,162],[1337]),
  ([39,49,103,135,153,378],[1326,1469,1340]),
  ([39,49,103,135,156,274],[1324,972]),
  ([39,49,103,135,156,278],[]),
  ([39,49,103,135,156,280],[]),
  ([39,49,103,135,156,293],[2827,2722,205,2123,302,1325,1265]),
  ([39,49,103,135,156,378],[1326,1472,1434,1341]),
  ([39,49,103,135,162,274],[1109,1338,972]),
  ([39,49,103,135,162,275],[1262]),
  ([39,49,103,135,162,276],[1263]),
  ([39,49,103,135,162,293],[2828,219,315,1267,1339,1265]),
  ([39,49,103,135,162,378],[1435,1340,1341]),
  ([39,49,103,135,173,274],[1297,1329,972]),
  ([39,49,103,135,173,293],[2829,2647,2125,2099,1298,1330,1265]),
  ([39,49,103,135,173,378],[2738,1299,1555,1331,1474,1437,1348,1341]),
  ([39,49,103,135,182,274],[1300,1333,972]),
  ([39,49,103,135,182,293],[2830,2724,2698,2048,1301,1334,1265]),
  ([39,49,103,135,182,378],[2140,1302,1556,1335,1476,1438,1349,1341]),
  ([39,49,103,135,241,274],[2434,972]),
  ([39,49,103,135,241,293],[2832,2648,1265]),
  ([39,49,103,135,243,274],[972]),
  ([39,49,103,135,250,274],[1835,972]),
  ([39,49,103,135,250,293],[2833,2049,1265]),
  ([39,49,103,135,252,274],[972]),
  ([39,49,103,135,257,274],[553,2239,2436,972]),
  ([39,49,103,135,260,274],[555,1640,1837,972]),
  ([39,49,103,135,274],[972,972,1291,972,972]),
  ([39,49,103,135,274,285],[2438,2646,1304,972]),
  ([39,49,103,135,274,289],[1839,2047,1305,972]),
  ([39,49,103,135,274,309],[1118,972]),
  ([39,49,103,135,274,317],[1122,1379,972]),
  ([39,49,103,135,274,323],[1126,1380,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b61ok : f5b61.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b62 : Array Row := #[
  ([39,49,103,135,274,351],[1307,982,972]),
  ([39,49,103,135,274,353],[972]),
  ([39,49,103,135,274,361],[1141,1430,972]),
  ([39,49,103,135,274,365],[1308,984,1346,972]),
  ([39,49,103,135,274,371],[1309,986,1347,972]),
  ([39,49,103,135,293],[2834,1649,2248,2697,1265,2098,1265,1292,1265,1265]),
  ([39,49,103,135,293,331],[2835,1269,1381,1265]),
  ([39,49,103,135,293,386],[2836,2725,2127,1313,1266,1352,1265]),
  ([39,49,103,135,309,378],[1445,1341]),
  ([39,49,103,135,336,378],[90,2739,2726,2693,2696,1382,1446,1341]),
  ([39,49,103,135,343,378],[110,2141,2128,2094,2097,1389,1447,1341]),
  ([39,49,103,135,351,378],[1315,1557,1448,1350,1341]),
  ([39,49,103,135,378],[78,1385,1353,1341,101,1392,1354,1341,1293,1432,1433,1341,1449,1341]),
  ([39,49,103,156,162,173],[2740,1348]),
  ([39,49,103,156,162,182],[2142,1349]),
  ([39,49,103,173,378],[431,79,2741,1386,2694,1348,102,1393,1355,1348,1332,1600,1566,1348,1567,1348]),
  ([39,49,103,182,378],[397,80,1387,1355,1349,103,2143,1394,2095,1349,1336,1609,1568,1349,1569,1349]),
  ([39,49,103,274,351],[982,1343,982,1343,982,1343,982,1343]),
  ([39,49,103,274,365],[432,984,1346,984,1346,984,1346,984,1346]),
  ([39,49,103,274,371],[398,986,1347,986,1347,986,1347,986,1347]),
  ([39,49,103,293,386],[2837,1650,2249,1266,1352,1266,1352,1266,1352,1266,1352]),
  ([39,49,103,351,378],[81,1388,1345,1350,104,1395,1345,1350,1551,1345,1544,1570,1350,1571,1345,1350]),
  ([39,49,120,135,156,162],[2740,1384]),
  ([39,49,120,135,378],[2741,1386,2738,1384,584,1397,1387,1384,1321,1474,1433,1384,1449,1384]),
  ([39,49,125,135,156,162],[2142,1391]),
  ([39,49,125,135,378],[577,1397,1393,1391,2143,1394,2140,1391,1322,1476,1433,1391,1449,1391]),
  ([39,49,131,135,156,162],[2754,2155,1573,1398]),
  ([39,49,131,135,162,378],[2763,2164,1596,1435,1414,1405,1398]),
  ([39,49,131,135,378],[5,2778,1553,2743,22,1415,1398,5,2179,1554,2144,39,1416,1398,1627,1421,1544,1433,1398,1449,1403,1398,1406]),
  ([39,49,131,156,162],[2780,1581,2744,2181,1582,2145,1403,1404,1405]),
  ([39,49,131,162,378],[2781,1598,2745,210,1417,1405,2182,1599,2146,309,1418,1405,1405,1403,1405,1406]),
  ([39,49,131,378],[364,796,3,2785,1633,2746,1424,1403,1406,3,2186,1634,2147,1425,1403,1406,1403,1406])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b62ok : f5b62.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b63 : Array Row := #[
  ([39,49,135,140,156,162],[1431]),
  ([39,49,135,140,378],[1555,94,1474,1431,1556,117,1476,1431,1431,1433,1431,1449]),
  ([39,49,135,153],[365,797,23,1566,1437,138,1439,40,1568,1438,248,1441,1403,1398,1434]),
  ([39,49,135,153,156],[1562,201,1440,1563,299,1442,1404]),
  ([39,49,135,153,156,162],[1407,1404,1436]),
  ([39,49,135,153,162],[1564,211,1443,1565,310,1444,1405,1454,1403,1398,1405,1436]),
  ([39,49,135,153,378],[1567,139,1477,1569,249,1479,1423,1401,1406,1456]),
  ([39,49,135,156,162,165],[1436]),
  ([39,49,135,156,162,173],[1437]),
  ([39,49,135,156,162,182],[1438]),
  ([39,49,135,156,162,190],[777,1440,1452]),
  ([39,49,135,156,162,193],[697,1442,1453]),
  ([39,49,135,156,162,197],[2779,791,1426,1443,1450]),
  ([39,49,135,156,162,198],[711,2180,1428,1444,1451]),
  ([39,49,135,156,378],[1583,202,1478,1434,1585,300,1480,1434,1434,1433,1434,1449]),
  ([39,49,135,162,274],[1109,1109,1419,1399,1409,1109,1109]),
  ([39,49,135,162,275],[1262,1262,1410,1262,1262]),
  ([39,49,135,162,276],[1263,1263,1411,1263,1263]),
  ([39,49,135,162,293],[2838,1651,2250,2756,220,1267,2157,316,1267,1420,1400,1412,1267,1267]),
  ([39,49,135,162,378],[1588,212,1483,1435,1589,311,1484,1435,1423,1401,1413,1472,1435,1433,1435,1449]),
  ([39,49,135,173,378],[434,25,1437,42,1601,568,1481,1437,1566,1437,1567,1433,1437,1449]),
  ([39,49,135,182,378],[400,26,1601,559,1481,1438,43,1438,1568,1438,1569,1433,1438,1449]),
  ([39,49,135,274,309],[1118,1343,1118,1343,1118,1343,1118,1343]),
  ([39,49,135,274,317],[1122,1379,1122,1379,1122,1379,1122,1379]),
  ([39,49,135,274,323],[1126,1380,1126,1380,1126,1380,1126,1380]),
  ([39,49,135,274,361],[1141,1430,1141,1430,1141,1430,1141,1430]),
  ([39,49,135,293,331],[2839,1652,2251,2764,1269,1381,2166,1269,1381,1269,1381,1269,1381]),
  ([39,49,135,309,378],[1604,1345,1445,1612,1345,1445,1345,1445,1345,1433,1445,1449]),
  ([39,49,135,336,378],[436,2252,35,2782,1605,2765,2737,1382,2736,2748,1446,2749,1613,1382,1446,1382,1446,1382,1433,1446,1449]),
  ([39,49,135,343,378],[402,1653,1606,1389,1447,49,2184,1614,2167,2139,1389,2138,2149,1447,2150,1389,1447,1389,1433,1447,1449]),
  ([39,49,135,351,378],[27,1607,1448,44,1615,1448,1570,1448,1571,1433,1448,1449]),
  ([39,49,135,378],[366,798,24,1608,1473,1433,1449,41,1616,1475,1433,1449,1433,1449])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b63ok : f5b63.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b64 : Array Row := #[
  ([39,49,156,162,173],[437,2779,1572,1566,1562,1564,1558,1559]),
  ([39,49,156,162,182],[403,1572,2180,1568,1563,1565,1560,1561]),
  ([39,49,173,378],[438,367,800,1566,1567,569,1617,1603,1566,1567,1566,1567]),
  ([39,49,182,378],[404,368,801,560,1617,1611,1568,1569,1568,1569,1568,1569]),
  ([39,49,351,378],[369,803,1551,1544,1570,1571,1551,1544,1570,1571,1551,1544,1570,1571]),
  ([39,55,56,71,103,135],[649]),
  ([39,55,71,86,103,135],[2791,647]),
  ([39,55,71,103,135],[647,2789,1638,1635]),
  ([39,55,71,103,135,260],[674]),
  ([39,56,71,86,92,135],[2816,648,1635,1712,1647]),
  ([39,56,71,86,135,162],[2817,651,345,1638,1641]),
  ([39,56,71,92,135,343],[2810,1768,1732,1653]),
  ([39,56,71,103,135,250],[972]),
  ([39,56,71,103,135,252],[]),
  ([39,56,71,103,135,260],[1636]),
  ([39,56,71,103,135,289],[1702,1642]),
  ([39,56,71,103,135,293],[191,2818,2793,346,1651,1646]),
  ([39,56,71,103,135,343],[1820]),
  ([39,56,83,86,103,135],[1646]),
  ([39,56,103,135,293],[91,2823,36,2829,2814,1646,2815,2099,1646,1648,1646,1646]),
  ([39,58,71,79,103,135],[2852,2047,1839,1705,1703,1654]),
  ([39,58,71,92,103,289],[2873,2071,1866,9,1784,1697,1654]),
  ([39,58,71,92,103,343],[2874,2844,1874,1670,1655]),
  ([39,58,71,92,135,289],[2887,2082,1984,1783,1698,1671,1654]),
  ([39,58,71,92,135,343],[2888,2845,2083,2005,1788,1732,1672,1655]),
  ([39,58,71,92,289],[9,2893,1776,2840,2842,1654,2090,1666,1775,9,2037,1662,1782,1696,1654,1700,1668,1654,1654]),
  ([39,58,71,92,343],[2894,1777,2841,2846,1663,2843,1655,1667,2041,1664,1787,1655,1673,1665,1669,1655,1655]),
  ([39,58,71,103,135,250],[2915,2102,1968,1853,972,1656]),
  ([39,58,71,103,135,260],[2923,2847,2108,1978,1860,1636,1657]),
  ([39,58,71,103,135,289],[2926,2112,1985,1867,1702,1658]),
  ([39,58,71,103,135,343],[2928,2114,2006,1875,1820,1659]),
  ([39,58,71,103,289,351],[2941,2132,2038,1703,1839])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b64ok : f5b64.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b65 : Array Row := #[
  ([39,58,71,135,162,289],[2963,2162,2021,1704,1660]),
  ([39,58,71,135,289,361],[2974,2173,2038,1705,1935]),
  ([39,58,103,135,274,289],[3014,2173,2132,1839,2047,1666]),
  ([39,60,71,103,135,289],[1867,1702,1675]),
  ([39,65,71,103,135,298],[2927,2849,2113,1988,1873,1710,1677]),
  ([39,67,71,86,103,135],[2867,654,1718,1689,1679]),
  ([39,67,71,103,135,289],[2929,2112,1986,1869,1702,1680]),
  ([39,67,86,103,135],[3000,2059,2850,656,592,655,1690,1688,1682,1683,1684]),
  ([39,67,86,103,135,182],[2997,657,1685,1686]),
  ([39,71,79,86,103,135],[658,1687,1695]),
  ([39,71,79,103,135],[1704,1696,1697,1698]),
  ([39,71,79,103,135,182],[1699,1701]),
  ([39,71,79,103,135,289],[1700]),
  ([39,71,83,92,135,343],[2862,2854,2056,1953,1674,1732]),
  ([39,71,83,103,135,250],[972]),
  ([39,71,83,103,135,260],[2789,2055,1636]),
  ([39,71,83,103,135,289],[195,1702,1706]),
  ([39,71,83,103,135,343],[2858,1955,1820]),
  ([39,71,86,92,103,182],[661,2868,2061,1683,1758,1697]),
  ([39,71,86,92,135,182],[662,2065,1684,1698]),
  ([39,71,86,92,135,343],[664,2872,2066,1676,1732]),
  ([39,71,86,92,182],[2050,665,593,659,2864,1712,2069,1726,2057,1682,1679,1685,1757,1696,1695,1699]),
  ([39,71,86,99,135,182],[666,1686,1701,1711]),
  ([39,71,86,103,135,195],[2986,668,1693,1710,1712]),
  ([39,71,86,103,135,250],[669,972]),
  ([39,71,86,103,135,251],[670]),
  ([39,71,86,103,135,253],[671]),
  ([39,71,86,103,135,257],[2987,673,2786,2063]),
  ([39,71,86,103,135,260],[2988,674,1636]),
  ([39,71,86,103,135,289],[675,1702,1713]),
  ([39,71,86,103,135,343],[676,1820]),
  ([39,71,86,103,135,371],[677,2064,1714,1717])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b65ok : f5b65.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b66 : Array Row := #[
  ([39,71,86,103,156,182],[678,2067,1715,1717]),
  ([39,71,86,103,173,182],[2989,679,1716]),
  ([39,71,86,103,371],[2051,682,594,660,1717,2068,1725,2060,1717,1717,1717]),
  ([39,71,86,135,162,182],[683,2067,1689,1704,1721,1723]),
  ([39,71,92,103,123,135],[2899,2094,1896,1842,1822]),
  ([39,71,92,103,125,182],[2900,2095]),
  ([39,71,92,103,135,250],[2916,2104,1961,1853,972,881]),
  ([39,71,92,103,135,260],[2925,2111,1971,1860,1636,1635]),
  ([39,71,92,103,135,289],[2930,2116,1980,1867,1702,1748,1698,1697]),
  ([39,71,92,103,135,343],[2931,2120,1994,1875,1820,1732]),
  ([39,71,92,103,173,343],[2936,2877,2126,2027,1821,1733]),
  ([39,71,92,103,182,343],[2937,2128,1734]),
  ([39,71,92,103,289],[2875,83,1731,1697,2072,66,1750,1697,1779,1697,1696,1697,1700]),
  ([39,71,92,103,343,351],[2942,2135,2039,1822,1842,1735,1746]),
  ([39,71,92,120,135,343],[2948,2877,2137,1894,1889,1732]),
  ([39,71,92,123,135],[2950,1897,2878,1733,2139,1898,2073,1655,1746,1735,1734]),
  ([39,71,92,123,135,343],[2951,2138,1767]),
  ([39,71,92,125,135,182],[2952,2140,1732]),
  ([39,71,92,125,135,343],[2953,2141,1732]),
  ([39,71,92,125,182],[2954,1901,2879,578,2143,1902,2074,1758,1734]),
  ([39,71,92,135,140,343],[2958,2148,1732]),
  ([39,71,92,135,156,343],[2959,2156,1732]),
  ([39,71,92,135,162,343],[2964,2163,2022,1895,1738,1732]),
  ([39,71,92,135,173,343],[2968,2165,1733,1732]),
  ([39,71,92,135,182,343],[2970,2167,1734,1732]),
  ([39,71,92,135,250],[2884,1752,881,2170,1969,2079,1656,881,1769,881,881]),
  ([39,71,92,135,260],[2853,2886,1753,1635,2172,1979,2081,1657,1635,1773,1635,1635]),
  ([39,71,92,135,289],[2889,28,1754,1698,2174,1987,2084,1658,1749,1698,1783,1698,1696,1698,1700]),
  ([39,71,92,135,309,343],[2975,2175,2039,1842,1896,1732]),
  ([39,71,92,135,336,343],[20,2891,2876,2878,2176,2040,1888,1897,1732]),
  ([39,71,92,135,343],[2976,2002,2890,1756,1732,2178,2007,2086,1659,1732,1788,1732,1732]),
  ([39,71,92,135,343,351],[2977,2177,1735,1732])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b66ok : f5b66.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b67 : Array Row := #[
  ([39,71,92,135,343,378],[2978,13,1669,2073,2075,2042,1898,1937,1732]),
  ([39,71,92,173,343],[2854,2982,2028,2891,1733,2183,2029,2087,1678,1733,1733,1733]),
  ([39,71,92,182,343],[2983,2032,2892,1768,1734,2184,2033,2089,1681,1734,1734,1734]),
  ([39,71,92,289],[146,1706,9,2895,1780,1696,1700,9,2091,1785,1696,1700,1696,1700]),
  ([39,71,92,343,351],[2984,2040,2896,1735,1746,2185,2042,2092,1735,1746,1735,1746,1735,1746]),
  ([39,71,94,103,125,182],[1736]),
  ([39,71,94,103,135,343],[1746,1875,1820]),
  ([39,71,99,103,135,343],[1994,1820,1813]),
  ([39,71,99,125,135,182],[1736,1813]),
  ([39,71,99,135,182,343],[1767,1813]),
  ([39,71,99,135,343],[2003,1818,1813,2008,1813,1746,1813,1813]),
  ([39,71,103,120,135,250],[972]),
  ([39,71,103,120,135,260],[1636]),
  ([39,71,103,120,135,289],[1731,1795,1702]),
  ([39,71,103,120,135,343],[2898,1889,1820]),
  ([39,71,103,123,125,135],[]),
  ([39,71,103,123,135],[1889,1821,1895,1813,1732]),
  ([39,71,103,123,135,182],[1734,1813]),
  ([39,71,103,123,135,343],[1817]),
  ([39,71,103,125,135,250],[972]),
  ([39,71,103,125,135,251],[]),
  ([39,71,103,125,135,260],[581,1636]),
  ([39,71,103,125,135,289],[1737,1798,1702]),
  ([39,71,103,125,135,343],[1820]),
  ([39,71,103,125,156,182],[2142,1799]),
  ([39,71,103,125,173,182],[2946,582,1805,1819,1821]),
  ([39,71,103,131,135,396],[2932,2121,1747,2010,1739,1909,1903,1881,1831,1824]),
  ([39,71,103,131,162,396],[2933,2124,1751,1911,1824]),
  ([39,71,103,131,396],[84,1890,2943,1883,2901,1824,67,1916,2136,1882,2096,1824,1794,1730,1739,1930,1919,1824,1920,1824]),
  ([39,71,103,135,140,250],[972]),
  ([39,71,103,135,140,260],[1636]),
  ([39,71,103,135,140,289],[1748,1702])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b67ok : f5b67.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b68 : Array Row := #[
  ([39,71,103,135,140,343],[1820]),
  ([39,71,103,135,156,250],[2151,1800,972]),
  ([39,71,103,135,156,260],[2152,1801,1636]),
  ([39,71,103,135,156,289],[2153,1749,1802,1702]),
  ([39,71,103,135,156,343],[2154,1803,1820]),
  ([39,71,103,135,162,250],[1109,1825,972]),
  ([39,71,103,135,162,260],[2990,1638,1826,1636]),
  ([39,71,103,135,162,289],[1750,1704,1827,1702]),
  ([39,71,103,135,162,343],[1895,1828,1820]),
  ([39,71,103,135,162,396],[2122,1751,1938,1829,1831]),
  ([39,71,103,135,173,250],[1752,1806,972]),
  ([39,71,103,135,173,260],[1753,1807,1636]),
  ([39,71,103,135,173,289],[1754,1808,1702]),
  ([39,71,103,135,173,298],[2991,1755,1809,1710]),
  ([39,71,103,135,173,343],[2947,1756,1810,1821,1820]),
  ([39,71,103,135,182,198],[712,1758,1831]),
  ([39,71,103,135,182,250],[1759,1814,972]),
  ([39,71,103,135,182,252],[1760]),
  ([39,71,103,135,182,253],[1761]),
  ([39,71,103,135,182,260],[566,1691,1762,1815,1636]),
  ([39,71,103,135,182,289],[1763,1816,1702]),
  ([39,71,103,135,182,293],[197,2934,2904,2157,2123,1692,2048,1764]),
  ([39,71,103,135,182,331],[2935,1766,1886]),
  ([39,71,103,135,182,343],[1767,1817,1820]),
  ([39,71,103,135,241,250],[2434,972]),
  ([39,71,103,135,241,260],[2790,1636]),
  ([39,71,103,135,242,250],[972]),
  ([39,71,103,135,244,250],[972]),
  ([39,71,103,135,247],[192,2902,733,1939,733,1740,733,733]),
  ([39,71,103,135,250],[972,1941,972,1741,972,972]),
  ([39,71,103,135,250,257],[2436,2787,972]),
  ([39,71,103,135,250,274],[2158,1343,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b68ok : f5b68.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b69 : Array Row := #[
  ([39,71,103,135,250,276],[2159,972]),
  ([39,71,103,135,250,280],[972]),
  ([39,71,103,135,250,293],[198,2160,1344,2049,972]),
  ([39,71,103,135,250,309],[1118,972]),
  ([39,71,103,135,250,311],[972]),
  ([39,71,103,135,250,323],[1126,1885,972]),
  ([39,71,103,135,250,331],[1132,1887,972]),
  ([39,71,103,135,250,351],[1769,982,972]),
  ([39,71,103,135,250,358],[1770,972]),
  ([39,71,103,135,250,371],[1771,986,1845,972]),
  ([39,71,103,135,250,386],[1772,989,1847,972]),
  ([39,71,103,135,260],[2856,1636,1942,1636,1742,1636,1636]),
  ([39,71,103,135,260,274],[2993,2161,1640,1636]),
  ([39,71,103,135,260,317],[1639,1884,1636]),
  ([39,71,103,135,260,365],[1774,1637,1844,1636]),
  ([39,71,103,135,274,289],[2162,2047,1775,1702]),
  ([39,71,103,135,285,289],[2851,2852,1776,1702]),
  ([39,71,103,135,289],[1702,1943,1702,1778,1728,1743,1702,1702]),
  ([39,71,103,135,289,351],[1783,1703,1702]),
  ([39,71,103,135,289,361],[1784,1705,1935,1702]),
  ([39,71,103,135,298],[2994,2053,2857,1710,1944,1710,1786,1729,1744,1710,1710]),
  ([39,71,103,135,309,343],[1896,1820]),
  ([39,71,103,135,336,343],[92,2948,2936,2897,2899,1888,1897,1820]),
  ([39,71,103,135,343],[1891,1848,1820,1945,1820,1746,1820,1820]),
  ([39,71,103,135,343,351],[1788,1822,1820]),
  ([39,71,103,135,343,378],[68,2163,1670,2094,2097,1898,1937,1820]),
  ([39,71,103,135,396],[1892,1849,1831,1946,1846,1831,1794,1730,1747,1831,1831]),
  ([39,71,103,173,343],[2858,2949,1893,2898,1821,2015,1821,1811,1821,1821]),
  ([39,71,103,250,351],[982,1835,2017,982,1835,982,1835,982,1835]),
  ([39,71,103,250,371],[986,1845,2018,986,1845,986,1845,986,1845]),
  ([39,71,103,250,386],[989,1847,2019,989,1847,989,1847,989,1847]),
  ([39,71,103,260,365],[2859,1637,1844,2020,1637,1844,1637,1844,1637,1844])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b69ok : f5b69.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b70 : Array Row := #[
  ([39,71,103,289,351],[1703,1839,2021,1703,1839,1703,1839,1703,1839]),
  ([39,71,103,343,351],[1894,1822,1842,2022,1822,1842,1822,1842,1822,1842]),
  ([39,71,120,125,135,182],[2946,1886,1796,1889]),
  ([39,71,120,135,343],[2949,1893,2947,1889,1955,1889,1797,1889,1889]),
  ([39,71,125,135,162,182],[2142,1895,1899]),
  ([39,71,131,135,162,396],[2965,2164,2145,2023,1938,1917,1911,1903]),
  ([39,71,131,135,396],[2979,2012,2955,29,1918,1903,2179,2011,2144,1661,1910,1903,1929,1903,1919,1903,1920]),
  ([39,71,131,162,396],[2980,2025,2956,213,1923,1911,2182,2024,2146,1911,1911,1919,1911,1920]),
  ([39,71,131,396],[148,1707,11,2985,2045,2957,1932,1919,1920,1661,2186,2044,2147,1931,1919,1920,1919,1920]),
  ([39,71,135,162,182,198],[713,2180,1921,1938]),
  ([39,71,135,162,250],[1109,2151,1109,1925,1904,1912,1109,1109]),
  ([39,71,135,162,260],[2995,2055,2860,1638,2152,1638,1926,1905,1913,1638,1638]),
  ([39,71,135,162,289],[1704,2153,1704,1927,1906,1914,1704,1704]),
  ([39,71,135,162,343],[2015,1955,1895,2154,1895,1928,1907,1915,1895,1895]),
  ([39,71,135,162,396],[2016,1956,1938,2181,2013,2155,1938,1933,1908,1916,1938,1938]),
  ([39,71,135,182,331],[2981,2026,2966,1886,2014,1886,1886,1886]),
  ([39,71,135,250,309],[1118,1835,1118,1835,1118,1835,1118,1835]),
  ([39,71,135,250,323],[1126,1885,1126,1885,1126,1885,1126,1885]),
  ([39,71,135,250,331],[2967,1132,1887,1132,1887,1132,1887,1132,1887]),
  ([39,71,135,260,317],[2861,1639,1884,1639,1884,1639,1884,1639,1884]),
  ([39,71,135,289,361],[1705,1935,1705,1935,1705,1935,1705,1935]),
  ([39,71,135,309,343],[2027,1842,1896,1842,1896,1842,1896,1842,1896]),
  ([39,71,135,336,343],[194,2862,37,2982,2028,2968,2945,1888,2944,2950,1897,2951,1663,1888,1897,1888,1897,1888,1897]),
  ([39,71,135,343,378],[150,2056,2029,1898,1937,1673,1665,1672,2156,2139,1898,2138,2149,1937,2150,1898,1937,1898,1937]),
  ([39,83,86,103,135,182],[2989,2986,2048,2046,2050]),
  ([39,92,103,135,343,378],[3015,2175,2135,2094,2097,2073,2075]),
  ([39,92,135,343,378],[13,3017,2176,3002,2087,2073,2075,2185,2092,2177,2139,2073,2138,2149,2075,2150,2073,2075,2073,2075]),
  ([39,103,135,182,293],[3016,2125,3003,3008,2099,3006,2048,2088,2070,2076,2093,2048,2048,2048]),
  ([39,103,135,250,274],[1343,1835,2077,1343,1835,1343,1835,1343,1835]),
  ([39,103,135,250,293],[3005,1344,2049,2078,1344,2049,1344,2049,1344,2049]),
  ([39,103,135,260,274],[1640,1837,2080,1640,1837,1640,1837,1640,1837]),
  ([39,103,135,274,289],[1839,2047,2090,2071,2082,1839,2047,1839,2047,1839,2047])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b70ok : f5b70.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b71 : Array Row := #[
  ([39,103,135,343,378],[85,2137,2126,2094,2097,2086,2148,2139,2094,2138,2149,2097,2150,2094,2097,2094,2097]),
  ([39,135,343,378],[30,2183,2165,2139,2138,2149,2150,2139,2138,2149,2150,2139,2138,2149,2150]),
  ([44,49,56,71,103,135],[2248]),
  ([44,49,71,103,135,173],[2697,2551,2222,2211,2187,2188]),
  ([44,49,71,103,135,257],[2914,2708,2576,2464,2235,2190]),
  ([44,56,71,83,103,135],[2818,2190]),
  ([44,56,71,103,135],[2834,2196,2802,2195,2193,348,2211,2194,2191]),
  ([44,71,83,103,135,173],[2198,2201,2202]),
  ([44,71,83,103,135,257],[2992,2190]),
  ([44,71,103,135,173],[2230,2228,2223,2210,2226,2221,2199,2197,2200,2208,2204,2205,2209]),
  ([44,71,103,135,257],[3012,2231,2921,2229,2224,2190,2227,2190,2206,2190,2190]),
  ([49,54,56,71,103,135],[2192]),
  ([49,54,71,83,103,135],[2788,2190]),
  ([49,54,71,103,135],[2190,2786,2237,2234]),
  ([49,54,71,103,135,257],[2216]),
  ([49,56,71,83,92,135],[2816,2191,2234,2307,2246]),
  ([49,56,71,83,135,162],[2817,2194,349,2237,2240]),
  ([49,56,71,92,135,336],[2810,2367,2330,2252]),
  ([49,56,71,103,135,241],[972]),
  ([49,56,71,103,135,243],[]),
  ([49,56,71,103,135,257],[2235]),
  ([49,56,71,103,135,285],[2301,2241]),
  ([49,56,71,103,135,293],[288,2819,2793,350,2250,2245]),
  ([49,56,71,103,135,336],[2419]),
  ([49,56,83,86,103,135],[2245]),
  ([49,56,103,135,293],[114,2824,53,2830,2814,2245,2815,2698,2245,2247,2245,2245]),
  ([49,58,71,77,103,135],[2851,2646,2438,2304,2302,2253]),
  ([49,58,71,92,103,285],[2873,2670,2465,14,2382,2296,2253]),
  ([49,58,71,92,103,336],[2875,2844,2473,2269,2254]),
  ([49,58,71,92,135,285],[2887,2681,2583,2381,2297,2270,2253]),
  ([49,58,71,92,135,336],[2889,2845,2682,2604,2387,2330,2271,2254]),
  ([49,58,71,92,285],[14,2893,2376,2840,2841,2253,2689,2265,2374,14,2636,2261,2380,2295,2253,2299,2267,2253,2253])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b71ok : f5b71.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b72 : Array Row := #[
  ([49,58,71,92,336],[2895,2384,2842,2846,2262,2843,2254,2266,2640,2263,2386,2254,2272,2264,2268,2254,2254]),
  ([49,58,71,103,135,241],[2910,2701,2567,2452,972,2255]),
  ([49,58,71,103,135,257],[2920,2848,2706,2577,2459,2235,2256]),
  ([49,58,71,103,135,285],[2926,2711,2584,2466,2301,2257]),
  ([49,58,71,103,135,336],[2930,2713,2605,2474,2419,2258]),
  ([49,58,71,103,285,351],[2941,2731,2637,2302,2438]),
  ([49,58,71,135,162,285],[2963,2761,2620,2303,2259]),
  ([49,58,71,135,285,361],[2974,2772,2637,2304,2534]),
  ([49,58,103,135,274,285],[3014,2772,2731,2438,2646,2265]),
  ([49,59,71,103,135,285],[2466,2301,2273]),
  ([49,65,71,83,103,135],[2857,2197,2313,2286,2276]),
  ([49,65,71,103,135,285],[2927,2711,2585,2467,2301,2277]),
  ([49,65,83,103,135],[2994,2654,2849,2199,2187,2198,2287,2285,2279,2280,2281]),
  ([49,65,83,103,135,173],[2991,2200,2282,2283]),
  ([49,67,71,103,135,296],[2929,2850,2712,2587,2472,2305,2290]),
  ([49,71,77,83,103,135],[2201,2284,2294]),
  ([49,71,77,103,135],[2303,2295,2296,2297]),
  ([49,71,77,103,135,173],[2298,2300]),
  ([49,71,77,103,135,285],[2299]),
  ([49,71,83,92,103,173],[2204,2858,2656,2280,2352,2296]),
  ([49,71,83,92,135,173],[2205,2660,2281,2297]),
  ([49,71,83,92,135,336],[2207,2862,2661,2274,2330]),
  ([49,71,83,92,173],[2649,2208,2188,2202,2854,2307,2664,2321,2652,2279,2276,2282,2351,2295,2294,2298]),
  ([49,71,83,97,135,173],[2209,2283,2300,2306]),
  ([49,71,83,103,135,195],[2986,2211,2292,2305,2307]),
  ([49,71,83,103,135,241],[2212,972]),
  ([49,71,83,103,135,242],[2213]),
  ([49,71,83,103,135,244],[2214]),
  ([49,71,83,103,135,257],[2987,2216,2235]),
  ([49,71,83,103,135,260],[2988,2217,2789,2658]),
  ([49,71,83,103,135,285],[2218,2301,2308]),
  ([49,71,83,103,135,336],[2219,2419])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b72ok : f5b72.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b73 : Array Row := #[
  ([49,71,83,103,135,365],[2220,2659,2309,2312]),
  ([49,71,83,103,156,173],[2221,2662,2310,2312]),
  ([49,71,83,103,173,182],[2989,2222,2311]),
  ([49,71,83,103,365],[2650,2225,2189,2203,2312,2663,2320,2655,2312,2312,2312]),
  ([49,71,83,135,162,173],[2226,2662,2286,2303,2316,2318]),
  ([49,71,86,92,135,336],[2872,2864,2668,2552,2275,2330]),
  ([49,71,86,103,135,241],[972]),
  ([49,71,86,103,135,257],[2786,2667,2235]),
  ([49,71,86,103,135,285],[292,2301,2323]),
  ([49,71,86,103,135,336],[2868,2554,2419]),
  ([49,71,92,103,118,135],[2897,2693,2489,2441,2421]),
  ([49,71,92,103,120,173],[2898,2694]),
  ([49,71,92,103,135,241],[2911,2703,2560,2452,972,881]),
  ([49,71,92,103,135,257],[2922,2709,2570,2459,2235,2234]),
  ([49,71,92,103,135,285],[2928,2715,2579,2466,2301,2347,2297,2296]),
  ([49,71,92,103,135,336],[2931,2719,2593,2474,2419,2330]),
  ([49,71,92,103,173,336],[2936,2726,2331]),
  ([49,71,92,103,182,336],[2937,2879,2727,2630,2420,2332]),
  ([49,71,92,103,285],[2874,111,2336,2296,2671,69,2349,2296,2377,2296,2295,2296,2299]),
  ([49,71,92,103,336,351],[2942,2734,2638,2421,2441,2333,2345]),
  ([49,71,92,118,135],[2945,2490,2876,2332,2737,2491,2672,2254,2345,2333,2331]),
  ([49,71,92,118,135,336],[2944,2736,2361]),
  ([49,71,92,120,135,173],[2947,2738,2330]),
  ([49,71,92,120,135,336],[2948,2739,2330]),
  ([49,71,92,120,173],[2949,2494,2877,587,2741,2495,2673,2352,2331]),
  ([49,71,92,125,135,336],[2953,2879,2742,2501,2487,2330]),
  ([49,71,92,135,140,336],[2958,2747,2330]),
  ([49,71,92,135,156,336],[2959,2755,2330]),
  ([49,71,92,135,162,336],[2964,2762,2621,2488,2337,2330]),
  ([49,71,92,135,173,336],[2968,2765,2331,2330]),
  ([49,71,92,135,182,336],[2970,2766,2332,2330]),
  ([49,71,92,135,241],[2882,2362,881,2769,2568,2678,2255,881,2368,881,881])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b73ok : f5b73.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b74 : Array Row := #[
  ([49,71,92,135,257],[2863,2885,2363,2234,2771,2578,2680,2256,2234,2372,2234,2234]),
  ([49,71,92,135,285],[2888,50,2364,2297,2773,2586,2683,2257,2348,2297,2381,2297,2295,2297,2299]),
  ([49,71,92,135,309,336],[2975,2774,2638,2441,2489,2330]),
  ([49,71,92,135,336],[2976,2602,2890,2366,2330,2777,2606,2685,2258,2330,2387,2330,2330]),
  ([49,71,92,135,336,343],[20,2892,2876,2878,2775,2639,2490,2496,2330]),
  ([49,71,92,135,336,351],[2977,2776,2333,2330]),
  ([49,71,92,135,336,378],[2978,18,2268,2672,2674,2641,2491,2536,2330]),
  ([49,71,92,173,336],[2982,2628,2891,2367,2331,2782,2629,2687,2278,2331,2331,2331]),
  ([49,71,92,182,336],[2864,2983,2631,2892,2332,2783,2632,2688,2291,2332,2332,2332]),
  ([49,71,92,285],[283,2323,14,2894,2379,2295,2299,14,2690,2383,2295,2299,2295,2299]),
  ([49,71,92,336,351],[2984,2639,2896,2333,2345,2784,2641,2691,2333,2345,2333,2345,2333,2345]),
  ([49,71,93,103,120,173],[2334]),
  ([49,71,93,103,135,336],[2345,2474,2419]),
  ([49,71,97,103,135,336],[2593,2419,2404]),
  ([49,71,97,120,135,173],[2334,2404]),
  ([49,71,97,135,173,336],[2361,2404]),
  ([49,71,97,135,336],[2603,2409,2404,2607,2404,2345,2404,2404]),
  ([49,71,103,118,120,135],[]),
  ([49,71,103,118,135],[2487,2420,2488,2404,2330]),
  ([49,71,103,118,135,173],[2331,2404]),
  ([49,71,103,118,135,336],[2408]),
  ([49,71,103,120,135,241],[972]),
  ([49,71,103,120,135,242],[]),
  ([49,71,103,120,135,257],[588,2235]),
  ([49,71,103,120,135,285],[2335,2394,2301]),
  ([49,71,103,120,135,336],[2419]),
  ([49,71,103,120,156,173],[2740,2398]),
  ([49,71,103,120,173,182],[2946,589,2410,2420,2418]),
  ([49,71,103,125,135,241],[972]),
  ([49,71,103,125,135,257],[2235]),
  ([49,71,103,125,135,285],[2336,2395,2301]),
  ([49,71,103,125,135,336],[2900,2487,2419])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b74ok : f5b74.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b75 : Array Row := #[
  ([49,71,103,131,135,392],[2932,2720,2346,2609,2338,2508,2502,2480,2430,2423]),
  ([49,71,103,131,162,392],[2933,2723,2350,2510,2423]),
  ([49,71,103,131,392],[112,2497,2943,2482,2901,2423,70,2515,2735,2481,2695,2423,2393,2329,2338,2529,2517,2423,2518,2423]),
  ([49,71,103,135,140,241],[972]),
  ([49,71,103,135,140,257],[2235]),
  ([49,71,103,135,140,285],[2347,2301]),
  ([49,71,103,135,140,336],[2419]),
  ([49,71,103,135,156,241],[2750,2399,972]),
  ([49,71,103,135,156,257],[2751,2400,2235]),
  ([49,71,103,135,156,285],[2752,2348,2401,2301]),
  ([49,71,103,135,156,336],[2753,2402,2419]),
  ([49,71,103,135,162,241],[1109,2424,972]),
  ([49,71,103,135,162,257],[2996,2237,2425,2235]),
  ([49,71,103,135,162,285],[2349,2303,2426,2301]),
  ([49,71,103,135,162,336],[2488,2427,2419]),
  ([49,71,103,135,162,392],[2721,2350,2537,2428,2430]),
  ([49,71,103,135,173,197],[2232,2352,2430]),
  ([49,71,103,135,173,241],[2353,2405,972]),
  ([49,71,103,135,173,243],[2354]),
  ([49,71,103,135,173,244],[2355]),
  ([49,71,103,135,173,257],[575,2288,2356,2406,2235]),
  ([49,71,103,135,173,285],[2357,2407,2301]),
  ([49,71,103,135,173,293],[294,2934,2904,2756,2722,2289,2647,2358]),
  ([49,71,103,135,173,331],[2935,2360,2485]),
  ([49,71,103,135,173,336],[2361,2408,2419]),
  ([49,71,103,135,182,241],[2362,2411,972]),
  ([49,71,103,135,182,257],[2363,2412,2235]),
  ([49,71,103,135,182,285],[2364,2413,2301]),
  ([49,71,103,135,182,296],[2997,2365,2414,2305]),
  ([49,71,103,135,182,336],[2952,2366,2415,2420,2419]),
  ([49,71,103,135,238],[289,2903,611,2538,611,2339,611,611]),
  ([49,71,103,135,241],[972,2540,972,2340,972,972])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b75ok : f5b75.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b76 : Array Row := #[
  ([49,71,103,135,241,250],[1835,972]),
  ([49,71,103,135,241,251],[972]),
  ([49,71,103,135,241,253],[972]),
  ([49,71,103,135,241,260],[1837,2790,972]),
  ([49,71,103,135,241,274],[2757,1343,972]),
  ([49,71,103,135,241,275],[2758,972]),
  ([49,71,103,135,241,278],[972]),
  ([49,71,103,135,241,293],[295,2759,1344,2648,972]),
  ([49,71,103,135,241,309],[1118,972]),
  ([49,71,103,135,241,310],[972]),
  ([49,71,103,135,241,317],[1122,2483,972]),
  ([49,71,103,135,241,331],[1132,2486,972]),
  ([49,71,103,135,241,351],[2368,982,972]),
  ([49,71,103,135,241,355],[2369,972]),
  ([49,71,103,135,241,365],[2370,984,2443,972]),
  ([49,71,103,135,241,386],[2371,989,2446,972]),
  ([49,71,103,135,250,257],[2787,2235]),
  ([49,71,103,135,257],[2866,2235,2541,2235,2341,2235,2235]),
  ([49,71,103,135,257,274],[2998,2760,2239,2235]),
  ([49,71,103,135,257,323],[2238,2484,2235]),
  ([49,71,103,135,257,371],[2373,2236,2444,2235]),
  ([49,71,103,135,274,285],[2761,2646,2374,2301]),
  ([49,71,103,135,285],[2301,2542,2301,2375,2327,2342,2301,2301]),
  ([49,71,103,135,285,289],[2851,2852,2376,2301]),
  ([49,71,103,135,285,351],[2381,2302,2301]),
  ([49,71,103,135,285,361],[2382,2304,2534,2301]),
  ([49,71,103,135,296],[3000,2665,2867,2305,2543,2305,2385,2328,2343,2305,2305]),
  ([49,71,103,135,309,336],[2489,2419]),
  ([49,71,103,135,336],[2498,2448,2419,2544,2419,2345,2419,2419]),
  ([49,71,103,135,336,343],[115,2953,2937,2897,2899,2490,2496,2419]),
  ([49,71,103,135,336,351],[2387,2421,2419]),
  ([49,71,103,135,336,378],[71,2762,2269,2693,2696,2491,2536,2419])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b76ok : f5b76.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b77 : Array Row := #[
  ([49,71,103,135,392],[2499,2449,2430,2545,2445,2430,2393,2329,2346,2430,2430]),
  ([49,71,103,182,336],[2868,2954,2500,2900,2420,2614,2420,2417,2420,2420]),
  ([49,71,103,241,351],[982,2434,2616,982,2434,982,2434,982,2434]),
  ([49,71,103,241,365],[984,2443,2617,984,2443,984,2443,984,2443]),
  ([49,71,103,241,386],[989,2446,2618,989,2446,989,2446,989,2446]),
  ([49,71,103,257,371],[2869,2236,2444,2619,2236,2444,2236,2444,2236,2444]),
  ([49,71,103,285,351],[2302,2438,2620,2302,2438,2302,2438,2302,2438]),
  ([49,71,103,336,351],[2501,2421,2441,2621,2421,2441,2421,2441,2421,2441]),
  ([49,71,120,125,135,173],[2946,2485,2487,2396]),
  ([49,71,120,135,162,173],[2740,2488,2492]),
  ([49,71,125,135,336],[2954,2500,2952,2487,2554,2487,2397,2487,2487]),
  ([49,71,131,135,162,392],[2965,2763,2744,2622,2537,2516,2510,2502]),
  ([49,71,131,135,392],[2979,2611,2955,51,2521,2502,2778,2610,2743,2260,2509,2502,2528,2502,2517,2502,2518]),
  ([49,71,131,162,392],[2980,2624,2956,317,2523,2510,2781,2623,2745,2510,2510,2517,2510,2518]),
  ([49,71,131,392],[285,2324,16,2985,2644,2957,2532,2517,2518,2260,2785,2643,2746,2530,2517,2518,2517,2518]),
  ([49,71,135,162,173,197],[2233,2779,2519,2537]),
  ([49,71,135,162,241],[1109,2750,1109,2524,2503,2511,1109,1109]),
  ([49,71,135,162,257],[3001,2667,2870,2237,2751,2237,2525,2504,2512,2237,2237]),
  ([49,71,135,162,285],[2303,2752,2303,2526,2505,2513,2303,2303]),
  ([49,71,135,162,336],[2614,2554,2488,2753,2488,2527,2506,2514,2488,2488]),
  ([49,71,135,162,392],[2615,2555,2537,2780,2612,2754,2537,2531,2507,2515,2537,2537]),
  ([49,71,135,173,331],[2981,2625,2966,2485,2613,2485,2485,2485]),
  ([49,71,135,241,309],[1118,2434,1118,2434,1118,2434,1118,2434]),
  ([49,71,135,241,317],[1122,2483,1122,2483,1122,2483,1122,2483]),
  ([49,71,135,241,331],[2969,1132,2486,1132,2486,1132,2486,1132,2486]),
  ([49,71,135,257,323],[2871,2238,2484,2238,2484,2238,2484,2238,2484]),
  ([49,71,135,285,361],[2304,2534,2304,2534,2304,2534,2304,2534]),
  ([49,71,135,309,336],[2630,2441,2489,2441,2489,2441,2489,2441,2489]),
  ([49,71,135,336,343],[291,2872,54,2983,2631,2970,2945,2490,2944,2950,2496,2951,2262,2490,2496,2490,2496,2490,2496]),
  ([49,71,135,336,378],[287,2668,2632,2491,2536,2272,2264,2271,2755,2737,2491,2736,2748,2536,2749,2491,2536,2491,2536]),
  ([49,83,86,103,135,173],[2989,2986,2647,2645,2649]),
  ([49,92,103,135,336,378],[3015,2774,2734,2693,2696,2672,2674])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b77ok : f5b77.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def f5b78 : Array Row := #[
  ([49,92,135,336,378],[18,3017,2775,3002,2688,2672,2674,2784,2691,2776,2737,2672,2736,2748,2674,2749,2672,2674,2672,2674]),
  ([49,103,135,173,293],[3016,2724,3003,3008,2698,3004,2647,2686,2669,2675,2692,2647,2647,2647]),
  ([49,103,135,241,274],[1343,2434,2676,1343,2434,1343,2434,1343,2434]),
  ([49,103,135,241,293],[3007,1344,2648,2677,1344,2648,1344,2648,1344,2648]),
  ([49,103,135,257,274],[2239,2436,2679,2239,2436,2239,2436,2239,2436]),
  ([49,103,135,274,285],[2438,2646,2689,2670,2681,2438,2646,2438,2646,2438,2646]),
  ([49,103,135,336,378],[113,2742,2727,2693,2696,2685,2747,2737,2693,2736,2748,2696,2749,2693,2696,2693,2696]),
  ([49,135,336,378],[52,2783,2766,2737,2736,2748,2749,2737,2736,2748,2749,2737,2736,2748,2749]),
  ([56,71,83,86,103,135],[2786,2789,2817,2793]),
  ([56,71,103,135,293],[352,2820,2904,2793,72,2838,2806,2828,2792,2827,2814,2793,2815,2794,2793,2793]),
  ([56,83,86,103,135],[2788,2791,2986,2814,2812,2813,2816]),
  ([56,103,135,293],[122,2825,57,3008,2831,2814,2815,2822,2821,2826,2814,2815,2814,2815]),
  ([58,71,103,135,285,289],[3014,2974,2941,2851,2852,2840]),
  ([71,83,103,135,260],[2995,2860,2990,2847,2789,2789,2853,2789,2789]),
  ([71,86,103,135,257],[3001,2870,2996,2848,2786,2786,2863,2786,2786]),
  ([71,92,103,135,336,343],[3015,2975,2942,2897,2899,2876,2878]),
  ([71,92,135,336,343],[20,3017,2978,3002,2843,2876,2878,2984,2896,2977,2945,2876,2944,2950,2878,2951,2876,2878,2876,2878]),
  ([71,103,135,241,250],[2960,1835,2434,2880,1835,2434,1835,2434,1835,2434]),
  ([71,103,135,241,260],[2961,1837,2790,2881,1837,2790,1837,2790,1837,2790]),
  ([71,103,135,250,257],[2962,2436,2787,2883,2436,2787,2436,2787,2436,2787]),
  ([71,103,135,285,289],[2963,2851,2852,2893,2873,2887,2851,2852,2851,2852,2851,2852]),
  ([71,103,135,336,343],[73,2964,2844,2897,2899,2890,2958,2945,2897,2944,2950,2899,2951,2897,2899,2897,2899]),
  ([71,135,336,343],[2846,2845,2959,2945,2944,2950,2951,2945,2944,2950,2951,2945,2944,2950,2951])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f5b78ok : f5b78.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true := by decide +kernel

private def layer5 (i : ℕ) : {s : List W // impossible 5 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer4 i).1) 4) = true} :=
    #[⟨f5b0, f5b0ok⟩, ⟨f5b1, f5b1ok⟩, ⟨f5b2, f5b2ok⟩, ⟨f5b3, f5b3ok⟩, ⟨f5b4, f5b4ok⟩, ⟨f5b5, f5b5ok⟩, ⟨f5b6, f5b6ok⟩, ⟨f5b7, f5b7ok⟩, ⟨f5b8, f5b8ok⟩, ⟨f5b9, f5b9ok⟩, ⟨f5b10, f5b10ok⟩, ⟨f5b11, f5b11ok⟩, ⟨f5b12, f5b12ok⟩, ⟨f5b13, f5b13ok⟩, ⟨f5b14, f5b14ok⟩, ⟨f5b15, f5b15ok⟩, ⟨f5b16, f5b16ok⟩, ⟨f5b17, f5b17ok⟩, ⟨f5b18, f5b18ok⟩, ⟨f5b19, f5b19ok⟩, ⟨f5b20, f5b20ok⟩, ⟨f5b21, f5b21ok⟩, ⟨f5b22, f5b22ok⟩, ⟨f5b23, f5b23ok⟩, ⟨f5b24, f5b24ok⟩, ⟨f5b25, f5b25ok⟩, ⟨f5b26, f5b26ok⟩, ⟨f5b27, f5b27ok⟩, ⟨f5b28, f5b28ok⟩, ⟨f5b29, f5b29ok⟩, ⟨f5b30, f5b30ok⟩, ⟨f5b31, f5b31ok⟩, ⟨f5b32, f5b32ok⟩, ⟨f5b33, f5b33ok⟩, ⟨f5b34, f5b34ok⟩, ⟨f5b35, f5b35ok⟩, ⟨f5b36, f5b36ok⟩, ⟨f5b37, f5b37ok⟩, ⟨f5b38, f5b38ok⟩, ⟨f5b39, f5b39ok⟩, ⟨f5b40, f5b40ok⟩, ⟨f5b41, f5b41ok⟩, ⟨f5b42, f5b42ok⟩, ⟨f5b43, f5b43ok⟩, ⟨f5b44, f5b44ok⟩, ⟨f5b45, f5b45ok⟩, ⟨f5b46, f5b46ok⟩, ⟨f5b47, f5b47ok⟩, ⟨f5b48, f5b48ok⟩, ⟨f5b49, f5b49ok⟩, ⟨f5b50, f5b50ok⟩, ⟨f5b51, f5b51ok⟩, ⟨f5b52, f5b52ok⟩, ⟨f5b53, f5b53ok⟩, ⟨f5b54, f5b54ok⟩, ⟨f5b55, f5b55ok⟩, ⟨f5b56, f5b56ok⟩, ⟨f5b57, f5b57ok⟩, ⟨f5b58, f5b58ok⟩, ⟨f5b59, f5b59ok⟩, ⟨f5b60, f5b60ok⟩, ⟨f5b61, f5b61ok⟩, ⟨f5b62, f5b62ok⟩, ⟨f5b63, f5b63ok⟩, ⟨f5b64, f5b64ok⟩, ⟨f5b65, f5b65ok⟩, ⟨f5b66, f5b66ok⟩, ⟨f5b67, f5b67ok⟩, ⟨f5b68, f5b68ok⟩, ⟨f5b69, f5b69ok⟩, ⟨f5b70, f5b70ok⟩, ⟨f5b71, f5b71ok⟩, ⟨f5b72, f5b72ok⟩, ⟨f5b73, f5b73ok⟩, ⟨f5b74, f5b74ok⟩, ⟨f5b75, f5b75ok⟩, ⟨f5b76, f5b76ok⟩, ⟨f5b77, f5b77ok⟩, ⟨f5b78, f5b78ok⟩]
  pick alphabet layer4 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f6b0 : Array Row := #[
  ([0,1,39,49,71,103,135],[1400,86,80,73,65,58,42,13]),
  ([0,2,39,49,71,103,135],[1401,134,127,119,111,104,36,13]),
  ([0,4,39,49,71,103,135],[1403,183,178,170,162,154,30,22]),
  ([0,5,39,49,71,103,135],[1406,228,222,216,209,200,42,22]),
  ([0,8,39,49,71,103,135],[1410,284,277,270,263,254,36,22]),
  ([0,14,39,49,71,103,135],[1415,383,364,352,340,331,42,37,30,23,14]),
  ([0,19,39,49,71,103,135],[1421,515,497,480,468,459,43,36,30,24,15]),
  ([0,28,39,49,71,103,135],[1428,665,631,608,596,587,42,36,31,25,16,0]),
  ([0,39,49,58,71,103,135],[2305,2075,1456,962,946,937,44,38,30,26,13,3]),
  ([0,39,49,71,92,103,135],[2348,2118,1907,1487,1159,1098,45,39,32,22,13]),
  ([0,39,49,71,92,135],[2367,40,1135,2137,34,1139,1923,28,1145,1832,21,1153,1215,7,1171,41,5,35,6,33,27,29,3,7]),
  ([0,39,49,71,103,135],[2431,42,1435,2205,36,1442,1978,30,1464,1836,22,1493,1622,13,1519,20,4]),
  ([1,2,39,49,71,103,135],[12,1402,134,104,80,58]),
  ([1,4,39,49,71,103,135],[12,1404,183,154,73,65]),
  ([1,5,39,49,71,103,135],[12,1407,228,200,86,65]),
  ([1,8,39,49,71,103,135],[12,1411,284,254,80,65]),
  ([1,14,39,49,71,103,135],[12,1416,383,331,86,81,73,66,59]),
  ([1,19,39,49,71,103,135],[12,1422,515,459,87,80,73,67,60]),
  ([1,28,39,49,71,103,135],[12,1429,665,632,587,86,80,74,68,61,46]),
  ([1,39,49,56,71,103,135],[2290,888,46]),
  ([1,39,49,58,71,103,135],[2305,12,1457,937,88,82,73,69,58,49]),
  ([1,39,49,71,83,103,135],[2329,1036,48]),
  ([1,39,49,71,86,103,135],[2342,2105,1900,12,1076,1061,47]),
  ([1,39,49,71,92,103,135],[2348,12,1488,4,1160,1098,89,83,75,65,58]),
  ([1,39,49,71,92,135],[2367,84,1135,4,1140,4,1146,4,1154,1215,52,1171,85,50,79,51,78,70,72,49,52]),
  ([1,39,49,71,103,120,135],[2389,1319]),
  ([1,39,49,71,103,125,135],[2396,2164,1660,12,1331,1327]),
  ([1,39,49,71,103,135,140],[2403,1550]),
  ([1,39,49,71,103,135,156],[2407,1563,76,53]),
  ([1,39,49,71,103,135,162],[2411,1960,20,1773,1569,12,1371,56]),
  ([1,39,49,71,103,135,173],[2417,1579,50,54]),
  ([1,39,49,71,103,135,182],[2425,1588,51,55])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b0ok : f6b0.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b1 : Array Row := #[
  ([1,39,49,71,103,135,241],[1595]),
  ([1,39,49,71,103,135,251],[2433,1602,872]),
  ([1,39,49,71,103,135,275],[2437,1608,1016,77]),
  ([1,39,49,71,103,135,310],[2441,1614,1307]),
  ([1,39,49,71,103,135,351],[2444,52]),
  ([1,39,49,71,103,351],[2466,90,1595,13,1602,13,1608,13,1614,1357,57,1519,57,57,71,57,57]),
  ([1,39,49,71,135,162],[2480,91,1752,20,1757,20,2032,77,1765,1871,71,1780,20,1738,76,62,63,64]),
  ([1,49,71,103,135,241],[42,2433,42,2437,42,2441,2466,90,2444,1357,57,1435,57,91,57,84,57,57]),
  ([2,4,39,49,71,103,135],[12,1405,178,154,119,111]),
  ([2,5,39,49,71,103,135],[12,1408,222,200,134,111]),
  ([2,8,39,49,71,103,135],[12,1412,277,254,127,111]),
  ([2,14,39,49,71,103,135],[12,1417,364,331,134,128,119,112,105]),
  ([2,19,39,49,71,103,135],[12,1423,497,459,135,127,119,113,106]),
  ([2,28,39,49,71,103,135],[12,1430,666,631,587,134,127,120,114,107,92]),
  ([2,39,49,56,71,103,135],[2060,888,92]),
  ([2,39,49,58,71,103,135],[2075,12,1458,937,136,129,119,115,104,95]),
  ([2,39,49,71,83,103,135],[2330,2094,1892,12,1051,1036,94]),
  ([2,39,49,71,86,103,135],[2104,1061,93]),
  ([2,39,49,71,92,103,135],[2118,12,1489,4,1161,1098,137,130,121,111,104]),
  ([2,39,49,71,92,135],[4,1136,2137,125,1139,4,1147,4,1155,1215,98,1171,133,96,126,97,124,116,118,95,98]),
  ([2,39,49,71,103,120,135],[2390,2155,1648,12,1323,1319]),
  ([2,39,49,71,103,125,135],[2163,1327]),
  ([2,39,49,71,103,135,140],[2173,1550]),
  ([2,39,49,71,103,135,156],[2177,1563,122,99]),
  ([2,39,49,71,103,135,162],[2181,1961,20,1774,1569,12,1372,102]),
  ([2,39,49,71,103,135,173],[2186,1579,96,100]),
  ([2,39,49,71,103,135,182],[2192,1588,97,101]),
  ([2,39,49,71,103,135,242],[2202,1598,815]),
  ([2,39,49,71,103,135,250],[1599]),
  ([2,39,49,71,103,135,276],[2208,1609,1017,123]),
  ([2,39,49,71,103,135,311],[2212,1615,1308]),
  ([2,39,49,71,103,135,351],[2215,98])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b1ok : f6b1.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b2 : Array Row := #[
  ([2,39,49,71,103,351],[13,1598,2236,131,1599,13,1609,13,1615,1357,103,1519,103,103,117,103,103]),
  ([2,39,49,71,135,162],[20,1753,2250,132,1756,20,2033,123,1766,1871,117,1780,20,1739,122,108,109,110]),
  ([2,39,71,103,135,250],[36,2202,36,2208,36,2212,2236,131,2215,1357,103,1442,103,132,103,125,103,103]),
  ([3,39,49,56,71,103,135],[888,138]),
  ([3,39,49,71,103,135],[57,1436,103,1443,12,1467,12,1496,1622,140,1519,141,139]),
  ([4,5,39,49,71,103,135],[12,1409,216,209,183,162]),
  ([4,8,39,49,71,103,135],[12,1413,270,263,178,162]),
  ([4,14,39,49,71,103,135],[12,1418,384,352,340,183,179,170,163,155]),
  ([4,19,39,49,71,103,135],[12,1424,498,480,468,184,178,170,164,156]),
  ([4,28,39,49,71,103,135],[12,1431,608,596,183,178,171,165,157,142]),
  ([4,39,49,56,71,103,135],[2291,2061,12,909,904,896,142]),
  ([4,39,49,58,71,103,135],[12,1459,962,946,185,180,170,166,154,145]),
  ([4,39,49,71,83,103,135],[1891,1044,144]),
  ([4,39,49,71,86,103,135],[1899,1069,143]),
  ([4,39,49,71,92,103,135],[1907,12,1490,1159,186,181,172,162,154]),
  ([4,39,49,71,92,135],[4,1137,4,1141,1923,168,1145,4,1833,161,1156,4,1172,182,146,177,147,176,167,169,145,148]),
  ([4,39,49,71,103,120,135],[1937,1647]),
  ([4,39,49,71,103,125,135],[1940,1659]),
  ([4,39,49,71,103,135,140],[1947,1716]),
  ([4,39,49,71,103,135,156],[1954,1732,173,149]),
  ([4,39,49,71,103,135,162],[1959,1772,152]),
  ([4,39,49,71,103,135,173],[2418,1964,1793,1580,12,1376,146,150]),
  ([4,39,49,71,103,135,182],[2193,1967,1801,1589,12,1380,147,151]),
  ([4,39,49,71,103,135,243],[1972,1814,816]),
  ([4,39,49,71,103,135,252],[1975,1819,873]),
  ([4,39,49,71,103,135,274],[1823,174]),
  ([4,39,49,71,103,135,309],[1981]),
  ([4,39,49,71,103,135,353],[1985,1840,1358]),
  ([4,39,49,71,135,162],[20,1754,20,1758,2031,174,1764,20,1781,173,158,159,160]),
  ([4,39,49,71,135,309],[22,1814,22,1819,2038,175,1823,22,1840,1357,153,1493,153,153,153,153]),
  ([4,39,49,103,135,274],[30,1972,30,1975,2038,175,1981,30,1985,1357,153,1464,153,153,168,153,153]),
  ([5,8,39,49,71,103,135],[12,1414,284,263,222,209])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b2ok : f6b2.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b3 : Array Row := #[
  ([5,14,39,49,71,103,135],[12,1419,383,353,340,228,223,216,210,201]),
  ([5,19,39,49,71,103,135],[12,1425,515,468,229,222,216,211,202]),
  ([5,28,39,49,71,103,135],[12,1432,665,633,596,228,222,217,212,203,187]),
  ([5,39,49,56,71,103,135],[2290,896,187]),
  ([5,39,49,58,71,103,135],[2305,12,1460,946,230,224,216,213,200,190]),
  ([5,39,49,71,83,103,135],[2329,1044,189]),
  ([5,39,49,71,86,103,135],[2342,2106,1901,12,1079,1069,188]),
  ([5,39,49,71,92,103,135],[2348,12,1491,1159,1099,231,225,218,209,200]),
  ([5,39,49,71,92,135],[2367,226,1135,4,1142,4,1148,4,1834,208,1157,4,1217,194,1173,227,191,221,192,220,214,215,190,193]),
  ([5,39,49,71,103,120,135],[2389,1647]),
  ([5,39,49,71,103,125,135],[2396,1659]),
  ([5,39,49,71,103,135,140],[2403,1716]),
  ([5,39,49,71,103,135,156],[2407,1955,1732,1564,12,1369,219,195]),
  ([5,39,49,71,103,135,162],[2411,1772,198]),
  ([5,39,49,71,103,135,173],[2417,1793,191,196]),
  ([5,39,49,71,103,135,182],[2425,2194,1801,1590,12,1381,192,197]),
  ([5,39,49,71,103,135,241],[1811]),
  ([5,39,49,71,103,135,253],[2434,1820,874]),
  ([5,39,49,71,103,135,278],[2438,1827,1018]),
  ([5,39,49,71,103,135,309],[2440]),
  ([5,39,49,71,103,135,355],[2445,1841,1359,194]),
  ([5,39,49,71,135,162],[2480,232,1752,20,1759,20,1767,20,1782,219,204,205,206]),
  ([5,39,49,71,135,309],[2486,233,1811,22,1820,22,1827,22,1841,1357,199,1493,199,199,199,199]),
  ([5,49,71,103,135,241],[42,2434,42,2438,2486,233,2440,42,2445,1357,199,1435,199,232,199,226,199,199]),
  ([6,39,49,71,103,135],[2431,236,1435,12,1446,12,1469,199,1494,57,1521,235,234]),
  ([6,39,49,71,103,135,140],[2403]),
  ([7,39,49,71,83,103,135],[1044,237]),
  ([7,39,49,71,103,135],[199,1437,12,1447,153,1468,1836,240,1493,12,1522,239,238]),
  ([8,14,39,49,71,103,135],[12,1420,364,340,284,278,270,264,255]),
  ([8,19,39,49,71,103,135],[12,1426,497,481,468,285,277,270,265,256]),
  ([8,28,39,49,71,103,135],[12,1433,667,631,596,284,277,271,266,257,241]),
  ([8,39,49,56,71,103,135],[2060,896,241])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b3ok : f6b3.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b4 : Array Row := #[
  ([8,39,49,58,71,103,135],[2075,12,1461,946,286,279,270,267,254,244]),
  ([8,39,49,71,83,103,135],[2331,2094,1893,12,1078,1044,243]),
  ([8,39,49,71,86,103,135],[2104,1069,242]),
  ([8,39,49,71,92,103,135],[2118,12,1492,1159,1100,287,280,272,263,254]),
  ([8,39,49,71,92,135],[4,1138,2137,275,1139,4,1149,4,1835,262,1158,4,1218,248,1174,283,245,276,246,274,268,269,244,247]),
  ([8,39,49,71,103,120,135],[2155,1647]),
  ([8,39,49,71,103,125,135],[2163,1659]),
  ([8,39,49,71,103,135,140],[2173,1716]),
  ([8,39,49,71,103,135,156],[2177,1956,1732,1565,12,1370,273,249]),
  ([8,39,49,71,103,135,162],[2181,1772,252]),
  ([8,39,49,71,103,135,173],[2419,2186,1793,1581,12,1377,245,250]),
  ([8,39,49,71,103,135,182],[2192,1801,246,251]),
  ([8,39,49,71,103,135,244],[2203,1815,818]),
  ([8,39,49,71,103,135,250],[1816]),
  ([8,39,49,71,103,135,280],[2209,1828,1020]),
  ([8,39,49,71,103,135,309],[2211]),
  ([8,39,49,71,103,135,358],[2216,1842,1360,248]),
  ([8,39,49,71,135,162],[20,1755,2250,281,1756,20,1768,20,1783,273,258,259,260]),
  ([8,39,49,71,135,309],[22,1815,2256,282,1816,22,1828,22,1842,1357,253,1493,253,253,253,253]),
  ([8,39,71,103,135,250],[36,2203,36,2209,2256,282,2211,36,2216,1357,253,1442,253,281,253,275,253,253]),
  ([9,39,49,71,103,135],[12,1439,2205,290,1442,12,1471,253,1495,103,1523,289,288]),
  ([9,39,49,71,103,135,140],[2173]),
  ([10,39,49,71,86,103,135],[1069,291]),
  ([10,39,49,71,103,135],[12,1440,253,1444,153,1470,1836,294,1493,12,1524,293,292]),
  ([11,39,49,56,71,103,135],[896,295]),
  ([11,39,49,71,103,135],[199,1438,253,1445,12,1472,1836,298,1493,12,1525,297,296]),
  ([14,19,39,49,71,103,135],[12,1427,515,499,480,469,460,385,364,352,343,333,301,302]),
  ([14,28,39,49,71,103,135],[12,1434,665,635,608,597,588,383,364,354,344,334,311]),
  ([14,28,49,71,103,135],[2430,382,664,716,314,669,309,307,677,304,672,313,397,310,387,308,305,301,312,306,303]),
  ([14,39,49,56,71,103,135],[2290,2062,904,897,889,311]),
  ([14,39,49,58,71,103,135],[2305,2076,12,1462,962,947,938,386,375,366,352,345,331,319]),
  ([14,39,49,71,83,103,135],[2329,2095,1891,1045,1037,318,349])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b4ok : f6b4.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b5 : Array Row := #[
  ([14,39,49,71,86,103,135],[2342,2108,1899,1070,1062,392,317]),
  ([14,39,49,71,92,103,135],[2348,2119,1907,12,1497,4,1163,1101,388,367,355,340,331]),
  ([14,39,49,71,92,135],[2367,380,1135,4,2138,362,1144,1923,350,1145,4,1844,341,1162,4,1219,324,1176,303,376,381,321,363,322,360,346,351,319,323]),
  ([14,39,49,71,103,120,135],[2389,2156,1937,1649,1320]),
  ([14,39,49,71,103,125,135],[2396,2165,1940,1661,12,1334,1328,316]),
  ([14,39,49,71,103,135,140],[2403,2174,1947,1717,1551,12,1364]),
  ([14,39,49,71,103,135,156],[2407,2178,1954,1733,1566,357,325]),
  ([14,39,49,71,103,135,162],[2411,2182,1959,20,1775,1570,393,328]),
  ([14,39,49,71,103,135,173],[2417,2187,1964,1794,1582,321,326]),
  ([14,39,49,71,103,135,182],[2425,2195,1967,1802,1591,12,1388,312,315,320,322,327]),
  ([14,39,49,71,103,135,241],[2201,1970,1812,1596]),
  ([14,39,49,71,103,135,260],[2435,37,1977,1822,1604,876,314,361]),
  ([14,39,49,71,103,135,274],[2436,2220,1824,1606,394,358]),
  ([14,39,49,71,103,135,317],[2442,2221,1982,23,1616,1310,335]),
  ([14,39,49,71,103,135,365],[2446,2222,1987,1846,14,1362,324,330]),
  ([14,39,49,71,103,365],[2467,389,1596,14,2239,368,1604,2002,356,1606,14,1878,348,1616,1554,330,1557,304,377,330,330,347,330,330]),
  ([14,39,49,71,135,162],[2480,390,1752,20,2251,369,1761,2031,358,1764,20,1872,347,1785,306,395,349,378,302,357,336,337,338]),
  ([14,39,49,71,135,317],[2487,391,1812,23,2259,370,1822,2039,359,1824,23,1878,348,1846,1632,335,1634,307,379,335,335,335,335]),
  ([14,39,49,103,135,274],[2498,396,1970,30,2270,371,1977,30,2039,359,1982,30,2002,356,1987,1357,329,1464,309,329,329,350,329,329]),
  ([14,39,71,103,135,260],[2514,399,2201,2270,371,2220,37,2259,370,2221,37,2239,368,2222,2055,361,2056,398,361,369,361,362,361,361]),
  ([14,49,71,83,103,135],[2509,398,2333,394,379,2339,377,2336,392,374,372,373,395,378,393,375,376]),
  ([14,49,71,103,135,241],[42,2514,399,2435,2498,396,2436,42,2487,391,2442,42,2467,389,2446,1357,329,1435,329,390,329,380,329,329]),
  ([15,39,49,71,103,135],[2431,407,1435,12,1452,329,1465,12,1499,57,1625,403,1529,400,406,404,401]),
  ([15,39,49,71,103,135,156],[2407,1566,405,402]),
  ([16,39,49,71,103,120,135],[1937,1649]),
  ([16,39,49,71,103,135],[329,1437,12,1453,1978,411,1464,153,1845,410,1498,12,1530,409,408]),
  ([17,39,49,71,103,135],[2431,424,1435,12,1455,329,1468,199,1845,420,1498,12,1531,412,422,419,414]),
  ([17,39,49,71,103,135,162],[2411,207,1775,415]),
  ([17,39,49,71,135,162],[2480,425,1752,20,1763,339,1767,20,1786,413,423,421,416,417,418]),
  ([19,28,39,49,71,103,135],[12,1441,668,631,608,598,589,515,497,482,472,462,436]),
  ([19,28,39,71,103,135],[2204,496,630,715,439,634,434,432,643,429,638,438,511,435,501,433,430,301,437,431,428]),
  ([19,39,49,56,71,103,135],[2292,2060,904,898,890,436])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b5ok : f6b5.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b6 : Array Row := #[
  ([19,39,49,58,71,103,135],[2306,2075,12,1463,962,948,939,517,500,489,480,473,459,447]),
  ([19,39,49,71,83,103,135],[2332,2094,1891,1046,1038,506,446]),
  ([19,39,49,71,86,103,135],[2343,2104,1899,1071,1063,443,477]),
  ([19,39,49,71,92,103,135],[2349,2118,1907,12,1500,4,1165,1102,518,502,483,468,459]),
  ([19,39,49,71,92,135],[4,2368,513,1143,2137,494,1139,1923,478,1145,4,1847,470,1164,4,1220,452,1177,428,514,449,490,495,450,488,474,479,447,451]),
  ([19,39,49,71,103,120,135],[2391,2155,1937,1650,12,1333,1321,441]),
  ([19,39,49,71,103,125,135],[2397,2163,1940,1662,1329]),
  ([19,39,49,71,103,135,140],[2404,2173,1947,1718,1552,12,1367]),
  ([19,39,49,71,103,135,156],[2408,2177,1954,1734,1567,485,453]),
  ([19,39,49,71,103,135,162],[2412,2181,1959,20,1776,1571,507,456]),
  ([19,39,49,71,103,135,173],[2420,2186,1964,1795,1583,12,1385,437,440,448,449,454]),
  ([19,39,49,71,103,135,182],[2426,2192,1967,1803,1592,450,455]),
  ([19,39,49,71,103,135,250],[2448,1973,1817,1600]),
  ([19,39,49,71,103,135,257],[43,2206,1976,1821,1603,875,439,512]),
  ([19,39,49,71,103,135,274],[2450,2207,1825,1607,508,486]),
  ([19,39,49,71,103,135,323],[2451,2213,1983,24,1617,1312,463]),
  ([19,39,49,71,103,135,371],[2452,2217,1988,1849,15,1365,452,458]),
  ([19,39,49,71,103,371],[15,2469,519,1603,2237,503,1600,2003,484,1607,15,1879,476,1617,1558,458,1561,429,458,491,458,475,458,458]),
  ([19,39,49,71,135,162],[20,2481,520,1760,2250,504,1756,2031,486,1764,20,1873,475,1787,431,302,509,477,492,485,464,465,466]),
  ([19,39,49,71,135,323],[24,2489,521,1821,2257,505,1817,2040,487,1825,24,1879,476,1849,1636,463,1638,432,463,493,463,463,463]),
  ([19,39,49,103,135,274],[30,2500,522,1976,2268,510,1973,30,2040,487,1983,30,2003,484,1988,1357,457,1464,434,457,457,478,457,457]),
  ([19,39,71,86,103,135],[2510,523,2107,508,493,2114,491,2111,506,445,442,444,509,492,507,489,490]),
  ([19,39,71,103,135,250],[36,2515,524,2206,2268,510,2207,36,2257,505,2213,36,2237,503,2217,1357,457,1442,457,504,457,494,457,457]),
  ([19,49,71,103,135,257],[2515,524,2448,2500,522,2450,43,2489,521,2451,43,2469,519,2452,2285,512,2286,523,512,520,512,513,512,512]),
  ([20,39,49,71,103,135],[12,1449,2205,532,1442,457,1466,12,1502,103,1626,528,1533,525,531,529,526]),
  ([20,39,49,71,103,135,156],[2177,1567,530,527]),
  ([21,39,49,71,103,125,135],[1940,1662]),
  ([21,39,49,71,103,135],[12,1450,457,1444,1978,536,1464,153,1848,535,1501,12,1534,534,533]),
  ([22,39,49,71,103,135],[12,1454,2205,549,1442,457,1470,253,1848,545,1501,12,1535,537,547,544,539]),
  ([22,39,49,71,103,135,162],[2181,261,1776,540]),
  ([22,39,49,71,135,162],[20,1762,2250,550,1756,467,1768,20,1788,538,548,546,541,542,543]),
  ([24,39,49,56,71,103,135],[2292,2062,904,899,891,555,557])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b6ok : f6b6.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b7 : Array Row := #[
  ([24,39,49,71,103,135],[329,2449,569,1448,457,2219,567,1451,1978,564,1464,12,1850,562,1503,12,1627,560,1537,556,553,554,568,566,565,561,563,558,559]),
  ([28,39,49,56,71,103,135],[2290,2060,905,900,892]),
  ([28,39,49,58,71,103,135],[2305,2075,12,1473,963,949,940,684,670,636,608,601,587,576]),
  ([28,39,49,71,83,103,135],[2329,2094,1894,1047,1039,685,575]),
  ([28,39,49,71,86,103,135],[2342,2104,1902,1072,1064,686,574]),
  ([28,39,49,71,92,103,135],[2348,2118,1908,12,1504,4,1167,1103,688,671,656,637,622,610,596,587]),
  ([28,39,49,71,92,135],[2367,658,1135,2137,624,1139,4,1924,606,1152,4,1851,599,1166,4,1221,580,1179,689,616,650,303,659,660,577,657,428,625,626,578,623,615,602,607,576,579]),
  ([28,39,49,71,103,120,135],[2389,2155,1938,1651,1322,690]),
  ([28,39,49,71,103,125,135],[2396,2163,1941,1663,1330,691]),
  ([28,39,49,71,103,135,140],[2403,2173,1948,1719,1553,12,1375,693]),
  ([28,39,49,71,103,135,156],[2407,2177,1957,1735,1568,12,1384,694,673,400,639,525,612,581]),
  ([28,39,49,71,103,135,162],[2411,2181,1962,20,1777,1572,12,1392,695,412,537,584]),
  ([28,39,49,71,103,135,173],[2417,2186,1965,1796,1585,696,640,629,577,582]),
  ([28,39,49,71,103,135,182],[2425,2192,1968,1804,1594,697,674,663,578,583]),
  ([28,39,49,71,103,135,241],[2200,1971,1813,1597,699]),
  ([28,39,49,71,103,135,250],[2432,1974,1818,1601,700]),
  ([28,39,49,71,103,135,293],[2439,2210,31,1831,1612,1026,701,310,435,613,605]),
  ([28,39,49,71,103,135,331],[2443,2214,1990,25,1618,1315,702,591]),
  ([28,39,49,71,103,135,386],[2447,2218,1991,1853,16,1374,703,675,641,580,586]),
  ([28,39,49,71,103,386],[2468,676,1597,2238,642,1601,16,2004,611,1612,16,1880,604,1618,1573,586,1576,704,617,651,305,586,430,586,603,586,586]),
  ([28,39,49,71,135,162],[2480,679,1752,2250,645,1756,20,2034,613,1771,20,1874,603,1790,20,1809,595,1746,705,618,652,306,678,413,431,644,538,612,592,593,594]),
  ([28,39,49,71,135,331],[2488,681,1813,2258,647,1818,25,2042,614,1831,25,1880,604,1853,1641,591,1642,706,619,653,308,680,591,433,646,591,591,591]),
  ([28,39,49,103,135,293],[2499,683,1971,2269,649,1974,31,2042,614,1990,31,2004,611,1991,1886,605,1887,707,620,654,682,605,648,605,606,605,605]),
  ([28,39,56,71,103,135],[699,2067,620,2064,619,617,311,685,187,690,46,696,553,629,618,616]),
  ([28,39,71,103,135,182],[712,2267,648,2197,2255,646,2198,641,312,717,640,708,713,629,711,644,639,621,626,622,623,627]),
  ([28,39,71,103,135,250],[2513,714,2200,36,2269,649,2210,36,2258,647,2214,36,2238,642,2218,1357,585,1442,313,710,585,645,585,624,585,585]),
  ([28,49,56,71,103,135],[700,2297,654,2294,653,651,436,686,241,691,92,697,554,663,652,650]),
  ([28,49,71,103,135,173],[710,2497,682,2422,2485,680,2423,675,437,717,674,708,713,663,709,678,673,655,660,656,657,661]),
  ([28,49,71,103,135,241],[2513,714,2432,42,2499,683,2439,42,2488,681,2443,42,2468,676,2447,1357,585,1435,438,712,585,679,585,658,585,585]),
  ([28,56,71,103,135],[0,2507,707,2505,701,0,706,702,0,704,703,556,555,687,295,692,138,713,698,142,705,695,684,694,689,688,693]),
  ([29,39,49,71,103,135],[2431,726,1435,585,1443,12,1481,12,1506,57,1628,721,1543,723,315,724,722,718]),
  ([29,39,49,71,103,135,182],[2425,628,1594,727,725,719,720])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b7ok : f6b7.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b8 : Array Row := #[
  ([30,39,49,71,103,135],[585,1436,2205,736,1442,12,1482,12,1507,103,1628,731,1543,733,440,734,732,728]),
  ([30,39,49,71,103,135,173],[662,2186,1585,737,735,729,730]),
  ([31,39,49,71,103,125,135],[2396,1663]),
  ([31,39,49,71,103,135],[2431,744,1435,585,1445,12,1484,199,1852,740,1505,12,1544,742,316,743,741,739,738]),
  ([33,39,49,71,103,120,135],[2155,1651]),
  ([33,39,49,71,103,135],[585,1438,2205,751,1442,12,1486,253,1852,748,1505,12,1545,749,752,441,750,747,746]),
  ([35,39,49,71,86,103,135],[2342,2108,1902,1073,1065,794,791,771]),
  ([35,39,49,71,103,135],[2431,783,1435,585,2219,761,1451,329,1989,758,1480,12,1856,757,1512,12,1629,755,1546,574,795,759,762,317,765,188,774,47,779,442,760,756,754]),
  ([35,49,71,86,103,135],[797,792,770,768,444,796,769,291,782,764,781,766]),
  ([35,49,71,103,135],[574,799,784,317,793,785,1,790,786,1,788,787,445,443,767,242,775,93,798,780,143,789,778,763,777,773,772,776]),
  ([39,44,49,71,83,103,135],[2332,2277,2094,1894,1048,1040,853,833]),
  ([39,44,49,71,103,135],[585,2449,1448,2276,575,2278,824,2274,372,2275,2205,845,1442,457,1989,823,1480,12,1858,822,1517,12,1630,820,1548,446,832,243,837,94,842,821,819]),
  ([39,44,71,83,103,135],[2280,373,2279,854,831,829,830,237,844,826,843,827]),
  ([39,44,71,103,135],[575,2282,846,374,318,828,189,836,48,2281,841,446,855,847,2,852,848,2,850,849,144,851,840,825,839,835,834,838]),
  ([39,49,56,58,71,103,135],[684,2293,2063,12,1077,558,904,901,888,877]),
  ([39,49,56,71,83,103,135],[685,2066,824,875,1081]),
  ([39,49,56,71,86,103,135],[686,2296,762,876,1081]),
  ([39,49,56,71,91,103,135],[687]),
  ([39,49,56,71,92,103,135],[688,2295,2065,12,1332,296,1115,1094,906,896,888]),
  ([39,49,56,71,92,135],[689,616,650,2287,2289,879,2057,2059,880,559,1080,4,1114,139,1208,881,1132,908,902,903,877,882]),
  ([39,49,56,71,103,120,135],[690,749,818,1335]),
  ([39,49,56,71,103,125,135],[691,742,874,1335]),
  ([39,49,56,71,103,130,135],[692]),
  ([39,49,56,71,103,135,140],[693,299,1399]),
  ([39,49,56,71,103,135,156],[694,1562,570,1395,907,883]),
  ([39,49,56,71,103,135,162],[695,563,297,1667,572,1396,887]),
  ([39,49,56,71,103,135,173],[696,733,815,1391,879,884]),
  ([39,49,56,71,103,135,182],[697,723,872,1391,880,885]),
  ([39,49,56,71,103,135,195],[698,878,881,886]),
  ([39,49,56,71,135,162],[705,618,652,2288,2058,565,557,561,1082,141,1745,573,1749,907,893,894,895]),
  ([39,49,58,71,83,103,135],[2334,375,2096,825,1891,1049,1036,910]),
  ([39,49,58,71,86,103,135],[2344,763,2109,489,1899,1074,1061,911])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b8ok : f6b8.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b9 : Array Row := #[
  ([39,49,58,71,92],[576,877,3,2377,1209,2303,920,319,910,3,2304,923,3,2147,1210,2073,921,447,911,3,2074,924,960,919,3,1881,954,1214,925,3,961,928]),
  ([39,49,58,71,92,103],[2354,1095,2299,2300,190,912,2124,1096,2069,2070,244,913,956,1621,936,1097,3,927,957,145,916,922]),
  ([39,49,58,71,92,103,135],[2350,2308,2120,2078,1907,12,1518,4,1175,1098,964,946,937,914]),
  ([39,49,58,71,92,135],[4,2369,1150,2301,2302,49,917,4,2139,1151,2071,2072,95,918,1923,958,1145,4,1859,950,1170,1215,926,1171,969,952,959,915,926]),
  ([39,49,58,71,103,120,135],[2392,2157,1937,1653,12,1378,1319,912,929]),
  ([39,49,58,71,103,125,135],[2398,2166,1940,1665,12,1382,1327,913,930]),
  ([39,49,58,71,103,135,140],[2405,2175,1947,1720,1550,914]),
  ([39,49,58,71,103,135,156],[2409,2179,1954,1736,1563,966,915,931]),
  ([39,49,58,71,103,135,162],[2413,2183,1959,20,1784,1569,916,934]),
  ([39,49,58,71,103,135,173],[2421,2188,1964,1797,1579,917,932]),
  ([39,49,58,71,103,135,182],[2427,2196,1967,1805,1588,918,933]),
  ([39,49,58,71,103,135,274],[2453,2223,1826,1605,967,919]),
  ([39,49,58,71,103,135,285],[44,2298,2224,1979,1829,1610,1023,920]),
  ([39,49,58,71,103,135,289],[2455,38,2068,1980,1830,1611,1025,921]),
  ([39,49,58,71,103,135,351],[2456,2226,1984,1860,926]),
  ([39,49,58,71,103,135,361],[2457,2227,1986,26,1623,1361,927,944]),
  ([39,49,58,71,103,351],[13,2470,1610,2309,935,13,2240,1611,2079,935,2001,965,1605,13,1882,955,1623,1357,935,1519,953,935,935]),
  ([39,49,58,71,135,162],[20,2482,1769,2310,20,2252,1770,2080,2031,967,1764,1871,953,1780,966,941,942,943]),
  ([39,49,58,71,135,361],[26,2490,1829,2311,944,26,2260,1830,2081,944,2041,968,1826,1882,955,1860,1712,944,1715,944,944]),
  ([39,49,58,103,135,274],[30,2501,1979,2312,935,30,2271,1980,2082,935,30,2041,968,1986,2001,965,1984,1357,935,1464,960,956,958,935,935]),
  ([39,49,59,71,83,103,135],[2334,826,1036,970]),
  ([39,49,59,71,103,135],[57,2454,1474,2313,12,1478,935,1465,12,1527,1622,974,1519,975,971,972,973]),
  ([39,49,60,71,86,103,135],[764,2109,1061,976]),
  ([39,49,60,71,103,135],[12,1475,103,2225,1477,2083,935,1466,12,1528,1622,980,1519,981,977,978,979]),
  ([39,49,62,71,103,135],[12,1476,12,1479,1978,986,1464,153,1862,985,1526,935,1520,984,983]),
  ([39,49,62,71,103,135,140],[1947,1720]),
  ([39,49,65,71,103,135],[655,329,2454,1474,2315,2316,997,2314,12,2228,1485,2084,448,1978,998,1464,12,1863,996,1532,935,1625,994,1529,995,989,990,991]),
  ([39,49,65,71,103,135,173],[2421,2317,2189,1964,1798,1582,992,993]),
  ([39,49,67,71,103,135],[621,12,2458,1483,2318,320,457,2225,1477,2086,2087,1008,2085,1978,1009,1464,12,1864,1007,1536,935,1626,1005,1533,1006,1000,1001,1002]),
  ([39,49,67,71,103,135,182],[2428,2196,2088,1967,1806,1592,1003,1004]),
  ([39,49,71,83,86,103,135],[2504,392,765,506,832,1889,1026,1081]),
  ([39,49,71,83,91,103,135],[833])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b9ok : f6b9.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b10 : Array Row := #[
  ([39,49,71,83,92,103,135],[2335,2323,834,2097,1895,12,1386,238,1133,972,1044,1036]),
  ([39,49,71,83,92,135],[2287,376,2325,2326,1027,2324,1888,835,819,827,1080,2093,1028,1897,1050,1890,910,4,1128,971,970,973,1129,1029]),
  ([39,49,71,83,103,120,135],[836,816,1393]),
  ([39,49,71,83,103,125,135],[837,1658,862,1396]),
  ([39,49,71,83,103,135,140],[838,987,1397]),
  ([39,49,71,83,103,135,156],[2337,406,839,1896,1016,1387,1030]),
  ([39,49,71,83,103,135,162],[393,422,840,239,1747,1018,1393,1034]),
  ([39,49,71,83,103,135,173],[841,997,1023,1387,1027,1031]),
  ([39,49,71,83,103,135,182],[2338,2328,2264,842,1586,1024,1395,1028,1033]),
  ([39,49,71,83,103,135,190],[843,857,1032]),
  ([39,49,71,83,103,135,197],[844,865,1035]),
  ([39,49,71,83,135,162],[2288,395,349,378,2340,423,1889,851,821,830,1082,1896,975,1743,1019,1747,1041,1042,1043]),
  ([39,49,71,86,91,103,135],[771]),
  ([39,49,71,86,92,103,135],[772,2345,2110,2098,1903,12,1389,292,1134,978,1069,1061]),
  ([39,49,71,86,92,135],[2057,1888,773,754,766,1080,2341,1052,490,2100,2101,1053,2099,1905,1075,1898,911,4,1130,977,976,979,1131,1054]),
  ([39,49,71,86,103,120,135],[774,1646,817,1396]),
  ([39,49,71,86,103,125,135],[775,873,1394]),
  ([39,49,71,86,103,135,140],[776,988,1398]),
  ([39,49,71,86,103,135,156],[777,2112,531,1904,1017,1390,1055]),
  ([39,49,71,86,103,135,162],[778,507,547,293,1748,1020,1394,1059]),
  ([39,49,71,86,103,135,173],[2494,779,2113,2103,1577,1022,1395,1052,1056]),
  ([39,49,71,86,103,135,182],[780,1008,1025,1390,1053,1057]),
  ([39,49,71,86,103,135,193],[781,801,1058]),
  ([39,49,71,86,103,135,198],[782,808,1060]),
  ([39,49,71,86,135,162],[2058,1889,789,756,769,1082,509,477,492,2115,548,1904,981,1744,1021,1748,1066,1067,1068]),
  ([39,49,71,91,103,135],[1082,300,1396,982,1395,1080]),
  ([39,49,71,92,103,120,135],[2393,2347,2158,1939,1647,1319]),
  ([39,49,71,92,103,125,135],[2399,2167,2117,1942,1659,1327]),
  ([39,49,71,92,103,135,140],[2406,2176,1949,1716,1550]),
  ([39,49,71,92,103,135,156],[2410,2180,1958,1918,1732,1563,1085,1123]),
  ([39,49,71,92,103,135,162],[2414,2184,1963,1772,1569,1090]),
  ([39,49,71,92,103,135,173],[2424,2358,2190,1966,1793,1579,1180,1086,1125])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b10ok : f6b10.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b11 : Array Row := #[
  ([39,49,71,92,103,135,182],[2429,2199,2129,1969,1801,1588,1181,1088,1127]),
  ([39,49,71,92,103,135,309],[2459,2229,1992,1613]),
  ([39,49,71,92,103,135,336],[45,227,2359,2352,2346,2230,1993,1837,1619,1316,1104]),
  ([39,49,71,92,103,135,343],[2461,39,276,2130,2123,2116,1994,1838,1620,1324,1109]),
  ([39,49,71,92,103,135,351],[2462,2232,1995,1839,1182]),
  ([39,49,71,92,103,135,378],[2463,2233,32,169,1920,957,1906,1843,1624,1368,1120]),
  ([39,49,71,92,103,173],[656,2323,2352,191,2360,1106,2347,2235,1578,2122,245,1111,1094,1999,1584,1910,146,1186,990,1194,1087,1190]),
  ([39,49,71,92,103,182],[622,2465,1587,2353,192,1107,1094,2098,2123,246,2131,1112,2117,2000,1593,1911,147,1187,1001,1203,1089,1200]),
  ([39,49,71,92,103,351],[13,2471,1619,2355,193,1108,1091,13,2241,1620,2125,247,1113,1091,13,2005,1624,1912,148,1188,1091,1877,1211,1613,1357,1091,1519,1119,1091,1171]),
  ([39,49,71,92,120,135],[2359,2360,1106,2358,2243,1652,2126,746,1115,1107,2007,1654,1913,408,1133,912,1108,1083,1125]),
  ([39,49,71,92,125,135],[2474,1664,2361,738,1115,1111,2130,2131,1112,2129,2009,1666,1914,533,1134,913,1113,1084,1127]),
  ([39,49,71,92,135,140],[2362,1180,234,1125,2132,1181,288,1127,2017,1721,1915,914,983,1123,1182]),
  ([39,49,71,92,135,156],[2363,1183,401,1129,2133,1184,526,1131,2030,1737,1919,915,1185]),
  ([39,49,71,92,135,162],[20,2483,1778,2364,1186,414,1133,20,2253,1779,2134,1187,539,1134,20,2035,1789,1920,916,1918,1871,1188,1780,1116,1117,1118,1123]),
  ([39,49,71,92,135,173],[657,2324,2365,50,2135,96,1191,728,1132,2036,1799,1921,917,1183,991,1129,1197]),
  ([39,49,71,92,135,182],[623,2366,51,1191,718,1132,2099,2136,97,2037,1807,1922,918,1184,1002,1131,1206]),
  ([39,49,71,92,135,309],[22,2491,1837,2370,1194,1091,22,2261,1838,2140,1203,1091,22,2043,1843,1925,922,1091,1877,1211,1839,1357,1091,1493,1091]),
  ([39,49,71,92,135,336],[659,2289,381,2325,41,85,2375,1195,2365,2356,1104,2357,2262,1854,2141,1204,1104,2044,1855,1926,923,1104,1212,1104,1104]),
  ([39,49,71,92,135,343],[625,2059,2492,1854,2372,1196,1109,495,2100,35,126,2146,1205,2136,2127,1109,2128,2045,1857,1927,924,1109,1213,1109,1109]),
  ([39,49,71,92,135,351],[2373,52,1197,2143,98,1206,2046,1861,1928,926,1185]),
  ([39,49,71,92,135,378],[351,1890,27,2493,1855,2374,1198,1120,479,1898,27,2263,1857,2144,1207,1120,33,27,29,961,928,959,1919,1916,1120,1917,1883,1216,1861,1728,1120,1731,1120]),
  ([39,49,71,92,173],[660,577,879,321,2326,1027,5,2375,1195,449,1052,5,2145,1196,729,1208,1193,5,2050,1875,1930,1198,989,992,1192]),
  ([39,49,71,92,182],[626,578,880,322,1028,6,2376,1204,719,1208,1202,450,2101,1053,6,2146,1205,6,2051,1876,1931,1207,1000,1003,1201]),
  ([39,49,71,92,351],[579,882,323,1029,7,2378,1212,1119,1171,451,1054,7,2148,1213,1119,1171,7,2052,1883,1932,1216,1119,1171,1119,1171]),
  ([39,49,71,93,103,120,135],[2393,2379,1105,1319]),
  ([39,49,71,93,103,135],[57,2460,1508,2380,1222,12,1514,1225,1223,12,1539,1226,929,1119,1083,1091,1494,1622,1224,1519,1083]),
  ([39,49,71,94,103,125,135],[2167,2149,1110,1327]),
  ([39,49,71,94,103,135],[12,1509,1230,1227,103,2231,1513,2150,1228,12,1540,1231,930,1119,1084,1091,1495,1622,1229,1519,1084]),
  ([39,49,71,96,103,135],[12,1510,195,1235,1233,12,1515,249,1236,1234,153,1996,1538,1933,149,1239,1836,1245,1493,1091,1520,1085,1237]),
  ([39,49,71,96,103,135,156],[1958,1934,1732,1240]),
  ([39,49,71,96,135],[581,883,325,1030,8,1246,53,1252,1241,453,1055,8,1247,99,1253,1242,149,2047,1865,1936,1249,931,1238,1119,1085,1248]),
  ([39,49,71,96,135,156],[1250,402,1243,1251,527,1244,2030,1737,1935,1121])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b11ok : f6b11.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b12 : Array Row := #[
  ([39,49,71,97,103,135],[199,2460,1508,2381,196,1255,12,1516,250,1256,1254,12,1541,150,1259,1836,1265,1493,1091,1521,1086,1257]),
  ([39,49,71,97,103,135,173],[2424,2382,1793,1092,1087,1261]),
  ([39,49,71,97,135],[582,884,326,1031,196,2384,1266,54,1260,454,1056,9,1267,100,1272,1262,9,1866,1269,932,1258,1119,1086,1268]),
  ([39,49,71,97,135,173],[661,2327,2383,1271,730,1264,1800,1270,993,1263,1189,1087,1124]),
  ([39,49,71,99,103,135],[12,1511,197,1279,1278,253,2231,1513,2151,251,1280,12,1542,151,1283,1836,1289,1493,1091,1523,1088,1281]),
  ([39,49,71,99,103,135,182],[2199,2152,1801,1093,1089,1286]),
  ([39,49,71,99,135],[583,885,327,1033,10,1290,55,1295,1284,455,1057,251,2154,1291,101,1285,10,1867,1293,933,1282,1119,1088,1292]),
  ([39,49,71,99,135,182],[627,1296,720,1288,2102,2153,1808,1294,1004,1287,1199,1089,1126]),
  ([39,49,71,103,120,125,135],[1315,1335]),
  ([39,49,71,103,120,130,135],[]),
  ([39,49,71,103,120,135,140],[1307,1379]),
  ([39,49,71,103,120,135,156],[2394,2006,1235,1309,1397]),
  ([39,49,71,103,120,135,162],[1310,1393,1317]),
  ([39,49,71,103,120,135,173],[1106,1255,1222,1316,1379]),
  ([39,49,71,103,120,135,177],[]),
  ([39,49,71,103,120,135,182],[2395,2242,750,1107,1279,1223,1314,1399]),
  ([39,49,71,103,120,135,197],[866,1318]),
  ([39,49,71,103,125,130,135],[]),
  ([39,49,71,103,125,135,140],[1308,1383]),
  ([39,49,71,103,125,135,156],[2168,2008,1236,1311,1398]),
  ([39,49,71,103,125,135,162],[1312,1394,1325]),
  ([39,49,71,103,125,135,173],[2472,743,2169,1111,1256,1227,1313,1399]),
  ([39,49,71,103,125,135,182],[1112,1280,1228,1324,1383]),
  ([39,49,71,103,125,135,186],[]),
  ([39,49,71,103,125,135,198],[809,1326]),
  ([39,49,71,103,130,135],[1667,571,1396,1115,1232,1399]),
  ([39,49,71,103,131],[584,887,328,1034,204,198,1643,1317,11,2402,1347,456,1059,258,252,1655,1325,11,2172,1348,158,152,1685,1338,934,1946,1346,1116,1090,1702,1345]),
  ([39,49,71,103,131,135],[205,1644,12,2464,1547,2400,56,1340,259,1656,12,2234,1549,2170,102,1341,159,1670,935,1996,1538,1943,934,1337,1119,1091,1117,1862,1526,1677,1116,1090,1117,1681,1336,1668,1622,1344,1519]),
  ([39,49,71,103,131,135,162],[2415,2185,1963,1944,1122,1784,1118,1682,1569,1339]),
  ([39,49,71,103,131,162],[206,1645,2401,415,1342,260,1657,2171,540,1343,160,1945,1118,1692]),
  ([39,49,71,103,135,140,156],[2016,1237,1358,1373]),
  ([39,49,71,103,135,140,162],[1336,1361,1373])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b12ok : f6b12.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b13 : Array Row := #[
  ([39,49,71,103,135,140,165],[]),
  ([39,49,71,103,135,140,173],[1180,1257,1359,1379]),
  ([39,49,71,103,135,140,177],[]),
  ([39,49,71,103,135,140,182],[1181,1281,1360,1383]),
  ([39,49,71,103,135,140,186],[]),
  ([39,49,71,103,135,156,162],[173,1239,1740,1337,1368,1373]),
  ([39,49,71,103,135,156,165],[2023,1240]),
  ([39,49,71,103,135,156,173],[2024,1183,1241,1258,1362,1387]),
  ([39,49,71,103,135,156,182],[2025,1184,1242,1282,1365,1390]),
  ([39,49,71,103,135,156,190],[859,2026,1243,1275]),
  ([39,49,71,103,135,156,193],[803,2027,1244,1299]),
  ([39,49,71,103,135,162,165],[1339]),
  ([39,49,71,103,135,162,173],[2473,2416,1997,1186,1259,1741,1340,1363,1397]),
  ([39,49,71,103,135,162,182],[2244,2191,1998,1187,1283,1742,1341,1366,1398]),
  ([39,49,71,103,135,162,197],[868,1342,1351]),
  ([39,49,71,103,135,162,198],[811,1343,1355]),
  ([39,49,71,103,135,165],[426,1397,551,1398,1740,1123]),
  ([39,49,71,103,135,173,177],[1190,1261]),
  ([39,49,71,103,135,173,182],[708,724,734,1191,1262,1284,1374,1391]),
  ([39,49,71,103,135,173,190],[860,1192,1263,1276]),
  ([39,49,71,103,135,173,195],[709,735,1013,1193,1264,1304]),
  ([39,49,71,103,135,177],[753,1399,1741,999,1397,1125]),
  ([39,49,71,103,135,182,186],[1200,1286]),
  ([39,49,71,103,135,182,193],[804,1201,1287,1300]),
  ([39,49,71,103,135,182,195],[711,725,1014,1202,1288,1305]),
  ([39,49,71,103,135,186],[745,1399,1742,1010,1398,1127]),
  ([39,49,71,103,135,190],[1586,858,856,861,1395,1743,1129,1274,1273,1277,1397]),
  ([39,49,71,103,135,193],[1577,802,800,805,1395,1744,1131,1298,1297,1301,1398]),
  ([39,49,71,103,135,195],[713,629,663,2328,2103,1745,1562,1012,1011,1015,1395,1208,1094,1132,1303,1302,1306,1399]),
  ([39,49,71,103,135,197],[2416,1658,867,863,869,1396,1747,1133,1349,1350,1352,1397]),
  ([39,49,71,103,135,198],[1646,810,806,812,1396,2191,1748,1134,1353,1354,1356,1398]),
  ([39,49,71,103,135,241],[665,2290,383,2329,228,2389,86,2417,1752,1135])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b13ok : f6b13.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b14 : Array Row := #[
  ([39,49,71,103,135,242],[666,2330,2390,815,815,1753,815,1136,815,815]),
  ([39,49,71,103,135,243],[2291,384,2418,816,816,1754,816,1137,816,816]),
  ([39,49,71,103,135,244],[667,2331,2419,818,818,1755,818,1138,818,818]),
  ([39,49,71,103,135,250],[631,2060,497,2104,277,2163,127,2192,1756,1139]),
  ([39,49,71,103,135,251],[632,872,2105,2164,872,1757,872,1140,872,872]),
  ([39,49,71,103,135,252],[2061,873,498,2193,873,1758,873,1141,873,873]),
  ([39,49,71,103,135,253],[633,874,2106,2194,874,1759,874,1142,874,874]),
  ([39,49,71,103,135,257],[715,634,668,2292,385,2332,229,2391,87,2420,2285,875,2286,2107,875,1760,875,1143,875,875]),
  ([39,49,71,103,135,260],[716,635,669,2062,2333,876,499,2108,278,2165,128,2195,2055,876,2056,1761,876,1144,876,876]),
  ([39,49,71,103,135,274],[352,1891,480,1899,170,2031,1764,1959,962,1954,1145]),
  ([39,49,71,103,135,275],[1016,1900,1016,2032,1765,1960,1016,1146,1016,1016]),
  ([39,49,71,103,135,276],[1892,1017,1017,2033,1766,1961,1017,1147,1017,1017]),
  ([39,49,71,103,135,278],[353,1018,1901,1018,1767,1955,1018,1148,1018,1018]),
  ([39,49,71,103,135,280],[1893,1020,481,1020,1768,1956,1020,1149,1020,1020]),
  ([39,49,71,103,135,285],[670,2293,386,2334,230,2392,88,2421,2320,1023,2322,1023,1769,1023,1209,1095,1150,1023,1023]),
  ([39,49,71,103,135,289],[636,2063,1025,500,2109,279,2166,129,2196,2090,1025,2092,1770,1025,1210,1096,1151,1025,1025]),
  ([39,49,71,103,135,293],[2505,2064,2294,397,354,387,1894,2422,1026,511,482,501,1902,2197,1026,171,2034,1771,1962,963,1957,1886,1026,1887,1152,1026,1026]),
  ([39,49,71,103,135,309],[209,1647,263,1659,162,1772,1159,1716]),
  ([39,49,71,103,135,310],[1307,1660,1307,1773,1307,1160,1307,1307]),
  ([39,49,71,103,135,311],[1648,1308,1308,1774,1308,1161,1308,1308]),
  ([39,49,71,103,135,317],[210,1649,1310,264,1661,1310,163,1775,1310,1163,1717,1632,1310,1634,1310]),
  ([39,49,71,103,135,323],[211,1650,1312,265,1662,1312,164,1776,1312,1165,1718,1636,1312,1638,1312]),
  ([39,49,71,103,135,331],[212,1651,2423,1315,266,1663,2198,1315,165,1777,1315,1167,1719,1641,1315,1642,1315]),
  ([39,49,71,103,135,336],[671,2295,388,2335,231,2393,89,2424,2386,1316,2388,1664,1587,1316,1778,1316,1168,1316,1316]),
  ([39,49,71,103,135,343],[637,2065,1652,1578,1324,502,2110,280,2167,130,2199,2160,1324,2162,1779,1324,1169,1324,1324]),
  ([39,49,71,103,135,351],[58,1579,104,1588,1780,937,1563,1215,1098,1171,1550]),
  ([39,49,71,103,135,353],[1580,1358,1589,1358,1781,1358,1172,1358,1358]),
  ([39,49,71,103,135,355],[1359,1590,1359,1782,1564,1359,1217,1099,1173,1359,1359]),
  ([39,49,71,103,135,358],[1581,1360,1360,1783,1565,1360,1218,1100,1174,1360,1360]),
  ([39,49,71,103,135,361],[213,1653,1361,267,1665,1361,166,1784,1361,1175,1720,1712,1361,1715,1361]),
  ([39,49,71,103,135,365],[672,2336,59,1582,1362,105,1591,1362,1785,938,1566,1362,1219,1101,1176,1551,1362,1554,1362,1557]),
  ([39,49,71,103,135,371],[638,60,1583,1365,2111,106,1592,1365,1787,939,1567,1365,1220,1102,1177,1552,1365,1558,1365,1561])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b14ok : f6b14.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b15 : Array Row := #[
  ([39,49,71,103,135,378],[355,1895,214,1654,1584,1368,483,1903,268,1666,1593,1368,176,167,172,2035,1789,1963,964,1958,1950,1368,1953,1178,1721,1728,1368,1731,1368]),
  ([39,49,71,103,135,386],[61,1585,1374,107,1594,1374,1790,940,1568,1374,1221,1103,1179,1553,1374,1573,1374,1576]),
  ([39,49,71,103,156,173],[673,2337,2394,1577,1562,2048,1868,1997,1252,1233,1250,1270,1554,1555,1556]),
  ([39,49,71,103,156,182],[639,1586,1562,2112,2168,2049,1869,1998,1253,1234,1251,1294,1558,1559,1560]),
  ([39,49,71,103,173,182],[717,640,674,2338,2395,727,2113,2169,737,1870,1586,1577,1272,1254,1271,1295,1278,1296,1573,1574,1575]),
  ([39,49,71,103,351],[587,888,331,1036,200,1319,1357,1519,459,1061,254,1327,1357,1519,154,1871,1569,1357,1519,1357,1519]),
  ([39,49,71,103,365],[677,588,889,332,2339,1037,201,1320,1554,1557,460,1062,255,1328,1554,1557,155,1872,1570,1554,1557,1554,1557]),
  ([39,49,71,103,371],[643,589,890,333,1038,202,1321,1558,1561,461,2114,1063,256,1329,1558,1561,156,1873,1571,1558,1561,1558,1561]),
  ([39,49,71,103,386],[590,892,334,1039,203,1322,1573,1576,462,1064,257,1330,1573,1576,157,1874,1572,1573,1576,1573,1576]),
  ([39,49,71,120,125,135],[2472,2242,1658,1646,1641,1639,1640,1225,1230]),
  ([39,49,71,120,135,162],[2473,747,1667,1646,409,1747,2006,1226,1741,1632,1631,1633,1747,1643,1644,1645]),
  ([39,49,71,125,135,162],[739,1667,1658,2244,534,1748,2008,1231,1742,1636,1635,1637,1748,1655,1656,1657]),
  ([39,49,71,131],[592,893,336,1041,17,2478,1704,464,1066,17,2248,1705,941,2015,1703]),
  ([39,49,71,131,135],[593,894,337,1042,18,2476,1679,62,63,1697,1672,465,1067,18,2246,1680,108,109,1698,1673,942,2047,1865,2012,1678,941,942,1683,1669,1701,1676]),
  ([39,49,71,131,135,162],[20,2484,1791,2475,64,1687,417,1674,20,2254,1792,2245,110,1688,542,1675,945,2035,1789,2011,943,2013,1684,2010,1871,1691,1780,1696,1671,1686]),
  ([39,49,71,131,162],[594,895,338,1043,19,2477,1694,416,418,1699,1689,466,1068,19,2247,1695,541,543,1700,1690,943,2014,1693]),
  ([39,49,71,135,140,162],[235,1741,289,1742,2016,984,1740,1681,1668,1682,1712,1713,1714,1740]),
  ([39,49,71,135,156,162],[357,1896,1868,404,1743,485,1904,1869,529,1744,966,1683,1669,1684,1728,1729,1730,1740]),
  ([39,49,71,135,162,165],[427,1750,552,1751,2023,1696,1671,1686]),
  ([39,49,71,135,162,173],[678,2340,2479,1870,732,1745,2048,1868,2024,995,1743,1697,1672,1687,1722,1723,1724,1750]),
  ([39,49,71,135,162,182],[644,1870,722,1745,2115,2249,2049,1869,2025,1006,1744,1698,1673,1688,1725,1726,1727,1751]),
  ([39,49,71,135,162,197],[2479,1810,870,864,871,1749,2028,1699,1674,1689,1707,1706,1708,1750]),
  ([39,49,71,135,162,198],[1810,813,807,814,1749,2249,2029,1700,1675,1690,1710,1709,1711,1751]),
  ([39,49,71,135,309],[596,896,340,1044,65,1793,1357,1493,468,1069,111,1801,1357,1493,946,1732,1357,1493,1357,1493]),
  ([39,49,71,135,317],[597,897,342,1045,66,1794,1632,1634,469,1070,112,1802,1632,1634,947,1733,1632,1634,1632,1634]),
  ([39,49,71,135,323],[598,898,343,1046,67,1795,1636,1638,471,1071,113,1803,1636,1638,948,1734,1636,1638,1636,1638]),
  ([39,49,71,135,331],[600,900,344,1047,68,2485,1796,1641,1642,472,1072,114,2255,1804,1641,1642,949,1735,1641,1642,1641,1642]),
  ([39,49,71,135,361],[601,901,345,1049,69,1797,1712,1715,473,1074,115,1805,1712,1715,951,1736,1712,1715,1712,1715]),
  ([39,49,71,135,378],[602,902,360,346,1897,1050,70,1875,1799,1728,1731,488,474,1905,1075,116,1876,1807,1728,1731,969,952,2030,1737,2018,1728,2022,1731,1728,1731]),
  ([39,49,83,86,103,135],[2506,2066,2296,791,2494,853,2264,1886,1884,1885,1888]),
  ([39,49,92,103,135,378],[32,2502,1993,2495,215,1913,1910,1906,32,2272,1994,2265,269,1914,1911,1906,2043,1925,1992,2005,1912,1995,1950,1906,1953,1915,1916,1906,1917,1906]),
  ([39,49,92,135,378],[607,903,33,29,2503,2044,2496,1926,72,1930,1921,1916,1917,33,29,2273,2045,2266,1927,118,1931,1922,1916,1917,2052,1932,2046,1928,2018,1916,2022,1917,1916,1917])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b15ok : f6b15.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def f6b16 : Array Row := #[
  ([39,49,103,135,156,162],[219,2006,1997,273,2008,1998,1918,2016,1934,2023,1944,1950,1951,1952]),
  ([39,49,103,135,274],[608,904,216,1937,73,1964,1357,1464,270,1940,119,1967,1357,1464,1923,1907,1947,1357,1464,1357,1464]),
  ([39,49,103,135,293],[609,2507,2067,2297,905,217,1938,74,2497,1965,1886,1887,271,1941,120,2267,1968,1886,1887,1924,1908,1948,1886,1887,1886,1887]),
  ([39,49,103,135,378],[610,906,220,218,2007,1939,75,1999,1966,1950,1953,274,272,2009,1942,121,2000,1969,1950,1953,1929,1909,2017,1949,2018,1950,2022,1953,1950,1953]),
  ([39,49,135,156,162],[612,907,76,2048,2024,405,2026,421,2028,122,2049,2025,530,2027,546,2029,2013,2010,2023,2018,2019,2021,2020,2023]),
  ([39,49,135,378],[615,908,78,2050,2036,2018,2022,124,2051,2037,2018,2022,2018,2022]),
  ([39,56,71,86,103,135],[2506,2066,2504,795,759,794,566,2055,2053,2054,2103,2058,2057]),
  ([39,58,71,103,135,289],[38,2516,2224,2508,2068,2271,2082,2223,38,2260,2081,2227,2240,2079,2226,2090,2068,2092,2080,2068,2073,2069,2071,2068,2068]),
  ([39,71,86,103,135,182],[2264,798,760,796,2113,2103,2115,2112,2087,2085,2088,2191,2090,2089,2091,2101,2098,2099,2102]),
  ([39,71,92,103,135,343],[39,2517,2230,2511,221,2126,2122,2116,39,2272,2233,2265,177,2134,2070,2116,2261,2140,2229,2241,2125,2232,2160,2116,2162,2132,2127,2116,2128,2116]),
  ([39,71,92,135,343],[363,2093,35,2518,2262,2512,2141,79,2145,2135,2127,2128,35,2273,2263,2266,2144,2074,2072,2133,2127,2128,2148,2143,2127,2128,2127,2128]),
  ([39,71,103,125,135,182],[2242,741,2169,2244,2191,2168,2131,2117,2129,2152,2149,2160,2159,2161]),
  ([39,71,103,135,250],[364,2094,222,2155,80,2186,1357,1442,178,2250,2181,2075,2177,1357,1442,2137,2118,2173,1357,1442,1357,1442]),
  ([39,71,103,135,260],[365,2509,2095,223,2156,81,2187,2055,2056,179,2251,2182,2076,2178,2055,2056,2138,2119,2174,2055,2056,2055,2056]),
  ([39,71,103,135,289],[366,2096,224,2157,82,2188,2090,2092,180,2252,2183,2077,2179,2090,2092,2147,2124,2139,2120,2175,2090,2092,2090,2092]),
  ([39,71,103,135,343],[367,2097,225,2243,2158,83,2235,2190,2160,2162,181,2253,2184,2078,2180,2160,2162,2142,2121,2176,2160,2162,2160,2162]),
  ([49,56,71,83,103,135],[2506,2296,2504,2278,2274,2277,568,2285,2283,2284,2328,2288,2287]),
  ([49,58,71,103,135,285],[44,2516,2455,2508,2298,2501,2312,2453,44,2490,2311,2457,2470,2309,2456,2320,2298,2322,2310,2298,2303,2299,2301,2298,2298]),
  ([49,71,83,103,135,173],[2494,2281,2275,2279,2338,2328,2340,2337,2316,2314,2317,2416,2320,2319,2321,2326,2323,2324,2327]),
  ([49,71,92,103,135,336],[45,2517,2461,2511,283,2361,2353,2346,45,2502,2463,2495,182,2364,2300,2346,2491,2370,2459,2471,2355,2462,2386,2346,2388,2362,2356,2346,2357,2346]),
  ([49,71,92,135,336],[514,2341,41,2518,2492,2512,2372,133,2376,2366,2356,2357,41,2503,2493,2496,2374,2304,2302,2363,2356,2357,2378,2373,2356,2357,2356,2357]),
  ([49,71,103,120,135,173],[2472,752,2395,2473,2416,2394,2360,2347,2358,2382,2379,2386,2385,2387]),
  ([49,71,103,135,241],[515,2342,284,2396,134,2425,1357,1435,183,2480,2411,2305,2407,1357,1435,2367,2348,2403,1357,1435,1357,1435]),
  ([49,71,103,135,257],[516,2510,2343,285,2397,135,2426,2285,2286,184,2481,2412,2306,2408,2285,2286,2368,2349,2404,2285,2286,2285,2286]),
  ([49,71,103,135,285],[517,2344,286,2398,136,2427,2320,2322,185,2482,2413,2307,2409,2320,2322,2377,2354,2369,2350,2405,2320,2322,2320,2322]),
  ([49,71,103,135,336],[518,2345,287,2474,2399,137,2465,2429,2386,2388,186,2483,2414,2308,2410,2386,2388,2371,2351,2406,2386,2388,2386,2388])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f6b16ok : f6b16.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true := by decide +kernel

private def layer6 (i : ℕ) : {s : List W // impossible 6 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer5 i).1) 5) = true} :=
    #[⟨f6b0, f6b0ok⟩, ⟨f6b1, f6b1ok⟩, ⟨f6b2, f6b2ok⟩, ⟨f6b3, f6b3ok⟩, ⟨f6b4, f6b4ok⟩, ⟨f6b5, f6b5ok⟩, ⟨f6b6, f6b6ok⟩, ⟨f6b7, f6b7ok⟩, ⟨f6b8, f6b8ok⟩, ⟨f6b9, f6b9ok⟩, ⟨f6b10, f6b10ok⟩, ⟨f6b11, f6b11ok⟩, ⟨f6b12, f6b12ok⟩, ⟨f6b13, f6b13ok⟩, ⟨f6b14, f6b14ok⟩, ⟨f6b15, f6b15ok⟩, ⟨f6b16, f6b16ok⟩]
  pick alphabet layer5 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f7b0 : Array Row := #[
  ([1,39,49,71,103,135],[534,39,447,32,11,0,452,33,11,0,458,34,11,0,466,35,485,37,473,36,18,19,16,21,14,25,30,17,22,15,26,12,31,13,38,29,20,28,24,23,27]),
  ([2,39,49,71,103,135],[11,1,448,59,524,66,451,60,11,1,459,61,11,1,467,62,485,64,473,63,45,46,43,48,41,52,12,57,44,49,42,53,58,40,65,56,47,55,51,50,54]),
  ([4,39,49,71,103,135],[11,2,449,87,11,2,453,88,513,94,457,89,503,93,465,90,11,2,474,91,73,74,71,76,69,80,13,85,72,77,70,81,40,86,92,84,75,83,79,78,82]),
  ([5,39,49,71,103,135],[534,119,447,112,11,3,454,113,11,3,460,114,503,118,465,115,11,3,475,116,98,99,96,101,105,14,110,97,102,95,106,41,111,69,117,109,100,108,104,103,107]),
  ([8,39,49,71,103,135],[11,4,450,140,524,147,451,141,11,4,461,142,503,146,465,143,11,4,476,144,126,127,124,129,95,133,15,138,125,130,134,42,139,70,145,137,128,136,132,131,135]),
  ([14,39,49,71,103,135],[534,181,447,170,11,5,525,179,456,171,513,178,457,172,11,5,504,177,468,173,11,5,486,175,478,174,156,155,157,180,159,96,163,16,168,154,160,124,164,43,169,71,176,167,158,166,162,161,165]),
  ([19,39,49,71,103,135],[11,6,535,215,455,205,524,214,451,204,513,212,457,206,11,6,505,211,469,207,11,6,487,209,479,208,190,189,191,154,193,97,197,17,202,213,194,125,198,44,203,72,210,201,192,200,196,195,199]),
  ([28,39,49,71,103,135],[534,252,447,238,524,249,451,239,11,7,514,246,464,240,11,7,506,245,470,241,11,7,488,243,481,242,253,247,250,225,156,155,227,98,231,18,251,236,190,189,228,126,232,45,248,237,73,244,235,226,234,230,229,233]),
  ([39,49,56,71,103,135],[253,247,250,225,157,528,271,99,276,19,282,191,518,272,127,277,46,283,224,223,345,273,153,152,409,278,68,67,444,284,74,285,281,270,280,275,274,279]),
  ([39,49,58,71,103,135],[226,270,11,8,536,462,529,300,158,286,100,292,20,297,11,8,526,463,519,301,192,287,128,293,47,298,513,307,457,299,11,8,507,306,477,303,485,304,473,302,75,305,296,295,288,289,291,290,294]),
  ([39,49,71,83,103,135],[227,528,271,180,159,101,322,21,530,327,193,509,318,269,267,268,266,345,319,129,323,48,328,76,331,326,286,325,123,122,445,330,309,308,442,329,321,320,324]),
  ([39,49,71,86,103,135],[228,518,272,160,509,318,265,263,264,262,345,332,102,335,22,340,213,194,130,336,49,520,341,77,344,339,287,338,151,150,446,343,311,310,443,342,334,333,337]),
  ([39,49,71,92,103,135],[229,274,161,320,11,9,537,471,531,354,104,103,361,346,23,358,351,195,333,11,9,527,472,521,355,132,131,362,347,50,359,352,11,9,515,480,510,357,79,78,365,350,289,290,349,503,368,465,353,485,360,473,356,363,348]),
  ([39,49,71,92,135],[230,275,162,321,10,532,369,24,373,366,196,334,10,522,370,51,374,367,10,517,508,511,372,288,291,364,375,371]),
  ([39,49,71,103,120,135],[231,276,163,322,105,25,533,397,197,335,133,489,392,261,260,409,393,52,399,80,490,396,185,184,445,400,292,395,361,346,394,377,376,437,398]),
  ([39,49,71,103,125,135],[232,277,164,323,106,489,392,259,258,409,401,26,405,198,336,134,53,523,406,81,491,404,219,218,446,408,293,403,362,347,402,379,378,441,407]),
  ([39,49,71,103,135,140],[233,279,165,324,107,394,27,417,120,121,437,418,199,337,135,402,54,419,148,149,441,420,82,496,415,294,414,312,313,432,416,363,348]),
  ([39,49,71,103,135,156],[234,280,166,325,108,395,28,482,423,182,183,442,425,200,338,136,403,55,483,424,216,217,443,426,83,516,497,512,421,295,364,349,414,382,380,383,381,432,422]),
  ([39,49,71,103,135,162],[235,281,167,326,117,109,490,396,29,428,186,187,445,430,201,339,145,137,491,404,56,429,220,221,446,431,92,84,296,512,421,365,350,496,415,410,411,413,412,432,427]),
  ([39,49,71,103,135,173],[251,236,282,168,530,327,110,533,397,30,202,340,138,405,57,484,434,256,257,444,436,85,499,428,297,482,423,314,315,442,435,373,358,366,351,417,386,384,387,385,437,433]),
  ([39,49,71,103,135,182],[248,237,283,169,328,111,399,31,484,434,254,255,444,440,203,520,341,139,523,406,58,86,500,429,298,483,424,316,317,443,439,374,359,367,352,419,390,388,391,389,441,438]),
  ([39,49,71,135,162],[244,285,176,331,38,499,188,501,210,344,65,500,222,502,305,516,497,492,493,495,494,498])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f7b0ok : f7b0.toList.all (rowOK alphabet (fun i => (layer6 i).1) 6) = true := by decide +kernel

private def layer7 (i : ℕ) : {s : List W // impossible 7 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer6 i).1) 6) = true} :=
    #[⟨f7b0, f7b0ok⟩]
  pick alphabet layer6 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

private def f8b0 : Array Row := #[
  ([71,39,49,135,103],[5,10,6,11,9,17,2,21,18,7,8,0,19,3,14,1,20,4,15,13,12,16])]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem f8b0ok : f8b0.toList.all (rowOK alphabet (fun i => (layer7 i).1) 7) = true := by decide +kernel

private def layer8 (i : ℕ) : {s : List W // impossible 8 s} :=
  let batches : Array {rs : Array Row // rs.toList.all (rowOK alphabet (fun i => (layer7 i).1) 7) = true} :=
    #[⟨f8b0, f8b0ok⟩]
  pick alphabet layer7 (batches[i / 32]?.getD ⟨#[], rfl⟩) (i % 32)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private theorem all_front : impossible 8 inputs := by
  have h : (layer8 0).1 = inputs := by decide +kernel
  exact h ▸ (layer8 0).2

private theorem singleton_assignment (p : Fin 5) :
    assignment (singletonRow p) = fun q => decide (q = p) := by
  revert p
  decide

private theorem word_wires (C : Circuit) (hm : Monotone2 C) (k : Fin 100) (j : ℕ) :
    bit k ((run C.gates rawInputs).getD j 0) =
      (C.wires (List.ofFn (assignment k))).getD j false := by
  rw [← read_bit, bits_run C.gates rawInputs hm, ← input_rows]
  rfl

private theorem initial_run (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) :
    (run C.gates rawInputs).getD C.output 0 = goalWord := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 100 := ⟨j,hj⟩
  change bit k _ = bit k goalWord
  rw [word_wires C hm k C.output]
  exact Bool.eq_iff_iff.mpr ((he (assignment k)).trans (graph_rows k))

def twoSingletons (C : Circuit) (j : ℕ) : Prop :=
  ∃ u v : Fin 5, u ≠ v ∧
    (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5+j) false = true ∧
    (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5+j) false = true

private theorem enough (C : Circuit) (hm : Monotone2 C) (A B D : Finset ℕ)
    (he : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)
    (ha : ∀ j g, C.gates[j]? = some g → g.op = .and → j ∈ A)
    (hb : ∀ j g, C.gates[j]? = some g → g.op = .or → twoSingletons C j → j ∈ B)
    (hd : ∀ j g, C.gates[j]? = some g → g.op = .or → ¬twoSingletons C j → j ∈ D) :
    9 ≤ A.card + B.card + 2 * D.card := by
  classical
  have hw : represents rawInputs.toFinset rawInputs :=
    fun _ h => .inr (.inr (List.mem_toFinset.mpr h))
  have seq := compile C.gates rawInputs C.output 0 rawInputs.toFinset A B D hw (initial_run C hm he)
  have legalRules (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
      (j ∈ A ∨ j ∈ B ∨ j ∈ D) ∧ (isUnion g.op = true → j ∉ D →
        wide ((run C.gates rawInputs).getD (5+j) 0) = true) := by
    have hop := (hm g (List.mem_of_getElem? h)).1
    change g.op = .and ∨ g.op = .or at hop
    constructor
    · rcases hop with h' | h'
      · exact .inl (ha j g h h')
      · by_cases t : twoSingletons C j
        · exact .inr (.inl (hb j g h h' t))
        · exact .inr (.inr (hd j g h h' t))
    · intro hu hj
      have hor : g.op = .or := hop.resolve_left (by intro e; simp [e,isUnion] at hu)
      have tw : twoSingletons C j := by
        by_contra ht
        exact hj (hd j g h hor ht)
      obtain ⟨u, v, huv, h1, h2⟩ := tw
      apply decide_eq_true
      refine ⟨u, v, huv, ?_, ?_⟩
      · simpa only [word_wires C hm, singleton_assignment] using h1
      · simpa only [word_wires C hm, singleton_assignment] using h2
  have compiled := seq (by simpa only [Nat.zero_add, show rawInputs.length = 5 from rfl] using legalRules)
  have ini : embedded rawInputs.toFinset = inputs.toFinset := by
    ext x
    simp [embedded, inputs]
  rw [ini] at compiled
  have hbudget : budget A B D 0 = A.card + B.card + 2 * D.card := by
    simp [budget, remaining]
  rw [hbudget] at compiled
  by_contra h
  exact all_front (by decide) (extend_live (by omega) (input_live _ compiled))

end PEqualNP.Outside.L_meta_701

theorem PEqualNP.Outside.L_meta_701 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin 5, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5 + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + j) false = true) → j ∈ D) → 9 ≤ A.card + B.card + 2 * D.card := by
  intro C A B D hm he ha hb hd
  exact PEqualNP.Outside.L_meta_701.enough C hm A B D he ha hb hd
