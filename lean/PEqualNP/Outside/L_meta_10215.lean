import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10215.Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The live-set search is adapted from L_meta_2964 in this repository.


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

abbrev m := 28
abbrev W := BitVec (2*m)
def ops (a b : W) : List W := [a &&& b, a ||| b]
def sep (w : W) : BitVec m := ((w >>> m) &&& ~~~w).setWidth m
def cuts (ws : List W) : BitVec m := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec m) ++ (0 : BitVec m)
def inputs : List W := [137178972197, 17454764013120, 2234207631589512, 69805794463353106, 70069677040276005, 1971287752706050, 16500259078168, 128985867712]
def available : List W := 0 :: (-1 : W) :: inputs
def rows : List Nat := [0, 13, 0, 10, 14, 0, 7, 11, 15, 4, 7, 13, 4, 7, 10, 14, 0, 4, 10, 11, 10, 11, 13, 0, 4, 13, 14, 15, 1, 1, 2, 2, 2, 3, 3, 3, 3, 5, 5, 5, 6, 6, 6, 6, 8, 8, 8, 8, 9, 9, 9, 12, 12, 12, 12, 12]
def leftAt (i : Fin (2*m)) : Fin 4 := Fin.ofNat 4 ((rows.getD i.val 0) / 4)
def rightAt (i : Fin (2*m)) : Fin 4 := Fin.ofNat 4 ((rows.getD i.val 0) % 4)
def graph (u v : Fin 4) : Bool := (4974 : Nat).testBit (4*u.val + v.val)


def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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
def differs (i : Fin m) (w : W) : Prop :=
  w.getLsbD (m+i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin m) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (h : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;>
    simp only [differs, BitVec.getLsbD_and, BitVec.getLsbD_or] at *
  all_goals
    cases ha : a.getLsbD (m+i.val) <;> cases hb : b.getLsbD (m+i.val) <;>
      cases hc : a.getLsbD i.val <;> cases hd : b.getLsbD i.val <;> simp_all


theorem goal_differs : ∀ i : Fin m, differs i goal := by unfold differs; decide +kernel

theorem cuts_spec (ws : List W) (i : Fin m) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or,Bool.or_eq_true,ih]
    have hi : i.val < 2*m := by have := i.isLt; omega
    simp [sep,i.isLt,differs,hi,Nat.add_comm, Bool.and_eq_true]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes m)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext w
  simp [ops, BitVec.and_comm, BitVec.or_comm]


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
    · exact List.nodup_cons.mpr ⟨fun hm => (List.nodup_cons.mp habr).1 (List.mem_cons_of_mem _ hm),
        (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2⟩
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

theorem must_have_inputs {s : Finset W} {k : Nat} (hs : s ⊆ available.toFinset)
    (hl : live basicOps goal k s) : inputs.toFinset ⊆ s := by
  intro a ha
  have necessary : inputs.all (fun a => (List.finRange m).any (fun i => available.all (fun b =>
      !(b.getLsbD (m+i.val) && !b.getLsbD i.val) || b == a))) = true := by decide +kernel
  obtain ⟨i, _, hall⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hl
  have checked := List.all_eq_true.mp hall b (List.mem_toFinset.mp (hs hb))
  have eq : b = a := by simpa [hd.1, hd.2] using checked
  exact eq ▸ hb

theorem starting_sets {s : Finset W} (hs : s ⊆ available.toFinset)
    (hl : live basicOps goal 8 s) :
    s = inputs.toFinset ∨ s = (0 :: inputs).toFinset ∨ s = ((-1 : W) :: inputs).toFinset := by
  have hi := must_have_inputs hs hl
  have hn : ¬ ((0 : W) ∈ s ∧ (-1 : W) ∈ s) := by
    rintro ⟨h0, h1⟩
    have ha : available.toFinset ⊆ s := by
      intro x hx
      simp only [available, List.toFinset_cons, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | h
      · exact h0
      · exact h1
      · exact hi h
    have hc := Finset.card_le_card ha
    have hd := live_card hl
    have h10 : available.toFinset.card = 10 := by decide
    omega
  by_cases h0 : (0 : W) ∈ s
  · right; left
    ext x
    have h1 : (-1 : W) ∉ s := fun h => hn ⟨h0,h⟩
    constructor
    · intro hx
      have h := hs hx
      simp only [available, List.toFinset_cons, Finset.mem_insert] at h ⊢
      rcases h with h | rfl | h
      · exact Or.inl h
      · exact (h1 hx).elim
      · exact Or.inr h
    · simp only [List.toFinset_cons, Finset.mem_insert]
      rintro (rfl | h)
      · exact h0
      · exact hi h
  · by_cases h1 : (-1 : W) ∈ s
    · right; right
      ext x
      constructor
      · intro hx
        have h := hs hx
        simp only [available, List.toFinset_cons, Finset.mem_insert] at h ⊢
        rcases h with rfl | h | h
        · exact (h0 hx).elim
        · exact Or.inl h
        · exact Or.inr h
      · simp only [List.toFinset_cons, Finset.mem_insert]
        rintro (rfl | h)
        · exact h1
        · exact hi h
    · left
      apply Finset.Subset.antisymm _ hi
      intro x hx
      have hh := hs hx
      simp only [available, List.toFinset_cons, Finset.mem_insert] at hh
      rcases hh with rfl | rfl | h
      · exact (h0 hx).elim
      · exact (h1 hx).elim
      · exact h


def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !(w == a || w == b || r.contains w) && (
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hfresh : z ∉ a :: b :: r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · simpa [List.mem_cons, and_assoc] using hfresh
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega,
      .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega,
      .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
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
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk
          (fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm)))
          (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run0 : optimized 8 1 inputs = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run1 : optimized 8 0 (0 :: inputs) = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run2 : optimized 8 0 ((-1 : W) :: inputs) = false := by decide +kernel

theorem noBuild : ¬ build basicOps goal 8 available.toFinset := by
  intro h
  obtain ⟨s, hs, hl⟩ := compress h
  rcases starting_sets hs hl with he | he | he
  · exact Bool.noConfusion (run0.symm.trans
      (optimized_complete 8 inputs 1 (by decide) (by decide) (he ▸ hl)))
  · exact Bool.noConfusion (run1.symm.trans
      (optimized_complete 8 (0 :: inputs) 0 (by decide) (by decide) (he ▸ hl)))
  · exact Bool.noConfusion (run2.symm.trans
      (optimized_complete 8 ((-1 : W) :: inputs) 0 (by decide) (by decide) (he ▸ hl)))


def gateWord (ws : List W) (g : Gate) : W :=
  let args := g.inputs.map fun i => ws.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes _)
  | .or => args.foldr (· ||| ·) 0
  | _ => 0

def stepWord (ws : List W) (g : Gate) : List W := ws ++ [gateWord ws g]
def stepBool (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_bits (ws : List W) (r j : Nat) :
    (ws.map fun w => w.getLsbD r).getD j false = (ws.getD j 0).getLsbD r := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> simp

theorem fold_and_bit (ws : List W) (r : Fin (2*m)) :
    (ws.foldr (· &&& ·) (BitVec.allOnes _)).getLsbD r.val =
      (ws.map fun w => w.getLsbD r.val).all id := by
  induction ws with
  | nil => simp [r.isLt]
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.all_cons, BitVec.getLsbD_and, id, ih]

theorem fold_or_bit (ws : List W) (r : Fin (2*m)) :
    (ws.foldr (· ||| ·) 0).getLsbD r.val =
      (ws.map fun w => w.getLsbD r.val).any id := by
  induction ws with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.any_cons, BitVec.getLsbD_or, id, ih]

theorem step_bits (ws : List W) (g : Gate) (hg : GateOK g) (r : Fin (2*m)) :
    (stepWord ws g).map (fun w => w.getLsbD r.val) =
      stepBool (ws.map fun w => w.getLsbD r.val) g := by
  have hopen : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
  unfold stepWord stepBool
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
  unfold gateWord
  rcases hopen with h | h
  · simp only [h, GateOp.eval, fold_and_bit, List.map_map, Function.comp_def, getD_bits]
  · simp only [h, GateOp.eval, fold_or_bit, List.map_map, Function.comp_def, getD_bits]

theorem run_bits (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (ws : List W) (r : Fin (2*m)) :
    (gs.foldl stepWord ws).map (fun w => w.getLsbD r.val) =
      gs.foldl stepBool (ws.map fun w => w.getLsbD r.val) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons]
    rw [ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)), step_bits ws g (hgs g (by simp)) r]

theorem getD_in (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, a ∈ s)
    (h0 : 0 ∈ s) (j : Nat) : ws.getD j 0 ∈ s := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => exact h0
  | some a => exact hw a (List.mem_of_getElem? h)

theorem gateWord_cases (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, a ∈ s)
    (h0 : 0 ∈ s) (h1 : (-1 : W) ∈ s) (g : Gate) (hg : GateOK g) :
    gateWord ws g ∈ s ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ gateWord ws g ∈ basicOps a b := by
  obtain ⟨op, xs⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or := by simpa using hg.1
  have hlen : xs.length ≤ 2 := hg.2
  cases xs with
  | nil =>
    rcases hop with rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h0
  | cons i xs =>
    cases xs with
    | nil =>
      rcases hop with rfl | rfl <;> exact Or.inl (by simpa [gateWord] using getD_in ws s hw h0 i)
    | cons j xs =>
      cases xs with
      | cons k ks => simp at hlen
      | nil =>
        let a := ws.getD i 0
        let b := ws.getD j 0
        have ha : a ∈ s := getD_in ws s hw h0 i
        have hb : b ∈ s := getD_in ws s hw h0 j
        have hform : gateWord ws ⟨op, [i,j]⟩ = a &&& b ∨
            gateWord ws ⟨op, [i,j]⟩ = a ||| b := by
          rcases hop with rfl | rfl
          · left; simp [gateWord, a, b]
          · right; simp [gateWord, a, b]
        by_cases eq : a = b
        · left
          rcases hform with h | h <;> rw [h, ← eq] <;> simpa using ha
        · right
          exact ⟨a, ha, b, hb, eq, by simpa [ops] using hform⟩

theorem run_build (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (ws : List W)
    (s : Finset W) (hw : ∀ a ∈ ws, a ∈ s)
    (h0 : 0 ∈ s) (h1 : (-1 : W) ∈ s) (out : Nat) :
    build basicOps ((gs.foldl stepWord ws).getD out 0) gs.length s := by
  induction gs generalizing ws s with
  | nil => exact getD_in ws s hw h0 out
  | cons g t ih =>
    have ht : ∀ u ∈ t, GateOK u := fun u hu => hgs u (List.mem_cons_of_mem _ hu)
    have hz := gateWord_cases ws s hw h0 h1 g (hgs g (by simp))
    rcases hz with hm | ⟨a, ha, b, hb, hab, hmem⟩
    · apply Or.inl
      apply ih ht (stepWord ws g) s _ h0 h1
      intro x hx
      simp only [stepWord, List.mem_append, List.mem_singleton] at hx
      exact hx.elim (hw x) (fun h => h ▸ hm)
    · apply Or.inr
      refine ⟨a, ha, b, hb, hab, gateWord ws g, hmem, ?_⟩
      apply ih ht (stepWord ws g) (insert (gateWord ws g) s) _
        (Finset.mem_insert_of_mem h0) (Finset.mem_insert_of_mem h1)
      intro x hx
      simp only [stepWord, List.mem_append, List.mem_singleton] at hx
      exact hx.elim (fun hx' => Finset.mem_insert_of_mem (hw x hx')) (fun h => h ▸ Finset.mem_insert_self _ _)

theorem extend_build {a b : Nat} {s : Finset W} (h : a ≤ b)
    (hb : build basicOps goal a s) : build basicOps goal b s := by
  induction h with
  | refl => exact hb
  | step _ ih => exact Or.inl ih

theorem inputs_bits : ∀ r : Fin (2*m),
    (inputs.map fun w => w.getLsbD r.val) = oneEach (leftAt r) (rightAt r) := by decide +kernel

theorem goal_bits : ∀ r : Fin (2*m),
    goal.getLsbD r.val = graph (leftAt r) (rightAt r) := by decide +kernel

theorem lower : ¬ RepSizeAtMost graph 8 := by
  rintro ⟨C, hC, hsz, hrep⟩
  have hgs : ∀ g ∈ C.gates, GateOK g := hC
  let out := (C.gates.foldl stepWord inputs).getD C.output 0
  have heq : out = goal := by
    apply BitVec.eq_of_getElem_eq
    intro i h
    have hr := run_bits C.gates hgs inputs ⟨i,h⟩
    have bit : out.getLsbD i = C.eval (oneEach (leftAt ⟨i,h⟩) (rightAt ⟨i,h⟩)) := by
      change ((C.gates.foldl stepWord inputs).getD C.output 0).getLsbD i = _
      rw [← getD_bits, hr, inputs_bits ⟨i,h⟩]
      rfl
    have ht := hrep (leftAt ⟨i,h⟩) (rightAt ⟨i,h⟩)
    have hg := goal_bits ⟨i,h⟩
    simpa only [BitVec.getLsbD_eq_getElem h] using bit.trans (ht.trans hg.symm)
  have hb : build basicOps out C.gates.length available.toFinset :=
    run_build C.gates hgs inputs available.toFinset (by intro a ha; simp [available, ha])
      (by simp [available]) (by simp [available]) C.output
  exact noBuild (extend_build hsz (heq ▸ hb))



end PEqualNP.Outside.L_meta_10215.Base

-- Circuit restriction adapts the implementation in open-goat/pequalnp-proofs
-- L-meta-6379 and L-meta-7147. The four-by-four bound uses L-meta-6032.
namespace PEqualNP.Outside.L_meta_10215.E
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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
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

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

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

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
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
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

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

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
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
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

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
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


end PEqualNP.Outside.L_meta_10215.E
namespace PEqualNP.Outside.L_meta_10215.K
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

lemma wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma W_nil (w : List Bool) : W [] w = w := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_append (a b : List Gate) (w : List Bool) :
    W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_length (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_append_lt (l₁ l₂ : List Bool) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma W_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_append_lt w _ i hi

lemma W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false :=
  getD_ge _ _ (by rw [W_length]; exact h)

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 := (List.take_append_drop j gs).symm
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1
  have htlen : (gs.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hprelen : (W (gs.take j) w).length = w.length + j := by
    rw [W_length, htlen]
  conv_lhs => rw [hsplit, W_append, W_cons]
  rw [W_prefix (gs.drop (j + 1)) (step (W (gs.take j) w) gs[j]) (w.length + j)
    (by rw [step_len, hprelen]; omega)]
  have hlast : (step (W (gs.take j) w) gs[j]).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (W (gs.take j) w).getD i false) := by
    rw [← hprelen]
    exact getD_append_len _ _
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length + j
  · simp only [hi, ↓reduceIte]
    have hpref : (W gs w).getD i false = (W (gs.take j) w).getD i false := by
      conv_lhs => rw [hsplit, W_append]
      exact W_prefix (gs[j] :: gs.drop (j + 1)) (W (gs.take j) w) i (by rw [hprelen]; exact hi)
    exact hpref.symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge (W (gs.take j) w) i (by rw [hprelen]; omega)

lemma val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false :=
  W_prefix C.gates x i hi

lemma val_ge (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    val C x i = false :=
  W_ge C.gates x i hi

lemma val_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (x.length + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then val C x i else false) :=
  W_gate C.gates x j hj

lemma op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  have hop' : op = GateOp.and ∨ op = GateOp.or := by simpa using hop
  rcases hop' with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      have hm : l₁[i] ∈ l₁ := List.getElem_mem hi1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
      exact h _ hm
    have h2 := hle i h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h2
    exact h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem ha
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact hget
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]


end PEqualNP.Outside.L_meta_10215.K
open PEqualNP.Outside.L_meta_10215.E PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_10215.K (op_mono)
namespace PEqualNP.Outside.L_meta_10215

def MG (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma mono_emit (g : Gate) (h : MG g) (m : Nat) (xs : List Stat) :
    ∀ a ∈ (simplify g.op m xs).1.toList, MG a := by
  rcases g with ⟨o,ins⟩
  obtain ⟨hop,_⟩ := h
  change o = .and ∨ o = .or at hop
  rcases hop with rfl | rfl <;> rcases xs with _ | ⟨a, _ | ⟨b,_ | ⟨c,ys⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp [simplify,simpAnd,simpOr,MG]

lemma mono_elim (n : Nat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, MG g) → (∀ g ∈ acc.2, MG g) → ∀ g ∈ (elim n gs acc).2, MG g := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc h hacc
    apply ih (elimStep n acc g) (fun a ha => h a (by simp [ha]))
    intro a ha
    rcases List.mem_append.mp ha with h'|h'
    · exact hacc _ h'
    · exact mono_emit g (h g (by simp)) _ _ _ h'

lemma nok (g : Gate) (h : MG g) : NOk g := by
  rcases h with ⟨h,h2⟩
  change g.op = .and ∨ g.op = .or at h
  constructor
  · exact ⟨h.elim Or.inl (fun x=> Or.inr (Or.inl x)), h2⟩
  · rcases h with h|h <;> simp [h]

lemma noRead (k : Nat) (gs : List Gate) (hgs : ∀ g ∈ gs, MG g ∧ k ∉ g.inputs)
    (x y : List Bool) (hl : x.length = y.length)
    (hord : ∀ i, i ≠ k → x.getD i false = true → y.getD i false = true) :
    ∀ i, i ≠ k → (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact hord
  | cons g gs ih =>
    apply ih (fun a ha => hgs a (by simp [ha]))
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
      (y ++ [g.op.eval (g.inputs.map fun i => y.getD i false)]) (by simp [hl])
    intro i hne
    by_cases he : i = x.length
    · rw [he, getD_snoc_len _ _ _ _ rfl, getD_snoc_len _ _ _ _ hl.symm]
      have hg := hgs g (by simp)
      apply op_mono _ hg.1.1 _ _ (by simp)
      intro a
      by_cases ha : a < g.inputs.length
      · simp [List.getD_eq_getElem?_getD, ha]
        exact hord _ (fun he => hg.2 (he ▸ List.getElem_mem ha))
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt ha)]
    · rw [getD_snoc_ne _ _ _ _ he, getD_snoc_ne _ _ _ _ (hl ▸ he)]
      exact hord _ hne

lemma readers {n m : Nat} (A : Fin n → Fin m → Bool) (C : Circuit) (hm : Monotone2 C) (hr : Represents A C)
    (k : Fin (n+m)) (a b d : Fin n) (p q r : Fin m)
    (ha : A a p = true) (hb : A b q = false) (hd : A d r = true)
    (hk : (oneEach d r).getD k false = false)
    (ho : ∀ i : Fin (n+m), i ≠ k → (oneEach a p).getD i false = true → (oneEach b q).getD i false = true) :
    ∃ g ∈ C.gates, k.val ∈ g.inputs := by
  by_contra h
  push Not at h
  have hout : C.output ≠ k.val := by
    intro he
    have hv := PEqualNP.Outside.L_meta_10215.K.val_input C (oneEach d r) k.val (by simpa [oneEach] using k.isLt)
    have hr' := (hr d r).trans hd
    change PEqualNP.Outside.L_meta_10215.K.val C (oneEach d r) C.output = true at hr'
    rw [he,hv,hk] at hr'
    contradiction
  have ord : ∀ i, i ≠ k.val → (oneEach a p).getD i false = true → (oneEach b q).getD i false = true := by
    intro i hi
    by_cases hil : i<n+m
    · exact ho ⟨i,hil⟩ (fun h => hi (congrArg Fin.val h))
    · have hz := PEqualNP.Outside.L_meta_10215.K.getD_ge (oneEach a p) i (by simpa only [PEqualNP.Outside.L_meta_10215.K.oneEach_length] using Nat.le_of_not_lt hil)
      rw [hz]; simp
  have H := noRead k.val C.gates (fun g hg => ⟨hm g hg, h g hg⟩) _ _ (by simp [oneEach]) ord C.output hout ((hr a p).trans ha)
  change C.eval (oneEach b q) = true at H
  rw [hr, hb] at H
  contradiction

def validB (n : Nat) : Stat → Bool
  | .inl _ => true
  | .inr j => decide (j<n)

lemma cut {n m n' m' s : Nat} (A : Fin n → Fin m → Bool) (B : Fin n' → Fin m' → Bool)
    (f : Fin n' → Fin n) (g : Fin m' → Fin m) (ss : List Stat) (k : Fin (n+m))
    (hs : ss.length = n+m)
    (hfixed : ss.getD k (.inl false) = .inl false)
    (hvalid : ∀ i : Fin (n+m), validB (n'+m') (ss.getD i (.inl false)) = true)
    (hmap : ∀ u v (i : Fin (n+m)), statVal (oneEach u v) (ss.getD i (.inl false)) = (oneEach (f u) (g v)).getD i false)
    (hval : ∀ u v, A (f u) (g v) = B u v)
    (ha : ∃ u v, B u v = true) (hb : ∃ u v, B u v = false)
    (hread : ∀ C, Monotone2 C → Represents A C → ∃ gate ∈ C.gates, k.val ∈ gate.inputs)
    (h : RepSizeAtMost A (s+1)) : RepSizeAtMost B s := by
  obtain ⟨C,hm,hsz,hr⟩ := h
  let res := elim (n'+m') C.gates (ss,[])
  have hmono : ∀ gate ∈ res.2, MG gate := mono_elim _ _ _ hm (by simp)
  have hsize : res.2.length ≤ s := by
    have hv := elim_len_lt (n'+m') k.val C.gates (ss,[]) (fun x hx => nok _ (hm x hx))
      (by simpa [hs] using k.isLt) ⟨false,hfixed⟩ (hread C hm hr)
    change res.2.length+1 ≤ 0+C.gates.length at hv
    change C.gates.length ≤ s+1 at hsz
    omega
  have hresult (u : Fin n') (v : Fin m') :
      statVal (wiresFrom res.2 (oneEach u v)) (res.1.getD C.output (.inl false)) = B u v := by
    have hinit : Inv (n'+m') (oneEach u v) (oneEach (f u) (g v)) (ss,[]) := by
      refine ⟨by simpa [oneEach] using hs, ?_⟩
      intro i
      by_cases hi : i<n+m
      · obtain hv := hvalid ⟨i,hi⟩
        constructor
        · change statValid (n'+m'+0) (ss.getD i (.inl false))
          cases e : ss.getD i (.inl false) with
          | inl => trivial
          | inr j =>
            change j < n'+m'+0
            change validB _ (ss.getD i _) = true at hv
            rw [e] at hv
            exact of_decide_eq_true hv
        · exact hmap u v ⟨i,hi⟩
      · have e := List.getElem?_eq_none (show ss.length ≤ i by omega)
        have e' := List.getElem?_eq_none (show (oneEach (f u) (g v)).length ≤ i by simp [oneEach];omega)
        simp [List.getD_eq_getElem?_getD,e,e',statValid,statVal]
    have result := ((inv_elim _ _ (by simp [oneEach]) C.gates _ _ (fun a h => (nok a (hm a h)).1) hinit).2 C.output).2
    exact result.trans ((hr _ _).trans (hval u v))
  cases e : res.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨u,v,h⟩ := ha
    obtain ⟨u',v',h'⟩ := hb
    have ht := hresult u v
    have hf := hresult u' v'
    simp [e,statVal,h] at ht
    simp [e,statVal,h'] at hf
    simp_all
  | inr j =>
    refine ⟨⟨res.2,j⟩,hmono,hsize,?_⟩
    intro u v
    have he := hresult u v
    change (wiresFrom res.2 (oneEach u v)).getD j false = B u v
    simpa only [e,statVal] using he

def A (u v : Fin 5) := (3249493 : Nat).testBit (5*u.val+v.val)
def row : Fin 4 → Fin 5 := ![0,2,3,1]
def col : Fin 4 → Fin 5 := ![1,0,2,4]
def B (u : Fin 4) (v : Fin 5) := A (row u) v
def D (u v : Fin 4) := (4974 : Nat).testBit (4*u.val+v.val)
def ss1 : List Stat := [.inr 0,.inr 3,.inr 1,.inr 2,.inl false,.inr 4,.inr 5,.inr 6,.inr 7,.inr 8]
def ss2 : List Stat := [.inr 0,.inr 1,.inr 2,.inr 3,.inr 5,.inr 4,.inr 6,.inl false,.inr 7]
theorem falsification : ¬ RepSizeAtMost (fun u v : Fin 5 => (3249493 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  intro hh
  have h9 : RepSizeAtMost B 9 := by
    apply cut A B row id ss1 4 (by decide) (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) _ hh
    intro C hm hr
    exact readers A C hm hr 4 4 1 0 0 0 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8 : RepSizeAtMost D 8 := by
    apply cut B D id col ss2 7 (by decide) (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) _ h9
    intro C hm hr
    exact readers B C hm hr 7 3 3 0 3 0 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact PEqualNP.Outside.L_meta_10215.Base.lower h8

end PEqualNP.Outside.L_meta_10215

theorem PEqualNP.Outside.L_meta_10215 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3249493 : ℕ).testBit (5 * u.val + v.val)) 10) :=
  PEqualNP.Outside.L_meta_10215.falsification
