import PEqualNP.Defs
import Mathlib.Data.Tree.Basic

-- The live-wire search proof is adapted from the project proof L-meta-6340.

namespace PEqualNP.Outside.L_meta_9399

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

abbrev W := BitVec 300

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 150 := ((x >>> 150) &&& ~~~x).setWidth 150

def cuts (ws : List W) : BitVec 150 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 150) ++ (0 : BitVec 150)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x7ffffffffffc00180030006000c00180030006000c0018003, 0xfffffffffff800000000000006000c00180030006000c00180030006000c, 0x7fff0000000000000000000000007800f001e003c007800f001e003c007800f0, 0x3fff8000000000000000000000000007800f001e003c007800f001e003c007800f00, 0xfffffffc0000000000000000000000000000038007000e001c0038007000e001c0038007000, 0x1fffc000000000000003fff8000000000000888111022204440888111022204440888111, 0xfffe000000000000000000000000000001fffc1120224044808901120224044808901120224, 0x1fffc000000000000000a21144228845108a21144228845108a211442, 0xfffe000144428885110a22144428885110a2214442888, 0x3ffffffffffe00000007fff000000020004000800100020004000800100020004000]

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

def differs (i : Fin 150) (w : W) : Prop :=
  w.getLsbD (150 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 150) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (150 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (150 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 150, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 150) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 300 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 150)[j]
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
  z == 0 || z == BitVec.allOnes 300 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 300) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 300) :
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
    · exact ⟨BitVec.allOnes 300, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 300 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 300 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 300 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 300 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 300) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 300 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def tryStep (next : ℕ → List W → Bool) (extra : ℕ) (ws : List W) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch extra next a b r)

theorem step_complete {k extra : ℕ} {ws : List W} (hn : ws.Nodup)
    (room : extra + ws.length = k + 2) (h : live basicOps goal (k+1) ws.toFinset)
    (next : ℕ → List W → Bool)
    (child : ∀ l e, l.Nodup → e + l.length = k + 1 → live basicOps goal k l.toFinset → next e l = true) :
    tryStep next extra ws = true := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · simp [tryStep, singleton_list hn done]
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        dispatch extra next a b r = true := by
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
      apply dispatch_complete (k := k) (extra := extra) next hop hk (by omega) (by omega) (cuts_full hl)
      exact child _ _ hnd (by simp; omega) hl
    simp only [tryStep, Bool.or_eq_true, List.any_eq_true]
    right
    rcases hm with direct | swap
    · exact ⟨(a, b, r), direct, go hp hs hz⟩
    · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

abbrev ReplayTree := BinaryTree (List W)

open BinaryTree

def ReplayTree.all (f : List W → Bool) : ReplayTree → Bool
  | nil => true
  | node w l r => ReplayTree.all f l && f w && ReplayTree.all f r

def ReplayTree.find (key : List W) : ReplayTree → Bool
  | nil => false
  | node w l r => if key == w then true else if key < w then ReplayTree.find key l else ReplayTree.find key r

theorem find_valid {f : List W → Bool} {key : List W} (t : ReplayTree) (h : ReplayTree.all f t = true)
    (hm : ReplayTree.find key t = true) : f key = true := by
  induction t with
  | nil => simp [ReplayTree.find] at hm
  | node w l r il ir =>
    simp only [ReplayTree.all, Bool.and_eq_true] at h
    simp only [ReplayTree.find] at hm
    split at hm
    · rename_i heq
      exact (eq_of_beq heq) ▸ h.1.2
    · split at hm
      · exact il h.1.1 hm
      · exact ir h.2 hm

def ins (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def sortedW : List W → List W
  | [] => []
  | x :: xs => ins x (sortedW xs)

theorem ins_perm (x : W) (l : List W) : (ins x l).Perm (x :: l) := by
  induction l with
  | nil => exact .refl _
  | cons y ys ih =>
    simp only [ins]
    split
    · exact .refl _
    · exact (ih.cons y).trans (.swap _ _ _)

theorem sorted_perm (l : List W) : (sortedW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (ins_perm x _).trans (ih.cons x)


def missed (t : ReplayTree) (_ : ℕ) (l : List W) : Bool := !(ReplayTree.find (sortedW l) t)

def blocked (k : ℕ) (t : ReplayTree) (l : List W) : Bool :=
  !(tryStep (missed t) (k+2-l.length) l)

def sound (k : ℕ) (t : ReplayTree) : Prop :=
  ∀ l : List W, ReplayTree.find l t = true → l.Nodup → ¬live basicOps goal k l.toFinset

theorem empty_sound (k : ℕ) : sound k nil := by
  intro l h
  cases h

theorem layer_sound {k : ℕ} {prev curr : ReplayTree} (hp : sound k prev)
    (hc : ReplayTree.all (blocked k prev) curr = true) : sound (k+1) curr := by
  intro l hm hn hl
  have len := live_card hl
  rw [List.toFinset_card_of_nodup hn] at len
  have h := step_complete hn (by omega : k+2-l.length+l.length = k+2) hl (missed prev) (by
    intro xs e nd room liveX
    unfold missed
    cases hh : ReplayTree.find (sortedW xs) prev with
    | false => rfl
    | true =>
      have perm := sorted_perm xs
      exact False.elim (hp _ hh (perm.nodup_iff.mpr nd) (by simpa only [List.toFinset_eq_of_perm _ _ perm] using liveX)))
  have hb := find_valid curr hc hm
  simp [blocked,h] at hb
def A : Fin 5 → Fin 5 → Bool := fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 3), (0, 4), (1, 0), (1, 2), (1, 4), (2, 4), (3, 4), (4, 0), (4, 1)]

def negL : List (Fin 5 × Fin 5) :=
  [(0, 0), (0, 2), (1, 1), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3), (4, 2), (4, 3), (4, 4)]

def samp (k : Fin 300) : Fin 5 × Fin 5 :=
  if k.val < 150 then negL.getD (k.val % 15) (0, 0) else posL.getD ((k.val - 150) / 15) (0, 0)

theorem input_rows : ∀ k : Fin 300,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 300, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 300) :
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

abbrev n (l : ReplayTree) (w : List W) (r : ReplayTree) : ReplayTree := BinaryTree.node w l r
abbrev z : ReplayTree := BinaryTree.nil

def w0 : W := 0xfffe00000000000000000000000000000000000000000
def w1 : W := 0xfffe000144428885110a22144428885110a2214442888
def w2 : W := 0x7ffffffffffc00180030006000c00180030006000c0018003
def w3 : W := 0x1fffc0000000000000000000000000000000000000000000000000000
def w4 : W := 0x1fffc000000000000000a21144228845108a21144228845108a211442
def w5 : W := 0x1fffc0007ffffffffffc00180030006000c00180030006000c0018003
def w6 : W := 0x1fffc0007ffffffffffca2194432886510ca2194432886510ca219443
def w7 : W := 0xfffffffffff800000000000006000c00180030006000c00180030006000c
def w8 : W := 0xfffffffffff8000fffe0000006000c00180030006000c00180030006000c
def w9 : W := 0xfffffffffff8000fffe0001446288c5118a231446288c5118a231446288c
def w10 : W := 0x7fff000000000000000000000000000000000000000000000000000000000000
def w11 : W := 0x7fff0000000000000000000000007800f001e003c007800f001e003c007800f0
def w12 : W := 0x7fff000000000000000fffe000007800f001e003c007800f001e003c007800f0
def w13 : W := 0x7fff000000000000000fffe000144428885110a22144428885110a2214442888
def w14 : W := 0x7fff000000000000000fffe000147c28f851f0a3e147c28f851f0a3e147c28f8
def w15 : W := 0x7fff000000000007ffffffffffc00180030006000c00180030006000c0018003
def w16 : W := 0x7fff000000000007ffffffffffc07980f301e603cc07980f301e603cc07980f3
def w17 : W := 0x7fff0001fffc00000000000000007800f001e003c007800f001e003c007800f0
def w18 : W := 0x7fff0001fffc000000000000000a21144228845108a21144228845108a211442
def w19 : W := 0x7fff0001fffc000000000000000a7914f229e453c8a7914f229e453c8a7914f2
def w20 : W := 0x7fff0001fffc0007ffffffffffca2194432886510ca2194432886510ca219443
def w21 : W := 0x7fff0001fffc0007ffffffffffca7994f329e653cca7994f329e653cca7994f3
def w22 : W := 0x7ffffffffffffff800000000000006000c00180030006000c00180030006000c
def w23 : W := 0x7ffffffffffffff80000000000007e00fc01f803f007e00fc01f803f007e00fc
def w24 : W := 0x7ffffffffffffff8000fffe0001446288c5118a231446288c5118a231446288c
def w25 : W := 0x7ffffffffffffff8000fffe000147e28fc51f8a3f147e28fc51f8a3f147e28fc
def w26 : W := 0x3fff8000000000000000000000000000000000000000000000000000000000000000
def w27 : W := 0x3fff8000000000000000000000000007800f001e003c007800f001e003c007800f00
def w28 : W := 0x3fff8000000000000000000fffe00007800f001e003c007800f001e003c007800f00
def w29 : W := 0x3fff8000000000000000000fffe000144428885110a22144428885110a2214442888
def w30 : W := 0x3fff8000000000000000000fffe00017c42f885f10be217c42f885f10be217c42f88
def w31 : W := 0x3fff8000000000000007ffffffffffc00180030006000c00180030006000c0018003
def w32 : W := 0x3fff8000000000000007ffffffffffc7818f031e063c0c7818f031e063c0c7818f03
def w33 : W := 0x3fff80000001fffc0000000000000007800f001e003c007800f001e003c007800f00
def w34 : W := 0x3fff80000001fffc000000000000000a21144228845108a21144228845108a211442
def w35 : W := 0x3fff80000001fffc000000000000000fa11f423e847d08fa11f423e847d08fa11f42
def w36 : W := 0x3fff80000001fffc0007ffffffffffca2194432886510ca2194432886510ca219443
def w37 : W := 0x3fff80000001fffc0007ffffffffffcfa19f433e867d0cfa19f433e867d0cfa19f43
def w38 : W := 0x3fff8000fffffffffff800000000000006000c00180030006000c00180030006000c
def w39 : W := 0x3fff8000fffffffffff8000000000007860f0c1e183c307860f0c1e183c307860f0c
def w40 : W := 0x3fff8000fffffffffff8000fffe0001446288c5118a231446288c5118a231446288c
def w41 : W := 0x3fff8000fffffffffff8000fffe00017c62f8c5f18be317c62f8c5f18be317c62f8c
def w42 : W := 0x3fffffff000000000000000000000000000000000000000000000000000000000000
def w43 : W := 0x3fffffff0000000000000000000000007800f001e003c007800f001e003c007800f0
def w44 : W := 0x3fffffff000000000000000000000007800f001e003c007800f001e003c007800f00
def w45 : W := 0x3fffffff000000000000000000000007f80ff01fe03fc07f80ff01fe03fc07f80ff0
def w46 : W := 0x3fffffff000000000000000fffe00007f80ff01fe03fc07f80ff01fe03fc07f80ff0
def w47 : W := 0x3fffffff000000000000000fffe000144428885110a22144428885110a2214442888
def w48 : W := 0x3fffffff000000000000000fffe000147c28f851f0a3e147c28f851f0a3e147c28f8
def w49 : W := 0x3fffffff000000000000000fffe00017c42f885f10be217c42f885f10be217c42f88
def w50 : W := 0x3fffffff000000000000000fffe00017fc2ff85ff0bfe17fc2ff85ff0bfe17fc2ff8
def w51 : W := 0x3fffffff000000000007ffffffffffc00180030006000c00180030006000c0018003
def w52 : W := 0x3fffffff000000000007ffffffffffc7f98ff31fe63fcc7f98ff31fe63fcc7f98ff3
def w53 : W := 0x3fffffff0001fffc0000000000000007f80ff01fe03fc07f80ff01fe03fc07f80ff0
def w54 : W := 0x3fffffff0001fffc000000000000000a21144228845108a21144228845108a211442
def w55 : W := 0x3fffffff0001fffc000000000000000a7914f229e453c8a7914f229e453c8a7914f2
def w56 : W := 0x3fffffff0001fffc000000000000000fa11f423e847d08fa11f423e847d08fa11f42
def w57 : W := 0x3fffffff0001fffc000000000000000ff91ff23fe47fc8ff91ff23fe47fc8ff91ff2
def w58 : W := 0x3fffffff0001fffc0007ffffffffffca2194432886510ca2194432886510ca219443
def w59 : W := 0x3fffffff0001fffc0007ffffffffffcff99ff33fe67fccff99ff33fe67fccff99ff3
def w60 : W := 0x3ffffffffffe00000007fff000000020004000800100020004000800100020004000
def w61 : W := 0x3ffffffffffe00000007ffffffe00020004000800100020004000800100020004000
def w62 : W := 0x3ffffffffffe00000007ffffffe00034446888d111a2234446888d111a2234446888
def w63 : W := 0x3ffffffffffffffc0007fff000000020004000800100020004000800100020004000
def w64 : W := 0x3ffffffffffffffc0007fff00000002a215442a885510aa215442a885510aa215442
def w65 : W := 0x3ffffffffffffffffff800000000000006000c00180030006000c00180030006000c
def w66 : W := 0x3ffffffffffffffffff8000000000007fe0ffc1ff83ff07fe0ffc1ff83ff07fe0ffc
def w67 : W := 0x3ffffffffffffffffff8000fffe0001446288c5118a231446288c5118a231446288c
def w68 : W := 0x3ffffffffffffffffff8000fffe00017fe2ffc5ff8bff17fe2ffc5ff8bff17fe2ffc
def w69 : W := 0x1fffc000000000000003fff8000000000000888111022204440888111022204440888111
def w70 : W := 0x1fffc000000000000003ffffffffffffffc08981130226044c08981130226044c0898113
def w71 : W := 0x1fffc00000000001fffffff8000000000000888111022204440888111022204440888111
def w72 : W := 0x1fffc00000000001fffffff800000000000aa995532aa6554caa995532aa6554caa99553
def w73 : W := 0x1fffc00000000001ffffffffffffffffffc08981130226044c08981130226044c0898113
def w74 : W := 0x1fffc00000000001ffffffffffffffffffcaa995532aa6554caa995532aa6554caa99553
def w75 : W := 0x1fffc0007fff00000003fff8000000000000888111022204440888111022204440888111
def w76 : W := 0x1fffc0007fff00000003fff8000000000000f881f103e207c40f881f103e207c40f881f1
def w77 : W := 0x1fffc0007fff00000003ffffffffffffffc08981130226044c08981130226044c0898113
def w78 : W := 0x1fffc0007fff00000003ffffffffffffffc0f981f303e607cc0f981f303e607cc0f981f3
def w79 : W := 0x1fffc0007fff0001fffffff8000000000000f881f103e207c40f881f103e207c40f881f1
def w80 : W := 0x1fffc0007fff0001fffffff800000000000af995f32be657ccaf995f32be657ccaf995f3
def w81 : W := 0x1fffc0007fff0001ffffffffffffffffffcaf995f32be657ccaf995f32be657ccaf995f3
def w82 : W := 0x1fffffff800000000003fff8000000000000888111022204440888111022204440888111
def w83 : W := 0x1fffffff800000000003fff8000000000007888f111e223c447888f111e223c447888f11
def w84 : W := 0x1fffffff800000000003ffffffffffffffc08981130226044c08981130226044c0898113
def w85 : W := 0x1fffffff800000000003ffffffffffffffc7898f131e263c4c7898f131e263c4c7898f13
def w86 : W := 0x1fffffff80000001fffffff8000000000007888f111e223c447888f111e223c447888f11
def w87 : W := 0x1fffffff80000001fffffff800000000000fa99f533ea67d4cfa99f533ea67d4cfa99f53
def w88 : W := 0x1fffffff80000001ffffffffffffffffffcfa99f533ea67d4cfa99f533ea67d4cfa99f53
def w89 : W := 0x1fffffffffff00000003fff8000000000000888111022204440888111022204440888111
def w90 : W := 0x1fffffffffff00000003fff8000000000000f881f103e207c40f881f103e207c40f881f1
def w91 : W := 0x1fffffffffff00000003fff8000000000007888f111e223c447888f111e223c447888f11
def w92 : W := 0x1fffffffffff00000003fff8000000000007f88ff11fe23fc47f88ff11fe23fc47f88ff1
def w93 : W := 0x1fffffffffff00000003ffffffffffffffc08981130226044c08981130226044c0898113
def w94 : W := 0x1fffffffffff00000003ffffffffffffffc7f98ff31fe63fcc7f98ff31fe63fcc7f98ff3
def w95 : W := 0x1fffffffffff0001fffffff8000000000007f88ff11fe23fc47f88ff11fe23fc47f88ff1
def w96 : W := 0x1fffffffffff0001fffffff800000000000ff99ff33fe67fccff99ff33fe67fccff99ff3
def w97 : W := 0x1fffffffffff0001ffffffffffffffffffcff99ff33fe67fccff99ff33fe67fccff99ff3
def w98 : W := 0xfffe000000000000000000000000000001fffc1120224044808901120224044808901120224
def w99 : W := 0xfffe00000000000000000000000000fffffffc1120224044808901120224044808901120224
def w100 : W := 0xfffe00000000000000000000000000fffffffd5562aac5558aab15562aac5558aab15562aac
def w101 : W := 0xfffe00000000000fffffffffff80000001fffc116022c045808b0116022c045808b0116022c
def w102 : W := 0xfffe00000000000fffffffffff8000fffffffc116022c045808b0116022c045808b0116022c
def w103 : W := 0xfffe00000000000fffffffffff8000fffffffd5562aac5558aab15562aac5558aab15562aac
def w104 : W := 0xfffe00000007fff0000000000000000001fffc1120224044808901120224044808901120224
def w105 : W := 0xfffe00000007fff0000000000000000001fffc17a02f405e80bd017a02f405e80bd017a02f4
def w106 : W := 0xfffe00000007fff000000000000000fffffffc17a02f405e80bd017a02f405e80bd017a02f4
def w107 : W := 0xfffe00000007fff000000000000000fffffffd57e2afc55f8abf157e2afc55f8abf157e2afc
def w108 : W := 0xfffe00000007ffffffffffffff80000001fffc116022c045808b0116022c045808b0116022c
def w109 : W := 0xfffe00000007ffffffffffffff80000001fffc17e02fc05f80bf017e02fc05f80bf017e02fc
def w110 : W := 0xfffe00000007ffffffffffffff8000fffffffd57e2afc55f8abf157e2afc55f8abf157e2afc
def w111 : W := 0xfffe0003fff80000000000000000000001fffc1120224044808901120224044808901120224
def w112 : W := 0xfffe0003fff80000000000000000000001fffc7920f241e483c907920f241e483c907920f24
def w113 : W := 0xfffe0003fff8000000000000000000fffffffc7920f241e483c907920f241e483c907920f24
def w114 : W := 0xfffe0003fff8000000000000000000fffffffd7d62fac5f58beb17d62fac5f58beb17d62fac
def w115 : W := 0xfffe0003fff8000fffffffffff80000001fffc116022c045808b0116022c045808b0116022c
def w116 : W := 0xfffe0003fff8000fffffffffff80000001fffc7960f2c1e583cb07960f2c1e583cb07960f2c
def w117 : W := 0xfffe0003fff8000fffffffffff8000fffffffd7d62fac5f58beb17d62fac5f58beb17d62fac
def w118 : W := 0xfffe0003fffffff0000000000000000001fffc1120224044808901120224044808901120224
def w119 : W := 0xfffe0003fffffff0000000000000000001fffc17a02f405e80bd017a02f405e80bd017a02f4
def w120 : W := 0xfffe0003fffffff0000000000000000001fffc7920f241e483c907920f241e483c907920f24
def w121 : W := 0xfffe0003fffffff0000000000000000001fffc7fa0ff41fe83fd07fa0ff41fe83fd07fa0ff4
def w122 : W := 0xfffe0003fffffff000000000000000fffffffc7fa0ff41fe83fd07fa0ff41fe83fd07fa0ff4
def w123 : W := 0xfffe0003fffffff000000000000000fffffffd7fe2ffc5ff8bff17fe2ffc5ff8bff17fe2ffc
def w124 : W := 0xfffe0003ffffffffffffffffff80000001fffc116022c045808b0116022c045808b0116022c
def w125 : W := 0xfffe0003ffffffffffffffffff80000001fffc7fe0ffc1ff83ff07fe0ffc1ff83ff07fe0ffc
def w126 : W := 0xfffe0003ffffffffffffffffff8000fffffffd7fe2ffc5ff8bff17fe2ffc5ff8bff17fe2ffc
def w127 : W := 0xfffffffc0000000000000000000000000000038007000e001c0038007000e001c0038007000
def w128 : W := 0xfffffffc0000000000000000000000fffe00038007000e001c0038007000e001c0038007000
def w129 : W := 0xfffffffc0000000000000000000000fffe0003c447888f111e223c447888f111e223c447888
def w130 : W := 0xfffffffc00000000001fffc0000000000000038007000e001c0038007000e001c0038007000
def w131 : W := 0xfffffffc00000000001fffc000000000000003a217442e885d10ba217442e885d10ba217442
def w132 : W := 0xffffffffffffffffffe00000007fff000000038007000e001c0038007000e001c0038007000
def w133 : W := 0xffffffffffffffffffe00000007ffffffe00038007000e001c0038007000e001c0038007000
def w134 : W := 0xffffffffffffffffffe00000007ffffffe0003c447888f111e223c447888f111e223c447888
def w135 : W := 0xffffffffffffffffffffffc0007fff000000038007000e001c0038007000e001c0038007000
def w136 : W := 0xffffffffffffffffffffffc0007fff00000003a217442e885d10ba217442e885d10ba217442
def t4 := (n (n (n (n z [w1,w4,w70,w124,w132] z) [w1,w4,w93,w101,w132] z) [w1,w45,w70,w101,w135] (n z [w1,w45,w73,w101,w132] z)) [w1,w74,w94,w101,w132] (n (n (n z [w4,w45,w70,w101,w133] z) [w4,w45,w70,w102,w132] z) [w4,w70,w103,w125,w132] (n z [w45,w70,w101,w134,w136] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht4 : ReplayTree.all (blocked 3 z) t4 = true := by
  decide +kernel
theorem s4 : sound 4 t4 := layer_sound (empty_sound 3) ht4
def t5aaaa := (n (n (n (n z [w0,w4,w45,w70,w101,w132] z) [w1,w2,w4,w69,w124,w132] (n z [w1,w2,w4,w89,w101,w132] z)) [w1,w2,w7,w69,w121,w135] (n (n z [w1,w2,w7,w71,w121,w132] z) [w1,w2,w7,w76,w112,w135] z)) [w1,w2,w7,w79,w112,w132] (n (n (n z [w1,w2,w7,w83,w105,w135] z) [w1,w2,w7,w86,w105,w132] (n z [w1,w2,w7,w92,w98,w135] z)) [w1,w2,w7,w95,w98,w132] (n (n z [w1,w2,w45,w69,w101,w135] z) [w1,w2,w45,w71,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aaaa : ReplayTree.all (blocked 4 t4) t5aaaa = true := by
  decide +kernel
def t5aaab := (n (n (n (n z [w1,w2,w60,w89,w101,w131] z) [w1,w2,w72,w92,w101,w132] (n z [w1,w3,w45,w70,w101,w132] z)) [w1,w4,w7,w70,w118,w132] (n (n z [w1,w4,w7,w93,w98,w132] z) [w1,w4,w11,w70,w115,w132] z)) [w1,w4,w11,w84,w101,w132] (n (n (n z [w1,w4,w27,w70,w108,w132] z) [w1,w4,w27,w77,w101,w132] z) [w1,w4,w42,w70,w101,w132] (n (n z [w1,w4,w43,w70,w101,w132] z) [w1,w4,w44,w70,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aaab : ReplayTree.all (blocked 4 t4) t5aaab = true := by
  decide +kernel
def t5aaa := (n t5aaaa [w1,w2,w60,w69,w124,w131] t5aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aaa : ReplayTree.all (blocked 4 t4) t5aaa = true := by
  simp only [t5aaa, ReplayTree.all, n, ht5aaaa, ht5aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaba := (n (n (n (n z [w1,w4,w51,w69,w101,w132] z) [w1,w4,w52,w70,w101,w132] (n z [w1,w4,w60,w70,w124,w127] z)) [w1,w4,w60,w93,w101,w127] (n (n z [w1,w4,w65,w70,w98,w132] z) [w1,w4,w66,w70,w101,w132] z)) [w1,w4,w70,w92,w101,w132] (n (n (n z [w1,w4,w70,w94,w101,w132] z) [w1,w4,w70,w101,w121,w132] z) [w1,w4,w70,w101,w125,w132] (n (n z [w1,w4,w70,w109,w116,w132] z) [w1,w4,w78,w85,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aaba : ReplayTree.all (blocked 4 t4) t5aaba = true := by
  decide +kernel
def t5aabb := (n (n (n (n z [w1,w5,w7,w76,w112,w132] z) [w1,w5,w7,w83,w105,w132] (n z [w1,w5,w7,w92,w98,w132] z)) [w1,w5,w45,w69,w101,w132] (n (n z [w1,w6,w7,w70,w121,w132] z) [w1,w6,w7,w78,w112,w132] z)) [w1,w6,w7,w85,w105,w132] (n (n (n z [w1,w6,w7,w94,w98,w132] z) [w1,w6,w45,w70,w101,w132] z) [w1,w6,w52,w69,w101,w132] (n (n z [w1,w6,w60,w69,w124,w127] z) [w1,w6,w60,w89,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aabb : ReplayTree.all (blocked 4 t4) t5aabb = true := by
  decide +kernel
def t5aab := (n t5aaba [w1,w5,w7,w69,w121,w132] t5aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aab : ReplayTree.all (blocked 4 t4) t5aab = true := by
  simp only [t5aab, ReplayTree.all, n, ht5aaba, ht5aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aa := (n t5aaa [w1,w4,w45,w70,w101,w132] t5aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aa : ReplayTree.all (blocked 4 t4) t5aa = true := by
  simp only [t5aa, ReplayTree.all, n, ht5aaa, ht5aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaa := (n (n (n (n z [w1,w7,w45,w73,w98,w132] z) [w1,w7,w53,w70,w98,w132] (n z [w1,w7,w74,w94,w98,w132] z)) [w1,w11,w27,w70,w101,w135] (n (n z [w1,w11,w27,w73,w101,w132] z) [w1,w11,w74,w85,w101,w132] z)) [w1,w27,w74,w78,w101,w132] (n (n (n z [w1,w45,w60,w70,w101,w130] z) [w1,w45,w60,w73,w101,w127] (n z [w1,w45,w63,w70,w101,w127] z)) [w1,w45,w64,w70,w101,w132] (n (n z [w1,w45,w70,w72,w101,w132] z) [w1,w45,w70,w74,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5abaa : ReplayTree.all (blocked 4 t4) t5abaa = true := by
  decide +kernel
def t5abab := (n (n (n (n z [w1,w45,w70,w101,w132,w136] z) [w1,w51,w60,w69,w101,w131] (n z [w1,w54,w60,w70,w101,w127] z)) [w1,w58,w60,w69,w101,w127] (n (n z [w1,w60,w70,w92,w101,w131] z) [w1,w60,w74,w92,w101,w127] z)) [w1,w60,w74,w94,w101,w127] (n (n (n z [w2,w4,w7,w69,w121,w133] z) [w2,w4,w7,w69,w122,w132] z) [w2,w4,w7,w76,w112,w133] (n (n z [w2,w4,w7,w76,w113,w132] z) [w2,w4,w7,w83,w105,w133] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5abab : ReplayTree.all (blocked 4 t4) t5abab = true := by
  decide +kernel
def t5aba := (n t5abaa [w1,w45,w70,w101,w131,w132] t5abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5aba : ReplayTree.all (blocked 4 t4) t5aba = true := by
  simp only [t5aba, ReplayTree.all, n, ht5abaa, ht5abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abba := (n (n (n (n z [w2,w4,w7,w92,w98,w133] z) [w2,w4,w7,w92,w99,w132] (n z [w2,w4,w8,w69,w121,w132] z)) [w2,w4,w8,w76,w112,w132] (n (n z [w2,w4,w8,w83,w105,w132] z) [w2,w4,w8,w92,w98,w132] z)) [w2,w4,w9,w69,w125,w132] (n (n (n z [w2,w4,w9,w76,w116,w132] z) [w2,w4,w9,w83,w109,w132] z) [w2,w4,w9,w92,w101,w132] (n (n z [w2,w4,w45,w69,w101,w133] z) [w2,w4,w45,w69,w102,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5abba : ReplayTree.all (blocked 4 t4) t5abba = true := by
  decide +kernel
def t5abbb := (n (n (n (n z [w2,w4,w69,w103,w125,w132] z) [w2,w7,w69,w121,w134,w136] (n z [w2,w7,w76,w112,w134,w136] z)) [w2,w7,w83,w105,w134,w136] (n (n z [w2,w7,w92,w98,w134,w136] z) [w2,w9,w60,w71,w121,w127] z)) [w2,w9,w63,w69,w121,w127] (n (n (n z [w2,w9,w64,w69,w121,w132] z) [w2,w14,w60,w69,w115,w131] z) [w2,w14,w60,w82,w101,w131] (n (n z [w2,w30,w60,w69,w108,w131] z) [w2,w30,w60,w75,w101,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5abbb : ReplayTree.all (blocked 4 t4) t5abbb = true := by
  decide +kernel
def t5abb := (n t5abba [w2,w4,w46,w69,w101,w132] t5abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5abb : ReplayTree.all (blocked 4 t4) t5abb = true := by
  simp only [t5abb, ReplayTree.all, n, ht5abba, ht5abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ab := (n t5aba [w2,w4,w7,w83,w106,w132] t5abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5ab : ReplayTree.all (blocked 4 t4) t5ab = true := by
  simp only [t5ab, ReplayTree.all, n, ht5aba, ht5abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5a := (n t5aa [w1,w7,w45,w70,w98,w135] t5ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5a : ReplayTree.all (blocked 4 t4) t5a = true := by
  simp only [t5a, ReplayTree.all, n, ht5aa, ht5ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaa := (n (n (n (n z [w2,w45,w61,w69,w101,w131] z) [w2,w45,w62,w69,w101,w136] (n z [w2,w45,w69,w101,w134,w136] z)) [w2,w46,w60,w69,w101,w131] (n (n z [w2,w47,w60,w69,w101,w131] z) [w2,w48,w60,w69,w101,w131] z)) [w2,w49,w60,w69,w101,w131] (n (n (n z [w2,w50,w60,w69,w101,w130] z) [w2,w50,w60,w69,w101,w131] (n z [w2,w50,w60,w69,w101,w136] z)) [w2,w50,w60,w71,w101,w127] (n (n z [w2,w50,w63,w69,w101,w127] z) [w2,w50,w64,w69,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5baaa : ReplayTree.all (blocked 4 t4) t5baaa = true := by
  decide +kernel
def t5baab := (n (n (n (n z [w2,w60,w69,w101,w123,w131] z) [w2,w60,w69,w101,w126,w131] (n z [w2,w60,w69,w103,w125,w131] z)) [w2,w60,w69,w109,w117,w131] (n (n z [w2,w60,w69,w110,w116,w131] z) [w4,w7,w45,w70,w98,w133] z)) [w4,w7,w45,w70,w99,w132] (n (n (n z [w4,w7,w60,w70,w118,w129] z) [w4,w7,w60,w93,w98,w129] z) [w4,w7,w70,w100,w121,w132] (n (n z [w4,w8,w45,w70,w98,w132] z) [w4,w9,w45,w70,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5baab : ReplayTree.all (blocked 4 t4) t5baab = true := by
  decide +kernel
def t5baa := (n t5baaa [w2,w60,w68,w69,w101,w131] t5baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5baa : ReplayTree.all (blocked 4 t4) t5baa = true := by
  simp only [t5baa, ReplayTree.all, n, ht5baaa, ht5baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baba := (n (n (n (n z [w4,w9,w60,w93,w98,w127] z) [w4,w9,w66,w70,w98,w132] (n z [w4,w11,w27,w70,w101,w133] z)) [w4,w11,w27,w70,w102,w132] (n (n z [w4,w11,w70,w103,w116,w132] z) [w4,w27,w70,w103,w109,w132] z)) [w4,w45,w60,w70,w101,w128] (n (n (n z [w4,w45,w60,w70,w102,w127] z) [w4,w45,w61,w70,w101,w127] z) [w4,w45,w62,w70,w101,w132] (n (n z [w4,w45,w70,w100,w101,w132] z) [w4,w45,w70,w101,w103,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5baba : ReplayTree.all (blocked 4 t4) t5baba = true := by
  decide +kernel
def t5babb := (n (n (n (n z [w4,w45,w70,w101,w132,w134] z) [w4,w47,w60,w70,w101,w127] (n z [w4,w60,w65,w70,w98,w129] z)) [w4,w60,w67,w70,w98,w127] (n (n z [w4,w60,w70,w101,w121,w129] z) [w4,w60,w70,w103,w121,w127] z)) [w4,w60,w70,w103,w125,w127] (n (n (n z [w5,w9,w60,w69,w121,w127] z) [w5,w50,w60,w69,w101,w127] z) [w6,w7,w60,w92,w99,w127] (n (n z [w6,w7,w61,w92,w98,w127] z) [w6,w7,w62,w92,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5babb : ReplayTree.all (blocked 4 t4) t5babb = true := by
  decide +kernel
def t5bab := (n t5baba [w4,w45,w70,w101,w129,w132] t5babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bab : ReplayTree.all (blocked 4 t4) t5bab = true := by
  simp only [t5bab, ReplayTree.all, n, ht5baba, ht5babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ba := (n t5baa [w4,w9,w60,w70,w118,w127] t5bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5ba : ReplayTree.all (blocked 4 t4) t5ba = true := by
  simp only [t5ba, ReplayTree.all, n, ht5baa, ht5bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaa := (n (n (n (n z [w6,w9,w60,w69,w118,w127] z) [w6,w9,w60,w70,w121,w127] (n z [w6,w9,w60,w89,w98,w127] z)) [w6,w9,w60,w92,w101,w127] (n (n z [w6,w45,w60,w69,w102,w127] z) [w6,w45,w61,w69,w101,w127] z)) [w6,w45,w62,w69,w101,w132] (n (n (n z [w6,w47,w60,w69,w101,w127] z) [w6,w50,w60,w70,w101,w127] (n z [w6,w60,w67,w69,w98,w127] z)) [w6,w60,w69,w103,w121,w127] (n (n z [w6,w60,w69,w103,w125,w127] z) [w7,w19,w60,w70,w111,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bbaa : ReplayTree.all (blocked 4 t4) t5bbaa = true := by
  decide +kernel
def t5bbab := (n (n (n (n z [w7,w35,w60,w70,w104,w129] z) [w7,w35,w60,w77,w98,w129] (n z [w7,w45,w60,w73,w98,w129] z)) [w7,w45,w63,w70,w98,w129] (n (n z [w7,w45,w64,w70,w98,w134] z) [w7,w45,w70,w98,w134,w136] z)) [w7,w53,w60,w70,w98,w129] (n (n (n z [w7,w54,w60,w70,w98,w129] z) [w7,w55,w60,w70,w98,w129] z) [w7,w56,w60,w70,w98,w129] (n (n z [w7,w57,w60,w70,w98,w128] z) [w7,w57,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bbab : ReplayTree.all (blocked 4 t4) t5bbab = true := by
  decide +kernel
def t5bba := (n t5bbaa [w7,w19,w60,w84,w98,w129] t5bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bba : ReplayTree.all (blocked 4 t4) t5bba = true := by
  simp only [t5bba, ReplayTree.all, n, ht5bbaa, ht5bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbba := (n (n (n (n z [w7,w57,w60,w70,w99,w127] z) [w7,w57,w61,w70,w98,w127] (n z [w7,w57,w62,w70,w98,w132] z)) [w7,w59,w60,w70,w98,w129] (n (n z [w7,w60,w70,w96,w98,w129] z) [w7,w60,w70,w97,w98,w129] z)) [w7,w60,w74,w94,w98,w129] (n (n (n z [w7,w60,w78,w88,w98,w129] z) [w7,w60,w81,w85,w98,w129] z) [w8,w57,w60,w70,w98,w127] (n (n z [w9,w45,w60,w73,w98,w127] z) [w9,w45,w63,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bbba : ReplayTree.all (blocked 4 t4) t5bbba = true := by
  decide +kernel
def t5bbbb := (n (n (n (n z [w9,w54,w60,w70,w98,w127] z) [w9,w57,w60,w70,w101,w127] (n z [w9,w58,w60,w69,w98,w127] z)) [w9,w60,w74,w92,w98,w127] (n (n z [w9,w60,w74,w94,w98,w127] z) [w11,w27,w70,w101,w134,w136] z)) [w14,w31,w60,w69,w101,w131] (n (n (n z [w15,w30,w60,w69,w101,w131] z) [w19,w38,w60,w70,w98,w129] z) [w22,w35,w60,w70,w98,w129] (n (n z [w45,w60,w70,w101,w129,w131] z) [w45,w62,w64,w70,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bbbb : ReplayTree.all (blocked 4 t4) t5bbbb = true := by
  decide +kernel
def t5bbb := (n t5bbba [w9,w45,w64,w70,w98,w132] t5bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bbb : ReplayTree.all (blocked 4 t4) t5bbb = true := by
  simp only [t5bbb, ReplayTree.all, n, ht5bbba, ht5bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bb := (n t5bba [w7,w57,w60,w70,w98,w134] t5bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5bb : ReplayTree.all (blocked 4 t4) t5bb = true := by
  simp only [t5bb, ReplayTree.all, n, ht5bba, ht5bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5b := (n t5ba [w6,w8,w60,w92,w98,w127] t5bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5b : ReplayTree.all (blocked 4 t4) t5b = true := by
  simp only [t5b, ReplayTree.all, n, ht5ba, ht5bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5 := (n t5a [w2,w45,w60,w69,w102,w131] t5b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht5 : ReplayTree.all (blocked 4 t4) t5 = true := by
  simp only [t5, ReplayTree.all, n, ht5a, ht5b, Bool.true_and, Bool.and_true]
  decide +kernel
theorem s5 : sound 5 t5 := layer_sound s4 ht5
def t6aaaaaa := (n (n (n (n z [w0,w2,w4,w7,w69,w121,w132] z) [w0,w2,w4,w7,w76,w112,w132] (n z [w0,w2,w4,w7,w83,w105,w132] z)) [w0,w2,w4,w7,w92,w98,w132] (n (n z [w0,w2,w4,w45,w69,w101,w132] z) [w0,w2,w45,w60,w69,w101,w131] (n z [w0,w4,w7,w45,w70,w98,w132] z))) [w0,w4,w11,w27,w70,w101,w132] (n (n (n z [w0,w4,w45,w60,w70,w101,w127] z) [w0,w6,w7,w60,w92,w98,w127] (n z [w0,w6,w45,w60,w69,w101,w127] z)) [w0,w7,w57,w60,w70,w98,w127] (n (n z [w1,w2,w3,w7,w69,w121,w132] z) [w1,w2,w3,w7,w76,w112,w132] (n z [w1,w2,w3,w7,w83,w105,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaaaa : ReplayTree.all (blocked 5 t5) t6aaaaaa = true := by
  decide +kernel
def t6aaaaab := (n (n (n (n z [w1,w2,w3,w45,w69,w101,w132] z) [w1,w2,w4,w7,w69,w118,w132] (n z [w1,w2,w4,w7,w69,w119,w132] z)) [w1,w2,w4,w7,w69,w120,w132] (n (n z [w1,w2,w4,w7,w69,w121,w132] z) [w1,w2,w4,w7,w69,w125,w132] (n z [w1,w2,w4,w7,w70,w121,w132] z))) [w1,w2,w4,w7,w75,w112,w132] (n (n (n z [w1,w2,w4,w7,w76,w111,w132] z) [w1,w2,w4,w7,w76,w112,w132] (n z [w1,w2,w4,w7,w76,w116,w132] z)) [w1,w2,w4,w7,w76,w121,w132] (n (n z [w1,w2,w4,w7,w78,w112,w132] z) [w1,w2,w4,w7,w82,w105,w132] (n z [w1,w2,w4,w7,w83,w104,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaaab : ReplayTree.all (blocked 5 t5) t6aaaaab = true := by
  decide +kernel
def t6aaaaa := (n t6aaaaaa [w1,w2,w3,w7,w92,w98,w132] t6aaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaaa : ReplayTree.all (blocked 5 t5) t6aaaaa = true := by
  simp only [t6aaaaa, ReplayTree.all, n, ht6aaaaaa, ht6aaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaaba := (n (n (n (n z [w1,w2,w4,w7,w83,w109,w132] z) [w1,w2,w4,w7,w83,w121,w132] (n z [w1,w2,w4,w7,w85,w105,w132] z)) [w1,w2,w4,w7,w89,w98,w132] (n (n z [w1,w2,w4,w7,w90,w98,w132] z) [w1,w2,w4,w7,w91,w98,w132] (n z [w1,w2,w4,w7,w92,w98,w132] z))) [w1,w2,w4,w7,w92,w101,w132] (n (n (n z [w1,w2,w4,w7,w92,w105,w132] z) [w1,w2,w4,w7,w92,w112,w132] (n z [w1,w2,w4,w7,w92,w121,w132] z)) [w1,w2,w4,w7,w94,w98,w132] (n (n z [w1,w2,w4,w11,w69,w115,w132] z) [w1,w2,w4,w11,w82,w101,w132] (n z [w1,w2,w4,w22,w69,w112,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaaba : ReplayTree.all (blocked 5 t5) t6aaaaba = true := by
  decide +kernel
def t6aaaabb := (n (n (n (n z [w1,w2,w4,w23,w69,w116,w132] z) [w1,w2,w4,w23,w83,w101,w132] (n z [w1,w2,w4,w27,w69,w108,w132] z)) [w1,w2,w4,w27,w75,w101,w132] (n (n z [w1,w2,w4,w38,w69,w105,w132] z) [w1,w2,w4,w38,w76,w98,w132] (n z [w1,w2,w4,w39,w69,w109,w132] z))) [w1,w2,w4,w39,w76,w101,w132] (n (n (n z [w1,w2,w4,w42,w69,w101,w132] z) [w1,w2,w4,w43,w69,w101,w132] (n z [w1,w2,w4,w44,w69,w101,w132] z)) [w1,w2,w4,w45,w69,w101,w132] (n (n z [w1,w2,w4,w45,w70,w101,w132] z) [w1,w2,w4,w52,w69,w101,w132] (n z [w1,w2,w4,w60,w69,w124,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaabb : ReplayTree.all (blocked 5 t5) t6aaaabb = true := by
  decide +kernel
def t6aaaab := (n t6aaaaba [w1,w2,w4,w22,w83,w98,w132] t6aaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaab : ReplayTree.all (blocked 5 t5) t6aaaab = true := by
  simp only [t6aaaab, ReplayTree.all, n, ht6aaaaba, ht6aaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaa := (n t6aaaaa [w1,w2,w4,w7,w83,w105,w132] t6aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaa : ReplayTree.all (blocked 5 t5) t6aaaa = true := by
  simp only [t6aaaa, ReplayTree.all, n, ht6aaaaa, ht6aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaabaa := (n (n (n (n z [w1,w2,w4,w65,w69,w98,w132] z) [w1,w2,w4,w66,w69,w101,w132] (n z [w1,w2,w4,w69,w92,w101,w132] z)) [w1,w2,w4,w69,w101,w121,w132] (n (n z [w1,w2,w4,w69,w101,w125,w132] z) [w1,w2,w4,w69,w109,w116,w132] (n z [w1,w2,w4,w76,w83,w101,w132] z))) [w1,w2,w6,w7,w69,w121,w132] (n (n (n z [w1,w2,w6,w7,w76,w112,w132] z) [w1,w2,w6,w7,w83,w105,w132] (n z [w1,w2,w6,w7,w92,w98,w132] z)) [w1,w2,w6,w45,w69,w101,w132] (n (n z [w1,w2,w7,w11,w69,w112,w135] z) [w1,w2,w7,w11,w71,w112,w132] (n z [w1,w2,w7,w11,w83,w98,w135] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaabaa : ReplayTree.all (blocked 5 t5) t6aaabaa = true := by
  decide +kernel
def t6aaabab := (n (n (n (n z [w1,w2,w7,w17,w69,w112,w132] z) [w1,w2,w7,w17,w83,w98,w132] (n z [w1,w2,w7,w19,w69,w121,w132] z)) [w1,w2,w7,w19,w76,w112,w132] (n (n z [w1,w2,w7,w19,w83,w105,w132] z) [w1,w2,w7,w19,w92,w98,w132] (n z [w1,w2,w7,w27,w69,w105,w135] z))) [w1,w2,w7,w27,w71,w105,w132] (n (n (n z [w1,w2,w7,w27,w76,w98,w135] z) [w1,w2,w7,w27,w79,w98,w132] (n z [w1,w2,w7,w33,w69,w105,w132] z)) [w1,w2,w7,w33,w76,w98,w132] (n (n z [w1,w2,w7,w35,w69,w121,w132] z) [w1,w2,w7,w35,w76,w112,w132] (n z [w1,w2,w7,w35,w83,w105,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaabab : ReplayTree.all (blocked 5 t5) t6aaabab = true := by
  decide +kernel
def t6aaaba := (n t6aaabaa [w1,w2,w7,w11,w86,w98,w132] t6aaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaaba : ReplayTree.all (blocked 5 t5) t6aaaba = true := by
  simp only [t6aaaba, ReplayTree.all, n, ht6aaabaa, ht6aaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaabba := (n (n (n (n z [w1,w2,w7,w45,w69,w98,w135] z) [w1,w2,w7,w45,w71,w98,w132] (n z [w1,w2,w7,w53,w69,w98,w132] z)) [w1,w2,w7,w57,w69,w121,w132] (n (n z [w1,w2,w7,w57,w92,w98,w132] z) [w1,w2,w7,w60,w69,w118,w131] (n z [w1,w2,w7,w60,w69,w121,w130] z))) [w1,w2,w7,w60,w71,w121,w127] (n (n (n z [w1,w2,w7,w60,w76,w112,w130] z) [w1,w2,w7,w60,w79,w112,w127] (n z [w1,w2,w7,w60,w83,w105,w130] z)) [w1,w2,w7,w60,w86,w105,w127] (n (n z [w1,w2,w7,w60,w89,w98,w131] z) [w1,w2,w7,w60,w92,w98,w130] (n z [w1,w2,w7,w60,w95,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaabba : ReplayTree.all (blocked 5 t5) t6aaabba = true := by
  decide +kernel
def t6aaabbb := (n (n (n (n z [w1,w2,w7,w63,w76,w112,w127] z) [w1,w2,w7,w63,w83,w105,w127] (n z [w1,w2,w7,w63,w92,w98,w127] z)) [w1,w2,w7,w64,w69,w121,w132] (n (n z [w1,w2,w7,w64,w76,w112,w132] z) [w1,w2,w7,w64,w83,w105,w132] (n z [w1,w2,w7,w64,w92,w98,w132] z))) [w1,w2,w7,w69,w72,w121,w132] (n (n (n z [w1,w2,w7,w69,w121,w131,w132] z) [w1,w2,w7,w69,w121,w132,w136] (n z [w1,w2,w7,w72,w76,w112,w132] z)) [w1,w2,w7,w72,w83,w105,w132] (n (n z [w1,w2,w7,w72,w92,w98,w132] z) [w1,w2,w7,w76,w80,w112,w132] (n z [w1,w2,w7,w76,w112,w131,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaabbb : ReplayTree.all (blocked 5 t5) t6aaabbb = true := by
  decide +kernel
def t6aaabb := (n t6aaabba [w1,w2,w7,w63,w69,w121,w127] t6aaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaabb : ReplayTree.all (blocked 5 t5) t6aaabb = true := by
  simp only [t6aaabb, ReplayTree.all, n, ht6aaabba, ht6aaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaab := (n t6aaaba [w1,w2,w7,w35,w92,w98,w132] t6aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaab : ReplayTree.all (blocked 5 t5) t6aaab = true := by
  simp only [t6aaab, ReplayTree.all, n, ht6aaaba, ht6aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaa := (n t6aaaa [w1,w2,w4,w60,w89,w101,w127] t6aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaa : ReplayTree.all (blocked 5 t5) t6aaa = true := by
  simp only [t6aaa, ReplayTree.all, n, ht6aaaa, ht6aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabaaa := (n (n (n (n z [w1,w2,w7,w80,w92,w98,w132] z) [w1,w2,w7,w83,w87,w105,w132] (n z [w1,w2,w7,w83,w105,w131,w132] z)) [w1,w2,w7,w83,w105,w132,w136] (n (n z [w1,w2,w7,w87,w92,w98,w132] z) [w1,w2,w7,w92,w96,w98,w132] (n z [w1,w2,w7,w92,w98,w131,w132] z))) [w1,w2,w7,w92,w98,w132,w136] (n (n (n z [w1,w2,w11,w27,w69,w101,w135] z) [w1,w2,w11,w27,w71,w101,w132] (n z [w1,w2,w11,w60,w69,w115,w131] z)) [w1,w2,w11,w60,w82,w101,w131] (n (n z [w1,w2,w11,w72,w83,w101,w132] z) [w1,w2,w27,w60,w69,w108,w131] (n z [w1,w2,w27,w60,w75,w101,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabaaa : ReplayTree.all (blocked 5 t5) t6aabaaa = true := by
  decide +kernel
def t6aabaab := (n (n (n (n z [w1,w2,w42,w60,w69,w101,w131] z) [w1,w2,w43,w60,w69,w101,w131] (n z [w1,w2,w44,w60,w69,w101,w131] z)) [w1,w2,w45,w60,w69,w101,w130] (n (n z [w1,w2,w45,w60,w69,w101,w131] z) [w1,w2,w45,w60,w69,w101,w136] (n z [w1,w2,w45,w60,w71,w101,w127] z))) [w1,w2,w45,w63,w69,w101,w127] (n (n (n z [w1,w2,w45,w64,w69,w101,w132] z) [w1,w2,w45,w69,w72,w101,w132] (n z [w1,w2,w45,w69,w101,w131,w132] z)) [w1,w2,w45,w69,w101,w132,w136] (n (n z [w1,w2,w50,w60,w69,w101,w131] z) [w1,w2,w52,w60,w69,w101,w131] (n z [w1,w2,w54,w60,w69,w101,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabaab : ReplayTree.all (blocked 5 t5) t6aabaab = true := by
  decide +kernel
def t6aabaa := (n t6aabaaa [w1,w2,w27,w72,w76,w101,w132] t6aabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabaa : ReplayTree.all (blocked 5 t5) t6aabaa = true := by
  simp only [t6aabaa, ReplayTree.all, n, ht6aabaaa, ht6aabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aababa := (n (n (n (n z [w1,w2,w60,w65,w69,w98,w131] z) [w1,w2,w60,w66,w69,w101,w131] (n z [w1,w2,w60,w69,w92,w101,w131] z)) [w1,w2,w60,w69,w101,w121,w131] (n (n z [w1,w2,w60,w69,w101,w125,w131] z) [w1,w2,w60,w69,w109,w116,w131] (n z [w1,w2,w60,w72,w92,w101,w127] z))) [w1,w2,w60,w76,w83,w101,w131] (n (n (n z [w1,w3,w7,w45,w70,w98,w132] z) [w1,w3,w11,w27,w70,w101,w132] (n z [w1,w3,w45,w60,w70,w101,w127] z)) [w1,w4,w7,w11,w70,w111,w132] (n (n z [w1,w4,w7,w11,w84,w98,w132] z) [w1,w4,w7,w15,w69,w112,w132] (n z [w1,w4,w7,w15,w83,w98,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aababa : ReplayTree.all (blocked 5 t5) t6aababa = true := by
  decide +kernel
def t6aababb := (n (n (n (n z [w1,w4,w7,w16,w85,w98,w132] z) [w1,w4,w7,w27,w70,w104,w132] (n z [w1,w4,w7,w27,w77,w98,w132] z)) [w1,w4,w7,w31,w69,w105,w132] (n (n z [w1,w4,w7,w31,w76,w98,w132] z) [w1,w4,w7,w32,w70,w105,w132] (n z [w1,w4,w7,w32,w78,w98,w132] z))) [w1,w4,w7,w42,w70,w98,w132] (n (n (n z [w1,w4,w7,w43,w70,w98,w132] z) [w1,w4,w7,w44,w70,w98,w132] (n z [w1,w4,w7,w45,w70,w98,w132] z)) [w1,w4,w7,w45,w70,w101,w132] (n (n z [w1,w4,w7,w51,w69,w98,w132] z) [w1,w4,w7,w52,w70,w98,w132] (n z [w1,w4,w7,w60,w70,w118,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aababb : ReplayTree.all (blocked 5 t5) t6aababb = true := by
  decide +kernel
def t6aabab := (n t6aababa [w1,w4,w7,w16,w70,w112,w132] t6aababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabab : ReplayTree.all (blocked 5 t5) t6aabab = true := by
  simp only [t6aabab, ReplayTree.all, n, ht6aababa, ht6aababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaba := (n t6aabaa [w1,w2,w57,w60,w69,w101,w131] t6aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aaba : ReplayTree.all (blocked 5 t5) t6aaba = true := by
  simp only [t6aaba, ReplayTree.all, n, ht6aabaa, ht6aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbaa := (n (n (n (n z [w1,w4,w7,w66,w70,w98,w132] z) [w1,w4,w7,w70,w92,w98,w132] (n z [w1,w4,w7,w70,w94,w98,w132] z)) [w1,w4,w7,w70,w98,w121,w132] (n (n z [w1,w4,w7,w70,w105,w112,w132] z) [w1,w4,w7,w78,w85,w98,w132] (n z [w1,w4,w10,w27,w70,w101,w132] z))) [w1,w4,w11,w26,w70,w101,w132] (n (n (n z [w1,w4,w11,w27,w70,w101,w132] z) [w1,w4,w11,w31,w69,w101,w132] (n z [w1,w4,w11,w32,w70,w101,w132] z)) [w1,w4,w11,w38,w70,w98,w132] (n (n z [w1,w4,w11,w39,w70,w101,w132] z) [w1,w4,w11,w45,w70,w101,w132] (n z [w1,w4,w11,w60,w70,w115,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabbaa : ReplayTree.all (blocked 5 t5) t6aabbaa = true := by
  decide +kernel
def t6aabbab := (n (n (n (n z [w1,w4,w11,w70,w83,w101,w132] z) [w1,w4,w11,w70,w85,w101,w132] (n z [w1,w4,w11,w70,w101,w112,w132] z)) [w1,w4,w11,w70,w101,w116,w132] (n (n z [w1,w4,w15,w27,w69,w101,w132] z) [w1,w4,w16,w27,w70,w101,w132] (n z [w1,w4,w16,w32,w69,w101,w132] z))) [w1,w4,w22,w27,w70,w98,w132] (n (n (n z [w1,w4,w23,w27,w70,w101,w132] z) [w1,w4,w23,w39,w70,w98,w132] (n z [w1,w4,w27,w45,w70,w101,w132] z)) [w1,w4,w27,w60,w70,w108,w127] (n (n z [w1,w4,w27,w60,w77,w101,w127] z) [w1,w4,w27,w70,w76,w101,w132] (n z [w1,w4,w27,w70,w78,w101,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabbab : ReplayTree.all (blocked 5 t5) t6aabbab = true := by
  decide +kernel
def t6aabba := (n t6aabbaa [w1,w4,w11,w60,w84,w101,w127] t6aabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabba : ReplayTree.all (blocked 5 t5) t6aabba = true := by
  simp only [t6aabba, ReplayTree.all, n, ht6aabbaa, ht6aabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbba := (n (n (n (n z [w1,w4,w27,w70,w101,w109,w132] z) [w1,w4,w42,w60,w70,w101,w127] (n z [w1,w4,w43,w60,w70,w101,w127] z)) [w1,w4,w44,w60,w70,w101,w127] (n (n z [w1,w4,w45,w60,w70,w101,w127] z) [w1,w4,w45,w60,w70,w101,w132] (n z [w1,w4,w45,w69,w70,w101,w132] z))) [w1,w4,w45,w70,w98,w101,w132] (n (n (n z [w1,w4,w45,w70,w101,w127,w132] z) [w1,w4,w45,w70,w101,w132] (n z [w1,w4,w50,w60,w70,w101,w127] z)) [w1,w4,w51,w60,w69,w101,w127] (n (n z [w1,w4,w52,w60,w70,w101,w127] z) [w1,w4,w57,w60,w70,w101,w127] (n z [w1,w4,w60,w65,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabbba : ReplayTree.all (blocked 5 t5) t6aabbba = true := by
  decide +kernel
def t6aabbbb := (n (n (n (n z [w1,w4,w60,w70,w92,w101,w127] z) [w1,w4,w60,w70,w94,w101,w127] (n z [w1,w4,w60,w70,w101,w121,w127] z)) [w1,w4,w60,w70,w101,w125,w127] (n (n z [w1,w4,w60,w70,w109,w116,w127] z) [w1,w4,w60,w78,w85,w101,w127] (n z [w1,w5,w7,w11,w69,w112,w132] z))) [w1,w5,w7,w11,w83,w98,w132] (n (n (n z [w1,w5,w7,w27,w69,w105,w132] z) [w1,w5,w7,w27,w76,w98,w132] (n z [w1,w5,w7,w45,w69,w98,w132] z)) [w1,w5,w7,w60,w69,w121,w127] (n (n z [w1,w5,w7,w60,w76,w112,w127] z) [w1,w5,w7,w60,w83,w105,w127] (n z [w1,w5,w7,w60,w92,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabbbb : ReplayTree.all (blocked 5 t5) t6aabbbb = true := by
  decide +kernel
def t6aabbb := (n t6aabbba [w1,w4,w60,w66,w70,w101,w127] t6aabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabbb : ReplayTree.all (blocked 5 t5) t6aabbb = true := by
  simp only [t6aabbb, ReplayTree.all, n, ht6aabbba, ht6aabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabb := (n t6aabba [w1,w4,w27,w70,w101,w105,w132] t6aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aabb : ReplayTree.all (blocked 5 t5) t6aabb = true := by
  simp only [t6aabb, ReplayTree.all, n, ht6aabba, ht6aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aab := (n t6aaba [w1,w4,w7,w60,w93,w98,w127] t6aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aab : ReplayTree.all (blocked 5 t5) t6aab = true := by
  simp only [t6aab, ReplayTree.all, n, ht6aaba, ht6aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aa := (n t6aaa [w1,w2,w7,w76,w112,w132,w136] t6aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aa : ReplayTree.all (blocked 5 t5) t6aa = true := by
  simp only [t6aa, ReplayTree.all, n, ht6aaa, ht6aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaaaa := (n (n (n (n z [w1,w5,w45,w60,w69,w101,w127] z) [w1,w6,w7,w11,w70,w112,w132] (n z [w1,w6,w7,w11,w85,w98,w132] z)) [w1,w6,w7,w16,w69,w112,w132] (n (n z [w1,w6,w7,w16,w83,w98,w132] z) [w1,w6,w7,w27,w70,w105,w132] (n z [w1,w6,w7,w27,w78,w98,w132] z))) [w1,w6,w7,w32,w69,w105,w132] (n (n (n z [w1,w6,w7,w32,w76,w98,w132] z) [w1,w6,w7,w45,w70,w98,w132] (n z [w1,w6,w7,w52,w69,w98,w132] z)) [w1,w6,w7,w60,w69,w118,w127] (n (n z [w1,w6,w7,w60,w70,w121,w127] z) [w1,w6,w7,w60,w76,w111,w127] (n z [w1,w6,w7,w60,w78,w112,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaaaa : ReplayTree.all (blocked 5 t5) t6abaaaa = true := by
  decide +kernel
def t6abaaab := (n (n (n (n z [w1,w6,w7,w60,w85,w105,w127] z) [w1,w6,w7,w60,w89,w98,w127] (n z [w1,w6,w7,w60,w90,w98,w127] z)) [w1,w6,w7,w60,w91,w98,w127] (n (n z [w1,w6,w7,w60,w92,w98,w127] z) [w1,w6,w7,w60,w92,w98,w132] (n z [w1,w6,w7,w60,w92,w101,w127] z))) [w1,w6,w7,w60,w94,w98,w127] (n (n (n z [w1,w6,w11,w27,w70,w101,w132] z) [w1,w6,w11,w32,w69,w101,w132] (n z [w1,w6,w11,w60,w69,w115,w127] z)) [w1,w6,w11,w60,w82,w101,w127] (n (n z [w1,w6,w16,w27,w69,w101,w132] z) [w1,w6,w22,w60,w83,w98,w127] (n z [w1,w6,w23,w60,w83,w101,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaaab : ReplayTree.all (blocked 5 t5) t6abaaab = true := by
  decide +kernel
def t6abaaa := (n t6abaaaa [w1,w6,w7,w60,w83,w104,w127] t6abaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaaa : ReplayTree.all (blocked 5 t5) t6abaaa = true := by
  simp only [t6abaaa, ReplayTree.all, n, ht6abaaaa, ht6abaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaaba := (n (n (n (n z [w1,w6,w27,w60,w75,w101,w127] z) [w1,w6,w38,w60,w76,w98,w127] (n z [w1,w6,w39,w60,w76,w101,w127] z)) [w1,w6,w42,w60,w69,w101,w127] (n (n z [w1,w6,w43,w60,w69,w101,w127] z) [w1,w6,w44,w60,w69,w101,w127] (n z [w1,w6,w45,w60,w69,w101,w127] z))) [w1,w6,w45,w60,w69,w101,w131] (n (n (n z [w1,w6,w45,w60,w69,w101,w132] z) [w1,w6,w45,w60,w70,w101,w127] (n z [w1,w6,w50,w60,w69,w101,w127] z)) [w1,w6,w52,w60,w69,w101,w127] (n (n z [w1,w6,w57,w60,w69,w101,w127] z) [w1,w6,w59,w60,w69,w101,w127] (n z [w1,w6,w60,w65,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaaba : ReplayTree.all (blocked 5 t5) t6abaaba = true := by
  decide +kernel
def t6abaabb := (n (n (n (n z [w1,w6,w60,w69,w92,w101,w127] z) [w1,w6,w60,w69,w101,w121,w127] (n z [w1,w6,w60,w69,w101,w125,w127] z)) [w1,w6,w60,w69,w109,w116,w127] (n (n z [w1,w6,w60,w76,w83,w101,w127] z) [w1,w7,w11,w27,w70,w98,w135] (n z [w1,w7,w11,w27,w73,w98,w132] z))) [w1,w7,w11,w33,w70,w98,w132] (n (n (n z [w1,w7,w11,w74,w85,w98,w132] z) [w1,w7,w17,w27,w70,w98,w132] (n z [w1,w7,w19,w45,w70,w98,w132] z)) [w1,w7,w19,w60,w70,w111,w127] (n (n z [w1,w7,w19,w60,w84,w98,w127] z) [w1,w7,w20,w60,w83,w98,w127] (n z [w1,w7,w21,w60,w70,w112,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaabb : ReplayTree.all (blocked 5 t5) t6abaabb = true := by
  decide +kernel
def t6abaab := (n t6abaaba [w1,w6,w60,w66,w69,w101,w127] t6abaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaab : ReplayTree.all (blocked 5 t5) t6abaab = true := by
  simp only [t6abaab, ReplayTree.all, n, ht6abaaba, ht6abaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaa := (n t6abaaa [w1,w6,w27,w60,w69,w108,w127] t6abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abaa : ReplayTree.all (blocked 5 t5) t6abaa = true := by
  simp only [t6abaa, ReplayTree.all, n, ht6abaaa, ht6abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababaa := (n (n (n (n z [w1,w7,w27,w74,w78,w98,w132] z) [w1,w7,w35,w45,w70,w98,w132] (n z [w1,w7,w35,w60,w70,w104,w127] z)) [w1,w7,w35,w60,w77,w98,w127] (n (n z [w1,w7,w36,w60,w76,w98,w127] z) [w1,w7,w37,w60,w70,w105,w127] (n z [w1,w7,w37,w60,w78,w98,w127] z))) [w1,w7,w45,w57,w70,w98,w132] (n (n (n z [w1,w7,w45,w60,w70,w98,w130] z) [w1,w7,w45,w60,w73,w98,w127] (n z [w1,w7,w45,w63,w70,w98,w127] z)) [w1,w7,w45,w64,w70,w98,w132] (n (n z [w1,w7,w45,w70,w72,w98,w132] z) [w1,w7,w45,w70,w74,w98,w132] (n z [w1,w7,w45,w70,w98,w131,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ababaa : ReplayTree.all (blocked 5 t5) t6ababaa = true := by
  decide +kernel
def t6ababab := (n (n (n (n z [w1,w7,w51,w60,w69,w98,w131] z) [w1,w7,w53,w60,w70,w98,w127] (n z [w1,w7,w54,w60,w70,w98,w127] z)) [w1,w7,w55,w60,w70,w98,w127] (n (n z [w1,w7,w56,w60,w70,w98,w127] z) [w1,w7,w57,w60,w70,w98,w127] (n z [w1,w7,w57,w60,w70,w98,w129] z))) [w1,w7,w57,w60,w70,w98,w132] (n (n (n z [w1,w7,w57,w60,w70,w101,w127] z) [w1,w7,w58,w60,w69,w98,w127] (n z [w1,w7,w59,w60,w70,w98,w127] z)) [w1,w7,w60,w70,w92,w98,w131] (n (n z [w1,w7,w60,w70,w96,w98,w127] z) [w1,w7,w60,w70,w97,w98,w127] (n z [w1,w7,w60,w74,w92,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ababab : ReplayTree.all (blocked 5 t5) t6ababab = true := by
  decide +kernel
def t6ababa := (n t6ababaa [w1,w7,w45,w70,w98,w132,w136] t6ababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ababa : ReplayTree.all (blocked 5 t5) t6ababa = true := by
  simp only [t6ababa, ReplayTree.all, n, ht6ababaa, ht6ababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababba := (n (n (n (n z [w1,w7,w60,w78,w88,w98,w127] z) [w1,w7,w60,w81,w85,w98,w127] (n z [w1,w11,w27,w60,w70,w101,w130] z)) [w1,w11,w27,w60,w73,w101,w127] (n (n z [w1,w11,w27,w63,w70,w101,w127] z) [w1,w11,w27,w64,w70,w101,w132] (n z [w1,w11,w27,w70,w72,w101,w132] z))) [w1,w11,w27,w70,w74,w101,w132] (n (n (n z [w1,w11,w27,w70,w101,w131,w132] z) [w1,w11,w27,w70,w101,w132,w136] (n z [w1,w11,w31,w60,w69,w101,w131] z)) [w1,w11,w34,w60,w70,w101,w127] (n (n z [w1,w11,w36,w60,w69,w101,w127] z) [w1,w11,w60,w70,w83,w101,w131] (n z [w1,w11,w60,w74,w83,w101,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ababba : ReplayTree.all (blocked 5 t5) t6ababba = true := by
  decide +kernel
def t6ababbb := (n (n (n (n z [w1,w15,w27,w60,w69,w101,w131] z) [w1,w16,w32,w60,w69,w101,w131] (n z [w1,w18,w27,w60,w70,w101,w127] z)) [w1,w19,w35,w60,w70,w101,w127] (n (n z [w1,w19,w38,w60,w70,w98,w127] z) [w1,w19,w39,w60,w70,w101,w127] (n z [w1,w20,w27,w60,w69,w101,w127] z))) [w1,w21,w37,w60,w69,w101,w127] (n (n (n z [w1,w22,w35,w60,w70,w98,w127] z) [w1,w23,w35,w60,w70,w101,w127] (n z [w1,w27,w60,w70,w76,w101,w131] z)) [w1,w27,w60,w74,w76,w101,w127] (n (n z [w1,w27,w60,w74,w78,w101,w127] z) [w1,w45,w60,w64,w70,w101,w127] (n z [w1,w45,w60,w69,w70,w101,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ababbb : ReplayTree.all (blocked 5 t5) t6ababbb = true := by
  decide +kernel
def t6ababb := (n t6ababba [w1,w11,w60,w74,w85,w101,w127] t6ababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ababb : ReplayTree.all (blocked 5 t5) t6ababb = true := by
  simp only [t6ababb, ReplayTree.all, n, ht6ababba, ht6ababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abab := (n t6ababa [w1,w7,w60,w74,w94,w98,w127] t6ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abab : ReplayTree.all (blocked 5 t5) t6abab = true := by
  simp only [t6abab, ReplayTree.all, n, ht6ababa, ht6ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aba := (n t6abaa [w1,w7,w21,w60,w85,w98,w127] t6abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6aba : ReplayTree.all (blocked 5 t5) t6aba = true := by
  simp only [t6aba, ReplayTree.all, n, ht6abaa, ht6abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbaaa := (n (n (n (n z [w1,w45,w60,w70,w72,w101,w127] z) [w1,w45,w60,w70,w74,w101,w127] (n z [w1,w45,w60,w70,w101,w127,w131] z)) [w2,w3,w9,w60,w69,w121,w127] (n (n z [w2,w3,w50,w60,w69,w101,w127] z) [w2,w4,w7,w9,w69,w121,w132] (n z [w2,w4,w7,w9,w76,w112,w132] z))) [w2,w4,w7,w9,w83,w105,w132] (n (n (n z [w2,w4,w7,w9,w92,w98,w132] z) [w2,w4,w7,w11,w69,w112,w133] (n z [w2,w4,w7,w11,w69,w113,w132] z)) [w2,w4,w7,w11,w83,w98,w133] (n (n z [w2,w4,w7,w11,w83,w99,w132] z) [w2,w4,w7,w12,w69,w112,w132] (n z [w2,w4,w7,w12,w83,w98,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbaaa : ReplayTree.all (blocked 5 t5) t6abbaaa = true := by
  decide +kernel
def t6abbaab := (n (n (n (n z [w2,w4,w7,w14,w76,w112,w132] z) [w2,w4,w7,w14,w83,w105,w132] (n z [w2,w4,w7,w14,w92,w98,w132] z)) [w2,w4,w7,w27,w69,w105,w133] (n (n z [w2,w4,w7,w27,w69,w106,w132] z) [w2,w4,w7,w27,w76,w98,w133] (n z [w2,w4,w7,w27,w76,w99,w132] z))) [w2,w4,w7,w28,w69,w105,w132] (n (n (n z [w2,w4,w7,w28,w76,w98,w132] z) [w2,w4,w7,w30,w69,w121,w132] (n z [w2,w4,w7,w30,w76,w112,w132] z)) [w2,w4,w7,w30,w83,w105,w132] (n (n z [w2,w4,w7,w30,w92,w98,w132] z) [w2,w4,w7,w45,w69,w98,w133] (n z [w2,w4,w7,w45,w69,w99,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbaab : ReplayTree.all (blocked 5 t5) t6abbaab = true := by
  decide +kernel
def t6abbaa := (n t6abbaaa [w2,w4,w7,w14,w69,w121,w132] t6abbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbaa : ReplayTree.all (blocked 5 t5) t6abbaa = true := by
  simp only [t6abbaa, ReplayTree.all, n, ht6abbaaa, ht6abbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbaba := (n (n (n (n z [w2,w4,w7,w50,w69,w121,w132] z) [w2,w4,w7,w50,w92,w98,w132] (n z [w2,w4,w7,w60,w69,w118,w129] z)) [w2,w4,w7,w60,w69,w121,w128] (n (n z [w2,w4,w7,w60,w69,w122,w127] z) [w2,w4,w7,w60,w76,w112,w128] (n z [w2,w4,w7,w60,w76,w113,w127] z))) [w2,w4,w7,w60,w83,w105,w128] (n (n (n z [w2,w4,w7,w60,w83,w106,w127] z) [w2,w4,w7,w60,w89,w98,w129] (n z [w2,w4,w7,w60,w92,w98,w128] z)) [w2,w4,w7,w60,w92,w99,w127] (n (n z [w2,w4,w7,w61,w69,w121,w127] z) [w2,w4,w7,w61,w76,w112,w127] (n z [w2,w4,w7,w61,w83,w105,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbaba : ReplayTree.all (blocked 5 t5) t6abbaba = true := by
  decide +kernel
def t6abbabb := (n (n (n (n z [w2,w4,w7,w62,w69,w121,w132] z) [w2,w4,w7,w62,w76,w112,w132] (n z [w2,w4,w7,w62,w83,w105,w132] z)) [w2,w4,w7,w62,w92,w98,w132] (n (n z [w2,w4,w7,w69,w100,w121,w132] z) [w2,w4,w7,w69,w107,w121,w132] (n z [w2,w4,w7,w69,w114,w121,w132] z))) [w2,w4,w7,w69,w121,w123,w132] (n (n (n z [w2,w4,w7,w69,w121,w129,w132] z) [w2,w4,w7,w69,w121,w132,w134] (n z [w2,w4,w7,w76,w100,w112,w132] z)) [w2,w4,w7,w76,w112,w114,w132] (n (n z [w2,w4,w7,w76,w112,w129,w132] z) [w2,w4,w7,w76,w112,w132,w134] (n z [w2,w4,w7,w83,w100,w105,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbabb : ReplayTree.all (blocked 5 t5) t6abbabb = true := by
  decide +kernel
def t6abbab := (n t6abbaba [w2,w4,w7,w61,w92,w98,w127] t6abbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbab : ReplayTree.all (blocked 5 t5) t6abbab = true := by
  simp only [t6abbab, ReplayTree.all, n, ht6abbaba, ht6abbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abba := (n t6abbaa [w2,w4,w7,w46,w69,w98,w132] t6abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abba : ReplayTree.all (blocked 5 t5) t6abba = true := by
  simp only [t6abba, ReplayTree.all, n, ht6abbaa, ht6abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbaa := (n (n (n (n z [w2,w4,w7,w83,w105,w129,w132] z) [w2,w4,w7,w83,w105,w132,w134] (n z [w2,w4,w7,w92,w98,w100,w132] z)) [w2,w4,w7,w92,w98,w129,w132] (n (n z [w2,w4,w7,w92,w98,w132,w134] z) [w2,w4,w8,w11,w69,w112,w132] (n z [w2,w4,w8,w11,w83,w98,w132] z))) [w2,w4,w8,w27,w69,w105,w132] (n (n (n z [w2,w4,w8,w27,w76,w98,w132] z) [w2,w4,w8,w45,w69,w98,w132] (n z [w2,w4,w8,w60,w69,w121,w127] z)) [w2,w4,w8,w60,w76,w112,w127] (n (n z [w2,w4,w8,w60,w83,w105,w127] z) [w2,w4,w8,w60,w92,w98,w127] (n z [w2,w4,w9,w11,w69,w116,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbbaa : ReplayTree.all (blocked 5 t5) t6abbbaa = true := by
  decide +kernel
def t6abbbab := (n (n (n (n z [w2,w4,w9,w23,w69,w112,w132] z) [w2,w4,w9,w23,w83,w98,w132] (n z [w2,w4,w9,w27,w69,w109,w132] z)) [w2,w4,w9,w27,w76,w101,w132] (n (n z [w2,w4,w9,w39,w69,w105,w132] z) [w2,w4,w9,w39,w76,w98,w132] (n z [w2,w4,w9,w45,w69,w101,w132] z))) [w2,w4,w9,w60,w69,w118,w127] (n (n (n z [w2,w4,w9,w60,w69,w119,w127] z) [w2,w4,w9,w60,w69,w120,w127] (n z [w2,w4,w9,w60,w69,w121,w127] z)) [w2,w4,w9,w60,w69,w121,w132] (n (n z [w2,w4,w9,w60,w69,w125,w127] z) [w2,w4,w9,w60,w70,w121,w127] (n z [w2,w4,w9,w60,w75,w112,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbbab : ReplayTree.all (blocked 5 t5) t6abbbab = true := by
  decide +kernel
def t6abbba := (n t6abbbaa [w2,w4,w9,w11,w83,w101,w132] t6abbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbba : ReplayTree.all (blocked 5 t5) t6abbba = true := by
  simp only [t6abbba, ReplayTree.all, n, ht6abbbaa, ht6abbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbba := (n (n (n (n z [w2,w4,w9,w60,w82,w105,w127] z) [w2,w4,w9,w60,w83,w109,w127] (n z [w2,w4,w9,w60,w89,w98,w127] z)) [w2,w4,w9,w60,w92,w101,w127] (n (n z [w2,w4,w9,w66,w69,w98,w132] z) [w2,w4,w11,w27,w69,w101,w133] (n z [w2,w4,w11,w27,w69,w102,w132] z))) [w2,w4,w11,w28,w69,w101,w132] (n (n (n z [w2,w4,w11,w69,w103,w116,w132] z) [w2,w4,w12,w27,w69,w101,w132] (n z [w2,w4,w14,w45,w69,w101,w132] z)) [w2,w4,w14,w60,w69,w115,w127] (n (n z [w2,w4,w14,w60,w82,w101,w127] z) [w2,w4,w24,w60,w69,w112,w127] (n z [w2,w4,w25,w60,w69,w116,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbbba : ReplayTree.all (blocked 5 t5) t6abbbba = true := by
  decide +kernel
def t6abbbbb := (n (n (n (n z [w2,w4,w27,w69,w103,w109,w132] z) [w2,w4,w30,w45,w69,w101,w132] (n z [w2,w4,w30,w60,w69,w108,w127] z)) [w2,w4,w30,w60,w75,w101,w127] (n (n z [w2,w4,w40,w60,w69,w105,w127] z) [w2,w4,w41,w60,w69,w109,w127] (n z [w2,w4,w41,w60,w76,w101,w127] z))) [w2,w4,w45,w50,w69,w101,w132] (n (n (n z [w2,w4,w45,w60,w69,w101,w128] z) [w2,w4,w45,w60,w69,w102,w127] (n z [w2,w4,w45,w61,w69,w101,w127] z)) [w2,w4,w45,w62,w69,w101,w132] (n (n z [w2,w4,w45,w69,w100,w101,w132] z) [w2,w4,w45,w69,w101,w103,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbbbb : ReplayTree.all (blocked 5 t5) t6abbbbb = true := by
  decide +kernel
def t6abbbb := (n t6abbbba [w2,w4,w25,w60,w83,w101,w127] t6abbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbbb : ReplayTree.all (blocked 5 t5) t6abbbb = true := by
  simp only [t6abbbb, ReplayTree.all, n, ht6abbbba, ht6abbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbb := (n t6abbba [w2,w4,w9,w60,w76,w116,w127] t6abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abbb : ReplayTree.all (blocked 5 t5) t6abbb = true := by
  simp only [t6abbb, ReplayTree.all, n, ht6abbba, ht6abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abb := (n t6abba [w2,w4,w7,w83,w105,w107,w132] t6abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6abb : ReplayTree.all (blocked 5 t5) t6abb = true := by
  simp only [t6abb, ReplayTree.all, n, ht6abba, ht6abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ab := (n t6aba [w1,w45,w60,w69,w74,w101,w127] t6abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ab : ReplayTree.all (blocked 5 t5) t6ab = true := by
  simp only [t6ab, ReplayTree.all, n, ht6aba, ht6abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6a := (n t6aa [w1,w5,w11,w27,w69,w101,w132] t6ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6a : ReplayTree.all (blocked 5 t5) t6a = true := by
  simp only [t6a, ReplayTree.all, n, ht6aa, ht6ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaaaa := (n (n (n (n z [w2,w4,w45,w69,w101,w132,w134] z) [w2,w4,w46,w60,w69,w101,w127] (n z [w2,w4,w47,w60,w69,w101,w127] z)) [w2,w4,w48,w60,w69,w101,w127] (n (n z [w2,w4,w49,w60,w69,w101,w127] z) [w2,w4,w50,w60,w69,w101,w127] (n z [w2,w4,w50,w60,w69,w101,w131] z))) [w2,w4,w50,w60,w69,w101,w132] (n (n (n z [w2,w4,w50,w60,w70,w101,w127] z) [w2,w4,w60,w65,w69,w98,w129] (n z [w2,w4,w60,w67,w69,w98,w127] z)) [w2,w4,w60,w68,w69,w101,w127] (n (n z [w2,w4,w60,w69,w101,w121,w129] z) [w2,w4,w60,w69,w101,w123,w127] (n z [w2,w4,w60,w69,w101,w126,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaaaa : ReplayTree.all (blocked 5 t5) t6baaaaa = true := by
  decide +kernel
def t6baaaab := (n (n (n (n z [w2,w4,w60,w69,w103,w125,w127] z) [w2,w4,w60,w69,w109,w117,w127] (n z [w2,w4,w60,w69,w110,w116,w127] z)) [w2,w6,w9,w60,w69,w121,w127] (n (n z [w2,w6,w50,w60,w69,w101,w127] z) [w2,w7,w11,w69,w112,w134,w136] (n z [w2,w7,w11,w83,w98,w134,w136] z))) [w2,w7,w14,w19,w69,w112,w132] (n (n (n z [w2,w7,w14,w19,w83,w98,w132] z) [w2,w7,w14,w60,w69,w111,w131] (n z [w2,w7,w14,w60,w69,w112,w130] z)) [w2,w7,w14,w60,w71,w112,w127] (n (n z [w2,w7,w14,w60,w82,w98,w131] z) [w2,w7,w14,w60,w83,w98,w130] (n z [w2,w7,w14,w60,w86,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaaab : ReplayTree.all (blocked 5 t5) t6baaaab = true := by
  decide +kernel
def t6baaaa := (n t6baaaaa [w2,w4,w60,w69,w103,w121,w127] t6baaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaaa : ReplayTree.all (blocked 5 t5) t6baaaa = true := by
  simp only [t6baaaa, ReplayTree.all, n, ht6baaaaa, ht6baaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaaba := (n (n (n (n z [w2,w7,w14,w63,w83,w98,w127] z) [w2,w7,w14,w64,w69,w112,w132] (n z [w2,w7,w14,w64,w83,w98,w132] z)) [w2,w7,w19,w60,w69,w111,w129] (n (n z [w2,w7,w19,w60,w69,w112,w128] z) [w2,w7,w19,w60,w69,w113,w127] (n z [w2,w7,w19,w60,w82,w98,w129] z))) [w2,w7,w19,w60,w83,w98,w128] (n (n (n z [w2,w7,w19,w60,w83,w99,w127] z) [w2,w7,w19,w61,w69,w112,w127] (n z [w2,w7,w19,w61,w83,w98,w127] z)) [w2,w7,w19,w62,w69,w112,w132] (n (n z [w2,w7,w19,w62,w83,w98,w132] z) [w2,w7,w27,w69,w105,w134,w136] (n z [w2,w7,w27,w76,w98,w134,w136] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaaba : ReplayTree.all (blocked 5 t5) t6baaaba = true := by
  decide +kernel
def t6baaabb := (n (n (n (n z [w2,w7,w30,w35,w76,w98,w132] z) [w2,w7,w30,w60,w69,w104,w131] (n z [w2,w7,w30,w60,w69,w105,w130] z)) [w2,w7,w30,w60,w71,w105,w127] (n (n z [w2,w7,w30,w60,w75,w98,w131] z) [w2,w7,w30,w60,w76,w98,w130] (n z [w2,w7,w30,w60,w79,w98,w127] z))) [w2,w7,w30,w63,w69,w105,w127] (n (n (n z [w2,w7,w30,w63,w76,w98,w127] z) [w2,w7,w30,w64,w69,w105,w132] (n z [w2,w7,w30,w64,w76,w98,w132] z)) [w2,w7,w35,w60,w69,w104,w129] (n (n z [w2,w7,w35,w60,w69,w105,w128] z) [w2,w7,w35,w60,w69,w106,w127] (n z [w2,w7,w35,w60,w75,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaabb : ReplayTree.all (blocked 5 t5) t6baaabb = true := by
  decide +kernel
def t6baaab := (n t6baaaba [w2,w7,w30,w35,w69,w105,w132] t6baaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaab : ReplayTree.all (blocked 5 t5) t6baaab = true := by
  simp only [t6baaab, ReplayTree.all, n, ht6baaaba, ht6baaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaa := (n t6baaaa [w2,w7,w14,w63,w69,w112,w127] t6baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaa : ReplayTree.all (blocked 5 t5) t6baaa = true := by
  simp only [t6baaa, ReplayTree.all, n, ht6baaaa, ht6baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baabaa := (n (n (n (n z [w2,w7,w35,w60,w76,w99,w127] z) [w2,w7,w35,w61,w69,w105,w127] (n z [w2,w7,w35,w61,w76,w98,w127] z)) [w2,w7,w35,w62,w69,w105,w132] (n (n z [w2,w7,w35,w62,w76,w98,w132] z) [w2,w7,w45,w60,w69,w99,w131] (n z [w2,w7,w45,w60,w71,w98,w129] z))) [w2,w7,w45,w61,w69,w98,w131] (n (n (n z [w2,w7,w45,w62,w69,w98,w136] z) [w2,w7,w45,w63,w69,w98,w129] (n z [w2,w7,w45,w64,w69,w98,w134] z)) [w2,w7,w45,w69,w98,w134,w136] (n (n z [w2,w7,w46,w60,w69,w98,w131] z) [w2,w7,w47,w60,w69,w98,w131] (n z [w2,w7,w48,w60,w69,w98,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baabaa : ReplayTree.all (blocked 5 t5) t6baabaa = true := by
  decide +kernel
def t6baabab := (n (n (n (n z [w2,w7,w50,w57,w69,w98,w132] z) [w2,w7,w50,w60,w69,w98,w130] (n z [w2,w7,w50,w60,w69,w98,w131] z)) [w2,w7,w50,w60,w69,w98,w136] (n (n z [w2,w7,w50,w60,w69,w101,w131] z) [w2,w7,w50,w60,w71,w98,w127] (n z [w2,w7,w50,w63,w69,w98,w127] z))) [w2,w7,w50,w64,w69,w98,w132] (n (n (n z [w2,w7,w53,w60,w69,w98,w129] z) [w2,w7,w54,w60,w69,w98,w129] (n z [w2,w7,w55,w60,w69,w98,w129] z)) [w2,w7,w56,w60,w69,w98,w129] (n (n z [w2,w7,w57,w60,w69,w98,w128] z) [w2,w7,w57,w60,w69,w98,w129] (n z [w2,w7,w57,w60,w69,w98,w134] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baabab : ReplayTree.all (blocked 5 t5) t6baabab = true := by
  decide +kernel
def t6baaba := (n t6baabaa [w2,w7,w49,w60,w69,w98,w131] t6baabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baaba : ReplayTree.all (blocked 5 t5) t6baaba = true := by
  simp only [t6baaba, ReplayTree.all, n, ht6baabaa, ht6baabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baabba := (n (n (n (n z [w2,w7,w57,w60,w70,w98,w129] z) [w2,w7,w57,w61,w69,w98,w127] (n z [w2,w7,w57,w62,w69,w98,w132] z)) [w2,w7,w59,w60,w69,w98,w129] (n (n z [w2,w7,w60,w68,w69,w98,w131] z) [w2,w7,w60,w69,w96,w98,w129] (n z [w2,w7,w60,w69,w98,w123,w131] z))) [w2,w7,w60,w69,w100,w121,w131] (n (n (n z [w2,w7,w60,w69,w105,w114,w131] z) [w2,w7,w60,w69,w107,w112,w131] (n z [w2,w7,w60,w69,w121,w129,w131] z)) [w2,w7,w60,w72,w92,w98,w129] (n (n z [w2,w7,w60,w76,w87,w98,w129] z) [w2,w7,w60,w76,w112,w129,w131] (n z [w2,w7,w60,w80,w83,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baabba : ReplayTree.all (blocked 5 t5) t6baabba = true := by
  decide +kernel
def t6baabbb := (n (n (n (n z [w2,w7,w60,w92,w98,w129,w131] z) [w2,w7,w62,w64,w69,w121,w127] (n z [w2,w7,w62,w64,w76,w112,w127] z)) [w2,w7,w62,w64,w83,w105,w127] (n (n z [w2,w7,w62,w64,w92,w98,w127] z) [w2,w8,w19,w60,w69,w112,w127] (n z [w2,w8,w19,w60,w83,w98,w127] z))) [w2,w8,w35,w60,w69,w105,w127] (n (n (n z [w2,w8,w35,w60,w76,w98,w127] z) [w2,w8,w45,w60,w69,w98,w131] (n z [w2,w8,w57,w60,w69,w98,w127] z)) [w2,w9,w11,w60,w71,w112,w127] (n (n z [w2,w9,w11,w63,w69,w112,w127] z) [w2,w9,w11,w64,w69,w112,w132] (n z [w2,w9,w18,w60,w69,w112,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baabbb : ReplayTree.all (blocked 5 t5) t6baabbb = true := by
  decide +kernel
def t6baabb := (n t6baabba [w2,w7,w60,w83,w105,w129,w131] t6baabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baabb : ReplayTree.all (blocked 5 t5) t6baabb = true := by
  simp only [t6baabb, ReplayTree.all, n, ht6baabba, ht6baabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baab := (n t6baaba [w2,w7,w57,w60,w69,w99,w127] t6baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baab : ReplayTree.all (blocked 5 t5) t6baab = true := by
  simp only [t6baab, ReplayTree.all, n, ht6baaba, ht6baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baa := (n t6baaa [w2,w7,w35,w60,w76,w98,w128] t6baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baa : ReplayTree.all (blocked 5 t5) t6baa = true := by
  simp only [t6baa, ReplayTree.all, n, ht6baaa, ht6baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babaaa := (n (n (n (n z [w2,w9,w19,w60,w83,w101,w127] z) [w2,w9,w27,w60,w71,w105,w127] (n z [w2,w9,w27,w63,w69,w105,w127] z)) [w2,w9,w27,w64,w69,w105,w132] (n (n z [w2,w9,w34,w60,w69,w105,w127] z) [w2,w9,w35,w60,w69,w109,w127] (n z [w2,w9,w35,w60,w76,w101,w127] z))) [w2,w9,w45,w60,w69,w101,w131] (n (n (n z [w2,w9,w45,w60,w71,w98,w127] z) [w2,w9,w45,w63,w69,w98,w127] (n z [w2,w9,w45,w64,w69,w98,w132] z)) [w2,w9,w54,w60,w69,w98,w127] (n (n z [w2,w9,w57,w60,w69,w98,w131] z) [w2,w9,w57,w60,w69,w101,w127] (n z [w2,w9,w60,w64,w69,w121,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babaaa : ReplayTree.all (blocked 5 t5) t6babaaa = true := by
  decide +kernel
def t6babaab := (n (n (n (n z [w2,w9,w60,w69,w72,w121,w127] z) [w2,w9,w60,w72,w76,w112,w127] (n z [w2,w9,w60,w72,w83,w105,w127] z)) [w2,w9,w60,w72,w92,w98,w127] (n (n z [w2,w10,w30,w60,w69,w101,w131] z) [w2,w11,w27,w60,w69,w102,w131] (n z [w2,w11,w27,w61,w69,w101,w131] z))) [w2,w11,w27,w62,w69,w101,w136] (n (n (n z [w2,w11,w27,w69,w101,w134,w136] z) [w2,w11,w28,w60,w69,w101,w131] (n z [w2,w11,w29,w60,w69,w101,w131] z)) [w2,w11,w30,w60,w69,w101,w130] (n (n z [w2,w11,w30,w60,w69,w101,w131] z) [w2,w11,w30,w60,w69,w101,w136] (n z [w2,w11,w30,w60,w71,w101,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babaab : ReplayTree.all (blocked 5 t5) t6babaab = true := by
  decide +kernel
def t6babaa := (n t6babaaa [w2,w9,w60,w66,w69,w98,w131] t6babaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babaa : ReplayTree.all (blocked 5 t5) t6babaa = true := by
  simp only [t6babaa, ReplayTree.all, n, ht6babaaa, ht6babaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bababa := (n (n (n (n z [w2,w11,w30,w64,w69,w101,w132] z) [w2,w11,w41,w60,w69,w101,w131] (n z [w2,w11,w50,w60,w69,w101,w131] z)) [w2,w11,w60,w69,w101,w114,w131] (n (n z [w2,w11,w60,w69,w101,w117,w131] z) [w2,w11,w60,w69,w103,w116,w131] (n z [w2,w12,w27,w60,w69,w101,w131] z))) [w2,w13,w27,w60,w69,w101,w131] (n (n (n z [w2,w14,w26,w60,w69,w101,w131] z) [w2,w14,w27,w60,w69,w101,w130] (n z [w2,w14,w27,w60,w69,w101,w131] z)) [w2,w14,w27,w60,w69,w101,w136] (n (n z [w2,w14,w27,w60,w71,w101,w127] z) [w2,w14,w27,w63,w69,w101,w127] (n z [w2,w14,w27,w64,w69,w101,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bababa : ReplayTree.all (blocked 5 t5) t6bababa = true := by
  decide +kernel
def t6bababb := (n (n (n (n z [w2,w14,w32,w60,w69,w101,w131] z) [w2,w14,w34,w60,w69,w101,w127] (n z [w2,w14,w35,w60,w69,w101,w131] z)) [w2,w14,w38,w60,w69,w98,w131] (n (n z [w2,w14,w39,w60,w69,w101,w131] z) [w2,w14,w45,w60,w69,w101,w131] (n z [w2,w14,w50,w60,w69,w101,w131] z))) [w2,w14,w60,w69,w83,w101,w131] (n (n (n z [w2,w14,w60,w69,w101,w112,w131] z) [w2,w14,w60,w69,w101,w116,w131] (n z [w2,w14,w60,w72,w83,w101,w127] z)) [w2,w16,w30,w60,w69,w101,w131] (n (n z [w2,w18,w30,w60,w69,w101,w127] z) [w2,w19,w30,w60,w69,w101,w131] (n z [w2,w19,w38,w60,w69,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bababb : ReplayTree.all (blocked 5 t5) t6bababb = true := by
  decide +kernel
def t6babab := (n t6bababa [w2,w14,w30,w60,w69,w101,w131] t6bababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babab : ReplayTree.all (blocked 5 t5) t6babab = true := by
  simp only [t6babab, ReplayTree.all, n, ht6bababa, ht6bababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baba := (n t6babaa [w2,w11,w30,w63,w69,w101,w127] t6babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6baba : ReplayTree.all (blocked 5 t5) t6baba = true := by
  simp only [t6baba, ReplayTree.all, n, ht6babaa, ht6babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbaa := (n (n (n (n z [w2,w22,w30,w60,w69,w98,w131] z) [w2,w22,w35,w60,w69,w98,w129] (n z [w2,w23,w30,w60,w69,w101,w131] z)) [w2,w23,w41,w60,w69,w98,w131] (n (n z [w2,w25,w27,w60,w69,w101,w131] z) [w2,w25,w35,w60,w69,w101,w127] (n z [w2,w25,w39,w60,w69,w98,w131] z))) [w2,w27,w50,w60,w69,w101,w131] (n (n (n z [w2,w27,w60,w69,w101,w107,w131] z) [w2,w27,w60,w69,w101,w110,w131] (n z [w2,w27,w60,w69,w103,w109,w131] z)) [w2,w30,w45,w60,w69,w101,w131] (n (n z [w2,w30,w50,w60,w69,w101,w131] z) [w2,w30,w60,w69,w76,w101,w131] (n z [w2,w30,w60,w69,w101,w105,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babbaa : ReplayTree.all (blocked 5 t5) t6babbaa = true := by
  decide +kernel
def t6babbab := (n (n (n (n z [w2,w30,w60,w72,w76,w101,w127] z) [w2,w45,w50,w60,w69,w101,w131] (n z [w2,w45,w60,w62,w69,w101,w131] z)) [w2,w45,w60,w69,w100,w101,w131] (n (n z [w2,w45,w60,w69,w101,w103,w131] z) [w2,w45,w60,w69,w101,w129,w131] (n z [w2,w45,w62,w64,w69,w101,w127] z))) [w2,w50,w60,w64,w69,w101,w127] (n (n (n z [w2,w50,w60,w69,w72,w101,w127] z) [w2,w50,w60,w69,w98,w101,w131] (n z [w2,w50,w60,w69,w101,w127,w131] z)) [w2,w50,w60,w69,w101,w131] (n (n z [w3,w7,w45,w60,w70,w98,w129] z) [w3,w9,w45,w60,w70,w98,w127] (n z [w4,w7,w9,w45,w70,w98,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babbab : ReplayTree.all (blocked 5 t5) t6babbab = true := by
  decide +kernel
def t6babba := (n t6babbaa [w2,w30,w60,w69,w101,w109,w131] t6babbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babba : ReplayTree.all (blocked 5 t5) t6babba = true := by
  simp only [t6babba, ReplayTree.all, n, ht6babbaa, ht6babbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbba := (n (n (n (n z [w4,w7,w11,w27,w70,w99,w132] z) [w4,w7,w11,w60,w70,w111,w129] (n z [w4,w7,w11,w60,w84,w98,w129] z)) [w4,w7,w11,w70,w100,w112,w132] (n (n z [w4,w7,w27,w60,w70,w104,w129] z) [w4,w7,w27,w60,w77,w98,w129] (n z [w4,w7,w27,w70,w100,w105,w132] z))) [w4,w7,w42,w60,w70,w98,w129] (n (n (n z [w4,w7,w43,w60,w70,w98,w129] z) [w4,w7,w44,w60,w70,w98,w129] (n z [w4,w7,w45,w60,w70,w98,w128] z)) [w4,w7,w45,w60,w70,w98,w129] (n (n z [w4,w7,w45,w60,w70,w98,w134] z) [w4,w7,w45,w60,w70,w99,w127] (n z [w4,w7,w45,w61,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babbba : ReplayTree.all (blocked 5 t5) t6babbba = true := by
  decide +kernel
def t6babbbb := (n (n (n (n z [w4,w7,w45,w70,w98,w100,w132] z) [w4,w7,w45,w70,w98,w129,w132] (n z [w4,w7,w45,w70,w98,w132,w134] z)) [w4,w7,w47,w60,w70,w98,w127] (n (n z [w4,w7,w50,w60,w70,w98,w129] z) [w4,w7,w51,w60,w69,w98,w129] (n z [w4,w7,w52,w60,w70,w98,w129] z))) [w4,w7,w57,w60,w70,w98,w129] (n (n (n z [w4,w7,w60,w66,w70,w98,w129] z) [w4,w7,w60,w70,w92,w98,w129] (n z [w4,w7,w60,w70,w94,w98,w129] z)) [w4,w7,w60,w70,w98,w121,w129] (n (n z [w4,w7,w60,w70,w100,w121,w127] z) [w4,w7,w60,w70,w105,w112,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babbbb : ReplayTree.all (blocked 5 t5) t6babbbb = true := by
  decide +kernel
def t6babbb := (n t6babbba [w4,w7,w45,w62,w70,w98,w132] t6babbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babbb : ReplayTree.all (blocked 5 t5) t6babbb = true := by
  simp only [t6babbb, ReplayTree.all, n, ht6babbba, ht6babbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babb := (n t6babba [w4,w7,w11,w27,w70,w98,w133] t6babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6babb : ReplayTree.all (blocked 5 t5) t6babb = true := by
  simp only [t6babb, ReplayTree.all, n, ht6babba, ht6babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bab := (n t6baba [w2,w19,w41,w60,w69,w101,w127] t6babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bab : ReplayTree.all (blocked 5 t5) t6bab = true := by
  simp only [t6bab, ReplayTree.all, n, ht6baba, ht6babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ba := (n t6baa [w2,w9,w19,w60,w69,w116,w127] t6bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6ba : ReplayTree.all (blocked 5 t5) t6ba = true := by
  simp only [t6ba, ReplayTree.all, n, ht6baa, ht6bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaaaa := (n (n (n (n z [w4,w8,w11,w27,w70,w98,w132] z) [w4,w8,w45,w60,w70,w98,w127] (n z [w4,w9,w11,w27,w70,w101,w132] z)) [w4,w9,w11,w39,w70,w98,w132] (n (n z [w4,w9,w11,w60,w70,w111,w127] z) [w4,w9,w11,w60,w84,w98,w127] (n z [w4,w9,w15,w60,w69,w112,w127] z))) [w4,w9,w16,w60,w70,w112,w127] (n (n (n z [w4,w9,w23,w27,w70,w98,w132] z) [w4,w9,w27,w60,w70,w104,w127] (n z [w4,w9,w27,w60,w77,w98,w127] z)) [w4,w9,w31,w60,w69,w105,w127] (n (n z [w4,w9,w32,w60,w70,w105,w127] z) [w4,w9,w42,w60,w70,w98,w127] (n z [w4,w9,w43,w60,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaaaa : ReplayTree.all (blocked 5 t5) t6bbaaaa = true := by
  decide +kernel
def t6bbaaab := (n (n (n (n z [w4,w9,w45,w60,w70,w98,w127] z) [w4,w9,w45,w60,w70,w98,w129] (n z [w4,w9,w45,w60,w70,w98,w132] z)) [w4,w9,w45,w60,w70,w101,w127] (n (n z [w4,w9,w50,w60,w70,w98,w127] z) [w4,w9,w51,w60,w69,w98,w127] (n z [w4,w9,w52,w60,w70,w98,w127] z))) [w4,w9,w57,w60,w70,w98,w127] (n (n (n z [w4,w9,w60,w66,w70,w98,w127] z) [w4,w9,w60,w68,w70,w98,w127] (n z [w4,w9,w60,w70,w92,w98,w127] z)) [w4,w9,w60,w70,w94,w98,w127] (n (n z [w4,w9,w60,w70,w98,w121,w127] z) [w4,w9,w60,w70,w105,w112,w127] (n z [w4,w9,w60,w78,w85,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaaab : ReplayTree.all (blocked 5 t5) t6bbaaab = true := by
  decide +kernel
def t6bbaaa := (n t6bbaaaa [w4,w9,w44,w60,w70,w98,w127] t6bbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaaa : ReplayTree.all (blocked 5 t5) t6bbaaa = true := by
  simp only [t6bbaaa, ReplayTree.all, n, ht6bbaaaa, ht6bbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaaba := (n (n (n (n z [w4,w11,w27,w60,w70,w102,w127] z) [w4,w11,w27,w61,w70,w101,w127] (n z [w4,w11,w27,w62,w70,w101,w132] z)) [w4,w11,w27,w70,w100,w101,w132] (n (n z [w4,w11,w27,w70,w101,w103,w132] z) [w4,w11,w27,w70,w101,w129,w132] (n z [w4,w11,w27,w70,w101,w132,w134] z))) [w4,w11,w29,w60,w70,w101,w127] (n (n (n z [w4,w11,w38,w60,w70,w98,w129] z) [w4,w11,w40,w60,w70,w98,w127] (n z [w4,w11,w60,w70,w101,w112,w129] z)) [w4,w11,w60,w70,w103,w112,w127] (n (n z [w4,w11,w60,w70,w103,w116,w127] z) [w4,w13,w27,w60,w70,w101,w127] (n z [w4,w14,w30,w60,w70,w101,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaaba : ReplayTree.all (blocked 5 t5) t6bbaaba = true := by
  decide +kernel
def t6bbaabb := (n (n (n (n z [w4,w14,w32,w60,w70,w101,w127] z) [w4,w15,w30,w60,w69,w101,w127] (n z [w4,w16,w30,w60,w70,w101,w127] z)) [w4,w22,w27,w60,w70,w98,w129] (n (n z [w4,w23,w39,w60,w70,w98,w129] z) [w4,w24,w27,w60,w70,w98,w127] (n z [w4,w25,w41,w60,w70,w98,w127] z))) [w4,w27,w60,w70,w101,w105,w129] (n (n (n z [w4,w27,w60,w70,w103,w105,w127] z) [w4,w27,w60,w70,w103,w109,w127] (n z [w4,w45,w60,w62,w70,w101,w127] z)) [w4,w45,w60,w70,w98,w101,w129] (n (n z [w4,w45,w60,w70,w98,w103,w127] z) [w4,w45,w60,w70,w100,w101,w127] (n z [w4,w45,w60,w70,w101,w103,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaabb : ReplayTree.all (blocked 5 t5) t6bbaabb = true := by
  decide +kernel
def t6bbaab := (n t6bbaaba [w4,w14,w31,w60,w69,w101,w127] t6bbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaab : ReplayTree.all (blocked 5 t5) t6bbaab = true := by
  simp only [t6bbaab, ReplayTree.all, n, ht6bbaaba, ht6bbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaa := (n t6bbaaa [w4,w11,w27,w60,w70,w101,w128] t6bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaa : ReplayTree.all (blocked 5 t5) t6bbaa = true := by
  simp only [t6bbaa, ReplayTree.all, n, ht6bbaaa, ht6bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbabaa := (n (n (n (n z [w5,w7,w14,w60,w69,w112,w127] z) [w5,w7,w14,w60,w83,w98,w127] (n z [w5,w7,w30,w60,w69,w105,w127] z)) [w5,w7,w30,w60,w76,w98,w127] (n (n z [w5,w7,w45,w60,w69,w98,w129] z) [w5,w7,w50,w60,w69,w98,w127] (n z [w5,w9,w11,w60,w69,w112,w127] z))) [w5,w9,w27,w60,w69,w105,w127] (n (n (n z [w5,w9,w45,w60,w69,w98,w127] z) [w5,w11,w30,w60,w69,w101,w127] (n z [w5,w14,w27,w60,w69,w101,w127] z)) [w6,w7,w9,w60,w92,w98,w127] (n (n z [w6,w7,w11,w60,w83,w99,w127] z) [w6,w7,w11,w61,w83,w98,w127] (n z [w6,w7,w11,w62,w83,w98,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbabaa : ReplayTree.all (blocked 5 t5) t6bbabaa = true := by
  decide +kernel
def t6bbabab := (n (n (n (n z [w6,w7,w14,w60,w70,w112,w127] z) [w6,w7,w14,w60,w85,w98,w127] (n z [w6,w7,w27,w60,w76,w99,w127] z)) [w6,w7,w27,w61,w76,w98,w127] (n (n z [w6,w7,w27,w62,w76,w98,w132] z) [w6,w7,w29,w60,w76,w98,w127] (n z [w6,w7,w30,w60,w70,w105,w127] z))) [w6,w7,w30,w60,w78,w98,w127] (n (n (n z [w6,w7,w45,w60,w69,w99,w127] z) [w6,w7,w45,w60,w70,w98,w129] (n z [w6,w7,w45,w61,w69,w98,w127] z)) [w6,w7,w45,w62,w69,w98,w132] (n (n z [w6,w7,w47,w60,w69,w98,w127] z) [w6,w7,w50,w60,w69,w98,w129] (n z [w6,w7,w50,w60,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbabab : ReplayTree.all (blocked 5 t5) t6bbabab = true := by
  decide +kernel
def t6bbaba := (n t6bbabaa [w6,w7,w13,w60,w83,w98,w127] t6bbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbaba : ReplayTree.all (blocked 5 t5) t6bbaba = true := by
  simp only [t6bbaba, ReplayTree.all, n, ht6bbabaa, ht6bbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbabba := (n (n (n (n z [w6,w7,w60,w62,w92,w98,w127] z) [w6,w7,w60,w69,w100,w121,w127] (n z [w6,w7,w60,w76,w100,w112,w127] z)) [w6,w7,w60,w83,w100,w105,w127] (n (n z [w6,w7,w60,w92,w98,w100,w127] z) [w6,w8,w11,w60,w83,w98,w127] (n z [w6,w8,w27,w60,w76,w98,w127] z))) [w6,w8,w45,w60,w69,w98,w127] (n (n (n z [w6,w9,w11,w60,w69,w111,w127] z) [w6,w9,w11,w60,w70,w112,w127] (n z [w6,w9,w11,w60,w82,w98,w127] z)) [w6,w9,w11,w60,w83,w101,w127] (n (n z [w6,w9,w16,w60,w69,w112,w127] z) [w6,w9,w23,w60,w83,w98,w127] (n z [w6,w9,w27,w60,w69,w104,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbabba : ReplayTree.all (blocked 5 t5) t6bbabba = true := by
  decide +kernel
def t6bbabbb := (n (n (n (n z [w6,w9,w27,w60,w75,w98,w127] z) [w6,w9,w27,w60,w76,w101,w127] (n z [w6,w9,w32,w60,w69,w105,w127] z)) [w6,w9,w39,w60,w76,w98,w127] (n (n z [w6,w9,w42,w60,w69,w98,w127] z) [w6,w9,w43,w60,w69,w98,w127] (n z [w6,w9,w44,w60,w69,w98,w127] z))) [w6,w9,w45,w60,w69,w98,w127] (n (n (n z [w6,w9,w45,w60,w69,w98,w129] z) [w6,w9,w45,w60,w69,w98,w131] (n z [w6,w9,w45,w60,w69,w98,w132] z)) [w6,w9,w45,w60,w69,w101,w127] (n (n z [w6,w9,w45,w60,w70,w98,w127] z) [w6,w9,w50,w60,w69,w98,w127] (n z [w6,w9,w52,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbabbb : ReplayTree.all (blocked 5 t5) t6bbabbb = true := by
  decide +kernel
def t6bbabb := (n t6bbabba [w6,w9,w27,w60,w70,w105,w127] t6bbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbabb : ReplayTree.all (blocked 5 t5) t6bbabb = true := by
  simp only [t6bbabb, ReplayTree.all, n, ht6bbabba, ht6bbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbab := (n t6bbaba [w6,w7,w52,w60,w69,w98,w129] t6bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbab : ReplayTree.all (blocked 5 t5) t6bbab = true := by
  simp only [t6bbab, ReplayTree.all, n, ht6bbaba, ht6bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bba := (n t6bbaa [w4,w45,w60,w70,w101,w127,w129] t6bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bba : ReplayTree.all (blocked 5 t5) t6bba = true := by
  simp only [t6bba, ReplayTree.all, n, ht6bbaa, ht6bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbaaa := (n (n (n (n z [w6,w9,w59,w60,w69,w98,w127] z) [w6,w9,w60,w66,w69,w98,w127] (n z [w6,w9,w60,w68,w69,w98,w127] z)) [w6,w9,w60,w69,w92,w98,w127] (n (n z [w6,w9,w60,w69,w98,w121,w127] z) [w6,w9,w60,w69,w105,w112,w127] (n z [w6,w9,w60,w76,w83,w98,w127] z))) [w6,w11,w27,w60,w69,w102,w127] (n (n (n z [w6,w11,w27,w61,w69,w101,w127] z) [w6,w11,w27,w62,w69,w101,w132] (n z [w6,w11,w29,w60,w69,w101,w127] z)) [w6,w11,w30,w60,w70,w101,w127] (n (n z [w6,w11,w40,w60,w69,w98,w127] z) [w6,w11,w60,w69,w103,w112,w127] (n z [w6,w11,w60,w69,w103,w116,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbaaa : ReplayTree.all (blocked 5 t5) t6bbbaaa = true := by
  decide +kernel
def t6bbbaab := (n (n (n (n z [w6,w14,w27,w60,w70,w101,w127] z) [w6,w14,w30,w60,w69,w101,w127] (n z [w6,w14,w32,w60,w69,w101,w127] z)) [w6,w16,w30,w60,w69,w101,w127] (n (n z [w6,w24,w27,w60,w69,w98,w127] z) [w6,w25,w41,w60,w69,w98,w127] (n z [w6,w27,w60,w69,w103,w105,w127] z))) [w6,w27,w60,w69,w103,w109,w127] (n (n (n z [w6,w45,w60,w62,w69,w101,w127] z) [w6,w45,w60,w69,w98,w103,w127] (n z [w6,w45,w60,w69,w100,w101,w127] z)) [w6,w45,w60,w69,w101,w103,w127] (n (n z [w7,w9,w57,w60,w70,w98,w127] z) [w7,w10,w35,w60,w70,w98,w129] (n z [w7,w11,w27,w60,w73,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbaab : ReplayTree.all (blocked 5 t5) t6bbbaab = true := by
  decide +kernel
def t6bbbaa := (n t6bbbaaa [w6,w13,w27,w60,w69,w101,w127] t6bbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbaa : ReplayTree.all (blocked 5 t5) t6bbbaa = true := by
  simp only [t6bbbaa, ReplayTree.all, n, ht6bbbaaa, ht6bbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbaba := (n (n (n (n z [w7,w11,w27,w64,w70,w98,w134] z) [w7,w11,w27,w70,w98,w134,w136] (n z [w7,w11,w33,w60,w70,w98,w129] z)) [w7,w11,w34,w60,w70,w98,w129] (n (n z [w7,w11,w35,w60,w70,w98,w128] z) [w7,w11,w35,w60,w70,w98,w129] (n z [w7,w11,w35,w60,w70,w98,w134] z))) [w7,w11,w35,w60,w70,w99,w127] (n (n (n z [w7,w11,w35,w61,w70,w98,w127] z) [w7,w11,w35,w62,w70,w98,w132] (n z [w7,w11,w37,w60,w70,w98,w129] z)) [w7,w11,w57,w60,w70,w98,w129] (n (n z [w7,w11,w60,w70,w87,w98,w129] z) [w7,w11,w60,w70,w88,w98,w129] (n z [w7,w11,w60,w74,w85,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbaba : ReplayTree.all (blocked 5 t5) t6bbbaba = true := by
  decide +kernel
def t6bbbabb := (n (n (n (n z [w7,w14,w31,w60,w69,w98,w131] z) [w7,w14,w35,w60,w70,w98,w129] (n z [w7,w14,w37,w60,w70,w98,w127] z)) [w7,w15,w30,w60,w69,w98,w131] (n (n z [w7,w15,w35,w60,w69,w98,w129] z) [w7,w16,w35,w60,w70,w98,w129] (n z [w7,w16,w37,w60,w69,w98,w129] z))) [w7,w17,w27,w60,w70,w98,w129] (n (n (n z [w7,w18,w27,w60,w70,w98,w129] z) [w7,w19,w26,w60,w70,w98,w129] (n z [w7,w19,w27,w60,w70,w98,w128] z)) [w7,w19,w27,w60,w70,w98,w129] (n (n z [w7,w19,w27,w60,w70,w98,w134] z) [w7,w19,w27,w60,w70,w99,w127] (n z [w7,w19,w27,w61,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbabb : ReplayTree.all (blocked 5 t5) t6bbbabb = true := by
  decide +kernel
def t6bbbab := (n t6bbbaba [w7,w13,w35,w60,w70,w98,w127] t6bbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbab : ReplayTree.all (blocked 5 t5) t6bbbab = true := by
  simp only [t6bbbab, ReplayTree.all, n, ht6bbbaba, ht6bbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbba := (n t6bbbaa [w7,w11,w27,w63,w70,w98,w129] t6bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbba : ReplayTree.all (blocked 5 t5) t6bbba = true := by
  simp only [t6bbba, ReplayTree.all, n, ht6bbbaa, ht6bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbaa := (n (n (n (n z [w7,w19,w29,w60,w70,w98,w127] z) [w7,w19,w30,w60,w70,w98,w129] (n z [w7,w19,w31,w60,w69,w98,w129] z)) [w7,w19,w32,w60,w70,w98,w129] (n (n z [w7,w19,w35,w60,w70,w98,w129] z) [w7,w19,w39,w60,w70,w98,w129] (n z [w7,w19,w45,w60,w70,w98,w129] z))) [w7,w19,w57,w60,w70,w98,w129] (n (n (n z [w7,w19,w60,w70,w83,w98,w129] z) [w7,w19,w60,w70,w85,w98,w129] (n z [w7,w19,w60,w70,w98,w112,w129] z)) [w7,w19,w60,w70,w100,w112,w127] (n (n z [w7,w21,w27,w60,w70,w98,w129] z) [w7,w21,w30,w60,w70,w98,w127] (n z [w7,w21,w32,w60,w69,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbbaa : ReplayTree.all (blocked 5 t5) t6bbbbaa = true := by
  decide +kernel
def t6bbbbab := (n (n (n (n z [w7,w27,w57,w60,w70,w98,w129] z) [w7,w27,w60,w70,w80,w98,w129] (n z [w7,w27,w60,w70,w81,w98,w129] z)) [w7,w27,w60,w74,w78,w98,w129] (n (n z [w7,w35,w45,w60,w70,w98,w129] z) [w7,w35,w57,w60,w70,w98,w129] (n z [w7,w35,w60,w70,w76,w98,w129] z))) [w7,w35,w60,w70,w78,w98,w129] (n (n (n z [w7,w35,w60,w70,w98,w105,w129] z) [w7,w35,w60,w70,w100,w105,w127] (n z [w7,w45,w57,w60,w70,w98,w129] z)) [w7,w45,w60,w64,w70,w98,w129] (n (n z [w7,w45,w60,w70,w72,w98,w129] z) [w7,w45,w60,w70,w74,w98,w129] (n z [w7,w45,w60,w70,w98,w129,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbbab : ReplayTree.all (blocked 5 t5) t6bbbbab = true := by
  decide +kernel
def t6bbbba := (n t6bbbbaa [w7,w23,w35,w60,w70,w98,w129] t6bbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbba : ReplayTree.all (blocked 5 t5) t6bbbba = true := by
  simp only [t6bbbba, ReplayTree.all, n, ht6bbbbaa, ht6bbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbba := (n (n (n (n z [w7,w57,w60,w62,w70,w98,w127] z) [w7,w57,w60,w69,w70,w98,w129] (n z [w7,w57,w60,w70,w98,w100,w127] z)) [w7,w57,w60,w70,w98,w127,w129] (n (n z [w7,w57,w60,w70,w98,w129] z) [w8,w11,w35,w60,w70,w98,w127] (n z [w8,w19,w27,w60,w70,w98,w127] z))) [w9,w11,w27,w60,w73,w98,w127] (n (n (n z [w9,w11,w27,w63,w70,w98,w127] z) [w9,w11,w27,w64,w70,w98,w132] (n z [w9,w11,w34,w60,w70,w98,w127] z)) [w9,w11,w35,w60,w70,w101,w127] (n (n z [w9,w11,w36,w60,w69,w98,w127] z) [w9,w11,w60,w74,w83,w98,w127] (n z [w9,w11,w60,w74,w85,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbbba : ReplayTree.all (blocked 5 t5) t6bbbbba = true := by
  decide +kernel
def t6bbbbbb := (n (n (n (n z [w9,w19,w27,w60,w70,w101,w127] z) [w9,w19,w35,w60,w70,w98,w127] (n z [w9,w19,w39,w60,w70,w98,w127] z)) [w9,w20,w27,w60,w69,w98,w127] (n (n z [w9,w21,w37,w60,w69,w98,w127] z) [w9,w23,w35,w60,w70,w98,w127] (n z [w9,w27,w60,w74,w76,w98,w127] z))) [w9,w27,w60,w74,w78,w98,w127] (n (n (n z [w9,w45,w60,w64,w70,w98,w127] z) [w9,w45,w60,w69,w74,w98,w127] (n z [w9,w45,w60,w70,w72,w98,w127] z)) [w9,w45,w60,w70,w74,w98,w127] (n (n z [w11,w27,w60,w70,w101,w129,w131] z) [w11,w27,w62,w64,w70,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbbbb : ReplayTree.all (blocked 5 t5) t6bbbbbb = true := by
  decide +kernel
def t6bbbbb := (n t6bbbbba [w9,w18,w27,w60,w70,w98,w127] t6bbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbbb : ReplayTree.all (blocked 5 t5) t6bbbbb = true := by
  simp only [t6bbbbb, ReplayTree.all, n, ht6bbbbba, ht6bbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbb := (n t6bbbba [w7,w45,w62,w64,w70,w98,w127] t6bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbbb : ReplayTree.all (blocked 5 t5) t6bbbb = true := by
  simp only [t6bbbb, ReplayTree.all, n, ht6bbbba, ht6bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbb := (n t6bbba [w7,w19,w27,w62,w70,w98,w132] t6bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bbb : ReplayTree.all (blocked 5 t5) t6bbb = true := by
  simp only [t6bbb, ReplayTree.all, n, ht6bbba, ht6bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bb := (n t6bba [w6,w9,w57,w60,w69,w98,w127] t6bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6bb : ReplayTree.all (blocked 5 t5) t6bb = true := by
  simp only [t6bb, ReplayTree.all, n, ht6bba, ht6bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6b := (n t6ba [w4,w7,w60,w78,w85,w98,w129] t6bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6b : ReplayTree.all (blocked 5 t5) t6b = true := by
  simp only [t6b, ReplayTree.all, n, ht6ba, ht6bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6 := (n t6a [w2,w4,w45,w69,w101,w129,w132] t6b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht6 : ReplayTree.all (blocked 5 t5) t6 = true := by
  simp only [t6, ReplayTree.all, n, ht6a, ht6b, Bool.true_and, Bool.and_true]
  decide +kernel
theorem s6 : sound 6 t6 := layer_sound s5 ht6
def t7aaaaaaa := (n (n (n (n z [w0,w2,w4,w7,w11,w69,w112,w132] z) [w0,w2,w4,w7,w11,w83,w98,w132] z) [w0,w2,w4,w7,w27,w69,w105,w132] (n (n z [w0,w2,w4,w7,w27,w76,w98,w132] z) [w0,w2,w4,w7,w45,w69,w98,w132] z)) [w0,w2,w4,w7,w60,w69,w121,w127] (n (n (n z [w0,w2,w4,w7,w60,w76,w112,w127] z) [w0,w2,w4,w7,w60,w83,w105,w127] z) [w0,w2,w4,w7,w60,w92,w98,w127] (n z [w0,w2,w4,w11,w27,w69,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaaaa : ReplayTree.all (blocked 6 t6) t7aaaaaaa = true := by
  decide +kernel
def t7aaaaaab := (n (n (n (n z [w0,w2,w7,w19,w60,w69,w112,w127] z) [w0,w2,w7,w19,w60,w83,w98,w127] z) [w0,w2,w7,w35,w60,w69,w105,w127] (n (n z [w0,w2,w7,w35,w60,w76,w98,w127] z) [w0,w2,w7,w45,w60,w69,w98,w131] z)) [w0,w2,w7,w57,w60,w69,w98,w127] (n (n (n z [w0,w2,w11,w27,w60,w69,w101,w131] z) [w0,w4,w7,w11,w27,w70,w98,w132] z) [w0,w4,w7,w45,w60,w70,w98,w127] (n z [w0,w4,w11,w27,w60,w70,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaaab : ReplayTree.all (blocked 6 t6) t7aaaaaab = true := by
  decide +kernel
def t7aaaaaa := (n t7aaaaaaa [w0,w2,w4,w45,w60,w69,w101,w127] t7aaaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaaa : ReplayTree.all (blocked 6 t6) t7aaaaaa = true := by
  simp only [t7aaaaaa, ReplayTree.all, n, ht7aaaaaaa, ht7aaaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaaaba := (n (n (n (n z [w0,w6,w7,w27,w60,w76,w98,w127] z) [w0,w6,w7,w45,w60,w69,w98,w127] z) [w0,w6,w11,w27,w60,w69,w101,w127] (n (n z [w0,w7,w11,w35,w60,w70,w98,w127] z) [w0,w7,w19,w27,w60,w70,w98,w127] z)) [w1,w2,w3,w7,w11,w69,w112,w132] (n (n (n z [w1,w2,w3,w7,w11,w83,w98,w132] z) [w1,w2,w3,w7,w27,w69,w105,w132] z) [w1,w2,w3,w7,w27,w76,w98,w132] (n z [w1,w2,w3,w7,w45,w69,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaaba : ReplayTree.all (blocked 6 t6) t7aaaaaba = true := by
  decide +kernel
def t7aaaaabb := (n (n (n (n z [w1,w2,w3,w7,w60,w76,w112,w127] z) [w1,w2,w3,w7,w60,w83,w105,w127] z) [w1,w2,w3,w7,w60,w92,w98,w127] (n (n z [w1,w2,w3,w11,w27,w69,w101,w132] z) [w1,w2,w3,w45,w60,w69,w101,w127] z)) [w1,w2,w4,w7,w10,w69,w112,w132] (n (n (n z [w1,w2,w4,w7,w10,w83,w98,w132] z) [w1,w2,w4,w7,w11,w69,w111,w132] z) [w1,w2,w4,w7,w11,w69,w112,w132] (n z [w1,w2,w4,w7,w11,w69,w116,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaabb : ReplayTree.all (blocked 6 t6) t7aaaaabb = true := by
  decide +kernel
def t7aaaaab := (n t7aaaaaba [w1,w2,w3,w7,w60,w69,w121,w127] t7aaaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaab : ReplayTree.all (blocked 6 t6) t7aaaaab = true := by
  simp only [t7aaaaab, ReplayTree.all, n, ht7aaaaaba, ht7aaaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaaa := (n t7aaaaaa [w0,w6,w7,w11,w60,w83,w98,w127] t7aaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaa : ReplayTree.all (blocked 6 t6) t7aaaaa = true := by
  simp only [t7aaaaa, ReplayTree.all, n, ht7aaaaaa, ht7aaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaabaa := (n (n (n (n z [w1,w2,w4,w7,w11,w70,w112,w132] z) [w1,w2,w4,w7,w11,w76,w112,w132] z) [w1,w2,w4,w7,w11,w82,w98,w132] (n (n z [w1,w2,w4,w7,w11,w83,w98,w132] z) [w1,w2,w4,w7,w11,w83,w101,w132] z)) [w1,w2,w4,w7,w11,w83,w105,w132] (n (n (n z [w1,w2,w4,w7,w11,w83,w112,w132] z) [w1,w2,w4,w7,w11,w85,w98,w132] z) [w1,w2,w4,w7,w11,w92,w98,w132] (n z [w1,w2,w4,w7,w16,w69,w112,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaabaa : ReplayTree.all (blocked 6 t6) t7aaaabaa = true := by
  decide +kernel
def t7aaaabab := (n (n (n (n z [w1,w2,w4,w7,w23,w69,w112,w132] z) [w1,w2,w4,w7,w23,w83,w98,w132] z) [w1,w2,w4,w7,w26,w69,w105,w132] (n (n z [w1,w2,w4,w7,w26,w76,w98,w132] z) [w1,w2,w4,w7,w27,w69,w104,w132] z)) [w1,w2,w4,w7,w27,w69,w105,w132] (n (n (n z [w1,w2,w4,w7,w27,w69,w109,w132] z) [w1,w2,w4,w7,w27,w69,w121,w132] z) [w1,w2,w4,w7,w27,w70,w105,w132] (n z [w1,w2,w4,w7,w27,w75,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaabab : ReplayTree.all (blocked 6 t6) t7aaaabab = true := by
  decide +kernel
def t7aaaaba := (n t7aaaabaa [w1,w2,w4,w7,w16,w83,w98,w132] t7aaaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaaba : ReplayTree.all (blocked 6 t6) t7aaaaba = true := by
  simp only [t7aaaaba, ReplayTree.all, n, ht7aaaabaa, ht7aaaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaabba := (n (n (n (n z [w1,w2,w4,w7,w27,w76,w101,w132] z) [w1,w2,w4,w7,w27,w76,w105,w132] z) [w1,w2,w4,w7,w27,w76,w112,w132] (n (n z [w1,w2,w4,w7,w27,w78,w98,w132] z) [w1,w2,w4,w7,w27,w83,w105,w132] z)) [w1,w2,w4,w7,w27,w92,w98,w132] (n (n (n z [w1,w2,w4,w7,w32,w69,w105,w132] z) [w1,w2,w4,w7,w32,w76,w98,w132] z) [w1,w2,w4,w7,w39,w69,w105,w132] (n z [w1,w2,w4,w7,w39,w76,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaabba : ReplayTree.all (blocked 6 t6) t7aaaabba = true := by
  decide +kernel
def t7aaaabbb := (n (n (n (n z [w1,w2,w4,w7,w43,w69,w98,w132] z) [w1,w2,w4,w7,w44,w69,w98,w132] z) [w1,w2,w4,w7,w45,w69,w98,w132] (n (n z [w1,w2,w4,w7,w45,w69,w101,w132] z) [w1,w2,w4,w7,w45,w69,w105,w132] z)) [w1,w2,w4,w7,w45,w69,w112,w132] (n (n (n z [w1,w2,w4,w7,w45,w69,w121,w132] z) [w1,w2,w4,w7,w45,w70,w98,w132] z) [w1,w2,w4,w7,w45,w76,w98,w132] (n z [w1,w2,w4,w7,w45,w83,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaabbb : ReplayTree.all (blocked 6 t6) t7aaaabbb = true := by
  decide +kernel
def t7aaaabb := (n t7aaaabba [w1,w2,w4,w7,w42,w69,w98,w132] t7aaaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaabb : ReplayTree.all (blocked 6 t6) t7aaaabb = true := by
  simp only [t7aaaabb, ReplayTree.all, n, ht7aaaabba, ht7aaaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaab := (n t7aaaaba [w1,w2,w4,w7,w27,w76,w98,w132] t7aaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaab : ReplayTree.all (blocked 6 t6) t7aaaab = true := by
  simp only [t7aaaab, ReplayTree.all, n, ht7aaaaba, ht7aaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaa := (n t7aaaaa [w1,w2,w4,w7,w11,w69,w121,w132] t7aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaa : ReplayTree.all (blocked 6 t6) t7aaaa = true := by
  simp only [t7aaaa, ReplayTree.all, n, ht7aaaaa, ht7aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaabaaa := (n (n (n (n z [w1,w2,w4,w7,w52,w69,w98,w132] z) [w1,w2,w4,w7,w60,w69,w118,w127] z) [w1,w2,w4,w7,w60,w69,w119,w127] (n (n z [w1,w2,w4,w7,w60,w69,w120,w127] z) [w1,w2,w4,w7,w60,w69,w121,w127] z)) [w1,w2,w4,w7,w60,w69,w121,w132] (n (n (n z [w1,w2,w4,w7,w60,w69,w125,w127] z) [w1,w2,w4,w7,w60,w70,w121,w127] z) [w1,w2,w4,w7,w60,w75,w112,w127] (n z [w1,w2,w4,w7,w60,w76,w111,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabaaa : ReplayTree.all (blocked 6 t6) t7aaabaaa = true := by
  decide +kernel
def t7aaabaab := (n (n (n (n z [w1,w2,w4,w7,w60,w76,w112,w132] z) [w1,w2,w4,w7,w60,w76,w116,w127] z) [w1,w2,w4,w7,w60,w76,w121,w127] (n (n z [w1,w2,w4,w7,w60,w78,w112,w127] z) [w1,w2,w4,w7,w60,w82,w105,w127] z)) [w1,w2,w4,w7,w60,w83,w104,w127] (n (n (n z [w1,w2,w4,w7,w60,w83,w105,w127] z) [w1,w2,w4,w7,w60,w83,w105,w132] z) [w1,w2,w4,w7,w60,w83,w109,w127] (n z [w1,w2,w4,w7,w60,w83,w121,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabaab : ReplayTree.all (blocked 6 t6) t7aaabaab = true := by
  decide +kernel
def t7aaabaa := (n t7aaabaaa [w1,w2,w4,w7,w60,w76,w112,w127] t7aaabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabaa : ReplayTree.all (blocked 6 t6) t7aaabaa = true := by
  simp only [t7aaabaa, ReplayTree.all, n, ht7aaabaaa, ht7aaabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaababa := (n (n (n (n z [w1,w2,w4,w7,w60,w89,w98,w127] z) [w1,w2,w4,w7,w60,w90,w98,w127] z) [w1,w2,w4,w7,w60,w91,w98,w127] (n (n z [w1,w2,w4,w7,w60,w92,w98,w127] z) [w1,w2,w4,w7,w60,w92,w98,w132] z)) [w1,w2,w4,w7,w60,w92,w101,w127] (n (n (n z [w1,w2,w4,w7,w60,w92,w105,w127] z) [w1,w2,w4,w7,w60,w92,w112,w127] z) [w1,w2,w4,w7,w60,w92,w121,w127] (n z [w1,w2,w4,w7,w60,w94,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaababa : ReplayTree.all (blocked 6 t6) t7aaababa = true := by
  decide +kernel
def t7aaababb := (n (n (n (n z [w1,w2,w4,w7,w69,w76,w112,w132] z) [w1,w2,w4,w7,w69,w83,w105,w132] z) [w1,w2,w4,w7,w69,w92,w98,w132] (n (n z [w1,w2,w4,w7,w69,w98,w121,w132] z) [w1,w2,w4,w7,w69,w105,w112,w132] z)) [w1,w2,w4,w7,w69,w105,w121,w132] (n (n (n z [w1,w2,w4,w7,w69,w112,w121,w132] z) [w1,w2,w4,w7,w69,w121,w127,w132] z) [w1,w2,w4,w7,w69,w121,w132] (n z [w1,w2,w4,w7,w76,w83,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaababb : ReplayTree.all (blocked 6 t6) t7aaababb = true := by
  decide +kernel
def t7aaabab := (n t7aaababa [w1,w2,w4,w7,w66,w69,w98,w132] t7aaababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabab : ReplayTree.all (blocked 6 t6) t7aaabab = true := by
  simp only [t7aaabab, ReplayTree.all, n, ht7aaababa, ht7aaababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaba := (n t7aaabaa [w1,w2,w4,w7,w60,w85,w105,w127] t7aaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaaba : ReplayTree.all (blocked 6 t6) t7aaaba = true := by
  simp only [t7aaaba, ReplayTree.all, n, ht7aaabaa, ht7aaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaabbaa := (n (n (n (n z [w1,w2,w4,w7,w76,w98,w112,w132] z) [w1,w2,w4,w7,w76,w112,w127,w132] z) [w1,w2,w4,w7,w76,w112,w132] (n (n z [w1,w2,w4,w7,w83,w92,w98,w132] z) [w1,w2,w4,w7,w83,w98,w105,w132] z)) [w1,w2,w4,w7,w83,w105,w127,w132] (n (n (n z [w1,w2,w4,w7,w83,w105,w132] z) [w1,w2,w4,w7,w92,w98,w127,w132] z) [w1,w2,w4,w7,w92,w98,w132] (n z [w1,w2,w4,w9,w60,w69,w121,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabbaa : ReplayTree.all (blocked 6 t6) t7aaabbaa = true := by
  decide +kernel
def t7aaabbab := (n (n (n (n z [w1,w2,w4,w11,w26,w69,w101,w132] z) [w1,w2,w4,w11,w27,w69,w101,w132] z) [w1,w2,w4,w11,w27,w70,w101,w132] (n (n z [w1,w2,w4,w11,w32,w69,w101,w132] z) [w1,w2,w4,w11,w38,w69,w98,w132] z)) [w1,w2,w4,w11,w39,w69,w101,w132] (n (n (n z [w1,w2,w4,w11,w45,w69,w101,w132] z) [w1,w2,w4,w11,w60,w69,w115,w127] z) [w1,w2,w4,w11,w60,w82,w101,w127] (n z [w1,w2,w4,w11,w69,w83,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabbab : ReplayTree.all (blocked 6 t6) t7aaabbab = true := by
  decide +kernel
def t7aaabba := (n t7aaabbaa [w1,w2,w4,w10,w27,w69,w101,w132] t7aaabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabba : ReplayTree.all (blocked 6 t6) t7aaabba = true := by
  simp only [t7aaabba, ReplayTree.all, n, ht7aaabbaa, ht7aaabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaabbba := (n (n (n (n z [w1,w2,w4,w11,w69,w101,w116,w132] z) [w1,w2,w4,w16,w27,w69,w101,w132] z) [w1,w2,w4,w22,w27,w69,w98,w132] (n (n z [w1,w2,w4,w22,w60,w69,w112,w127] z) [w1,w2,w4,w22,w60,w83,w98,w127] z)) [w1,w2,w4,w23,w27,w69,w101,w132] (n (n (n z [w1,w2,w4,w23,w39,w69,w98,w132] z) [w1,w2,w4,w23,w60,w69,w116,w127] z) [w1,w2,w4,w23,w60,w83,w101,w127] (n z [w1,w2,w4,w27,w45,w69,w101,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabbba : ReplayTree.all (blocked 6 t6) t7aaabbba = true := by
  decide +kernel
def t7aaabbbb := (n (n (n (n z [w1,w2,w4,w27,w60,w75,w101,w127] z) [w1,w2,w4,w27,w69,w76,w101,w132] z) [w1,w2,w4,w27,w69,w101,w105,w132] (n z [w1,w2,w4,w27,w69,w101,w109,w132] z)) [w1,w2,w4,w38,w60,w69,w105,w127] (n (n (n z [w1,w2,w4,w38,w60,w76,w98,w127] z) [w1,w2,w4,w39,w60,w69,w109,w127] z) [w1,w2,w4,w39,w60,w76,w101,w127] (n z [w1,w2,w4,w42,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabbbb : ReplayTree.all (blocked 6 t6) t7aaabbbb = true := by
  decide +kernel
def t7aaabbb := (n t7aaabbba [w1,w2,w4,w27,w60,w69,w108,w127] t7aaabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabbb : ReplayTree.all (blocked 6 t6) t7aaabbb = true := by
  simp only [t7aaabbb, ReplayTree.all, n, ht7aaabbba, ht7aaabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaabb := (n t7aaabba [w1,w2,w4,w11,w69,w101,w112,w132] t7aaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaabb : ReplayTree.all (blocked 6 t6) t7aaabb = true := by
  simp only [t7aaabb, ReplayTree.all, n, ht7aaabba, ht7aaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaab := (n t7aaaba [w1,w2,w4,w7,w76,w92,w98,w132] t7aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaab : ReplayTree.all (blocked 6 t6) t7aaab = true := by
  simp only [t7aaab, ReplayTree.all, n, ht7aaaba, ht7aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaa := (n t7aaaa [w1,w2,w4,w7,w45,w92,w98,w132] t7aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaa : ReplayTree.all (blocked 6 t6) t7aaa = true := by
  simp only [t7aaa, ReplayTree.all, n, ht7aaaa, ht7aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabaaaa := (n (n (n (n z [w1,w2,w4,w44,w60,w69,w101,w127] z) [w1,w2,w4,w45,w60,w69,w101,w127] z) [w1,w2,w4,w45,w60,w69,w101,w131] (n (n z [w1,w2,w4,w45,w60,w69,w101,w132] z) [w1,w2,w4,w45,w60,w70,w101,w127] z)) [w1,w2,w4,w45,w69,w98,w101,w132] (n (n (n z [w1,w2,w4,w45,w69,w101,w127,w132] z) [w1,w2,w4,w45,w69,w101,w132] z) [w1,w2,w4,w50,w60,w69,w101,w127] (n z [w1,w2,w4,w52,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaaaa : ReplayTree.all (blocked 6 t6) t7aabaaaa = true := by
  decide +kernel
def t7aabaaab := (n (n (n (n z [w1,w2,w4,w60,w65,w69,w98,w127] z) [w1,w2,w4,w60,w66,w69,w101,w127] z) [w1,w2,w4,w60,w69,w92,w101,w127] (n (n z [w1,w2,w4,w60,w69,w101,w121,w127] z) [w1,w2,w4,w60,w69,w101,w125,w127] z)) [w1,w2,w4,w60,w69,w109,w116,w127] (n (n (n z [w1,w2,w4,w60,w76,w83,w101,w127] z) [w1,w2,w6,w7,w11,w69,w112,w132] z) [w1,w2,w6,w7,w11,w83,w98,w132] (n z [w1,w2,w6,w7,w27,w69,w105,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaaab : ReplayTree.all (blocked 6 t6) t7aabaaab = true := by
  decide +kernel
def t7aabaaa := (n t7aabaaaa [w1,w2,w4,w57,w60,w69,w101,w127] t7aabaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaaa : ReplayTree.all (blocked 6 t6) t7aabaaa = true := by
  simp only [t7aabaaa, ReplayTree.all, n, ht7aabaaaa, ht7aabaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabaaba := (n (n (n (n z [w1,w2,w6,w7,w45,w69,w98,w132] z) [w1,w2,w6,w7,w60,w69,w121,w127] z) [w1,w2,w6,w7,w60,w76,w112,w127] (n (n z [w1,w2,w6,w7,w60,w83,w105,w127] z) [w1,w2,w6,w7,w60,w92,w98,w127] z)) [w1,w2,w6,w11,w27,w69,w101,w132] (n (n (n z [w1,w2,w6,w45,w60,w69,w101,w127] z) [w1,w2,w7,w11,w19,w69,w112,w132] z) [w1,w2,w7,w11,w19,w83,w98,w132] (n z [w1,w2,w7,w11,w27,w69,w98,w135] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaaba : ReplayTree.all (blocked 6 t6) t7aabaaba = true := by
  decide +kernel
def t7aabaabb := (n (n (n (n z [w1,w2,w7,w11,w33,w69,w98,w132] z) [w1,w2,w7,w11,w35,w69,w112,w132] z) [w1,w2,w7,w11,w35,w83,w98,w132] (n (n z [w1,w2,w7,w11,w60,w69,w111,w131] z) [w1,w2,w7,w11,w60,w69,w112,w130] z)) [w1,w2,w7,w11,w60,w71,w112,w127] (n (n (n z [w1,w2,w7,w11,w60,w82,w98,w131] z) [w1,w2,w7,w11,w60,w83,w98,w130] z) [w1,w2,w7,w11,w60,w86,w98,w127] (n z [w1,w2,w7,w11,w63,w69,w112,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaabb : ReplayTree.all (blocked 6 t6) t7aabaabb = true := by
  decide +kernel
def t7aabaab := (n t7aabaaba [w1,w2,w7,w11,w27,w71,w98,w132] t7aabaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaab : ReplayTree.all (blocked 6 t6) t7aabaab = true := by
  simp only [t7aabaab, ReplayTree.all, n, ht7aabaaba, ht7aabaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabaa := (n t7aabaaa [w1,w2,w6,w7,w27,w76,w98,w132] t7aabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabaa : ReplayTree.all (blocked 6 t6) t7aabaa = true := by
  simp only [t7aabaa, ReplayTree.all, n, ht7aabaaa, ht7aabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aababaa := (n (n (n (n z [w1,w2,w7,w11,w64,w69,w112,w132] z) [w1,w2,w7,w11,w64,w83,w98,w132] z) [w1,w2,w7,w11,w69,w72,w112,w132] (n (n z [w1,w2,w7,w11,w69,w112,w131,w132] z) [w1,w2,w7,w11,w69,w112,w132,w136] z)) [w1,w2,w7,w11,w72,w83,w98,w132] (n (n (n z [w1,w2,w7,w11,w83,w87,w98,w132] z) [w1,w2,w7,w11,w83,w98,w131,w132] z) [w1,w2,w7,w11,w83,w98,w132,w136] (n z [w1,w2,w7,w17,w27,w69,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aababaa : ReplayTree.all (blocked 6 t6) t7aababaa = true := by
  decide +kernel
def t7aababab := (n (n (n (n z [w1,w2,w7,w17,w60,w83,w98,w127] z) [w1,w2,w7,w18,w60,w69,w112,w127] z) [w1,w2,w7,w18,w60,w83,w98,w127] (n (n z [w1,w2,w7,w19,w27,w69,w105,w132] z) [w1,w2,w7,w19,w27,w76,w98,w132] z)) [w1,w2,w7,w19,w45,w69,w98,w132] (n (n (n z [w1,w2,w7,w19,w60,w69,w111,w127] z) [w1,w2,w7,w19,w60,w69,w112,w127] z) [w1,w2,w7,w19,w60,w69,w112,w132] (n z [w1,w2,w7,w19,w60,w69,w116,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aababab : ReplayTree.all (blocked 6 t6) t7aababab = true := by
  decide +kernel
def t7aababa := (n t7aababaa [w1,w2,w7,w17,w60,w69,w112,w127] t7aababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aababa : ReplayTree.all (blocked 6 t6) t7aababa = true := by
  simp only [t7aababa, ReplayTree.all, n, ht7aababaa, ht7aababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aababba := (n (n (n (n z [w1,w2,w7,w19,w60,w70,w112,w127] z) [w1,w2,w7,w19,w60,w76,w112,w127] z) [w1,w2,w7,w19,w60,w82,w98,w127] (n (n z [w1,w2,w7,w19,w60,w83,w98,w127] z) [w1,w2,w7,w19,w60,w83,w98,w132] z)) [w1,w2,w7,w19,w60,w83,w101,w127] (n (n (n z [w1,w2,w7,w19,w60,w83,w105,w127] z) [w1,w2,w7,w19,w60,w83,w112,w127] z) [w1,w2,w7,w19,w60,w85,w98,w127] (n z [w1,w2,w7,w19,w60,w92,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aababba : ReplayTree.all (blocked 6 t6) t7aababba = true := by
  decide +kernel
def t7aababbb := (n (n (n (n z [w1,w2,w7,w21,w60,w83,w98,w127] z) [w1,w2,w7,w27,w35,w69,w105,w132] z) [w1,w2,w7,w27,w35,w76,w98,w132] (n (n z [w1,w2,w7,w27,w60,w69,w104,w131] z) [w1,w2,w7,w27,w60,w69,w105,w130] z)) [w1,w2,w7,w27,w60,w71,w105,w127] (n (n (n z [w1,w2,w7,w27,w60,w75,w98,w131] z) [w1,w2,w7,w27,w60,w76,w98,w130] z) [w1,w2,w7,w27,w60,w79,w98,w127] (n z [w1,w2,w7,w27,w63,w69,w105,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aababbb : ReplayTree.all (blocked 6 t6) t7aababbb = true := by
  decide +kernel
def t7aababb := (n t7aababba [w1,w2,w7,w21,w60,w69,w112,w127] t7aababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aababb : ReplayTree.all (blocked 6 t6) t7aababb = true := by
  simp only [t7aababb, ReplayTree.all, n, ht7aababba, ht7aababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabab := (n t7aababa [w1,w2,w7,w19,w60,w69,w121,w127] t7aababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabab : ReplayTree.all (blocked 6 t6) t7aabab = true := by
  simp only [t7aabab, ReplayTree.all, n, ht7aababa, ht7aababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaba := (n t7aabaa [w1,w2,w7,w11,w63,w83,w98,w127] t7aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aaba : ReplayTree.all (blocked 6 t6) t7aaba = true := by
  simp only [t7aaba, ReplayTree.all, n, ht7aabaa, ht7aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabbaaa := (n (n (n (n z [w1,w2,w7,w27,w64,w69,w105,w132] z) [w1,w2,w7,w27,w64,w76,w98,w132] z) [w1,w2,w7,w27,w69,w72,w105,w132] (n (n z [w1,w2,w7,w27,w69,w105,w131,w132] z) [w1,w2,w7,w27,w69,w105,w132,w136] z)) [w1,w2,w7,w27,w72,w76,w98,w132] (n (n (n z [w1,w2,w7,w27,w76,w80,w98,w132] z) [w1,w2,w7,w27,w76,w98,w131,w132] z) [w1,w2,w7,w27,w76,w98,w132,w136] (n z [w1,w2,w7,w33,w60,w69,w105,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbaaa : ReplayTree.all (blocked 6 t6) t7aabbaaa = true := by
  decide +kernel
def t7aabbaab := (n (n (n (n z [w1,w2,w7,w34,w60,w69,w105,w127] z) [w1,w2,w7,w34,w60,w76,w98,w127] z) [w1,w2,w7,w35,w45,w69,w98,w132] (n (n z [w1,w2,w7,w35,w60,w69,w104,w127] z) [w1,w2,w7,w35,w60,w69,w105,w127] z)) [w1,w2,w7,w35,w60,w69,w105,w132] (n (n (n z [w1,w2,w7,w35,w60,w69,w109,w127] z) [w1,w2,w7,w35,w60,w69,w121,w127] z) [w1,w2,w7,w35,w60,w70,w105,w127] (n z [w1,w2,w7,w35,w60,w75,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbaab : ReplayTree.all (blocked 6 t6) t7aabbaab = true := by
  decide +kernel
def t7aabbaa := (n t7aabbaaa [w1,w2,w7,w33,w60,w76,w98,w127] t7aabbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbaa : ReplayTree.all (blocked 6 t6) t7aabbaa = true := by
  simp only [t7aabbaa, ReplayTree.all, n, ht7aabbaaa, ht7aabbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabbaba := (n (n (n (n z [w1,w2,w7,w35,w60,w76,w98,w132] z) [w1,w2,w7,w35,w60,w76,w101,w127] z) [w1,w2,w7,w35,w60,w76,w105,w127] (n (n z [w1,w2,w7,w35,w60,w76,w112,w127] z) [w1,w2,w7,w35,w60,w78,w98,w127] z)) [w1,w2,w7,w35,w60,w83,w105,w127] (n (n (n z [w1,w2,w7,w35,w60,w92,w98,w127] z) [w1,w2,w7,w37,w60,w69,w105,w127] z) [w1,w2,w7,w37,w60,w76,w98,w127] (n z [w1,w2,w7,w42,w60,w69,w98,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbaba : ReplayTree.all (blocked 6 t6) t7aabbaba = true := by
  decide +kernel
def t7aabbabb := (n (n (n (n z [w1,w2,w7,w44,w60,w69,w98,w131] z) [w1,w2,w7,w45,w57,w69,w98,w132] z) [w1,w2,w7,w45,w60,w69,w98,w130] (n (n z [w1,w2,w7,w45,w60,w69,w98,w131] z) [w1,w2,w7,w45,w60,w69,w98,w136] z)) [w1,w2,w7,w45,w60,w69,w101,w131] (n (n (n z [w1,w2,w7,w45,w60,w71,w98,w127] z) [w1,w2,w7,w45,w63,w69,w98,w127] z) [w1,w2,w7,w45,w64,w69,w98,w132] (n z [w1,w2,w7,w45,w69,w72,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbabb : ReplayTree.all (blocked 6 t6) t7aabbabb = true := by
  decide +kernel
def t7aabbab := (n t7aabbaba [w1,w2,w7,w43,w60,w69,w98,w131] t7aabbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbab : ReplayTree.all (blocked 6 t6) t7aabbab = true := by
  simp only [t7aabbab, ReplayTree.all, n, ht7aabbaba, ht7aabbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabba := (n t7aabbaa [w1,w2,w7,w35,w60,w76,w98,w127] t7aabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabba : ReplayTree.all (blocked 6 t6) t7aabba = true := by
  simp only [t7aabba, ReplayTree.all, n, ht7aabbaa, ht7aabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabbbaa := (n (n (n (n z [w1,w2,w7,w45,w69,w98,w132,w136] z) [w1,w2,w7,w50,w60,w69,w98,w131] z) [w1,w2,w7,w52,w60,w69,w98,w131] (n (n z [w1,w2,w7,w53,w60,w69,w98,w127] z) [w1,w2,w7,w54,w60,w69,w98,w127] z)) [w1,w2,w7,w55,w60,w69,w98,w127] (n (n (n z [w1,w2,w7,w56,w60,w69,w98,w127] z) [w1,w2,w7,w57,w60,w69,w98,w127] z) [w1,w2,w7,w57,w60,w69,w98,w129] (n z [w1,w2,w7,w57,w60,w69,w98,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbbaa : ReplayTree.all (blocked 6 t6) t7aabbbaa = true := by
  decide +kernel
def t7aabbbab := (n (n (n (n z [w1,w2,w7,w57,w60,w69,w101,w127] z) [w1,w2,w7,w57,w60,w69,w105,w127] z) [w1,w2,w7,w57,w60,w69,w112,w127] (n (n z [w1,w2,w7,w57,w60,w69,w121,w127] z) [w1,w2,w7,w57,w60,w70,w98,w127] z)) [w1,w2,w7,w57,w60,w76,w98,w127] (n (n (n z [w1,w2,w7,w57,w60,w83,w98,w127] z) [w1,w2,w7,w57,w60,w92,w98,w127] z) [w1,w2,w7,w59,w60,w69,w98,w127] (n z [w1,w2,w7,w60,w64,w69,w121,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbbab : ReplayTree.all (blocked 6 t6) t7aabbbab = true := by
  decide +kernel
def t7aabbba := (n t7aabbbaa [w1,w2,w7,w57,w60,w69,w98,w132] t7aabbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbba : ReplayTree.all (blocked 6 t6) t7aabbba = true := by
  simp only [t7aabbba, ReplayTree.all, n, ht7aabbbaa, ht7aabbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabbbba := (n (n (n (n z [w1,w2,w7,w60,w64,w83,w105,w127] z) [w1,w2,w7,w60,w64,w92,w98,w127] z) [w1,w2,w7,w60,w66,w69,w98,w131] (n (n z [w1,w2,w7,w60,w69,w72,w121,w127] z) [w1,w2,w7,w60,w69,w80,w112,w127] z)) [w1,w2,w7,w60,w69,w87,w105,w127] (n (n (n z [w1,w2,w7,w60,w69,w92,w98,w131] z) [w1,w2,w7,w60,w69,w96,w98,w127] z) [w1,w2,w7,w60,w69,w98,w121,w131] (n z [w1,w2,w7,w60,w69,w105,w112,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbbba : ReplayTree.all (blocked 6 t6) t7aabbbba = true := by
  decide +kernel
def t7aabbbbb := (n (n (n (n z [w1,w2,w7,w60,w72,w76,w112,w127] z) [w1,w2,w7,w60,w72,w83,w105,w127] z) [w1,w2,w7,w60,w72,w92,w98,w127] (n z [w1,w2,w7,w60,w76,w80,w112,w127] z)) [w1,w2,w7,w60,w76,w83,w98,w131] (n (n (n z [w1,w2,w7,w60,w76,w87,w98,w127] z) [w1,w2,w7,w60,w76,w96,w98,w127] z) [w1,w2,w7,w60,w76,w112,w127,w131] (n z [w1,w2,w7,w60,w80,w83,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbbbb : ReplayTree.all (blocked 6 t6) t7aabbbbb = true := by
  decide +kernel
def t7aabbbb := (n t7aabbbba [w1,w2,w7,w60,w69,w121,w127,w131] t7aabbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbbb : ReplayTree.all (blocked 6 t6) t7aabbbb = true := by
  simp only [t7aabbbb, ReplayTree.all, n, ht7aabbbba, ht7aabbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabbb := (n t7aabbba [w1,w2,w7,w60,w64,w76,w112,w127] t7aabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabbb : ReplayTree.all (blocked 6 t6) t7aabbb = true := by
  simp only [t7aabbb, ReplayTree.all, n, ht7aabbba, ht7aabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabb := (n t7aabba [w1,w2,w7,w45,w69,w98,w131,w132] t7aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aabb : ReplayTree.all (blocked 6 t6) t7aabb = true := by
  simp only [t7aabb, ReplayTree.all, n, ht7aabba, ht7aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aab := (n t7aaba [w1,w2,w7,w27,w63,w76,w98,w127] t7aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aab : ReplayTree.all (blocked 6 t6) t7aab = true := by
  simp only [t7aab, ReplayTree.all, n, ht7aaba, ht7aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aa := (n t7aaa [w1,w2,w4,w43,w60,w69,w101,w127] t7aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aa : ReplayTree.all (blocked 6 t6) t7aa = true := by
  simp only [t7aa, ReplayTree.all, n, ht7aaa, ht7aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaaaaa := (n (n (n (n z [w1,w2,w7,w60,w83,w87,w105,w127] z) [w1,w2,w7,w60,w83,w96,w98,w127] z) [w1,w2,w7,w60,w83,w105,w127,w131] (n (n z [w1,w2,w7,w60,w87,w92,w98,w127] z) [w1,w2,w7,w60,w92,w96,w98,w127] z)) [w1,w2,w7,w60,w92,w98,w127,w131] (n (n (n z [w1,w2,w10,w27,w60,w69,w101,w131] z) [w1,w2,w11,w26,w60,w69,w101,w131] z) [w1,w2,w11,w27,w60,w69,w101,w130] (n z [w1,w2,w11,w27,w60,w69,w101,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaaaa : ReplayTree.all (blocked 6 t6) t7abaaaaa = true := by
  decide +kernel
def t7abaaaab := (n (n (n (n z [w1,w2,w11,w27,w60,w71,w101,w127] z) [w1,w2,w11,w27,w63,w69,w101,w127] z) [w1,w2,w11,w27,w64,w69,w101,w132] (n (n z [w1,w2,w11,w27,w69,w72,w101,w132] z) [w1,w2,w11,w27,w69,w101,w131,w132] z)) [w1,w2,w11,w27,w69,w101,w132,w136] (n (n (n z [w1,w2,w11,w30,w60,w69,w101,w131] z) [w1,w2,w11,w32,w60,w69,w101,w131] z) [w1,w2,w11,w34,w60,w69,w101,w127] (n z [w1,w2,w11,w35,w60,w69,w101,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaaab : ReplayTree.all (blocked 6 t6) t7abaaaab = true := by
  decide +kernel
def t7abaaaa := (n t7abaaaaa [w1,w2,w11,w27,w60,w69,w101,w136] t7abaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaaa : ReplayTree.all (blocked 6 t6) t7abaaaa = true := by
  simp only [t7abaaaa, ReplayTree.all, n, ht7abaaaaa, ht7abaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaaaba := (n (n (n (n z [w1,w2,w11,w39,w60,w69,w101,w131] z) [w1,w2,w11,w45,w60,w69,w101,w131] z) [w1,w2,w11,w60,w69,w83,w101,w131] (n (n z [w1,w2,w11,w60,w69,w101,w112,w131] z) [w1,w2,w11,w60,w69,w101,w116,w131] z)) [w1,w2,w11,w60,w72,w83,w101,w127] (n (n (n z [w1,w2,w14,w27,w60,w69,w101,w131] z) [w1,w2,w16,w27,w60,w69,w101,w131] z) [w1,w2,w18,w27,w60,w69,w101,w127] (n z [w1,w2,w19,w27,w60,w69,w101,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaaba : ReplayTree.all (blocked 6 t6) t7abaaaba = true := by
  decide +kernel
def t7abaaabb := (n (n (n (n z [w1,w2,w19,w38,w60,w69,w98,w127] z) [w1,w2,w19,w39,w60,w69,w101,w127] z) [w1,w2,w22,w27,w60,w69,w98,w131] (n (n z [w1,w2,w22,w35,w60,w69,w98,w127] z) [w1,w2,w23,w27,w60,w69,w101,w131] z)) [w1,w2,w23,w35,w60,w69,w101,w127] (n (n (n z [w1,w2,w23,w39,w60,w69,w98,w131] z) [w1,w2,w27,w45,w60,w69,w101,w131] z) [w1,w2,w27,w60,w69,w76,w101,w131] (n z [w1,w2,w27,w60,w69,w101,w105,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaabb : ReplayTree.all (blocked 6 t6) t7abaaabb = true := by
  decide +kernel
def t7abaaab := (n t7abaaaba [w1,w2,w19,w35,w60,w69,w101,w127] t7abaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaab : ReplayTree.all (blocked 6 t6) t7abaaab = true := by
  simp only [t7abaaab, ReplayTree.all, n, ht7abaaaba, ht7abaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaaa := (n t7abaaaa [w1,w2,w11,w38,w60,w69,w98,w131] t7abaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaa : ReplayTree.all (blocked 6 t6) t7abaaa = true := by
  simp only [t7abaaa, ReplayTree.all, n, ht7abaaaa, ht7abaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaabaa := (n (n (n (n z [w1,w2,w27,w60,w72,w76,w101,w127] z) [w1,w2,w45,w60,w64,w69,w101,w127] z) [w1,w2,w45,w60,w69,w72,w101,w127] (n (n z [w1,w2,w45,w60,w69,w98,w101,w131] z) [w1,w2,w45,w60,w69,w101,w127,w131] z)) [w1,w2,w45,w60,w69,w101,w131] (n (n (n z [w1,w3,w7,w11,w27,w70,w98,w132] z) [w1,w3,w7,w45,w60,w70,w98,w127] z) [w1,w3,w11,w27,w60,w70,w101,w127] (n z [w1,w4,w6,w7,w60,w92,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaabaa : ReplayTree.all (blocked 6 t6) t7abaabaa = true := by
  decide +kernel
def t7abaabab := (n (n (n (n z [w1,w4,w7,w10,w27,w70,w98,w132] z) [w1,w4,w7,w11,w26,w70,w98,w132] z) [w1,w4,w7,w11,w27,w70,w98,w132] (n (n z [w1,w4,w7,w11,w27,w70,w101,w132] z) [w1,w4,w7,w11,w31,w69,w98,w132] z)) [w1,w4,w7,w11,w32,w70,w98,w132] (n (n (n z [w1,w4,w7,w11,w39,w70,w98,w132] z) [w1,w4,w7,w11,w45,w70,w98,w132] z) [w1,w4,w7,w11,w60,w70,w111,w127] (n z [w1,w4,w7,w11,w60,w84,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaabab : ReplayTree.all (blocked 6 t6) t7abaabab = true := by
  decide +kernel
def t7abaaba := (n t7abaabaa [w1,w4,w6,w45,w60,w69,w101,w127] t7abaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaaba : ReplayTree.all (blocked 6 t6) t7abaaba = true := by
  simp only [t7abaaba, ReplayTree.all, n, ht7abaabaa, ht7abaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaabba := (n (n (n (n z [w1,w4,w7,w11,w70,w85,w98,w132] z) [w1,w4,w7,w11,w70,w98,w112,w132] z) [w1,w4,w7,w15,w27,w69,w98,w132] (n (n z [w1,w4,w7,w15,w60,w69,w112,w127] z) [w1,w4,w7,w15,w60,w83,w98,w127] z)) [w1,w4,w7,w16,w27,w70,w98,w132] (n (n (n z [w1,w4,w7,w16,w32,w69,w98,w132] z) [w1,w4,w7,w16,w60,w70,w112,w127] z) [w1,w4,w7,w16,w60,w85,w98,w127] (n z [w1,w4,w7,w23,w27,w70,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaabba : ReplayTree.all (blocked 6 t6) t7abaabba = true := by
  decide +kernel
def t7abaabbb := (n (n (n (n z [w1,w4,w7,w27,w60,w70,w104,w127] z) [w1,w4,w7,w27,w60,w77,w98,w127] z) [w1,w4,w7,w27,w70,w76,w98,w132] (n (n z [w1,w4,w7,w27,w70,w78,w98,w132] z) [w1,w4,w7,w27,w70,w98,w105,w132] z)) [w1,w4,w7,w31,w60,w69,w105,w127] (n (n (n z [w1,w4,w7,w31,w60,w76,w98,w127] z) [w1,w4,w7,w32,w60,w70,w105,w127] z) [w1,w4,w7,w32,w60,w78,w98,w127] (n z [w1,w4,w7,w42,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaabbb : ReplayTree.all (blocked 6 t6) t7abaabbb = true := by
  decide +kernel
def t7abaabb := (n t7abaabba [w1,w4,w7,w27,w45,w70,w98,w132] t7abaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaabb : ReplayTree.all (blocked 6 t6) t7abaabb = true := by
  simp only [t7abaabb, ReplayTree.all, n, ht7abaabba, ht7abaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaab := (n t7abaaba [w1,w4,w7,w11,w70,w83,w98,w132] t7abaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaab : ReplayTree.all (blocked 6 t6) t7abaab = true := by
  simp only [t7abaab, ReplayTree.all, n, ht7abaaba, ht7abaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaa := (n t7abaaa [w1,w2,w27,w60,w69,w101,w109,w131] t7abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abaa : ReplayTree.all (blocked 6 t6) t7abaa = true := by
  simp only [t7abaa, ReplayTree.all, n, ht7abaaa, ht7abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ababaaa := (n (n (n (n z [w1,w4,w7,w44,w60,w70,w98,w127] z) [w1,w4,w7,w45,w60,w70,w98,w127] z) [w1,w4,w7,w45,w60,w70,w98,w129] (n (n z [w1,w4,w7,w45,w60,w70,w98,w132] z) [w1,w4,w7,w45,w60,w70,w101,w127] z)) [w1,w4,w7,w45,w69,w70,w98,w132] (n (n (n z [w1,w4,w7,w45,w70,w98,w127,w132] z) [w1,w4,w7,w45,w70,w98,w132] z) [w1,w4,w7,w50,w60,w70,w98,w127] (n z [w1,w4,w7,w51,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababaaa : ReplayTree.all (blocked 6 t6) t7ababaaa = true := by
  decide +kernel
def t7ababaab := (n (n (n (n z [w1,w4,w7,w57,w60,w70,w98,w127] z) [w1,w4,w7,w60,w66,w70,w98,w127] z) [w1,w4,w7,w60,w70,w92,w98,w127] (n (n z [w1,w4,w7,w60,w70,w94,w98,w127] z) [w1,w4,w7,w60,w70,w98,w121,w127] z)) [w1,w4,w7,w60,w70,w105,w112,w127] (n (n (n z [w1,w4,w7,w60,w78,w85,w98,w127] z) [w1,w4,w9,w45,w60,w70,w98,w127] z) [w1,w4,w10,w27,w60,w70,w101,w127] (n z [w1,w4,w11,w26,w60,w70,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababaab : ReplayTree.all (blocked 6 t6) t7ababaab = true := by
  decide +kernel
def t7ababaa := (n t7ababaaa [w1,w4,w7,w52,w60,w70,w98,w127] t7ababaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababaa : ReplayTree.all (blocked 6 t6) t7ababaa = true := by
  simp only [t7ababaa, ReplayTree.all, n, ht7ababaaa, ht7ababaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abababa := (n (n (n (n z [w1,w4,w11,w27,w60,w70,w101,w132] z) [w1,w4,w11,w27,w69,w70,w101,w132] z) [w1,w4,w11,w27,w70,w98,w101,w132] (n (n z [w1,w4,w11,w27,w70,w101,w127,w132] z) [w1,w4,w11,w27,w70,w101,w132] z)) [w1,w4,w11,w30,w60,w70,w101,w127] (n (n (n z [w1,w4,w11,w31,w60,w69,w101,w127] z) [w1,w4,w11,w32,w60,w70,w101,w127] z) [w1,w4,w11,w35,w60,w70,w101,w127] (n z [w1,w4,w11,w38,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abababa : ReplayTree.all (blocked 6 t6) t7abababa = true := by
  decide +kernel
def t7abababb := (n (n (n (n z [w1,w4,w11,w45,w60,w70,w101,w127] z) [w1,w4,w11,w60,w70,w83,w101,w127] z) [w1,w4,w11,w60,w70,w85,w101,w127] (n (n z [w1,w4,w11,w60,w70,w101,w112,w127] z) [w1,w4,w11,w60,w70,w101,w116,w127] z)) [w1,w4,w14,w27,w60,w70,w101,w127] (n (n (n z [w1,w4,w15,w27,w60,w69,w101,w127] z) [w1,w4,w16,w27,w60,w70,w101,w127] z) [w1,w4,w16,w32,w60,w69,w101,w127] (n z [w1,w4,w19,w27,w60,w70,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abababb : ReplayTree.all (blocked 6 t6) t7abababb = true := by
  decide +kernel
def t7ababab := (n t7abababa [w1,w4,w11,w39,w60,w70,w101,w127] t7abababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababab : ReplayTree.all (blocked 6 t6) t7ababab = true := by
  simp only [t7ababab, ReplayTree.all, n, ht7abababa, ht7abababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ababa := (n t7ababaa [w1,w4,w11,w27,w60,w70,w101,w127] t7ababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababa : ReplayTree.all (blocked 6 t6) t7ababa = true := by
  simp only [t7ababa, ReplayTree.all, n, ht7ababaa, ht7ababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ababbaa := (n (n (n (n z [w1,w4,w23,w27,w60,w70,w101,w127] z) [w1,w4,w23,w39,w60,w70,w98,w127] z) [w1,w4,w27,w45,w60,w70,w101,w127] (n (n z [w1,w4,w27,w60,w70,w76,w101,w127] z) [w1,w4,w27,w60,w70,w78,w101,w127] z)) [w1,w4,w27,w60,w70,w101,w105,w127] (n (n (n z [w1,w4,w27,w60,w70,w101,w109,w127] z) [w1,w4,w45,w60,w69,w70,w101,w127] z) [w1,w4,w45,w60,w70,w98,w101,w127] (n z [w1,w4,w45,w60,w70,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababbaa : ReplayTree.all (blocked 6 t6) t7ababbaa = true := by
  decide +kernel
def t7ababbab := (n (n (n (n z [w1,w5,w7,w11,w60,w69,w112,w127] z) [w1,w5,w7,w11,w60,w83,w98,w127] z) [w1,w5,w7,w27,w60,w69,w105,w127] (n (n z [w1,w5,w7,w27,w60,w76,w98,w127] z) [w1,w5,w7,w45,w60,w69,w98,w127] z)) [w1,w5,w11,w27,w60,w69,w101,w127] (n (n (n z [w1,w6,w7,w10,w60,w83,w98,w127] z) [w1,w6,w7,w11,w27,w70,w98,w132] z) [w1,w6,w7,w11,w32,w69,w98,w132] (n z [w1,w6,w7,w11,w60,w69,w111,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababbab : ReplayTree.all (blocked 6 t6) t7ababbab = true := by
  decide +kernel
def t7ababba := (n t7ababbaa [w1,w5,w7,w11,w27,w69,w98,w132] t7ababbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababba : ReplayTree.all (blocked 6 t6) t7ababba = true := by
  simp only [t7ababba, ReplayTree.all, n, ht7ababbaa, ht7ababbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ababbba := (n (n (n (n z [w1,w6,w7,w11,w60,w82,w98,w127] z) [w1,w6,w7,w11,w60,w83,w98,w127] z) [w1,w6,w7,w11,w60,w83,w98,w132] (n (n z [w1,w6,w7,w11,w60,w83,w101,w127] z) [w1,w6,w7,w11,w60,w85,w98,w127] z)) [w1,w6,w7,w11,w60,w92,w98,w127] (n (n (n z [w1,w6,w7,w14,w60,w83,w98,w127] z) [w1,w6,w7,w16,w27,w69,w98,w132] z) [w1,w6,w7,w16,w60,w69,w112,w127] (n z [w1,w6,w7,w16,w60,w83,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababbba : ReplayTree.all (blocked 6 t6) t7ababbba = true := by
  decide +kernel
def t7ababbbb := (n (n (n (n z [w1,w6,w7,w21,w60,w83,w98,w127] z) [w1,w6,w7,w23,w60,w83,w98,w127] z) [w1,w6,w7,w26,w60,w76,w98,w127] (n z [w1,w6,w7,w27,w60,w69,w104,w127] z)) [w1,w6,w7,w27,w60,w70,w105,w127] (n (n (n z [w1,w6,w7,w27,w60,w75,w98,w127] z) [w1,w6,w7,w27,w60,w76,w98,w127] z) [w1,w6,w7,w27,w60,w76,w98,w132] (n z [w1,w6,w7,w27,w60,w76,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababbbb : ReplayTree.all (blocked 6 t6) t7ababbbb = true := by
  decide +kernel
def t7ababbb := (n t7ababbba [w1,w6,w7,w19,w60,w83,w98,w127] t7ababbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababbb : ReplayTree.all (blocked 6 t6) t7ababbb = true := by
  simp only [t7ababbb, ReplayTree.all, n, ht7ababbba, ht7ababbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ababb := (n t7ababba [w1,w6,w7,w11,w60,w70,w112,w127] t7ababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ababb : ReplayTree.all (blocked 6 t6) t7ababb = true := by
  simp only [t7ababb, ReplayTree.all, n, ht7ababba, ht7ababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abab := (n t7ababa [w1,w4,w22,w27,w60,w70,w98,w127] t7ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abab : ReplayTree.all (blocked 6 t6) t7abab = true := by
  simp only [t7abab, ReplayTree.all, n, ht7ababa, ht7ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aba := (n t7abaa [w1,w4,w7,w43,w60,w70,w98,w127] t7abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7aba : ReplayTree.all (blocked 6 t6) t7aba = true := by
  simp only [t7aba, ReplayTree.all, n, ht7abaa, ht7abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbaaaa := (n (n (n (n z [w1,w6,w7,w27,w60,w92,w98,w127] z) [w1,w6,w7,w30,w60,w76,w98,w127] z) [w1,w6,w7,w32,w60,w69,w105,w127] (n (n z [w1,w6,w7,w32,w60,w76,w98,w127] z) [w1,w6,w7,w35,w60,w76,w98,w127] z)) [w1,w6,w7,w37,w60,w76,w98,w127] (n (n (n z [w1,w6,w7,w39,w60,w76,w98,w127] z) [w1,w6,w7,w42,w60,w69,w98,w127] z) [w1,w6,w7,w43,w60,w69,w98,w127] (n z [w1,w6,w7,w44,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaaaa : ReplayTree.all (blocked 6 t6) t7abbaaaa = true := by
  decide +kernel
def t7abbaaab := (n (n (n (n z [w1,w6,w7,w45,w60,w69,w98,w129] z) [w1,w6,w7,w45,w60,w69,w98,w131] z) [w1,w6,w7,w45,w60,w69,w98,w132] (n (n z [w1,w6,w7,w45,w60,w69,w101,w127] z) [w1,w6,w7,w45,w60,w70,w98,w127] z)) [w1,w6,w7,w45,w60,w76,w98,w127] (n (n (n z [w1,w6,w7,w45,w60,w83,w98,w127] z) [w1,w6,w7,w45,w60,w92,w98,w127] z) [w1,w6,w7,w50,w60,w69,w98,w127] (n z [w1,w6,w7,w52,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaaab : ReplayTree.all (blocked 6 t6) t7abbaaab = true := by
  decide +kernel
def t7abbaaa := (n t7abbaaaa [w1,w6,w7,w45,w60,w69,w98,w127] t7abbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaaa : ReplayTree.all (blocked 6 t6) t7abbaaa = true := by
  simp only [t7abbaaa, ReplayTree.all, n, ht7abbaaaa, ht7abbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbaaba := (n (n (n (n z [w1,w6,w7,w59,w60,w69,w98,w127] z) [w1,w6,w7,w60,w66,w69,w98,w127] z) [w1,w6,w7,w60,w69,w92,w98,w127] (n (n z [w1,w6,w7,w60,w69,w98,w121,w127] z) [w1,w6,w7,w60,w69,w105,w112,w127] z)) [w1,w6,w7,w60,w76,w83,w98,w127] (n (n (n z [w1,w6,w7,w60,w76,w92,w98,w127] z) [w1,w6,w7,w60,w76,w98,w112,w127] z) [w1,w6,w7,w60,w83,w92,w98,w127] (n z [w1,w6,w7,w60,w83,w98,w105,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaaba : ReplayTree.all (blocked 6 t6) t7abbaaba = true := by
  decide +kernel
def t7abbaabb := (n (n (n (n z [w1,w6,w9,w45,w60,w69,w98,w127] z) [w1,w6,w10,w27,w60,w69,w101,w127] z) [w1,w6,w11,w26,w60,w69,w101,w127] (n (n z [w1,w6,w11,w27,w60,w69,w101,w127] z) [w1,w6,w11,w27,w60,w69,w101,w131] z)) [w1,w6,w11,w27,w60,w69,w101,w132] (n (n (n z [w1,w6,w11,w27,w60,w70,w101,w127] z) [w1,w6,w11,w30,w60,w69,w101,w127] z) [w1,w6,w11,w32,w60,w69,w101,w127] (n z [w1,w6,w11,w35,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaabb : ReplayTree.all (blocked 6 t6) t7abbaabb = true := by
  decide +kernel
def t7abbaab := (n t7abbaaba [w1,w6,w7,w60,w92,w98,w127] t7abbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaab : ReplayTree.all (blocked 6 t6) t7abbaab = true := by
  simp only [t7abbaab, ReplayTree.all, n, ht7abbaaba, ht7abbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbaa := (n t7abbaaa [w1,w6,w7,w57,w60,w69,w98,w127] t7abbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaa : ReplayTree.all (blocked 6 t6) t7abbaa = true := by
  simp only [t7abbaa, ReplayTree.all, n, ht7abbaaa, ht7abbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbabaa := (n (n (n (n z [w1,w6,w11,w38,w60,w69,w98,w127] z) [w1,w6,w11,w39,w60,w69,w101,w127] z) [w1,w6,w11,w45,w60,w69,w101,w127] (n (n z [w1,w6,w11,w60,w69,w83,w101,w127] z) [w1,w6,w11,w60,w69,w101,w112,w127] z)) [w1,w6,w11,w60,w69,w101,w116,w127] (n (n (n z [w1,w6,w14,w27,w60,w69,w101,w127] z) [w1,w6,w16,w27,w60,w69,w101,w127] z) [w1,w6,w19,w27,w60,w69,w101,w127] (n z [w1,w6,w21,w27,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbabaa : ReplayTree.all (blocked 6 t6) t7abbabaa = true := by
  decide +kernel
def t7abbabab := (n (n (n (n z [w1,w6,w23,w27,w60,w69,w101,w127] z) [w1,w6,w23,w39,w60,w69,w98,w127] z) [w1,w6,w27,w45,w60,w69,w101,w127] (n (n z [w1,w6,w27,w60,w69,w76,w101,w127] z) [w1,w6,w27,w60,w69,w101,w105,w127] z)) [w1,w6,w27,w60,w69,w101,w109,w127] (n (n (n z [w1,w6,w45,w60,w69,w98,w101,w127] z) [w1,w6,w45,w60,w69,w101,w127] z) [w1,w7,w10,w35,w60,w70,w98,w127] (n z [w1,w7,w11,w19,w27,w70,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbabab : ReplayTree.all (blocked 6 t6) t7abbabab = true := by
  decide +kernel
def t7abbaba := (n t7abbabaa [w1,w6,w22,w27,w60,w69,w98,w127] t7abbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbaba : ReplayTree.all (blocked 6 t6) t7abbaba = true := by
  simp only [t7abbaba, ReplayTree.all, n, ht7abbabaa, ht7abbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbabba := (n (n (n (n z [w1,w7,w11,w27,w60,w70,w98,w130] z) [w1,w7,w11,w27,w60,w73,w98,w127] z) [w1,w7,w11,w27,w63,w70,w98,w127] (n (n z [w1,w7,w11,w27,w64,w70,w98,w132] z) [w1,w7,w11,w27,w70,w72,w98,w132] z)) [w1,w7,w11,w27,w70,w74,w98,w132] (n (n (n z [w1,w7,w11,w27,w70,w98,w131,w132] z) [w1,w7,w11,w27,w70,w98,w132,w136] z) [w1,w7,w11,w31,w60,w69,w98,w131] (n z [w1,w7,w11,w33,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbabba : ReplayTree.all (blocked 6 t6) t7abbabba = true := by
  decide +kernel
def t7abbabbb := (n (n (n (n z [w1,w7,w11,w35,w60,w70,w98,w127] z) [w1,w7,w11,w35,w60,w70,w98,w129] z) [w1,w7,w11,w35,w60,w70,w98,w132] (n z [w1,w7,w11,w35,w60,w70,w101,w127] z)) [w1,w7,w11,w36,w60,w69,w98,w127] (n (n (n z [w1,w7,w11,w37,w60,w70,w98,w127] z) [w1,w7,w11,w57,w60,w70,w98,w127] z) [w1,w7,w11,w60,w70,w83,w98,w131] (n z [w1,w7,w11,w60,w70,w87,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbabbb : ReplayTree.all (blocked 6 t6) t7abbabbb = true := by
  decide +kernel
def t7abbabb := (n t7abbabba [w1,w7,w11,w34,w60,w70,w98,w127] t7abbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbabb : ReplayTree.all (blocked 6 t6) t7abbabb = true := by
  simp only [t7abbabb, ReplayTree.all, n, ht7abbabba, ht7abbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbab := (n t7abbaba [w1,w7,w11,w27,w35,w70,w98,w132] t7abbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbab : ReplayTree.all (blocked 6 t6) t7abbab = true := by
  simp only [t7abbab, ReplayTree.all, n, ht7abbaba, ht7abbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abba := (n t7abbaa [w1,w6,w11,w37,w60,w69,w101,w127] t7abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abba : ReplayTree.all (blocked 6 t6) t7abba = true := by
  simp only [t7abba, ReplayTree.all, n, ht7abbaa, ht7abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbbaaa := (n (n (n (n z [w1,w7,w11,w60,w74,w83,w98,w127] z) [w1,w7,w11,w60,w74,w85,w98,w127] z) [w1,w7,w14,w35,w60,w70,w98,w127] (n (n z [w1,w7,w15,w27,w60,w69,w98,w131] z) [w1,w7,w15,w35,w60,w69,w98,w127] z)) [w1,w7,w16,w32,w60,w69,w98,w131] (n (n (n z [w1,w7,w16,w35,w60,w70,w98,w127] z) [w1,w7,w16,w37,w60,w69,w98,w127] z) [w1,w7,w17,w27,w60,w70,w98,w127] (n z [w1,w7,w18,w27,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbaaa : ReplayTree.all (blocked 6 t6) t7abbbaaa = true := by
  decide +kernel
def t7abbbaab := (n (n (n (n z [w1,w7,w19,w27,w60,w70,w98,w127] z) [w1,w7,w19,w27,w60,w70,w98,w129] z) [w1,w7,w19,w27,w60,w70,w98,w132] (n (n z [w1,w7,w19,w27,w60,w70,w101,w127] z) [w1,w7,w19,w30,w60,w70,w98,w127] z)) [w1,w7,w19,w31,w60,w69,w98,w127] (n (n (n z [w1,w7,w19,w32,w60,w70,w98,w127] z) [w1,w7,w19,w35,w60,w70,w98,w127] z) [w1,w7,w19,w39,w60,w70,w98,w127] (n z [w1,w7,w19,w45,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbaab : ReplayTree.all (blocked 6 t6) t7abbbaab = true := by
  decide +kernel
def t7abbbaa := (n t7abbbaaa [w1,w7,w19,w26,w60,w70,w98,w127] t7abbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbaa : ReplayTree.all (blocked 6 t6) t7abbbaa = true := by
  simp only [t7abbbaa, ReplayTree.all, n, ht7abbbaaa, ht7abbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbbaba := (n (n (n (n z [w1,w7,w19,w60,w70,w83,w98,w127] z) [w1,w7,w19,w60,w70,w85,w98,w127] z) [w1,w7,w19,w60,w70,w98,w112,w127] (n (n z [w1,w7,w20,w27,w60,w69,w98,w127] z) [w1,w7,w21,w27,w60,w70,w98,w127] z)) [w1,w7,w21,w32,w60,w69,w98,w127] (n (n (n z [w1,w7,w21,w37,w60,w69,w98,w127] z) [w1,w7,w23,w35,w60,w70,w98,w127] z) [w1,w7,w27,w57,w60,w70,w98,w127] (n z [w1,w7,w27,w60,w70,w76,w98,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbaba : ReplayTree.all (blocked 6 t6) t7abbbaba = true := by
  decide +kernel
def t7abbbabb := (n (n (n (n z [w1,w7,w27,w60,w70,w81,w98,w127] z) [w1,w7,w27,w60,w74,w76,w98,w127] z) [w1,w7,w27,w60,w74,w78,w98,w127] (n (n z [w1,w7,w35,w45,w60,w70,w98,w127] z) [w1,w7,w35,w57,w60,w70,w98,w127] z)) [w1,w7,w35,w60,w70,w76,w98,w127] (n (n (n z [w1,w7,w35,w60,w70,w78,w98,w127] z) [w1,w7,w35,w60,w70,w98,w105,w127] z) [w1,w7,w45,w57,w60,w70,w98,w127] (n z [w1,w7,w45,w60,w64,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbabb : ReplayTree.all (blocked 6 t6) t7abbbabb = true := by
  decide +kernel
def t7abbbab := (n t7abbbaba [w1,w7,w27,w60,w70,w80,w98,w127] t7abbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbab : ReplayTree.all (blocked 6 t6) t7abbbab = true := by
  simp only [t7abbbab, ReplayTree.all, n, ht7abbbaba, ht7abbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbba := (n t7abbbaa [w1,w7,w19,w57,w60,w70,w98,w127] t7abbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbba : ReplayTree.all (blocked 6 t6) t7abbba = true := by
  simp only [t7abbba, ReplayTree.all, n, ht7abbbaa, ht7abbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbbbaa := (n (n (n (n z [w1,w7,w45,w60,w69,w74,w98,w127] z) [w1,w7,w45,w60,w70,w72,w98,w127] z) [w1,w7,w45,w60,w70,w74,w98,w127] (n (n z [w1,w7,w45,w60,w70,w98,w127,w131] z) [w1,w7,w57,w60,w69,w70,w98,w127] z)) [w1,w7,w57,w60,w70,w98,w127] (n (n (n z [w1,w11,w27,w60,w64,w70,w101,w127] z) [w1,w11,w27,w60,w69,w70,w101,w131] z) [w1,w11,w27,w60,w69,w74,w101,w127] (n z [w1,w11,w27,w60,w70,w72,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbbaa : ReplayTree.all (blocked 6 t6) t7abbbbaa = true := by
  decide +kernel
def t7abbbbab := (n (n (n (n z [w1,w11,w27,w60,w70,w101,w127,w131] z) [w2,w3,w7,w14,w60,w69,w112,w127] z) [w2,w3,w7,w14,w60,w83,w98,w127] (n (n z [w2,w3,w7,w30,w60,w69,w105,w127] z) [w2,w3,w7,w30,w60,w76,w98,w127] z)) [w2,w3,w7,w45,w60,w69,w98,w129] (n (n (n z [w2,w3,w7,w50,w60,w69,w98,w127] z) [w2,w3,w9,w11,w60,w69,w112,w127] z) [w2,w3,w9,w27,w60,w69,w105,w127] (n z [w2,w3,w9,w45,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbbab : ReplayTree.all (blocked 6 t6) t7abbbbab = true := by
  decide +kernel
def t7abbbba := (n t7abbbbaa [w1,w11,w27,w60,w70,w74,w101,w127] t7abbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbba : ReplayTree.all (blocked 6 t6) t7abbbba = true := by
  simp only [t7abbbba, ReplayTree.all, n, ht7abbbbaa, ht7abbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbbbba := (n (n (n (n z [w2,w3,w14,w27,w60,w69,w101,w127] z) [w2,w4,w7,w9,w11,w69,w112,w132] z) [w2,w4,w7,w9,w11,w83,w98,w132] (n (n z [w2,w4,w7,w9,w27,w69,w105,w132] z) [w2,w4,w7,w9,w27,w76,w98,w132] z)) [w2,w4,w7,w9,w45,w69,w98,w132] (n (n (n z [w2,w4,w7,w9,w60,w69,w121,w127] z) [w2,w4,w7,w9,w60,w76,w112,w127] z) [w2,w4,w7,w9,w60,w83,w105,w127] (n z [w2,w4,w7,w9,w60,w92,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbbba : ReplayTree.all (blocked 6 t6) t7abbbbba = true := by
  decide +kernel
def t7abbbbbb := (n (n (n (n z [w2,w4,w7,w11,w14,w83,w98,w132] z) [w2,w4,w7,w11,w27,w69,w98,w133] z) [w2,w4,w7,w11,w27,w69,w99,w132] (n z [w2,w4,w7,w11,w28,w69,w98,w132] z)) [w2,w4,w7,w11,w30,w69,w112,w132] (n (n (n z [w2,w4,w7,w11,w30,w83,w98,w132] z) [w2,w4,w7,w11,w60,w69,w111,w129] z) [w2,w4,w7,w11,w60,w69,w112,w128] (n z [w2,w4,w7,w11,w60,w69,w113,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbbbb : ReplayTree.all (blocked 6 t6) t7abbbbbb = true := by
  decide +kernel
def t7abbbbb := (n t7abbbbba [w2,w4,w7,w11,w14,w69,w112,w132] t7abbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbbb : ReplayTree.all (blocked 6 t6) t7abbbbb = true := by
  simp only [t7abbbbb, ReplayTree.all, n, ht7abbbbba, ht7abbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbbb := (n t7abbbba [w2,w3,w11,w30,w60,w69,w101,w127] t7abbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbbb : ReplayTree.all (blocked 6 t6) t7abbbb = true := by
  simp only [t7abbbb, ReplayTree.all, n, ht7abbbba, ht7abbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbb := (n t7abbba [w1,w7,w45,w60,w69,w70,w98,w131] t7abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abbb : ReplayTree.all (blocked 6 t6) t7abbb = true := by
  simp only [t7abbb, ReplayTree.all, n, ht7abbba, ht7abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abb := (n t7abba [w1,w7,w11,w60,w70,w88,w98,w127] t7abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7abb : ReplayTree.all (blocked 6 t6) t7abb = true := by
  simp only [t7abb, ReplayTree.all, n, ht7abba, ht7abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ab := (n t7aba [w1,w6,w7,w27,w60,w78,w98,w127] t7abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ab : ReplayTree.all (blocked 6 t6) t7ab = true := by
  simp only [t7ab, ReplayTree.all, n, ht7aba, ht7abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7a := (n t7aa [w1,w2,w7,w60,w80,w92,w98,w127] t7ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7a : ReplayTree.all (blocked 6 t6) t7a = true := by
  simp only [t7a, ReplayTree.all, n, ht7aa, ht7ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaaaaa := (n (n (n (n z [w2,w4,w7,w11,w60,w83,w98,w128] z) [w2,w4,w7,w11,w60,w83,w99,w127] z) [w2,w4,w7,w11,w61,w69,w112,w127] (n (n z [w2,w4,w7,w11,w61,w83,w98,w127] z) [w2,w4,w7,w11,w62,w69,w112,w132] z)) [w2,w4,w7,w11,w62,w83,w98,w132] (n (n (n z [w2,w4,w7,w11,w69,w100,w112,w132] z) [w2,w4,w7,w11,w69,w112,w114,w132] z) [w2,w4,w7,w11,w69,w112,w129,w132] (n z [w2,w4,w7,w11,w69,w112,w132,w134] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaaaa : ReplayTree.all (blocked 6 t6) t7baaaaaa = true := by
  decide +kernel
def t7baaaaab := (n (n (n (n z [w2,w4,w7,w11,w83,w98,w129,w132] z) [w2,w4,w7,w11,w83,w98,w132,w134] z) [w2,w4,w7,w12,w27,w69,w98,w132] (n (n z [w2,w4,w7,w12,w60,w69,w112,w127] z) [w2,w4,w7,w12,w60,w83,w98,w127] z)) [w2,w4,w7,w13,w60,w69,w112,w127] (n (n (n z [w2,w4,w7,w13,w60,w83,w98,w127] z) [w2,w4,w7,w14,w27,w69,w105,w132] z) [w2,w4,w7,w14,w27,w76,w98,w132] (n z [w2,w4,w7,w14,w45,w69,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaaab : ReplayTree.all (blocked 6 t6) t7baaaaab = true := by
  decide +kernel
def t7baaaaa := (n t7baaaaaa [w2,w4,w7,w11,w83,w98,w100,w132] t7baaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaaa : ReplayTree.all (blocked 6 t6) t7baaaaa = true := by
  simp only [t7baaaaa, ReplayTree.all, n, ht7baaaaaa, ht7baaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaaaba := (n (n (n (n z [w2,w4,w7,w14,w60,w69,w112,w127] z) [w2,w4,w7,w14,w60,w69,w112,w132] z) [w2,w4,w7,w14,w60,w69,w116,w127] (n (n z [w2,w4,w7,w14,w60,w69,w121,w127] z) [w2,w4,w7,w14,w60,w70,w112,w127] z)) [w2,w4,w7,w14,w60,w76,w112,w127] (n (n (n z [w2,w4,w7,w14,w60,w82,w98,w127] z) [w2,w4,w7,w14,w60,w83,w98,w127] z) [w2,w4,w7,w14,w60,w83,w98,w132] (n z [w2,w4,w7,w14,w60,w83,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaaba : ReplayTree.all (blocked 6 t6) t7baaaaba = true := by
  decide +kernel
def t7baaaabb := (n (n (n (n z [w2,w4,w7,w14,w60,w83,w112,w127] z) [w2,w4,w7,w14,w60,w85,w98,w127] z) [w2,w4,w7,w14,w60,w92,w98,w127] (n (n z [w2,w4,w7,w25,w60,w69,w112,w127] z) [w2,w4,w7,w25,w60,w83,w98,w127] z)) [w2,w4,w7,w27,w30,w69,w105,w132] (n (n (n z [w2,w4,w7,w27,w30,w76,w98,w132] z) [w2,w4,w7,w27,w60,w69,w104,w129] z) [w2,w4,w7,w27,w60,w69,w105,w128] (n z [w2,w4,w7,w27,w60,w69,w106,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaabb : ReplayTree.all (blocked 6 t6) t7baaaabb = true := by
  decide +kernel
def t7baaaab := (n t7baaaaba [w2,w4,w7,w14,w60,w83,w105,w127] t7baaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaab : ReplayTree.all (blocked 6 t6) t7baaaab = true := by
  simp only [t7baaaab, ReplayTree.all, n, ht7baaaaba, ht7baaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaaa := (n t7baaaaa [w2,w4,w7,w14,w60,w69,w111,w127] t7baaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaa : ReplayTree.all (blocked 6 t6) t7baaaa = true := by
  simp only [t7baaaa, ReplayTree.all, n, ht7baaaaa, ht7baaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaabaa := (n (n (n (n z [w2,w4,w7,w27,w60,w76,w98,w128] z) [w2,w4,w7,w27,w60,w76,w99,w127] z) [w2,w4,w7,w27,w61,w69,w105,w127] (n (n z [w2,w4,w7,w27,w61,w76,w98,w127] z) [w2,w4,w7,w27,w62,w69,w105,w132] z)) [w2,w4,w7,w27,w62,w76,w98,w132] (n (n (n z [w2,w4,w7,w27,w69,w100,w105,w132] z) [w2,w4,w7,w27,w69,w105,w107,w132] z) [w2,w4,w7,w27,w69,w105,w129,w132] (n z [w2,w4,w7,w27,w69,w105,w132,w134] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaabaa : ReplayTree.all (blocked 6 t6) t7baaabaa = true := by
  decide +kernel
def t7baaabab := (n (n (n (n z [w2,w4,w7,w27,w76,w98,w129,w132] z) [w2,w4,w7,w27,w76,w98,w132,w134] z) [w2,w4,w7,w28,w60,w69,w105,w127] (n (n z [w2,w4,w7,w28,w60,w76,w98,w127] z) [w2,w4,w7,w29,w60,w69,w105,w127] z)) [w2,w4,w7,w29,w60,w76,w98,w127] (n (n (n z [w2,w4,w7,w30,w45,w69,w98,w132] z) [w2,w4,w7,w30,w60,w69,w104,w127] z) [w2,w4,w7,w30,w60,w69,w105,w127] (n z [w2,w4,w7,w30,w60,w69,w105,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaabab : ReplayTree.all (blocked 6 t6) t7baaabab = true := by
  decide +kernel
def t7baaaba := (n t7baaabaa [w2,w4,w7,w27,w76,w98,w100,w132] t7baaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaaba : ReplayTree.all (blocked 6 t6) t7baaaba = true := by
  simp only [t7baaaba, ReplayTree.all, n, ht7baaabaa, ht7baaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaabba := (n (n (n (n z [w2,w4,w7,w30,w60,w69,w121,w127] z) [w2,w4,w7,w30,w60,w70,w105,w127] z) [w2,w4,w7,w30,w60,w75,w98,w127] (n (n z [w2,w4,w7,w30,w60,w76,w98,w127] z) [w2,w4,w7,w30,w60,w76,w98,w132] z)) [w2,w4,w7,w30,w60,w76,w101,w127] (n (n (n z [w2,w4,w7,w30,w60,w76,w105,w127] z) [w2,w4,w7,w30,w60,w76,w112,w127] z) [w2,w4,w7,w30,w60,w78,w98,w127] (n z [w2,w4,w7,w30,w60,w83,w105,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaabba : ReplayTree.all (blocked 6 t6) t7baaabba = true := by
  decide +kernel
def t7baaabbb := (n (n (n (n z [w2,w4,w7,w41,w60,w69,w105,w127] z) [w2,w4,w7,w41,w60,w76,w98,w127] z) [w2,w4,w7,w42,w60,w69,w98,w129] (n (n z [w2,w4,w7,w43,w60,w69,w98,w129] z) [w2,w4,w7,w44,w60,w69,w98,w129] z)) [w2,w4,w7,w45,w50,w69,w98,w132] (n (n (n z [w2,w4,w7,w45,w60,w69,w98,w128] z) [w2,w4,w7,w45,w60,w69,w98,w129] z) [w2,w4,w7,w45,w60,w69,w98,w134] (n z [w2,w4,w7,w45,w60,w69,w99,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaabbb : ReplayTree.all (blocked 6 t6) t7baaabbb = true := by
  decide +kernel
def t7baaabb := (n t7baaabba [w2,w4,w7,w30,w60,w92,w98,w127] t7baaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaabb : ReplayTree.all (blocked 6 t6) t7baaabb = true := by
  simp only [t7baaabb, ReplayTree.all, n, ht7baaabba, ht7baaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaab := (n t7baaaba [w2,w4,w7,w30,w60,w69,w109,w127] t7baaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaab : ReplayTree.all (blocked 6 t6) t7baaab = true := by
  simp only [t7baaab, ReplayTree.all, n, ht7baaaba, ht7baaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaa := (n t7baaaa [w2,w4,w7,w27,w60,w75,w98,w129] t7baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaa : ReplayTree.all (blocked 6 t6) t7baaa = true := by
  simp only [t7baaa, ReplayTree.all, n, ht7baaaa, ht7baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baabaaa := (n (n (n (n z [w2,w4,w7,w45,w61,w69,w98,w127] z) [w2,w4,w7,w45,w62,w69,w98,w132] z) [w2,w4,w7,w45,w69,w98,w100,w132] (n (n z [w2,w4,w7,w45,w69,w98,w129,w132] z) [w2,w4,w7,w45,w69,w98,w132,w134] z)) [w2,w4,w7,w46,w60,w69,w98,w127] (n (n (n z [w2,w4,w7,w47,w60,w69,w98,w127] z) [w2,w4,w7,w48,w60,w69,w98,w127] z) [w2,w4,w7,w49,w60,w69,w98,w127] (n z [w2,w4,w7,w50,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabaaa : ReplayTree.all (blocked 6 t6) t7baabaaa = true := by
  decide +kernel
def t7baabaab := (n (n (n (n z [w2,w4,w7,w50,w60,w69,w98,w131] z) [w2,w4,w7,w50,w60,w69,w98,w132] z) [w2,w4,w7,w50,w60,w69,w101,w127] (n (n z [w2,w4,w7,w50,w60,w69,w105,w127] z) [w2,w4,w7,w50,w60,w69,w112,w127] z)) [w2,w4,w7,w50,w60,w69,w121,w127] (n (n (n z [w2,w4,w7,w50,w60,w70,w98,w127] z) [w2,w4,w7,w50,w60,w76,w98,w127] z) [w2,w4,w7,w50,w60,w83,w98,w127] (n z [w2,w4,w7,w50,w60,w92,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabaab : ReplayTree.all (blocked 6 t6) t7baabaab = true := by
  decide +kernel
def t7baabaa := (n t7baabaaa [w2,w4,w7,w50,w60,w69,w98,w129] t7baabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabaa : ReplayTree.all (blocked 6 t6) t7baabaa = true := by
  simp only [t7baabaa, ReplayTree.all, n, ht7baabaaa, ht7baabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baababa := (n (n (n (n z [w2,w4,w7,w57,w60,w69,w98,w129] z) [w2,w4,w7,w60,w62,w69,w121,w127] z) [w2,w4,w7,w60,w62,w76,w112,w127] (n (n z [w2,w4,w7,w60,w62,w83,w105,w127] z) [w2,w4,w7,w60,w62,w92,w98,w127] z)) [w2,w4,w7,w60,w66,w69,w98,w129] (n (n (n z [w2,w4,w7,w60,w68,w69,w98,w127] z) [w2,w4,w7,w60,w69,w92,w98,w129] z) [w2,w4,w7,w60,w69,w98,w121,w129] (n z [w2,w4,w7,w60,w69,w98,w123,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baababa : ReplayTree.all (blocked 6 t6) t7baababa = true := by
  decide +kernel
def t7baababb := (n (n (n (n z [w2,w4,w7,w60,w69,w105,w112,w129] z) [w2,w4,w7,w60,w69,w105,w114,w127] z) [w2,w4,w7,w60,w69,w105,w123,w127] (n (n z [w2,w4,w7,w60,w69,w107,w112,w127] z) [w2,w4,w7,w60,w69,w107,w121,w127] z)) [w2,w4,w7,w60,w69,w112,w123,w127] (n (n (n z [w2,w4,w7,w60,w69,w114,w121,w127] z) [w2,w4,w7,w60,w69,w121,w123,w127] z) [w2,w4,w7,w60,w69,w121,w127,w129] (n z [w2,w4,w7,w60,w76,w83,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baababb : ReplayTree.all (blocked 6 t6) t7baababb = true := by
  decide +kernel
def t7baabab := (n t7baababa [w2,w4,w7,w60,w69,w100,w121,w127] t7baababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabab : ReplayTree.all (blocked 6 t6) t7baabab = true := by
  simp only [t7baabab, ReplayTree.all, n, ht7baababa, ht7baababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaba := (n t7baabaa [w2,w4,w7,w52,w60,w69,w98,w129] t7baabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baaba : ReplayTree.all (blocked 6 t6) t7baaba = true := by
  simp only [t7baaba, ReplayTree.all, n, ht7baabaa, ht7baabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baabbaa := (n (n (n (n z [w2,w4,w7,w60,w76,w100,w112,w127] z) [w2,w4,w7,w60,w76,w112,w114,w127] z) [w2,w4,w7,w60,w76,w112,w127,w129] (n (n z [w2,w4,w7,w60,w83,w98,w107,w127] z) [w2,w4,w7,w60,w83,w100,w105,w127] z)) [w2,w4,w7,w60,w83,w105,w107,w127] (n (n (n z [w2,w4,w7,w60,w83,w105,w127,w129] z) [w2,w4,w7,w60,w92,w98,w100,w127] z) [w2,w4,w7,w60,w92,w98,w127,w129] (n z [w2,w4,w8,w11,w27,w69,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabbaa : ReplayTree.all (blocked 6 t6) t7baabbaa = true := by
  decide +kernel
def t7baabbab := (n (n (n (n z [w2,w4,w8,w11,w60,w83,w98,w127] z) [w2,w4,w8,w27,w60,w69,w105,w127] z) [w2,w4,w8,w27,w60,w76,w98,w127] (n (n z [w2,w4,w8,w45,w60,w69,w98,w127] z) [w2,w4,w9,w10,w60,w69,w112,w127] z)) [w2,w4,w9,w11,w27,w69,w101,w132] (n (n (n z [w2,w4,w9,w11,w39,w69,w98,w132] z) [w2,w4,w9,w11,w60,w69,w111,w127] z) [w2,w4,w9,w11,w60,w69,w112,w127] (n z [w2,w4,w9,w11,w60,w69,w112,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabbab : ReplayTree.all (blocked 6 t6) t7baabbab = true := by
  decide +kernel
def t7baabba := (n t7baabbaa [w2,w4,w8,w11,w60,w69,w112,w127] t7baabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabba : ReplayTree.all (blocked 6 t6) t7baabba = true := by
  simp only [t7baabba, ReplayTree.all, n, ht7baabbaa, ht7baabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baabbba := (n (n (n (n z [w2,w4,w9,w11,w60,w69,w121,w127] z) [w2,w4,w9,w11,w60,w70,w112,w127] z) [w2,w4,w9,w11,w60,w82,w98,w127] (n (n z [w2,w4,w9,w11,w60,w83,w101,w127] z) [w2,w4,w9,w14,w60,w69,w112,w127] z)) [w2,w4,w9,w16,w60,w69,w112,w127] (n (n (n z [w2,w4,w9,w19,w60,w69,w112,w127] z) [w2,w4,w9,w23,w27,w69,w98,w132] z) [w2,w4,w9,w23,w60,w69,w112,w127] (n z [w2,w4,w9,w23,w60,w83,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabbba : ReplayTree.all (blocked 6 t6) t7baabbba = true := by
  decide +kernel
def t7baabbbb := (n (n (n (n z [w2,w4,w9,w26,w60,w69,w105,w127] z) [w2,w4,w9,w27,w60,w69,w104,w127] z) [w2,w4,w9,w27,w60,w69,w105,w127] (n z [w2,w4,w9,w27,w60,w69,w105,w132] z)) [w2,w4,w9,w27,w60,w69,w109,w127] (n (n (n z [w2,w4,w9,w27,w60,w69,w121,w127] z) [w2,w4,w9,w27,w60,w70,w105,w127] z) [w2,w4,w9,w27,w60,w75,w98,w127] (n z [w2,w4,w9,w27,w60,w76,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabbbb : ReplayTree.all (blocked 6 t6) t7baabbbb = true := by
  decide +kernel
def t7baabbb := (n t7baabbba [w2,w4,w9,w25,w60,w69,w112,w127] t7baabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabbb : ReplayTree.all (blocked 6 t6) t7baabbb = true := by
  simp only [t7baabbb, ReplayTree.all, n, ht7baabbba, ht7baabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baabb := (n t7baabba [w2,w4,w9,w11,w60,w69,w116,w127] t7baabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baabb : ReplayTree.all (blocked 6 t6) t7baabb = true := by
  simp only [t7baabb, ReplayTree.all, n, ht7baabba, ht7baabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baab := (n t7baaba [w2,w4,w7,w60,w76,w98,w114,w127] t7baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baab : ReplayTree.all (blocked 6 t6) t7baab = true := by
  simp only [t7baab, ReplayTree.all, n, ht7baaba, ht7baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baa := (n t7baaa [w2,w4,w7,w45,w60,w70,w98,w129] t7baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baa : ReplayTree.all (blocked 6 t6) t7baa = true := by
  simp only [t7baa, ReplayTree.all, n, ht7baaa, ht7baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babaaaa := (n (n (n (n z [w2,w4,w9,w32,w60,w69,w105,w127] z) [w2,w4,w9,w35,w60,w69,w105,w127] z) [w2,w4,w9,w39,w60,w69,w105,w127] (n (n z [w2,w4,w9,w39,w60,w76,w98,w127] z) [w2,w4,w9,w41,w60,w69,w105,w127] z)) [w2,w4,w9,w42,w60,w69,w98,w127] (n (n (n z [w2,w4,w9,w43,w60,w69,w98,w127] z) [w2,w4,w9,w44,w60,w69,w98,w127] z) [w2,w4,w9,w45,w60,w69,w98,w127] (n z [w2,w4,w9,w45,w60,w69,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaaaa : ReplayTree.all (blocked 6 t6) t7babaaaa = true := by
  decide +kernel
def t7babaaab := (n (n (n (n z [w2,w4,w9,w45,w60,w69,w98,w132] z) [w2,w4,w9,w45,w60,w69,w101,w127] z) [w2,w4,w9,w45,w60,w69,w105,w127] (n (n z [w2,w4,w9,w45,w60,w69,w112,w127] z) [w2,w4,w9,w45,w60,w69,w121,w127] z)) [w2,w4,w9,w45,w60,w70,w98,w127] (n (n (n z [w2,w4,w9,w50,w60,w69,w98,w127] z) [w2,w4,w9,w52,w60,w69,w98,w127] z) [w2,w4,w9,w57,w60,w69,w98,w127] (n z [w2,w4,w9,w60,w66,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaaab : ReplayTree.all (blocked 6 t6) t7babaaab = true := by
  decide +kernel
def t7babaaa := (n t7babaaaa [w2,w4,w9,w45,w60,w69,w98,w131] t7babaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaaa : ReplayTree.all (blocked 6 t6) t7babaaa = true := by
  simp only [t7babaaa, ReplayTree.all, n, ht7babaaaa, ht7babaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babaaba := (n (n (n (n z [w2,w4,w9,w60,w69,w76,w112,w127] z) [w2,w4,w9,w60,w69,w83,w105,w127] z) [w2,w4,w9,w60,w69,w92,w98,w127] (n (n z [w2,w4,w9,w60,w69,w98,w121,w127] z) [w2,w4,w9,w60,w69,w105,w112,w127] z)) [w2,w4,w9,w60,w69,w105,w121,w127] (n (n (n z [w2,w4,w9,w60,w69,w112,w121,w127] z) [w2,w4,w9,w60,w69,w121,w127] z) [w2,w4,w9,w60,w76,w83,w98,w127] (n z [w2,w4,w10,w30,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaaba : ReplayTree.all (blocked 6 t6) t7babaaba = true := by
  decide +kernel
def t7babaabb := (n (n (n (n z [w2,w4,w11,w27,w30,w69,w101,w132] z) [w2,w4,w11,w27,w60,w69,w101,w128] z) [w2,w4,w11,w27,w60,w69,w102,w127] (n (n z [w2,w4,w11,w27,w61,w69,w101,w127] z) [w2,w4,w11,w27,w62,w69,w101,w132] z)) [w2,w4,w11,w27,w69,w100,w101,w132] (n (n (n z [w2,w4,w11,w27,w69,w101,w103,w132] z) [w2,w4,w11,w27,w69,w101,w129,w132] z) [w2,w4,w11,w27,w69,w101,w132,w134] (n z [w2,w4,w11,w28,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaabb : ReplayTree.all (blocked 6 t6) t7babaabb = true := by
  decide +kernel
def t7babaab := (n t7babaaba [w2,w4,w11,w14,w27,w69,w101,w132] t7babaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaab : ReplayTree.all (blocked 6 t6) t7babaab = true := by
  simp only [t7babaab, ReplayTree.all, n, ht7babaaba, ht7babaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babaa := (n t7babaaa [w2,w4,w9,w60,w68,w69,w98,w127] t7babaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babaa : ReplayTree.all (blocked 6 t6) t7babaa = true := by
  simp only [t7babaa, ReplayTree.all, n, ht7babaaa, ht7babaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bababaa := (n (n (n (n z [w2,w4,w11,w30,w60,w69,w101,w127] z) [w2,w4,w11,w30,w60,w69,w101,w131] z) [w2,w4,w11,w30,w60,w69,w101,w132] (n (n z [w2,w4,w11,w30,w60,w70,w101,w127] z) [w2,w4,w11,w38,w60,w69,w98,w129] z)) [w2,w4,w11,w40,w60,w69,w98,w127] (n (n (n z [w2,w4,w11,w41,w60,w69,w101,w127] z) [w2,w4,w11,w50,w60,w69,w101,w127] z) [w2,w4,w11,w60,w69,w101,w112,w129] (n z [w2,w4,w11,w60,w69,w101,w114,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bababaa : ReplayTree.all (blocked 6 t6) t7bababaa = true := by
  decide +kernel
def t7bababab := (n (n (n (n z [w2,w4,w11,w60,w69,w103,w112,w127] z) [w2,w4,w11,w60,w69,w103,w116,w127] z) [w2,w4,w12,w27,w60,w69,w101,w127] (n (n z [w2,w4,w13,w27,w60,w69,w101,w127] z) [w2,w4,w14,w26,w60,w69,w101,w127] z)) [w2,w4,w14,w27,w60,w69,w101,w127] (n (n (n z [w2,w4,w14,w27,w60,w69,w101,w131] z) [w2,w4,w14,w27,w60,w69,w101,w132] z) [w2,w4,w14,w27,w60,w70,w101,w127] (n z [w2,w4,w14,w30,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bababab : ReplayTree.all (blocked 6 t6) t7bababab = true := by
  decide +kernel
def t7bababa := (n t7bababaa [w2,w4,w11,w60,w69,w101,w117,w127] t7bababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bababa : ReplayTree.all (blocked 6 t6) t7bababa = true := by
  simp only [t7bababa, ReplayTree.all, n, ht7bababaa, ht7bababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bababba := (n (n (n (n z [w2,w4,w14,w35,w60,w69,w101,w127] z) [w2,w4,w14,w38,w60,w69,w98,w127] z) [w2,w4,w14,w39,w60,w69,w101,w127] (n (n z [w2,w4,w14,w45,w60,w69,w101,w127] z) [w2,w4,w14,w50,w60,w69,w101,w127] z)) [w2,w4,w14,w60,w69,w83,w101,w127] (n (n (n z [w2,w4,w14,w60,w69,w101,w112,w127] z) [w2,w4,w14,w60,w69,w101,w116,w127] z) [w2,w4,w16,w30,w60,w69,w101,w127] (n z [w2,w4,w19,w30,w60,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bababba : ReplayTree.all (blocked 6 t6) t7bababba = true := by
  decide +kernel
def t7bababbb := (n (n (n (n z [w2,w4,w22,w30,w60,w69,w98,w127] z) [w2,w4,w23,w30,w60,w69,w101,w127] z) [w2,w4,w23,w39,w60,w69,w98,w129] (n (n z [w2,w4,w23,w41,w60,w69,w98,w127] z) [w2,w4,w24,w27,w60,w69,w98,w127] z)) [w2,w4,w25,w27,w60,w69,w101,w127] (n (n (n z [w2,w4,w25,w39,w60,w69,w98,w127] z) [w2,w4,w25,w41,w60,w69,w98,w127] z) [w2,w4,w27,w50,w60,w69,w101,w127] (n z [w2,w4,w27,w60,w69,w101,w105,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bababbb : ReplayTree.all (blocked 6 t6) t7bababbb = true := by
  decide +kernel
def t7bababb := (n t7bababba [w2,w4,w22,w27,w60,w69,w98,w129] t7bababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bababb : ReplayTree.all (blocked 6 t6) t7bababb = true := by
  simp only [t7bababb, ReplayTree.all, n, ht7bababba, ht7bababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babab := (n t7bababa [w2,w4,w14,w32,w60,w69,w101,w127] t7bababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babab : ReplayTree.all (blocked 6 t6) t7babab = true := by
  simp only [t7babab, ReplayTree.all, n, ht7bababa, ht7bababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baba := (n t7babaa [w2,w4,w11,w29,w60,w69,w101,w127] t7babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7baba : ReplayTree.all (blocked 6 t6) t7baba = true := by
  simp only [t7baba, ReplayTree.all, n, ht7babaa, ht7babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babbaaa := (n (n (n (n z [w2,w4,w27,w60,w69,w101,w110,w127] z) [w2,w4,w27,w60,w69,w103,w105,w127] z) [w2,w4,w27,w60,w69,w103,w109,w127] (n (n z [w2,w4,w30,w45,w60,w69,w101,w127] z) [w2,w4,w30,w50,w60,w69,w101,w127] z)) [w2,w4,w30,w60,w69,w76,w101,w127] (n (n (n z [w2,w4,w30,w60,w69,w101,w105,w127] z) [w2,w4,w30,w60,w69,w101,w109,w127] z) [w2,w4,w45,w50,w60,w69,w101,w127] (n z [w2,w4,w45,w60,w62,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbaaa : ReplayTree.all (blocked 6 t6) t7babbaaa = true := by
  decide +kernel
def t7babbaab := (n (n (n (n z [w2,w4,w45,w60,w69,w98,w103,w127] z) [w2,w4,w45,w60,w69,w100,w101,w127] z) [w2,w4,w45,w60,w69,w101,w103,w127] (n (n z [w2,w4,w45,w60,w69,w101,w127,w129] z) [w2,w4,w50,w60,w69,w98,w101,w127] z)) [w2,w4,w50,w60,w69,w101,w127] (n (n (n z [w2,w6,w7,w14,w60,w69,w112,w127] z) [w2,w6,w7,w14,w60,w83,w98,w127] z) [w2,w6,w7,w30,w60,w69,w105,w127] (n z [w2,w6,w7,w30,w60,w76,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbaab : ReplayTree.all (blocked 6 t6) t7babbaab = true := by
  decide +kernel
def t7babbaa := (n t7babbaaa [w2,w4,w45,w60,w69,w98,w101,w129] t7babbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbaa : ReplayTree.all (blocked 6 t6) t7babbaa = true := by
  simp only [t7babbaa, ReplayTree.all, n, ht7babbaaa, ht7babbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babbaba := (n (n (n (n z [w2,w6,w7,w50,w60,w69,w98,w127] z) [w2,w6,w9,w11,w60,w69,w112,w127] z) [w2,w6,w9,w27,w60,w69,w105,w127] (n (n z [w2,w6,w9,w45,w60,w69,w98,w127] z) [w2,w6,w11,w30,w60,w69,w101,w127] z)) [w2,w6,w14,w27,w60,w69,w101,w127] (n (n (n z [w2,w7,w9,w19,w60,w69,w112,w127] z) [w2,w7,w9,w19,w60,w83,w98,w127] z) [w2,w7,w9,w35,w60,w69,w105,w127] (n z [w2,w7,w9,w35,w60,w76,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbaba : ReplayTree.all (blocked 6 t6) t7babbaba = true := by
  decide +kernel
def t7babbabb := (n (n (n (n z [w2,w7,w9,w57,w60,w69,w98,w127] z) [w2,w7,w10,w30,w60,w69,w98,w131] z) [w2,w7,w10,w35,w60,w69,w98,w129] (n (n z [w2,w7,w11,w27,w60,w69,w99,w131] z) [w2,w7,w11,w27,w60,w71,w98,w129] z)) [w2,w7,w11,w27,w61,w69,w98,w131] (n (n (n z [w2,w7,w11,w27,w62,w69,w98,w136] z) [w2,w7,w11,w27,w63,w69,w98,w129] z) [w2,w7,w11,w27,w64,w69,w98,w134] (n z [w2,w7,w11,w27,w69,w98,w134,w136] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbabb : ReplayTree.all (blocked 6 t6) t7babbabb = true := by
  decide +kernel
def t7babbab := (n t7babbaba [w2,w7,w9,w45,w60,w69,w98,w131] t7babbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbab : ReplayTree.all (blocked 6 t6) t7babbab = true := by
  simp only [t7babbab, ReplayTree.all, n, ht7babbaba, ht7babbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babba := (n t7babbaa [w2,w6,w7,w45,w60,w69,w98,w129] t7babbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babba : ReplayTree.all (blocked 6 t6) t7babba = true := by
  simp only [t7babba, ReplayTree.all, n, ht7babbaa, ht7babbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babbbaa := (n (n (n (n z [w2,w7,w11,w29,w60,w69,w98,w131] z) [w2,w7,w11,w30,w35,w69,w98,w132] z) [w2,w7,w11,w30,w60,w69,w98,w130] (n (n z [w2,w7,w11,w30,w60,w69,w98,w131] z) [w2,w7,w11,w30,w60,w69,w98,w136] z)) [w2,w7,w11,w30,w60,w69,w101,w131] (n (n (n z [w2,w7,w11,w30,w60,w71,w98,w127] z) [w2,w7,w11,w30,w63,w69,w98,w127] z) [w2,w7,w11,w30,w64,w69,w98,w132] (n z [w2,w7,w11,w33,w60,w69,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbbaa : ReplayTree.all (blocked 6 t6) t7babbbaa = true := by
  decide +kernel
def t7babbbab := (n (n (n (n z [w2,w7,w11,w35,w60,w69,w98,w128] z) [w2,w7,w11,w35,w60,w69,w98,w129] z) [w2,w7,w11,w35,w60,w69,w98,w134] (n (n z [w2,w7,w11,w35,w60,w69,w99,w127] z) [w2,w7,w11,w35,w60,w70,w98,w129] z)) [w2,w7,w11,w35,w61,w69,w98,w127] (n (n (n z [w2,w7,w11,w35,w62,w69,w98,w132] z) [w2,w7,w11,w37,w60,w69,w98,w129] z) [w2,w7,w11,w41,w60,w69,w98,w131] (n z [w2,w7,w11,w50,w60,w69,w98,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbbab : ReplayTree.all (blocked 6 t6) t7babbbab = true := by
  decide +kernel
def t7babbba := (n t7babbbaa [w2,w7,w11,w34,w60,w69,w98,w129] t7babbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbba : ReplayTree.all (blocked 6 t6) t7babbba = true := by
  simp only [t7babbba, ReplayTree.all, n, ht7babbbaa, ht7babbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babbbba := (n (n (n (n z [w2,w7,w11,w60,w69,w87,w98,w129] z) [w2,w7,w11,w60,w69,w98,w114,w131] z) [w2,w7,w11,w60,w69,w100,w112,w131] (n (n z [w2,w7,w11,w60,w69,w112,w129,w131] z) [w2,w7,w11,w60,w72,w83,w98,w129] z)) [w2,w7,w11,w60,w83,w98,w129,w131] (n (n (n z [w2,w7,w11,w62,w64,w69,w112,w127] z) [w2,w7,w11,w62,w64,w83,w98,w127] z) [w2,w7,w12,w27,w60,w69,w98,w131] (n z [w2,w7,w12,w35,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbbba : ReplayTree.all (blocked 6 t6) t7babbbba = true := by
  decide +kernel
def t7babbbbb := (n (n (n (n z [w2,w7,w13,w35,w60,w69,w98,w127] z) [w2,w7,w14,w19,w27,w69,w98,w132] z) [w2,w7,w14,w19,w60,w69,w112,w127] (n z [w2,w7,w14,w19,w60,w83,w98,w127] z)) [w2,w7,w14,w26,w60,w69,w98,w131] (n (n (n z [w2,w7,w14,w27,w60,w69,w98,w130] z) [w2,w7,w14,w27,w60,w69,w98,w131] z) [w2,w7,w14,w27,w60,w69,w98,w136] (n z [w2,w7,w14,w27,w60,w69,w101,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbbbb : ReplayTree.all (blocked 6 t6) t7babbbbb = true := by
  decide +kernel
def t7babbbb := (n t7babbbba [w2,w7,w13,w27,w60,w69,w98,w131] t7babbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbbb : ReplayTree.all (blocked 6 t6) t7babbbb = true := by
  simp only [t7babbbb, ReplayTree.all, n, ht7babbbba, ht7babbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babbb := (n t7babbba [w2,w7,w11,w57,w60,w69,w98,w129] t7babbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babbb : ReplayTree.all (blocked 6 t6) t7babbb = true := by
  simp only [t7babbb, ReplayTree.all, n, ht7babbba, ht7babbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babb := (n t7babba [w2,w7,w11,w28,w60,w69,w98,w131] t7babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7babb : ReplayTree.all (blocked 6 t6) t7babb = true := by
  simp only [t7babb, ReplayTree.all, n, ht7babba, ht7babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bab := (n t7baba [w2,w4,w27,w60,w69,w101,w107,w127] t7babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bab : ReplayTree.all (blocked 6 t6) t7bab = true := by
  simp only [t7bab, ReplayTree.all, n, ht7baba, ht7babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ba := (n t7baa [w2,w4,w9,w30,w60,w69,w105,w127] t7bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7ba : ReplayTree.all (blocked 6 t6) t7ba = true := by
  simp only [t7ba, ReplayTree.all, n, ht7baa, ht7bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaaaaa := (n (n (n (n z [w2,w7,w14,w27,w63,w69,w98,w127] z) [w2,w7,w14,w27,w64,w69,w98,w132] z) [w2,w7,w14,w30,w60,w69,w98,w131] (n (n z [w2,w7,w14,w32,w60,w69,w98,w131] z) [w2,w7,w14,w33,w60,w69,w98,w127] z)) [w2,w7,w14,w34,w60,w69,w98,w127] (n (n (n z [w2,w7,w14,w35,w60,w69,w98,w127] z) [w2,w7,w14,w35,w60,w69,w98,w129] z) [w2,w7,w14,w35,w60,w69,w98,w131] (n z [w2,w7,w14,w35,w60,w69,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaaaa : ReplayTree.all (blocked 6 t6) t7bbaaaaa = true := by
  decide +kernel
def t7bbaaaab := (n (n (n (n z [w2,w7,w14,w35,w60,w69,w105,w127] z) [w2,w7,w14,w35,w60,w69,w112,w127] z) [w2,w7,w14,w35,w60,w70,w98,w127] (n (n z [w2,w7,w14,w35,w60,w76,w98,w127] z) [w2,w7,w14,w35,w60,w83,w98,w127] z)) [w2,w7,w14,w37,w60,w69,w98,w127] (n (n (n z [w2,w7,w14,w39,w60,w69,w98,w131] z) [w2,w7,w14,w45,w60,w69,w98,w131] z) [w2,w7,w14,w50,w60,w69,w98,w131] (n z [w2,w7,w14,w57,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaaab : ReplayTree.all (blocked 6 t6) t7bbaaaab = true := by
  decide +kernel
def t7bbaaaa := (n t7bbaaaaa [w2,w7,w14,w35,w60,w69,w101,w127] t7bbaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaaa : ReplayTree.all (blocked 6 t6) t7bbaaaa = true := by
  simp only [t7bbaaaa, ReplayTree.all, n, ht7bbaaaaa, ht7bbaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaaaba := (n (n (n (n z [w2,w7,w14,w60,w64,w83,w98,w127] z) [w2,w7,w14,w60,w69,w72,w112,w127] z) [w2,w7,w14,w60,w69,w83,w98,w131] (n (n z [w2,w7,w14,w60,w69,w87,w98,w127] z) [w2,w7,w14,w60,w69,w98,w112,w131] z)) [w2,w7,w14,w60,w69,w112,w127,w131] (n (n (n z [w2,w7,w14,w60,w72,w83,w98,w127] z) [w2,w7,w14,w60,w83,w87,w98,w127] z) [w2,w7,w14,w60,w83,w98,w127,w131] (n z [w2,w7,w16,w30,w60,w69,w98,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaaba : ReplayTree.all (blocked 6 t6) t7bbaaaba = true := by
  decide +kernel
def t7bbaaabb := (n (n (n (n z [w2,w7,w17,w27,w60,w69,w98,w129] z) [w2,w7,w17,w30,w60,w69,w98,w127] z) [w2,w7,w18,w27,w60,w69,w98,w129] (n (n z [w2,w7,w18,w30,w60,w69,w98,w127] z) [w2,w7,w19,w26,w60,w69,w98,w129] z)) [w2,w7,w19,w27,w60,w69,w98,w128] (n (n (n z [w2,w7,w19,w27,w60,w69,w98,w129] z) [w2,w7,w19,w27,w60,w69,w98,w134] z) [w2,w7,w19,w27,w60,w69,w99,w127] (n z [w2,w7,w19,w27,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaabb : ReplayTree.all (blocked 6 t6) t7bbaaabb = true := by
  decide +kernel
def t7bbaaab := (n t7bbaaaba [w2,w7,w16,w35,w60,w69,w98,w129] t7bbaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaab : ReplayTree.all (blocked 6 t6) t7bbaaab = true := by
  simp only [t7bbaaab, ReplayTree.all, n, ht7bbaaaba, ht7bbaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaaa := (n t7bbaaaa [w2,w7,w14,w60,w64,w69,w112,w127] t7bbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaa : ReplayTree.all (blocked 6 t6) t7bbaaa = true := by
  simp only [t7bbaaa, ReplayTree.all, n, ht7bbaaaa, ht7bbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaabaa := (n (n (n (n z [w2,w7,w19,w27,w62,w69,w98,w132] z) [w2,w7,w19,w28,w60,w69,w98,w127] z) [w2,w7,w19,w29,w60,w69,w98,w127] (n (n z [w2,w7,w19,w30,w60,w69,w98,w127] z) [w2,w7,w19,w30,w60,w69,w98,w129] z)) [w2,w7,w19,w30,w60,w69,w98,w131] (n (n (n z [w2,w7,w19,w30,w60,w69,w98,w132] z) [w2,w7,w19,w30,w60,w69,w101,w127] z) [w2,w7,w19,w30,w60,w69,w105,w127] (n z [w2,w7,w19,w30,w60,w69,w112,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaabaa : ReplayTree.all (blocked 6 t6) t7bbaabaa = true := by
  decide +kernel
def t7bbaabab := (n (n (n (n z [w2,w7,w19,w30,w60,w76,w98,w127] z) [w2,w7,w19,w30,w60,w83,w98,w127] z) [w2,w7,w19,w32,w60,w69,w98,w129] (n (n z [w2,w7,w19,w35,w60,w69,w98,w129] z) [w2,w7,w19,w39,w60,w69,w98,w129] z)) [w2,w7,w19,w41,w60,w69,w98,w127] (n (n (n z [w2,w7,w19,w45,w60,w69,w98,w129] z) [w2,w7,w19,w50,w60,w69,w98,w127] z) [w2,w7,w19,w57,w60,w69,w98,w129] (n z [w2,w7,w19,w60,w62,w69,w112,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaabab : ReplayTree.all (blocked 6 t6) t7bbaabab = true := by
  decide +kernel
def t7bbaaba := (n t7bbaabaa [w2,w7,w19,w30,w60,w70,w98,w127] t7bbaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaaba : ReplayTree.all (blocked 6 t6) t7bbaaba = true := by
  simp only [t7bbaaba, ReplayTree.all, n, ht7bbaabaa, ht7bbaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaabba := (n (n (n (n z [w2,w7,w19,w60,w69,w83,w98,w129] z) [w2,w7,w19,w60,w69,w98,w112,w129] z) [w2,w7,w19,w60,w69,w98,w114,w127] (n (n z [w2,w7,w19,w60,w69,w100,w112,w127] z) [w2,w7,w19,w60,w69,w112,w114,w127] z)) [w2,w7,w19,w60,w69,w112,w127,w129] (n (n (n z [w2,w7,w19,w60,w83,w98,w100,w127] z) [w2,w7,w19,w60,w83,w98,w127,w129] z) [w2,w7,w21,w27,w60,w69,w98,w129] (n z [w2,w7,w21,w30,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaabba : ReplayTree.all (blocked 6 t6) t7bbaabba = true := by
  decide +kernel
def t7bbaabbb := (n (n (n (n z [w2,w7,w23,w35,w60,w69,w98,w129] z) [w2,w7,w25,w27,w60,w69,w98,w131] z) [w2,w7,w25,w35,w60,w69,w98,w127] (n (n z [w2,w7,w27,w50,w60,w69,w98,w131] z) [w2,w7,w27,w57,w60,w69,w98,w129] z)) [w2,w7,w27,w60,w69,w80,w98,w129] (n (n (n z [w2,w7,w27,w60,w69,w98,w107,w131] z) [w2,w7,w27,w60,w69,w100,w105,w131] z) [w2,w7,w27,w60,w69,w105,w129,w131] (n z [w2,w7,w27,w60,w72,w76,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaabbb : ReplayTree.all (blocked 6 t6) t7bbaabbb = true := by
  decide +kernel
def t7bbaabb := (n t7bbaabba [w2,w7,w23,w30,w60,w69,w98,w131] t7bbaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaabb : ReplayTree.all (blocked 6 t6) t7bbaabb = true := by
  simp only [t7bbaabb, ReplayTree.all, n, ht7bbaabba, ht7bbaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaab := (n t7bbaaba [w2,w7,w19,w60,w62,w83,w98,w127] t7bbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaab : ReplayTree.all (blocked 6 t6) t7bbaab = true := by
  simp only [t7bbaab, ReplayTree.all, n, ht7bbaaba, ht7bbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaa := (n t7bbaaa [w2,w7,w19,w27,w61,w69,w98,w127] t7bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaa : ReplayTree.all (blocked 6 t6) t7bbaa = true := by
  simp only [t7bbaa, ReplayTree.all, n, ht7bbaaa, ht7bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbabaaa := (n (n (n (n z [w2,w7,w27,w62,w64,w69,w105,w127] z) [w2,w7,w27,w62,w64,w76,w98,w127] z) [w2,w7,w30,w35,w60,w69,w105,w127] (n (n z [w2,w7,w30,w35,w60,w76,w98,w127] z) [w2,w7,w30,w45,w60,w69,w98,w131] z)) [w2,w7,w30,w50,w60,w69,w98,w131] (n (n (n z [w2,w7,w30,w57,w60,w69,w98,w127] z) [w2,w7,w30,w60,w64,w69,w105,w127] z) [w2,w7,w30,w60,w64,w76,w98,w127] (n z [w2,w7,w30,w60,w69,w72,w105,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabaaa : ReplayTree.all (blocked 6 t6) t7bbabaaa = true := by
  decide +kernel
def t7bbabaab := (n (n (n (n z [w2,w7,w30,w60,w69,w80,w98,w127] z) [w2,w7,w30,w60,w69,w98,w105,w131] z) [w2,w7,w30,w60,w69,w105,w127,w131] (n (n z [w2,w7,w30,w60,w72,w76,w98,w127] z) [w2,w7,w30,w60,w76,w80,w98,w127] z)) [w2,w7,w30,w60,w76,w98,w127,w131] (n (n (n z [w2,w7,w35,w45,w60,w69,w98,w129] z) [w2,w7,w35,w50,w60,w69,w98,w127] z) [w2,w7,w35,w57,w60,w69,w98,w129] (n z [w2,w7,w35,w60,w62,w69,w105,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabaab : ReplayTree.all (blocked 6 t6) t7bbabaab = true := by
  decide +kernel
def t7bbabaa := (n t7bbabaaa [w2,w7,w30,w60,w69,w76,w98,w131] t7bbabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabaa : ReplayTree.all (blocked 6 t6) t7bbabaa = true := by
  simp only [t7bbabaa, ReplayTree.all, n, ht7bbabaaa, ht7bbabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbababa := (n (n (n (n z [w2,w7,w35,w60,w69,w76,w98,w129] z) [w2,w7,w35,w60,w69,w98,w105,w129] z) [w2,w7,w35,w60,w69,w98,w107,w127] (n (n z [w2,w7,w35,w60,w69,w100,w105,w127] z) [w2,w7,w35,w60,w69,w105,w107,w127] z)) [w2,w7,w35,w60,w69,w105,w127,w129] (n (n (n z [w2,w7,w35,w60,w76,w98,w100,w127] z) [w2,w7,w35,w60,w76,w98,w127,w129] z) [w2,w7,w45,w50,w60,w69,w98,w131] (n z [w2,w7,w45,w57,w60,w69,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbababa : ReplayTree.all (blocked 6 t6) t7bbababa = true := by
  decide +kernel
def t7bbababb := (n (n (n (n z [w2,w7,w45,w60,w64,w69,w98,w129] z) [w2,w7,w45,w60,w69,w72,w98,w129] z) [w2,w7,w45,w60,w69,w98,w100,w131] (n (n z [w2,w7,w45,w60,w69,w98,w129,w131] z) [w2,w7,w45,w62,w64,w69,w98,w127] z)) [w2,w7,w50,w57,w60,w69,w98,w127] (n (n (n z [w2,w7,w50,w60,w64,w69,w98,w127] z) [w2,w7,w50,w60,w69,w72,w98,w127] z) [w2,w7,w50,w60,w69,w98,w127,w131] (n z [w2,w7,w50,w60,w69,w98,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbababb : ReplayTree.all (blocked 6 t6) t7bbababb = true := by
  decide +kernel
def t7bbabab := (n t7bbababa [w2,w7,w45,w60,w62,w69,w98,w131] t7bbababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabab : ReplayTree.all (blocked 6 t6) t7bbabab = true := by
  simp only [t7bbabab, ReplayTree.all, n, ht7bbababa, ht7bbababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaba := (n t7bbabaa [w2,w7,w35,w60,w62,w76,w98,w127] t7bbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbaba : ReplayTree.all (blocked 6 t6) t7bbaba = true := by
  simp only [t7bbaba, ReplayTree.all, n, ht7bbabaa, ht7bbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbabbaa := (n (n (n (n z [w2,w7,w57,w60,w69,w98,w100,w127] z) [w2,w7,w57,w60,w69,w98,w127,w129] z) [w2,w7,w57,w60,w69,w98,w129] (n (n z [w2,w8,w11,w27,w60,w69,w98,w131] z) [w2,w8,w11,w35,w60,w69,w98,w127] z)) [w2,w8,w19,w27,w60,w69,w98,w127] (n (n (n z [w2,w9,w11,w27,w60,w69,w101,w131] z) [w2,w9,w11,w27,w60,w71,w98,w127] z) [w2,w9,w11,w27,w63,w69,w98,w127] (n z [w2,w9,w11,w27,w64,w69,w98,w132] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabbaa : ReplayTree.all (blocked 6 t6) t7bbabbaa = true := by
  decide +kernel
def t7bbabbab := (n (n (n (n z [w2,w9,w11,w35,w60,w69,w98,w131] z) [w2,w9,w11,w35,w60,w69,w101,w127] z) [w2,w9,w11,w39,w60,w69,w98,w131] (n (n z [w2,w9,w11,w60,w64,w69,w112,w127] z) [w2,w9,w11,w60,w69,w72,w112,w127] z)) [w2,w9,w11,w60,w72,w83,w98,w127] (n (n (n z [w2,w9,w18,w27,w60,w69,w98,w127] z) [w2,w9,w19,w27,w60,w69,w98,w131] z) [w2,w9,w19,w27,w60,w69,w101,w127] (n z [w2,w9,w19,w35,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabbab : ReplayTree.all (blocked 6 t6) t7bbabbab = true := by
  decide +kernel
def t7bbabba := (n t7bbabbaa [w2,w9,w11,w34,w60,w69,w98,w127] t7bbabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabba : ReplayTree.all (blocked 6 t6) t7bbabba = true := by
  simp only [t7bbabba, ReplayTree.all, n, ht7bbabbaa, ht7bbabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbabbba := (n (n (n (n z [w2,w9,w23,w27,w60,w69,w98,w131] z) [w2,w9,w23,w35,w60,w69,w98,w127] z) [w2,w9,w27,w60,w64,w69,w105,w127] (n (n z [w2,w9,w27,w60,w69,w72,w105,w127] z) [w2,w9,w27,w60,w72,w76,w98,w127] z)) [w2,w9,w45,w60,w64,w69,w98,w127] (n (n (n z [w2,w9,w45,w60,w69,w72,w98,w127] z) [w2,w11,w14,w27,w60,w69,w101,w131] z) [w2,w11,w27,w30,w60,w69,w101,w131] (n z [w2,w11,w27,w60,w62,w69,w101,w131] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabbba : ReplayTree.all (blocked 6 t6) t7bbabbba = true := by
  decide +kernel
def t7bbabbbb := (n (n (n (n z [w2,w11,w27,w60,w69,w101,w103,w131] z) [w2,w11,w27,w60,w69,w101,w129,w131] z) [w2,w11,w27,w62,w64,w69,w101,w127] (n z [w2,w11,w30,w60,w64,w69,w101,w127] z)) [w2,w11,w30,w60,w69,w72,w101,w127] (n (n (n z [w2,w11,w30,w60,w69,w98,w101,w131] z) [w2,w11,w30,w60,w69,w101,w127,w131] z) [w2,w11,w30,w60,w69,w101,w131] (n z [w2,w14,w27,w60,w64,w69,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabbbb : ReplayTree.all (blocked 6 t6) t7bbabbbb = true := by
  decide +kernel
def t7bbabbb := (n t7bbabbba [w2,w11,w27,w60,w69,w100,w101,w131] t7bbabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabbb : ReplayTree.all (blocked 6 t6) t7bbabbb = true := by
  simp only [t7bbabbb, ReplayTree.all, n, ht7bbabbba, ht7bbabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbabb := (n t7bbabba [w2,w9,w19,w39,w60,w69,w98,w127] t7bbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbabb : ReplayTree.all (blocked 6 t6) t7bbabb = true := by
  simp only [t7bbabb, ReplayTree.all, n, ht7bbabba, ht7bbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbab := (n t7bbaba [w2,w7,w57,w60,w62,w69,w98,w127] t7bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbab : ReplayTree.all (blocked 6 t6) t7bbab = true := by
  simp only [t7bbab, ReplayTree.all, n, ht7bbaba, ht7bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bba := (n t7bbaa [w2,w7,w27,w60,w76,w98,w129,w131] t7bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bba : ReplayTree.all (blocked 6 t6) t7bba = true := by
  simp only [t7bba, ReplayTree.all, n, ht7bbaa, ht7bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbaaaa := (n (n (n (n z [w2,w14,w27,w60,w69,w98,w101,w131] z) [w2,w14,w27,w60,w69,w101,w127,w131] z) [w2,w14,w27,w60,w69,w101,w131] (n (n z [w3,w7,w11,w27,w60,w70,w98,w129] z) [w3,w9,w11,w27,w60,w70,w98,w127] z)) [w4,w6,w9,w45,w60,w69,w98,w127] (n (n (n z [w4,w7,w9,w11,w27,w70,w98,w132] z) [w4,w7,w9,w45,w60,w70,w98,w127] z) [w4,w7,w10,w27,w60,w70,w98,w129] (n z [w4,w7,w11,w26,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaaaa : ReplayTree.all (blocked 6 t6) t7bbbaaaa = true := by
  decide +kernel
def t7bbbaaab := (n (n (n (n z [w4,w7,w11,w27,w60,w70,w98,w129] z) [w4,w7,w11,w27,w60,w70,w98,w134] z) [w4,w7,w11,w27,w60,w70,w99,w127] (n (n z [w4,w7,w11,w27,w61,w70,w98,w127] z) [w4,w7,w11,w27,w62,w70,w98,w132] z)) [w4,w7,w11,w27,w70,w98,w100,w132] (n (n (n z [w4,w7,w11,w27,w70,w98,w129,w132] z) [w4,w7,w11,w27,w70,w98,w132,w134] z) [w4,w7,w11,w29,w60,w70,w98,w127] (n z [w4,w7,w11,w30,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaaab : ReplayTree.all (blocked 6 t6) t7bbbaaab = true := by
  decide +kernel
def t7bbbaaa := (n t7bbbaaaa [w4,w7,w11,w27,w60,w70,w98,w128] t7bbbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaaa : ReplayTree.all (blocked 6 t6) t7bbbaaa = true := by
  simp only [t7bbbaaa, ReplayTree.all, n, ht7bbbaaaa, ht7bbbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbaaba := (n (n (n (n z [w4,w7,w11,w32,w60,w70,w98,w129] z) [w4,w7,w11,w35,w60,w70,w98,w129] z) [w4,w7,w11,w39,w60,w70,w98,w129] (n (n z [w4,w7,w11,w45,w60,w70,w98,w129] z) [w4,w7,w11,w60,w70,w83,w98,w129] z)) [w4,w7,w11,w60,w70,w85,w98,w129] (n (n (n z [w4,w7,w11,w60,w70,w98,w112,w129] z) [w4,w7,w11,w60,w70,w100,w112,w127] z) [w4,w7,w13,w27,w60,w70,w98,w127] (n z [w4,w7,w14,w27,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaaba : ReplayTree.all (blocked 6 t6) t7bbbaaba = true := by
  decide +kernel
def t7bbbaabb := (n (n (n (n z [w4,w7,w14,w31,w60,w69,w98,w127] z) [w4,w7,w14,w32,w60,w70,w98,w127] z) [w4,w7,w15,w27,w60,w69,w98,w129] (n (n z [w4,w7,w15,w30,w60,w69,w98,w127] z) [w4,w7,w16,w27,w60,w70,w98,w129] z)) [w4,w7,w16,w30,w60,w70,w98,w127] (n (n (n z [w4,w7,w16,w32,w60,w69,w98,w129] z) [w4,w7,w19,w27,w60,w70,w98,w129] z) [w4,w7,w23,w27,w60,w70,w98,w129] (n z [w4,w7,w27,w45,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaabb : ReplayTree.all (blocked 6 t6) t7bbbaabb = true := by
  decide +kernel
def t7bbbaab := (n t7bbbaaba [w4,w7,w14,w30,w60,w70,w98,w127] t7bbbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaab : ReplayTree.all (blocked 6 t6) t7bbbaab = true := by
  simp only [t7bbbaab, ReplayTree.all, n, ht7bbbaaba, ht7bbbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbaa := (n t7bbbaaa [w4,w7,w11,w31,w60,w69,w98,w129] t7bbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaa : ReplayTree.all (blocked 6 t6) t7bbbaa = true := by
  simp only [t7bbbaa, ReplayTree.all, n, ht7bbbaaa, ht7bbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbabaa := (n (n (n (n z [w4,w7,w27,w60,w70,w78,w98,w129] z) [w4,w7,w27,w60,w70,w98,w105,w129] z) [w4,w7,w27,w60,w70,w100,w105,w127] (n (n z [w4,w7,w45,w60,w62,w70,w98,w127] z) [w4,w7,w45,w60,w69,w70,w98,w129] z)) [w4,w7,w45,w60,w70,w98,w100,w127] (n (n (n z [w4,w7,w45,w60,w70,w98,w127,w129] z) [w4,w7,w45,w60,w70,w98,w129] z) [w4,w8,w11,w27,w60,w70,w98,w127] (n z [w4,w9,w10,w27,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbabaa : ReplayTree.all (blocked 6 t6) t7bbbabaa = true := by
  decide +kernel
def t7bbbabab := (n (n (n (n z [w4,w9,w11,w27,w60,w70,w98,w127] z) [w4,w9,w11,w27,w60,w70,w98,w129] z) [w4,w9,w11,w27,w60,w70,w98,w132] (n (n z [w4,w9,w11,w27,w60,w70,w101,w127] z) [w4,w9,w11,w30,w60,w70,w98,w127] z)) [w4,w9,w11,w31,w60,w69,w98,w127] (n (n (n z [w4,w9,w11,w32,w60,w70,w98,w127] z) [w4,w9,w11,w35,w60,w70,w98,w127] z) [w4,w9,w11,w39,w60,w70,w98,w127] (n z [w4,w9,w11,w41,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbabab : ReplayTree.all (blocked 6 t6) t7bbbabab = true := by
  decide +kernel
def t7bbbaba := (n t7bbbabaa [w4,w9,w11,w26,w60,w70,w98,w127] t7bbbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbaba : ReplayTree.all (blocked 6 t6) t7bbbaba = true := by
  simp only [t7bbbaba, ReplayTree.all, n, ht7bbbabaa, ht7bbbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbabba := (n (n (n (n z [w4,w9,w11,w60,w70,w83,w98,w127] z) [w4,w9,w11,w60,w70,w85,w98,w127] z) [w4,w9,w11,w60,w70,w98,w112,w127] (n (n z [w4,w9,w14,w27,w60,w70,w98,w127] z) [w4,w9,w15,w27,w60,w69,w98,w127] z)) [w4,w9,w16,w27,w60,w70,w98,w127] (n (n (n z [w4,w9,w16,w32,w60,w69,w98,w127] z) [w4,w9,w19,w27,w60,w70,w98,w127] z) [w4,w9,w23,w27,w60,w70,w98,w127] (n z [w4,w9,w25,w27,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbabba : ReplayTree.all (blocked 6 t6) t7bbbabba = true := by
  decide +kernel
def t7bbbabbb := (n (n (n (n z [w4,w9,w27,w60,w70,w76,w98,w127] z) [w4,w9,w27,w60,w70,w78,w98,w127] z) [w4,w9,w27,w60,w70,w98,w105,w127] (n z [w4,w9,w45,w60,w69,w70,w98,w127] z)) [w4,w9,w45,w60,w70,w98,w127] (n (n (n z [w4,w11,w27,w60,w62,w70,w101,w127] z) [w4,w11,w27,w60,w70,w98,w101,w129] z) [w4,w11,w27,w60,w70,w98,w103,w127] (n z [w4,w11,w27,w60,w70,w100,w101,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbabbb : ReplayTree.all (blocked 6 t6) t7bbbabbb = true := by
  decide +kernel
def t7bbbabb := (n t7bbbabba [w4,w9,w27,w45,w60,w70,w98,w127] t7bbbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbabb : ReplayTree.all (blocked 6 t6) t7bbbabb = true := by
  simp only [t7bbbabb, ReplayTree.all, n, ht7bbbabba, ht7bbbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbab := (n t7bbbaba [w4,w9,w11,w45,w60,w70,w98,w127] t7bbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbab : ReplayTree.all (blocked 6 t6) t7bbbab = true := by
  simp only [t7bbbab, ReplayTree.all, n, ht7bbbaba, ht7bbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbba := (n t7bbbaa [w4,w7,w27,w60,w70,w76,w98,w129] t7bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbba : ReplayTree.all (blocked 6 t6) t7bbba = true := by
  simp only [t7bbba, ReplayTree.all, n, ht7bbbaa, ht7bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbbaaa := (n (n (n (n z [w4,w11,w27,w60,w70,w101,w127,w129] z) [w5,w7,w11,w27,w60,w69,w98,w129] z) [w5,w7,w11,w30,w60,w69,w98,w127] (n (n z [w5,w7,w14,w27,w60,w69,w98,w127] z) [w5,w9,w11,w27,w60,w69,w98,w127] z)) [w6,w7,w9,w11,w60,w83,w98,w127] (n (n (n z [w6,w7,w9,w27,w60,w76,w98,w127] z) [w6,w7,w9,w45,w60,w69,w98,w127] z) [w6,w7,w11,w27,w60,w69,w99,w127] (n z [w6,w7,w11,w27,w60,w70,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbaaa : ReplayTree.all (blocked 6 t6) t7bbbbaaa = true := by
  decide +kernel
def t7bbbbaab := (n (n (n (n z [w6,w7,w11,w27,w62,w69,w98,w132] z) [w6,w7,w11,w29,w60,w69,w98,w127] z) [w6,w7,w11,w30,w60,w69,w98,w129] (n (n z [w6,w7,w11,w30,w60,w70,w98,w127] z) [w6,w7,w11,w32,w60,w69,w98,w129] z)) [w6,w7,w11,w60,w62,w83,w98,w127] (n (n (n z [w6,w7,w11,w60,w69,w100,w112,w127] z) [w6,w7,w11,w60,w83,w98,w100,w127] z) [w6,w7,w13,w27,w60,w69,w98,w127] (n z [w6,w7,w14,w27,w60,w69,w98,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbaab : ReplayTree.all (blocked 6 t6) t7bbbbaab = true := by
  decide +kernel
def t7bbbbaa := (n t7bbbbaaa [w6,w7,w11,w27,w61,w69,w98,w127] t7bbbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbaa : ReplayTree.all (blocked 6 t6) t7bbbbaa = true := by
  simp only [t7bbbbaa, ReplayTree.all, n, ht7bbbbaaa, ht7bbbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbbaba := (n (n (n (n z [w6,w7,w14,w30,w60,w69,w98,w127] z) [w6,w7,w14,w32,w60,w69,w98,w127] z) [w6,w7,w16,w27,w60,w69,w98,w129] (n (n z [w6,w7,w16,w30,w60,w69,w98,w127] z) [w6,w7,w27,w60,w62,w76,w98,w127] z)) [w6,w7,w27,w60,w69,w100,w105,w127] (n (n (n z [w6,w7,w27,w60,w76,w98,w100,w127] z) [w6,w7,w45,w60,w62,w69,w98,w127] z) [w6,w7,w45,w60,w69,w98,w100,w127] (n z [w6,w8,w11,w27,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbaba : ReplayTree.all (blocked 6 t6) t7bbbbaba = true := by
  decide +kernel
def t7bbbbabb := (n (n (n (n z [w6,w9,w11,w26,w60,w69,w98,w127] z) [w6,w9,w11,w27,w60,w69,w98,w127] z) [w6,w9,w11,w27,w60,w69,w98,w129] (n (n z [w6,w9,w11,w27,w60,w69,w98,w131] z) [w6,w9,w11,w27,w60,w69,w98,w132] z)) [w6,w9,w11,w27,w60,w69,w101,w127] (n (n (n z [w6,w9,w11,w27,w60,w70,w98,w127] z) [w6,w9,w11,w30,w60,w69,w98,w127] z) [w6,w9,w11,w32,w60,w69,w98,w127] (n z [w6,w9,w11,w35,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbabb : ReplayTree.all (blocked 6 t6) t7bbbbabb = true := by
  decide +kernel
def t7bbbbab := (n t7bbbbaba [w6,w9,w10,w27,w60,w69,w98,w127] t7bbbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbab : ReplayTree.all (blocked 6 t6) t7bbbbab = true := by
  simp only [t7bbbbab, ReplayTree.all, n, ht7bbbbaba, ht7bbbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbba := (n t7bbbbaa [w6,w7,w14,w27,w60,w70,w98,w127] t7bbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbba : ReplayTree.all (blocked 6 t6) t7bbbba = true := by
  simp only [t7bbbba, ReplayTree.all, n, ht7bbbbaa, ht7bbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbbbaa := (n (n (n (n z [w6,w9,w11,w39,w60,w69,w98,w127] z) [w6,w9,w11,w41,w60,w69,w98,w127] z) [w6,w9,w11,w45,w60,w69,w98,w127] (n (n z [w6,w9,w11,w60,w69,w83,w98,w127] z) [w6,w9,w11,w60,w69,w98,w112,w127] z)) [w6,w9,w14,w27,w60,w69,w98,w127] (n (n (n z [w6,w9,w16,w27,w60,w69,w98,w127] z) [w6,w9,w19,w27,w60,w69,w98,w127] z) [w6,w9,w21,w27,w60,w69,w98,w127] (n z [w6,w9,w23,w27,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbbaa : ReplayTree.all (blocked 6 t6) t7bbbbbaa = true := by
  decide +kernel
def t7bbbbbab := (n (n (n (n z [w6,w9,w27,w45,w60,w69,w98,w127] z) [w6,w9,w27,w60,w69,w76,w98,w127] z) [w6,w9,w27,w60,w69,w98,w105,w127] (n (n z [w6,w9,w45,w60,w69,w98,w127] z) [w6,w11,w27,w60,w62,w69,w101,w127] z)) [w6,w11,w27,w60,w69,w98,w103,w127] (n (n (n z [w6,w11,w27,w60,w69,w100,w101,w127] z) [w6,w11,w27,w60,w69,w101,w103,w127] z) [w7,w9,w11,w35,w60,w70,w98,w127] (n z [w7,w9,w19,w27,w60,w70,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbbab : ReplayTree.all (blocked 6 t6) t7bbbbbab = true := by
  decide +kernel
def t7bbbbba := (n t7bbbbbaa [w6,w9,w25,w27,w60,w69,w98,w127] t7bbbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbba : ReplayTree.all (blocked 6 t6) t7bbbbba = true := by
  simp only [t7bbbbba, ReplayTree.all, n, ht7bbbbbaa, ht7bbbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbbbba := (n (n (n (n z [w7,w11,w27,w35,w60,w70,w98,w129] z) [w7,w11,w27,w60,w64,w70,w98,w129] z) [w7,w11,w27,w60,w70,w72,w98,w129] (n (n z [w7,w11,w27,w60,w70,w74,w98,w129] z) [w7,w11,w27,w60,w70,w98,w129,w131] z)) [w7,w11,w27,w62,w64,w70,w98,w127] (n (n (n z [w7,w11,w35,w60,w62,w70,w98,w127] z) [w7,w11,w35,w60,w69,w70,w98,w129] z) [w7,w11,w35,w60,w70,w98,w100,w127] (n z [w7,w11,w35,w60,w70,w98,w127,w129] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbbba : ReplayTree.all (blocked 6 t6) t7bbbbbba = true := by
  decide +kernel
def t7bbbbbbb := (n (n (n (n z [w7,w19,w27,w60,w62,w70,w98,w127] z) [w7,w19,w27,w60,w69,w70,w98,w129] z) [w7,w19,w27,w60,w70,w98,w100,w127] (n z [w7,w19,w27,w60,w70,w98,w127,w129] z)) [w7,w19,w27,w60,w70,w98,w129] (n (n (n z [w9,w11,w27,w60,w64,w70,w98,w127] z) [w9,w11,w27,w60,w69,w74,w98,w127] z) [w9,w11,w27,w60,w70,w72,w98,w127] (n z [w9,w11,w27,w60,w70,w74,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbbbb : ReplayTree.all (blocked 6 t6) t7bbbbbbb = true := by
  decide +kernel
def t7bbbbbb := (n t7bbbbbba [w7,w11,w35,w60,w70,w98,w129] t7bbbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbbb : ReplayTree.all (blocked 6 t6) t7bbbbbb = true := by
  simp only [t7bbbbbb, ReplayTree.all, n, ht7bbbbbba, ht7bbbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbbb := (n t7bbbbba [w7,w11,w19,w27,w60,w70,w98,w129] t7bbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbbb : ReplayTree.all (blocked 6 t6) t7bbbbb = true := by
  simp only [t7bbbbb, ReplayTree.all, n, ht7bbbbba, ht7bbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbb := (n t7bbbba [w6,w9,w11,w37,w60,w69,w98,w127] t7bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbbb : ReplayTree.all (blocked 6 t6) t7bbbb = true := by
  simp only [t7bbbb, ReplayTree.all, n, ht7bbbba, ht7bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbb := (n t7bbba [w4,w11,w27,w60,w70,w101,w103,w127] t7bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bbb : ReplayTree.all (blocked 6 t6) t7bbb = true := by
  simp only [t7bbb, ReplayTree.all, n, ht7bbba, ht7bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bb := (n t7bba [w2,w14,w27,w60,w69,w72,w101,w127] t7bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7bb : ReplayTree.all (blocked 6 t6) t7bb = true := by
  simp only [t7bb, ReplayTree.all, n, ht7bba, ht7bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7b := (n t7ba [w2,w7,w14,w27,w60,w71,w98,w127] t7bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7b : ReplayTree.all (blocked 6 t6) t7b = true := by
  simp only [t7b, ReplayTree.all, n, ht7ba, ht7bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7 := (n t7a [w2,w4,w7,w11,w60,w82,w98,w129] t7b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht7 : ReplayTree.all (blocked 6 t6) t7 = true := by
  simp only [t7, ReplayTree.all, n, ht7a, ht7b, Bool.true_and, Bool.and_true]
  decide +kernel
theorem s7 : sound 7 t7 := layer_sound s6 ht7
def t8aaaaa := (n (n (n (n (n z [w0,w2,w4,w7,w11,w27,w69,w98,w132] z) [w0,w2,w4,w7,w11,w60,w69,w112,w127] z) [w0,w2,w4,w7,w11,w60,w83,w98,w127] (n z [w0,w2,w4,w7,w27,w60,w69,w105,w127] z)) [w0,w2,w4,w7,w27,w60,w76,w98,w127] (n (n z [w0,w2,w4,w7,w45,w60,w69,w98,w127] z) [w0,w2,w4,w11,w27,w60,w69,w101,w127] (n z [w0,w2,w7,w11,w27,w60,w69,w98,w131] z))) [w0,w2,w7,w11,w35,w60,w69,w98,w127] (n (n (n (n z [w0,w2,w7,w19,w27,w60,w69,w98,w127] z) [w0,w4,w7,w11,w27,w60,w70,w98,w127] z) [w0,w6,w7,w11,w27,w60,w69,w98,w127] (n z [w1,w2,w3,w7,w11,w27,w69,w98,w132] z)) [w1,w2,w3,w7,w11,w60,w69,w112,w127] (n (n z [w1,w2,w3,w7,w11,w60,w83,w98,w127] z) [w1,w2,w3,w7,w27,w60,w69,w105,w127] (n z [w1,w2,w3,w7,w27,w60,w76,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaaaa : ReplayTree.all (blocked 7 t7) t8aaaaa = true := by
  decide +kernel
def t8aaaab := (n (n (n (n (n z [w1,w2,w3,w11,w27,w60,w69,w101,w127] z) [w1,w2,w4,w7,w10,w27,w69,w98,w132] z) [w1,w2,w4,w7,w10,w60,w69,w112,w127] (n z [w1,w2,w4,w7,w10,w60,w83,w98,w127] z)) [w1,w2,w4,w7,w11,w26,w69,w98,w132] (n (n z [w1,w2,w4,w7,w11,w27,w69,w98,w132] z) [w1,w2,w4,w7,w11,w27,w69,w101,w132] (n z [w1,w2,w4,w7,w11,w27,w69,w105,w132] z))) [w1,w2,w4,w7,w11,w27,w69,w112,w132] (n (n (n (n z [w1,w2,w4,w7,w11,w27,w70,w98,w132] z) [w1,w2,w4,w7,w11,w27,w76,w98,w132] z) [w1,w2,w4,w7,w11,w27,w83,w98,w132] (n z [w1,w2,w4,w7,w11,w32,w69,w98,w132] z)) [w1,w2,w4,w7,w11,w39,w69,w98,w132] (n (n z [w1,w2,w4,w7,w11,w45,w69,w98,w132] z) [w1,w2,w4,w7,w11,w60,w69,w111,w127] (n z [w1,w2,w4,w7,w11,w60,w69,w112,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaaab : ReplayTree.all (blocked 7 t7) t8aaaab = true := by
  decide +kernel
def t8aaaa := (n t8aaaaa [w1,w2,w3,w7,w45,w60,w69,w98,w127] t8aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaaa : ReplayTree.all (blocked 7 t7) t8aaaa = true := by
  simp only [t8aaaa, ReplayTree.all, n, ht8aaaaa, ht8aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aaaba := (n (n (n (n (n z [w1,w2,w4,w7,w11,w60,w69,w116,w127] z) [w1,w2,w4,w7,w11,w60,w69,w121,w127] z) [w1,w2,w4,w7,w11,w60,w70,w112,w127] (n z [w1,w2,w4,w7,w11,w60,w76,w112,w127] z)) [w1,w2,w4,w7,w11,w60,w82,w98,w127] (n (n z [w1,w2,w4,w7,w11,w60,w83,w98,w127] z) [w1,w2,w4,w7,w11,w60,w83,w98,w132] (n z [w1,w2,w4,w7,w11,w60,w83,w101,w127] z))) [w1,w2,w4,w7,w11,w60,w83,w105,w127] (n (n (n (n z [w1,w2,w4,w7,w11,w60,w83,w112,w127] z) [w1,w2,w4,w7,w11,w60,w85,w98,w127] z) [w1,w2,w4,w7,w11,w60,w92,w98,w127] (n z [w1,w2,w4,w7,w11,w69,w83,w98,w132] z)) [w1,w2,w4,w7,w11,w69,w98,w112,w132] (n (n z [w1,w2,w4,w7,w11,w69,w112,w127,w132] z) [w1,w2,w4,w7,w11,w69,w112,w132] (n z [w1,w2,w4,w7,w11,w83,w98,w127,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaaba : ReplayTree.all (blocked 7 t7) t8aaaba = true := by
  decide +kernel
def t8aaabb := (n (n (n (n (n z [w1,w2,w4,w7,w14,w60,w69,w112,w127] z) [w1,w2,w4,w7,w14,w60,w83,w98,w127] z) [w1,w2,w4,w7,w16,w27,w69,w98,w132] (n z [w1,w2,w4,w7,w16,w60,w69,w112,w127] z)) [w1,w2,w4,w7,w16,w60,w83,w98,w127] (n (n z [w1,w2,w4,w7,w19,w60,w69,w112,w127] z) [w1,w2,w4,w7,w19,w60,w83,w98,w127] (n z [w1,w2,w4,w7,w23,w27,w69,w98,w132] z))) [w1,w2,w4,w7,w23,w60,w69,w112,w127] (n (n (n (n z [w1,w2,w4,w7,w23,w60,w83,w98,w127] z) [w1,w2,w4,w7,w26,w60,w69,w105,w127] z) [w1,w2,w4,w7,w26,w60,w76,w98,w127] (n z [w1,w2,w4,w7,w27,w45,w69,w98,w132] z)) [w1,w2,w4,w7,w27,w60,w69,w104,w127] (n (n z [w1,w2,w4,w7,w27,w60,w69,w105,w127] z) [w1,w2,w4,w7,w27,w60,w69,w105,w132] (n z [w1,w2,w4,w7,w27,w60,w69,w109,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaabb : ReplayTree.all (blocked 7 t7) t8aaabb = true := by
  decide +kernel
def t8aaab := (n t8aaaba [w1,w2,w4,w7,w11,w83,w98,w132] t8aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaab : ReplayTree.all (blocked 7 t7) t8aaab = true := by
  simp only [t8aaab, ReplayTree.all, n, ht8aaaba, ht8aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aaa := (n t8aaaa [w1,w2,w4,w7,w11,w60,w69,w112,w132] t8aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaa : ReplayTree.all (blocked 7 t7) t8aaa = true := by
  simp only [t8aaa, ReplayTree.all, n, ht8aaaa, ht8aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aabaa := (n (n (n (n (n z [w1,w2,w4,w7,w27,w60,w70,w105,w127] z) [w1,w2,w4,w7,w27,w60,w75,w98,w127] z) [w1,w2,w4,w7,w27,w60,w76,w98,w127] (n z [w1,w2,w4,w7,w27,w60,w76,w98,w132] z)) [w1,w2,w4,w7,w27,w60,w76,w101,w127] (n (n z [w1,w2,w4,w7,w27,w60,w76,w105,w127] z) [w1,w2,w4,w7,w27,w60,w76,w112,w127] (n z [w1,w2,w4,w7,w27,w60,w78,w98,w127] z))) [w1,w2,w4,w7,w27,w60,w83,w105,w127] (n (n (n (n z [w1,w2,w4,w7,w27,w60,w92,w98,w127] z) [w1,w2,w4,w7,w27,w69,w76,w98,w132] z) [w1,w2,w4,w7,w27,w69,w98,w105,w132] (n z [w1,w2,w4,w7,w27,w69,w105,w127,w132] z)) [w1,w2,w4,w7,w27,w69,w105,w132] (n (n z [w1,w2,w4,w7,w27,w76,w98,w127,w132] z) [w1,w2,w4,w7,w27,w76,w98,w132] (n z [w1,w2,w4,w7,w30,w60,w69,w105,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aabaa : ReplayTree.all (blocked 7 t7) t8aabaa = true := by
  decide +kernel
def t8aabab := (n (n (n (n (n z [w1,w2,w4,w7,w32,w60,w69,w105,w127] z) [w1,w2,w4,w7,w32,w60,w76,w98,w127] z) [w1,w2,w4,w7,w35,w60,w69,w105,w127] (n z [w1,w2,w4,w7,w35,w60,w76,w98,w127] z)) [w1,w2,w4,w7,w39,w60,w69,w105,w127] (n (n z [w1,w2,w4,w7,w39,w60,w76,w98,w127] z) [w1,w2,w4,w7,w42,w60,w69,w98,w127] (n z [w1,w2,w4,w7,w43,w60,w69,w98,w127] z))) [w1,w2,w4,w7,w44,w60,w69,w98,w127] (n (n (n (n z [w1,w2,w4,w7,w45,w60,w69,w98,w127] z) [w1,w2,w4,w7,w45,w60,w69,w98,w129] z) [w1,w2,w4,w7,w45,w60,w69,w98,w131] (n z [w1,w2,w4,w7,w45,w60,w69,w98,w132] z)) [w1,w2,w4,w7,w45,w60,w69,w101,w127] (n (n z [w1,w2,w4,w7,w45,w60,w69,w105,w127] z) [w1,w2,w4,w7,w45,w60,w69,w112,w127] (n z [w1,w2,w4,w7,w45,w60,w69,w121,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aabab : ReplayTree.all (blocked 7 t7) t8aabab = true := by
  decide +kernel
def t8aaba := (n t8aabaa [w1,w2,w4,w7,w30,w60,w76,w98,w127] t8aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aaba : ReplayTree.all (blocked 7 t7) t8aaba = true := by
  simp only [t8aaba, ReplayTree.all, n, ht8aabaa, ht8aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aabba := (n (n (n (n (n z [w1,w2,w4,w7,w45,w60,w76,w98,w127] z) [w1,w2,w4,w7,w45,w60,w83,w98,w127] z) [w1,w2,w4,w7,w45,w60,w92,w98,w127] (n z [w1,w2,w4,w7,w45,w69,w98,w127,w132] z)) [w1,w2,w4,w7,w45,w69,w98,w132] (n (n z [w1,w2,w4,w7,w50,w60,w69,w98,w127] z) [w1,w2,w4,w7,w52,w60,w69,w98,w127] (n z [w1,w2,w4,w7,w57,w60,w69,w98,w127] z))) [w1,w2,w4,w7,w60,w66,w69,w98,w127] (n (n (n (n z [w1,w2,w4,w7,w60,w69,w76,w112,w127] z) [w1,w2,w4,w7,w60,w69,w83,w105,w127] z) [w1,w2,w4,w7,w60,w69,w92,w98,w127] (n z [w1,w2,w4,w7,w60,w69,w98,w121,w127] z)) [w1,w2,w4,w7,w60,w69,w105,w112,w127] (n (n z [w1,w2,w4,w7,w60,w69,w105,w121,w127] z) [w1,w2,w4,w7,w60,w69,w112,w121,w127] (n z [w1,w2,w4,w7,w60,w69,w121,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aabba : ReplayTree.all (blocked 7 t7) t8aabba = true := by
  decide +kernel
def t8aabbb := (n (n (n (n (n z [w1,w2,w4,w7,w60,w76,w92,w98,w127] z) [w1,w2,w4,w7,w60,w76,w98,w112,w127] z) [w1,w2,w4,w7,w60,w76,w112,w127] (n z [w1,w2,w4,w7,w60,w83,w92,w98,w127] z)) [w1,w2,w4,w7,w60,w83,w98,w105,w127] (n (n z [w1,w2,w4,w7,w60,w83,w105,w127] z) [w1,w2,w4,w7,w60,w92,w98,w127] (n z [w1,w2,w4,w9,w11,w60,w69,w112,w127] z))) [w1,w2,w4,w9,w27,w60,w69,w105,w127] (n (n (n (n z [w1,w2,w4,w9,w45,w60,w69,w98,w127] z) [w1,w2,w4,w10,w27,w60,w69,w101,w127] z) [w1,w2,w4,w11,w26,w60,w69,w101,w127] (n z [w1,w2,w4,w11,w27,w60,w69,w101,w127] z)) [w1,w2,w4,w11,w27,w60,w69,w101,w131] (n (n z [w1,w2,w4,w11,w27,w60,w69,w101,w132] z) [w1,w2,w4,w11,w27,w60,w70,w101,w127] (n z [w1,w2,w4,w11,w27,w69,w98,w101,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aabbb : ReplayTree.all (blocked 7 t7) t8aabbb = true := by
  decide +kernel
def t8aabb := (n t8aabba [w1,w2,w4,w7,w60,w76,w83,w98,w127] t8aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aabb : ReplayTree.all (blocked 7 t7) t8aabb = true := by
  simp only [t8aabb, ReplayTree.all, n, ht8aabba, ht8aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aab := (n t8aaba [w1,w2,w4,w7,w45,w60,w70,w98,w127] t8aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aab : ReplayTree.all (blocked 7 t7) t8aab = true := by
  simp only [t8aab, ReplayTree.all, n, ht8aaba, ht8aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aa := (n t8aaa [w1,w2,w4,w7,w27,w60,w69,w121,w127] t8aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aa : ReplayTree.all (blocked 7 t7) t8aa = true := by
  simp only [t8aa, ReplayTree.all, n, ht8aaa, ht8aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8abaaa := (n (n (n (n (n z [w1,w2,w4,w11,w27,w69,w101,w132] z) [w1,w2,w4,w11,w30,w60,w69,w101,w127] z) [w1,w2,w4,w11,w32,w60,w69,w101,w127] (n z [w1,w2,w4,w11,w35,w60,w69,w101,w127] z)) [w1,w2,w4,w11,w38,w60,w69,w98,w127] (n (n z [w1,w2,w4,w11,w39,w60,w69,w101,w127] z) [w1,w2,w4,w11,w45,w60,w69,w101,w127] (n z [w1,w2,w4,w11,w60,w69,w83,w101,w127] z))) [w1,w2,w4,w11,w60,w69,w101,w112,w127] (n (n (n (n z [w1,w2,w4,w11,w60,w69,w101,w116,w127] z) [w1,w2,w4,w14,w27,w60,w69,w101,w127] z) [w1,w2,w4,w16,w27,w60,w69,w101,w127] (n z [w1,w2,w4,w19,w27,w60,w69,w101,w127] z)) [w1,w2,w4,w22,w27,w60,w69,w98,w127] (n (n z [w1,w2,w4,w23,w27,w60,w69,w101,w127] z) [w1,w2,w4,w23,w39,w60,w69,w98,w127] (n z [w1,w2,w4,w27,w45,w60,w69,w101,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abaaa : ReplayTree.all (blocked 7 t7) t8abaaa = true := by
  decide +kernel
def t8abaab := (n (n (n (n (n z [w1,w2,w4,w27,w60,w69,w101,w105,w127] z) [w1,w2,w4,w27,w60,w69,w101,w109,w127] z) [w1,w2,w4,w45,w60,w69,w98,w101,w127] (n z [w1,w2,w4,w45,w60,w69,w101,w127] z)) [w1,w2,w6,w7,w11,w27,w69,w98,w132] (n (n z [w1,w2,w6,w7,w11,w60,w69,w112,w127] z) [w1,w2,w6,w7,w11,w60,w83,w98,w127] (n z [w1,w2,w6,w7,w27,w60,w69,w105,w127] z))) [w1,w2,w6,w7,w27,w60,w76,w98,w127] (n (n (n (n z [w1,w2,w6,w7,w45,w60,w69,w98,w127] z) [w1,w2,w6,w11,w27,w60,w69,w101,w127] z) [w1,w2,w7,w10,w27,w60,w69,w98,w131] (n z [w1,w2,w7,w10,w35,w60,w69,w98,w127] z)) [w1,w2,w7,w11,w19,w27,w69,w98,w132] (n (n z [w1,w2,w7,w11,w19,w60,w69,w112,w127] z) [w1,w2,w7,w11,w19,w60,w83,w98,w127] (n z [w1,w2,w7,w11,w26,w60,w69,w98,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abaab : ReplayTree.all (blocked 7 t7) t8abaab = true := by
  decide +kernel
def t8abaa := (n t8abaaa [w1,w2,w4,w27,w60,w69,w76,w101,w127] t8abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abaa : ReplayTree.all (blocked 7 t7) t8abaa = true := by
  simp only [t8abaa, ReplayTree.all, n, ht8abaaa, ht8abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8ababa := (n (n (n (n (n z [w1,w2,w7,w11,w27,w60,w69,w98,w130] z) [w1,w2,w7,w11,w27,w60,w69,w98,w131] z) [w1,w2,w7,w11,w27,w60,w69,w98,w136] (n z [w1,w2,w7,w11,w27,w60,w69,w101,w131] z)) [w1,w2,w7,w11,w27,w60,w71,w98,w127] (n (n z [w1,w2,w7,w11,w27,w63,w69,w98,w127] z) [w1,w2,w7,w11,w27,w64,w69,w98,w132] (n z [w1,w2,w7,w11,w27,w69,w72,w98,w132] z))) [w1,w2,w7,w11,w27,w69,w98,w131,w132] (n (n (n (n z [w1,w2,w7,w11,w27,w69,w98,w132,w136] z) [w1,w2,w7,w11,w30,w60,w69,w98,w131] z) [w1,w2,w7,w11,w32,w60,w69,w98,w131] (n z [w1,w2,w7,w11,w33,w60,w69,w98,w127] z)) [w1,w2,w7,w11,w34,w60,w69,w98,w127] (n (n z [w1,w2,w7,w11,w35,w60,w69,w98,w127] z) [w1,w2,w7,w11,w35,w60,w69,w98,w129] (n z [w1,w2,w7,w11,w35,w60,w69,w98,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8ababa : ReplayTree.all (blocked 7 t7) t8ababa = true := by
  decide +kernel
def t8ababb := (n (n (n (n (n z [w1,w2,w7,w11,w35,w60,w69,w101,w127] z) [w1,w2,w7,w11,w35,w60,w69,w105,w127] z) [w1,w2,w7,w11,w35,w60,w69,w112,w127] (n z [w1,w2,w7,w11,w35,w60,w70,w98,w127] z)) [w1,w2,w7,w11,w35,w60,w76,w98,w127] (n (n z [w1,w2,w7,w11,w35,w60,w83,w98,w127] z) [w1,w2,w7,w11,w37,w60,w69,w98,w127] (n z [w1,w2,w7,w11,w39,w60,w69,w98,w131] z))) [w1,w2,w7,w11,w45,w60,w69,w98,w131] (n (n (n (n z [w1,w2,w7,w11,w57,w60,w69,w98,w127] z) [w1,w2,w7,w11,w60,w64,w69,w112,w127] z) [w1,w2,w7,w11,w60,w64,w83,w98,w127] (n z [w1,w2,w7,w11,w60,w69,w72,w112,w127] z)) [w1,w2,w7,w11,w60,w69,w83,w98,w131] (n (n z [w1,w2,w7,w11,w60,w69,w87,w98,w127] z) [w1,w2,w7,w11,w60,w69,w98,w112,w131] (n z [w1,w2,w7,w11,w60,w69,w112,w127,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8ababb : ReplayTree.all (blocked 7 t7) t8ababb = true := by
  decide +kernel
def t8abab := (n t8ababa [w1,w2,w7,w11,w35,w60,w69,w98,w132] t8ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abab : ReplayTree.all (blocked 7 t7) t8abab = true := by
  simp only [t8abab, ReplayTree.all, n, ht8ababa, ht8ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8aba := (n t8abaa [w1,w2,w7,w11,w27,w35,w69,w98,w132] t8abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8aba : ReplayTree.all (blocked 7 t7) t8aba = true := by
  simp only [t8aba, ReplayTree.all, n, ht8abaa, ht8abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8abbaa := (n (n (n (n (n z [w1,w2,w7,w11,w60,w83,w87,w98,w127] z) [w1,w2,w7,w11,w60,w83,w98,w127,w131] z) [w1,w2,w7,w14,w27,w60,w69,w98,w131] (n z [w1,w2,w7,w14,w35,w60,w69,w98,w127] z)) [w1,w2,w7,w16,w27,w60,w69,w98,w131] (n (n z [w1,w2,w7,w16,w35,w60,w69,w98,w127] z) [w1,w2,w7,w17,w27,w60,w69,w98,w127] (n z [w1,w2,w7,w18,w27,w60,w69,w98,w127] z))) [w1,w2,w7,w19,w26,w60,w69,w98,w127] (n (n (n (n z [w1,w2,w7,w19,w27,w60,w69,w98,w127] z) [w1,w2,w7,w19,w27,w60,w69,w98,w129] z) [w1,w2,w7,w19,w27,w60,w69,w98,w131] (n z [w1,w2,w7,w19,w27,w60,w69,w98,w132] z)) [w1,w2,w7,w19,w27,w60,w69,w101,w127] (n (n z [w1,w2,w7,w19,w27,w60,w69,w105,w127] z) [w1,w2,w7,w19,w27,w60,w69,w112,w127] (n z [w1,w2,w7,w19,w27,w60,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abbaa : ReplayTree.all (blocked 7 t7) t8abbaa = true := by
  decide +kernel
def t8abbab := (n (n (n (n (n z [w1,w2,w7,w19,w27,w60,w83,w98,w127] z) [w1,w2,w7,w19,w30,w60,w69,w98,w127] z) [w1,w2,w7,w19,w32,w60,w69,w98,w127] (n z [w1,w2,w7,w19,w35,w60,w69,w98,w127] z)) [w1,w2,w7,w19,w39,w60,w69,w98,w127] (n (n z [w1,w2,w7,w19,w45,w60,w69,w98,w127] z) [w1,w2,w7,w19,w57,w60,w69,w98,w127] (n z [w1,w2,w7,w19,w60,w69,w83,w98,w127] z))) [w1,w2,w7,w19,w60,w69,w98,w112,w127] (n (n (n (n z [w1,w2,w7,w19,w60,w69,w112,w127] z) [w1,w2,w7,w19,w60,w83,w98,w127] z) [w1,w2,w7,w21,w27,w60,w69,w98,w127] (n z [w1,w2,w7,w23,w27,w60,w69,w98,w131] z)) [w1,w2,w7,w23,w35,w60,w69,w98,w127] (n (n z [w1,w2,w7,w27,w35,w60,w69,w105,w127] z) [w1,w2,w7,w27,w35,w60,w76,w98,w127] (n z [w1,w2,w7,w27,w45,w60,w69,w98,w131] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abbab : ReplayTree.all (blocked 7 t7) t8abbab = true := by
  decide +kernel
def t8abba := (n t8abbaa [w1,w2,w7,w19,w27,w60,w76,w98,w127] t8abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abba : ReplayTree.all (blocked 7 t7) t8abba = true := by
  simp only [t8abba, ReplayTree.all, n, ht8abbaa, ht8abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8abbba := (n (n (n (n (n z [w1,w2,w7,w27,w60,w64,w69,w105,w127] z) [w1,w2,w7,w27,w60,w64,w76,w98,w127] z) [w1,w2,w7,w27,w60,w69,w72,w105,w127] (n z [w1,w2,w7,w27,w60,w69,w76,w98,w131] z)) [w1,w2,w7,w27,w60,w69,w80,w98,w127] (n (n z [w1,w2,w7,w27,w60,w69,w98,w105,w131] z) [w1,w2,w7,w27,w60,w69,w105,w127,w131] (n z [w1,w2,w7,w27,w60,w72,w76,w98,w127] z))) [w1,w2,w7,w27,w60,w76,w80,w98,w127] (n (n (n (n z [w1,w2,w7,w27,w60,w76,w98,w127,w131] z) [w1,w2,w7,w35,w45,w60,w69,w98,w127] z) [w1,w2,w7,w35,w57,w60,w69,w98,w127] (n z [w1,w2,w7,w35,w60,w69,w76,w98,w127] z)) [w1,w2,w7,w35,w60,w69,w98,w105,w127] (n (n z [w1,w2,w7,w35,w60,w69,w105,w127] z) [w1,w2,w7,w35,w60,w76,w98,w127] (n z [w1,w2,w7,w45,w57,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abbba : ReplayTree.all (blocked 7 t7) t8abbba = true := by
  decide +kernel
def t8abbbb := (n (n (n (n (n z [w1,w2,w7,w45,w60,w69,w72,w98,w127] z) [w1,w2,w7,w45,w60,w69,w98,w127,w131] z) [w1,w2,w7,w45,w60,w69,w98,w131] (n z [w1,w2,w7,w57,w60,w69,w98,w127] z)) [w1,w2,w11,w27,w60,w64,w69,w101,w127] (n (n z [w1,w2,w11,w27,w60,w69,w72,w101,w127] z) [w1,w2,w11,w27,w60,w69,w98,w101,w131] (n z [w1,w2,w11,w27,w60,w69,w101,w127,w131] z))) [w1,w2,w11,w27,w60,w69,w101,w131] (n (n (n z [w1,w3,w7,w11,w27,w60,w70,w98,w127] z) [w1,w4,w6,w7,w11,w60,w83,w98,w127] (n z [w1,w4,w6,w7,w27,w60,w76,w98,w127] z)) [w1,w4,w6,w7,w45,w60,w69,w98,w127] (n (n z [w1,w4,w6,w11,w27,w60,w69,w101,w127] z) [w1,w4,w7,w10,w27,w60,w70,w98,w127] (n z [w1,w4,w7,w11,w26,w60,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abbbb : ReplayTree.all (blocked 7 t7) t8abbbb = true := by
  decide +kernel
def t8abbb := (n t8abbba [w1,w2,w7,w45,w60,w64,w69,w98,w127] t8abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abbb : ReplayTree.all (blocked 7 t7) t8abbb = true := by
  simp only [t8abbb, ReplayTree.all, n, ht8abbba, ht8abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8abb := (n t8abba [w1,w2,w7,w27,w57,w60,w69,w98,w127] t8abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8abb : ReplayTree.all (blocked 7 t7) t8abb = true := by
  simp only [t8abb, ReplayTree.all, n, ht8abba, ht8abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8ab := (n t8aba [w1,w2,w7,w11,w60,w72,w83,w98,w127] t8abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8ab : ReplayTree.all (blocked 7 t7) t8ab = true := by
  simp only [t8ab, ReplayTree.all, n, ht8aba, ht8abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8a := (n t8aa [w1,w2,w4,w11,w27,w69,w101,w127,w132] t8ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8a : ReplayTree.all (blocked 7 t7) t8a = true := by
  simp only [t8a, ReplayTree.all, n, ht8aa, ht8ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8baaaa := (n (n (n (n (n z [w1,w4,w7,w11,w27,w60,w70,w98,w129] z) [w1,w4,w7,w11,w27,w60,w70,w98,w132] z) [w1,w4,w7,w11,w27,w60,w70,w101,w127] (n z [w1,w4,w7,w11,w27,w69,w70,w98,w132] z)) [w1,w4,w7,w11,w27,w70,w98,w127,w132] (n (n z [w1,w4,w7,w11,w27,w70,w98,w132] z) [w1,w4,w7,w11,w30,w60,w70,w98,w127] (n z [w1,w4,w7,w11,w31,w60,w69,w98,w127] z))) [w1,w4,w7,w11,w32,w60,w70,w98,w127] (n (n (n (n z [w1,w4,w7,w11,w35,w60,w70,w98,w127] z) [w1,w4,w7,w11,w39,w60,w70,w98,w127] z) [w1,w4,w7,w11,w45,w60,w70,w98,w127] (n z [w1,w4,w7,w11,w60,w70,w83,w98,w127] z)) [w1,w4,w7,w11,w60,w70,w85,w98,w127] (n (n z [w1,w4,w7,w11,w60,w70,w98,w112,w127] z) [w1,w4,w7,w14,w27,w60,w70,w98,w127] (n z [w1,w4,w7,w15,w27,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baaaa : ReplayTree.all (blocked 7 t7) t8baaaa = true := by
  decide +kernel
def t8baaab := (n (n (n (n (n z [w1,w4,w7,w16,w32,w60,w69,w98,w127] z) [w1,w4,w7,w19,w27,w60,w70,w98,w127] z) [w1,w4,w7,w23,w27,w60,w70,w98,w127] (n z [w1,w4,w7,w27,w45,w60,w70,w98,w127] z)) [w1,w4,w7,w27,w60,w70,w76,w98,w127] (n (n z [w1,w4,w7,w27,w60,w70,w78,w98,w127] z) [w1,w4,w7,w27,w60,w70,w98,w105,w127] (n z [w1,w4,w7,w45,w60,w69,w70,w98,w127] z))) [w1,w4,w7,w45,w60,w70,w98,w127] (n (n (n (n z [w1,w4,w9,w11,w27,w60,w70,w98,w127] z) [w1,w4,w11,w27,w60,w69,w70,w101,w127] z) [w1,w4,w11,w27,w60,w70,w98,w101,w127] (n z [w1,w4,w11,w27,w60,w70,w101,w127] z)) [w1,w5,w7,w11,w27,w60,w69,w98,w127] (n (n z [w1,w6,w7,w10,w27,w60,w69,w98,w127] z) [w1,w6,w7,w11,w26,w60,w69,w98,w127] (n z [w1,w6,w7,w11,w27,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baaab : ReplayTree.all (blocked 7 t7) t8baaab = true := by
  decide +kernel
def t8baaa := (n t8baaaa [w1,w4,w7,w16,w27,w60,w70,w98,w127] t8baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baaa : ReplayTree.all (blocked 7 t7) t8baaa = true := by
  simp only [t8baaa, ReplayTree.all, n, ht8baaaa, ht8baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8baaba := (n (n (n (n (n z [w1,w6,w7,w11,w27,w60,w69,w98,w131] z) [w1,w6,w7,w11,w27,w60,w69,w98,w132] z) [w1,w6,w7,w11,w27,w60,w69,w101,w127] (n z [w1,w6,w7,w11,w27,w60,w70,w98,w127] z)) [w1,w6,w7,w11,w27,w60,w76,w98,w127] (n (n z [w1,w6,w7,w11,w27,w60,w83,w98,w127] z) [w1,w6,w7,w11,w30,w60,w69,w98,w127] (n z [w1,w6,w7,w11,w32,w60,w69,w98,w127] z))) [w1,w6,w7,w11,w35,w60,w69,w98,w127] (n (n (n (n z [w1,w6,w7,w11,w37,w60,w69,w98,w127] z) [w1,w6,w7,w11,w39,w60,w69,w98,w127] z) [w1,w6,w7,w11,w45,w60,w69,w98,w127] (n z [w1,w6,w7,w11,w60,w69,w83,w98,w127] z)) [w1,w6,w7,w11,w60,w69,w98,w112,w127] (n (n z [w1,w6,w7,w11,w60,w83,w98,w127] z) [w1,w6,w7,w14,w27,w60,w69,w98,w127] (n z [w1,w6,w7,w16,w27,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baaba : ReplayTree.all (blocked 7 t7) t8baaba = true := by
  decide +kernel
def t8baabb := (n (n (n (n (n z [w1,w6,w7,w21,w27,w60,w69,w98,w127] z) [w1,w6,w7,w23,w27,w60,w69,w98,w127] z) [w1,w6,w7,w27,w45,w60,w69,w98,w127] (n z [w1,w6,w7,w27,w60,w69,w76,w98,w127] z)) [w1,w6,w7,w27,w60,w69,w98,w105,w127] (n (n z [w1,w6,w7,w27,w60,w76,w98,w127] z) [w1,w6,w7,w45,w60,w69,w98,w127] (n z [w1,w6,w9,w11,w27,w60,w69,w98,w127] z))) [w1,w6,w11,w27,w60,w69,w98,w101,w127] (n (n (n (n z [w1,w6,w11,w27,w60,w69,w101,w127] z) [w1,w7,w11,w19,w27,w60,w70,w98,w127] z) [w1,w7,w11,w27,w35,w60,w70,w98,w127] (n z [w1,w7,w11,w27,w60,w64,w70,w98,w127] z)) [w1,w7,w11,w27,w60,w69,w70,w98,w131] (n (n z [w1,w7,w11,w27,w60,w69,w74,w98,w127] z) [w1,w7,w11,w27,w60,w70,w72,w98,w127] (n z [w1,w7,w11,w27,w60,w70,w74,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baabb : ReplayTree.all (blocked 7 t7) t8baabb = true := by
  decide +kernel
def t8baab := (n t8baaba [w1,w6,w7,w19,w27,w60,w69,w98,w127] t8baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baab : ReplayTree.all (blocked 7 t7) t8baab = true := by
  simp only [t8baab, ReplayTree.all, n, ht8baaba, ht8baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8baa := (n t8baaa [w1,w6,w7,w11,w27,w60,w69,w98,w129] t8baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baa : ReplayTree.all (blocked 7 t7) t8baa = true := by
  simp only [t8baa, ReplayTree.all, n, ht8baaa, ht8baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8babaa := (n (n (n (n (n z [w1,w7,w11,w35,w60,w69,w70,w98,w127] z) [w1,w7,w11,w35,w60,w70,w98,w127] z) [w1,w7,w19,w27,w60,w69,w70,w98,w127] (n z [w1,w7,w19,w27,w60,w70,w98,w127] z)) [w2,w3,w7,w11,w27,w60,w69,w98,w129] (n (n z [w2,w3,w7,w11,w30,w60,w69,w98,w127] z) [w2,w3,w7,w14,w27,w60,w69,w98,w127] (n z [w2,w3,w9,w11,w27,w60,w69,w98,w127] z))) [w2,w4,w7,w9,w11,w27,w69,w98,w132] (n (n (n (n z [w2,w4,w7,w9,w11,w60,w69,w112,w127] z) [w2,w4,w7,w9,w11,w60,w83,w98,w127] z) [w2,w4,w7,w9,w27,w60,w69,w105,w127] (n z [w2,w4,w7,w9,w27,w60,w76,w98,w127] z)) [w2,w4,w7,w9,w45,w60,w69,w98,w127] (n (n z [w2,w4,w7,w10,w27,w60,w69,w98,w129] z) [w2,w4,w7,w10,w30,w60,w69,w98,w127] (n z [w2,w4,w7,w11,w14,w27,w69,w98,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8babaa : ReplayTree.all (blocked 7 t7) t8babaa = true := by
  decide +kernel
def t8babab := (n (n (n (n (n z [w2,w4,w7,w11,w14,w60,w83,w98,w127] z) [w2,w4,w7,w11,w26,w60,w69,w98,w129] z) [w2,w4,w7,w11,w27,w30,w69,w98,w132] (n z [w2,w4,w7,w11,w27,w60,w69,w98,w128] z)) [w2,w4,w7,w11,w27,w60,w69,w98,w129] (n (n z [w2,w4,w7,w11,w27,w60,w69,w98,w134] z) [w2,w4,w7,w11,w27,w60,w69,w99,w127] (n z [w2,w4,w7,w11,w27,w60,w70,w98,w129] z))) [w2,w4,w7,w11,w27,w61,w69,w98,w127] (n (n (n (n z [w2,w4,w7,w11,w27,w62,w69,w98,w132] z) [w2,w4,w7,w11,w27,w69,w98,w100,w132] z) [w2,w4,w7,w11,w27,w69,w98,w129,w132] (n z [w2,w4,w7,w11,w27,w69,w98,w132,w134] z)) [w2,w4,w7,w11,w28,w60,w69,w98,w127] (n (n z [w2,w4,w7,w11,w29,w60,w69,w98,w127] z) [w2,w4,w7,w11,w30,w60,w69,w98,w127] (n z [w2,w4,w7,w11,w30,w60,w69,w98,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8babab : ReplayTree.all (blocked 7 t7) t8babab = true := by
  decide +kernel
def t8baba := (n t8babaa [w2,w4,w7,w11,w14,w60,w69,w112,w127] t8babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8baba : ReplayTree.all (blocked 7 t7) t8baba = true := by
  simp only [t8baba, ReplayTree.all, n, ht8babaa, ht8babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8babba := (n (n (n (n (n z [w2,w4,w7,w11,w30,w60,w69,w98,w132] z) [w2,w4,w7,w11,w30,w60,w69,w101,w127] z) [w2,w4,w7,w11,w30,w60,w69,w105,w127] (n z [w2,w4,w7,w11,w30,w60,w69,w112,w127] z)) [w2,w4,w7,w11,w30,w60,w70,w98,w127] (n (n z [w2,w4,w7,w11,w30,w60,w76,w98,w127] z) [w2,w4,w7,w11,w30,w60,w83,w98,w127] (n z [w2,w4,w7,w11,w32,w60,w69,w98,w129] z))) [w2,w4,w7,w11,w35,w60,w69,w98,w129] (n (n (n (n z [w2,w4,w7,w11,w39,w60,w69,w98,w129] z) [w2,w4,w7,w11,w41,w60,w69,w98,w127] z) [w2,w4,w7,w11,w45,w60,w69,w98,w129] (n z [w2,w4,w7,w11,w50,w60,w69,w98,w127] z)) [w2,w4,w7,w11,w60,w62,w69,w112,w127] (n (n z [w2,w4,w7,w11,w60,w62,w83,w98,w127] z) [w2,w4,w7,w11,w60,w69,w83,w98,w129] (n z [w2,w4,w7,w11,w60,w69,w98,w112,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8babba : ReplayTree.all (blocked 7 t7) t8babba = true := by
  decide +kernel
def t8babbb := (n (n (n (n (n z [w2,w4,w7,w11,w60,w69,w100,w112,w127] z) [w2,w4,w7,w11,w60,w69,w112,w114,w127] z) [w2,w4,w7,w11,w60,w69,w112,w127,w129] (n z [w2,w4,w7,w11,w60,w83,w98,w100,w127] z)) [w2,w4,w7,w11,w60,w83,w98,w127,w129] (n (n z [w2,w4,w7,w12,w27,w60,w69,w98,w127] z) [w2,w4,w7,w13,w27,w60,w69,w98,w127] (n z [w2,w4,w7,w14,w26,w60,w69,w98,w127] z))) [w2,w4,w7,w14,w27,w60,w69,w98,w127] (n (n (n z [w2,w4,w7,w14,w27,w60,w69,w98,w129] z) [w2,w4,w7,w14,w27,w60,w69,w98,w131] (n z [w2,w4,w7,w14,w27,w60,w69,w98,w132] z)) [w2,w4,w7,w14,w27,w60,w69,w101,w127] (n (n z [w2,w4,w7,w14,w27,w60,w69,w105,w127] z) [w2,w4,w7,w14,w27,w60,w69,w112,w127] (n z [w2,w4,w7,w14,w27,w60,w70,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8babbb : ReplayTree.all (blocked 7 t7) t8babbb = true := by
  decide +kernel
def t8babb := (n t8babba [w2,w4,w7,w11,w60,w69,w98,w114,w127] t8babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8babb : ReplayTree.all (blocked 7 t7) t8babb = true := by
  simp only [t8babb, ReplayTree.all, n, ht8babba, ht8babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bab := (n t8baba [w2,w4,w7,w11,w30,w60,w69,w98,w131] t8babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bab : ReplayTree.all (blocked 7 t7) t8bab = true := by
  simp only [t8bab, ReplayTree.all, n, ht8baba, ht8babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8ba := (n t8baa [w1,w7,w11,w27,w60,w70,w98,w127,w131] t8bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8ba : ReplayTree.all (blocked 7 t7) t8ba = true := by
  simp only [t8ba, ReplayTree.all, n, ht8baa, ht8bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bbaaa := (n (n (n (n (n z [w2,w4,w7,w14,w27,w60,w83,w98,w127] z) [w2,w4,w7,w14,w30,w60,w69,w98,w127] z) [w2,w4,w7,w14,w32,w60,w69,w98,w127] (n z [w2,w4,w7,w14,w35,w60,w69,w98,w127] z)) [w2,w4,w7,w14,w39,w60,w69,w98,w127] (n (n z [w2,w4,w7,w14,w45,w60,w69,w98,w127] z) [w2,w4,w7,w14,w50,w60,w69,w98,w127] (n z [w2,w4,w7,w14,w60,w69,w83,w98,w127] z))) [w2,w4,w7,w14,w60,w69,w98,w112,w127] (n (n (n (n z [w2,w4,w7,w14,w60,w69,w112,w127] z) [w2,w4,w7,w14,w60,w83,w98,w127] z) [w2,w4,w7,w16,w27,w60,w69,w98,w129] (n z [w2,w4,w7,w16,w30,w60,w69,w98,w127] z)) [w2,w4,w7,w19,w27,w60,w69,w98,w129] (n (n z [w2,w4,w7,w19,w30,w60,w69,w98,w127] z) [w2,w4,w7,w23,w27,w60,w69,w98,w129] (n z [w2,w4,w7,w23,w30,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbaaa : ReplayTree.all (blocked 7 t7) t8bbaaa = true := by
  decide +kernel
def t8bbaab := (n (n (n (n (n z [w2,w4,w7,w27,w30,w60,w69,w105,w127] z) [w2,w4,w7,w27,w30,w60,w76,w98,w127] z) [w2,w4,w7,w27,w45,w60,w69,w98,w129] (n z [w2,w4,w7,w27,w50,w60,w69,w98,w127] z)) [w2,w4,w7,w27,w60,w62,w69,w105,w127] (n (n z [w2,w4,w7,w27,w60,w62,w76,w98,w127] z) [w2,w4,w7,w27,w60,w69,w76,w98,w129] (n z [w2,w4,w7,w27,w60,w69,w98,w105,w129] z))) [w2,w4,w7,w27,w60,w69,w98,w107,w127] (n (n (n (n z [w2,w4,w7,w27,w60,w69,w100,w105,w127] z) [w2,w4,w7,w27,w60,w69,w105,w107,w127] z) [w2,w4,w7,w27,w60,w69,w105,w127,w129] (n z [w2,w4,w7,w27,w60,w76,w98,w100,w127] z)) [w2,w4,w7,w27,w60,w76,w98,w127,w129] (n (n z [w2,w4,w7,w30,w45,w60,w69,w98,w127] z) [w2,w4,w7,w30,w50,w60,w69,w98,w127] (n z [w2,w4,w7,w30,w60,w69,w76,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbaab : ReplayTree.all (blocked 7 t7) t8bbaab = true := by
  decide +kernel
def t8bbaa := (n t8bbaaa [w2,w4,w7,w25,w27,w60,w69,w98,w127] t8bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbaa : ReplayTree.all (blocked 7 t7) t8bbaa = true := by
  simp only [t8bbaa, ReplayTree.all, n, ht8bbaaa, ht8bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bbaba := (n (n (n (n (n z [w2,w4,w7,w30,w60,w69,w105,w127] z) [w2,w4,w7,w30,w60,w76,w98,w127] z) [w2,w4,w7,w45,w50,w60,w69,w98,w127] (n z [w2,w4,w7,w45,w60,w62,w69,w98,w127] z)) [w2,w4,w7,w45,w60,w69,w98,w100,w127] (n (n z [w2,w4,w7,w45,w60,w69,w98,w127,w129] z) [w2,w4,w7,w45,w60,w69,w98,w129] (n z [w2,w4,w7,w50,w60,w69,w98,w127] z))) [w2,w4,w8,w11,w27,w60,w69,w98,w127] (n (n (n (n z [w2,w4,w9,w10,w27,w60,w69,w98,w127] z) [w2,w4,w9,w11,w26,w60,w69,w98,w127] z) [w2,w4,w9,w11,w27,w60,w69,w98,w127] (n z [w2,w4,w9,w11,w27,w60,w69,w98,w129] z)) [w2,w4,w9,w11,w27,w60,w69,w98,w131] (n (n z [w2,w4,w9,w11,w27,w60,w69,w98,w132] z) [w2,w4,w9,w11,w27,w60,w69,w101,w127] (n z [w2,w4,w9,w11,w27,w60,w69,w105,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbaba : ReplayTree.all (blocked 7 t7) t8bbaba = true := by
  decide +kernel
def t8bbabb := (n (n (n (n (n z [w2,w4,w9,w11,w27,w60,w70,w98,w127] z) [w2,w4,w9,w11,w30,w60,w69,w98,w127] z) [w2,w4,w9,w11,w32,w60,w69,w98,w127] (n z [w2,w4,w9,w11,w35,w60,w69,w98,w127] z)) [w2,w4,w9,w11,w39,w60,w69,w98,w127] (n (n z [w2,w4,w9,w11,w41,w60,w69,w98,w127] z) [w2,w4,w9,w11,w45,w60,w69,w98,w127] (n z [w2,w4,w9,w11,w60,w69,w83,w98,w127] z))) [w2,w4,w9,w11,w60,w69,w98,w112,w127] (n (n (n (n z [w2,w4,w9,w11,w60,w69,w112,w127] z) [w2,w4,w9,w14,w27,w60,w69,w98,w127] z) [w2,w4,w9,w16,w27,w60,w69,w98,w127] (n z [w2,w4,w9,w19,w27,w60,w69,w98,w127] z)) [w2,w4,w9,w23,w27,w60,w69,w98,w127] (n (n z [w2,w4,w9,w25,w27,w60,w69,w98,w127] z) [w2,w4,w9,w27,w45,w60,w69,w98,w127] (n z [w2,w4,w9,w27,w60,w69,w76,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbabb : ReplayTree.all (blocked 7 t7) t8bbabb = true := by
  decide +kernel
def t8bbab := (n t8bbaba [w2,w4,w9,w11,w27,w60,w69,w112,w127] t8bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbab : ReplayTree.all (blocked 7 t7) t8bbab = true := by
  simp only [t8bbab, ReplayTree.all, n, ht8bbaba, ht8bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bba := (n t8bbaa [w2,w4,w7,w30,w60,w69,w98,w105,w127] t8bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bba : ReplayTree.all (blocked 7 t7) t8bba = true := by
  simp only [t8bba, ReplayTree.all, n, ht8bbaa, ht8bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bbbaa := (n (n (n (n (n z [w2,w4,w9,w27,w60,w69,w105,w127] z) [w2,w4,w9,w45,w60,w69,w98,w127] z) [w2,w4,w11,w14,w27,w60,w69,w101,w127] (n z [w2,w4,w11,w27,w30,w60,w69,w101,w127] z)) [w2,w4,w11,w27,w60,w62,w69,w101,w127] (n (n z [w2,w4,w11,w27,w60,w69,w98,w101,w129] z) [w2,w4,w11,w27,w60,w69,w98,w103,w127] (n z [w2,w4,w11,w27,w60,w69,w100,w101,w127] z))) [w2,w4,w11,w27,w60,w69,w101,w103,w127] (n (n (n (n z [w2,w4,w11,w27,w60,w69,w101,w127,w129] z) [w2,w4,w11,w30,w60,w69,w98,w101,w127] z) [w2,w4,w11,w30,w60,w69,w101,w127] (n z [w2,w4,w14,w27,w60,w69,w98,w101,w127] z)) [w2,w4,w14,w27,w60,w69,w101,w127] (n (n z [w2,w6,w7,w11,w27,w60,w69,w98,w129] z) [w2,w6,w7,w11,w30,w60,w69,w98,w127] (n z [w2,w6,w7,w14,w27,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbbaa : ReplayTree.all (blocked 7 t7) t8bbbaa = true := by
  decide +kernel
def t8bbbab := (n (n (n (n (n z [w2,w7,w9,w11,w27,w60,w69,w98,w131] z) [w2,w7,w9,w11,w35,w60,w69,w98,w127] z) [w2,w7,w9,w19,w27,w60,w69,w98,w127] (n z [w2,w7,w11,w14,w27,w60,w69,w98,w131] z)) [w2,w7,w11,w14,w35,w60,w69,w98,w127] (n (n z [w2,w7,w11,w19,w27,w60,w69,w98,w129] z) [w2,w7,w11,w19,w30,w60,w69,w98,w127] (n z [w2,w7,w11,w27,w30,w60,w69,w98,w131] z))) [w2,w7,w11,w27,w35,w60,w69,w98,w129] (n (n (n (n z [w2,w7,w11,w27,w60,w62,w69,w98,w131] z) [w2,w7,w11,w27,w60,w64,w69,w98,w129] z) [w2,w7,w11,w27,w60,w69,w72,w98,w129] (n z [w2,w7,w11,w27,w60,w69,w98,w100,w131] z)) [w2,w7,w11,w27,w60,w69,w98,w129,w131] (n (n z [w2,w7,w11,w27,w62,w64,w69,w98,w127] z) [w2,w7,w11,w30,w35,w60,w69,w98,w127] (n z [w2,w7,w11,w30,w60,w64,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbbab : ReplayTree.all (blocked 7 t7) t8bbbab = true := by
  decide +kernel
def t8bbba := (n t8bbbaa [w2,w6,w9,w11,w27,w60,w69,w98,w127] t8bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbba : ReplayTree.all (blocked 7 t7) t8bbba = true := by
  simp only [t8bbba, ReplayTree.all, n, ht8bbbaa, ht8bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bbbba := (n (n (n (n (n z [w2,w7,w11,w30,w60,w69,w98,w127,w131] z) [w2,w7,w11,w30,w60,w69,w98,w131] z) [w2,w7,w11,w35,w60,w62,w69,w98,w127] (n z [w2,w7,w11,w35,w60,w69,w98,w100,w127] z)) [w2,w7,w11,w35,w60,w69,w98,w127,w129] (n (n z [w2,w7,w11,w35,w60,w69,w98,w129] z) [w2,w7,w14,w19,w27,w60,w69,w98,w127] (n z [w2,w7,w14,w27,w35,w60,w69,w98,w127] z))) [w2,w7,w14,w27,w60,w64,w69,w98,w127] (n (n (n (n z [w2,w7,w14,w27,w60,w69,w72,w98,w127] z) [w2,w7,w14,w27,w60,w69,w98,w127,w131] z) [w2,w7,w14,w27,w60,w69,w98,w131] (n z [w2,w7,w14,w35,w60,w69,w98,w127] z)) [w2,w7,w19,w27,w30,w60,w69,w98,w127] (n (n z [w2,w7,w19,w27,w60,w62,w69,w98,w127] z) [w2,w7,w19,w27,w60,w69,w98,w100,w127] (n z [w2,w7,w19,w27,w60,w69,w98,w127,w129] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbbba : ReplayTree.all (blocked 7 t7) t8bbbba = true := by
  decide +kernel
def t8bbbbb := (n (n (n (n (n z [w2,w7,w19,w30,w60,w69,w98,w127] z) [w2,w9,w11,w27,w60,w64,w69,w98,w127] z) [w2,w9,w11,w27,w60,w69,w72,w98,w127] (n z [w4,w6,w9,w11,w27,w60,w69,w98,w127] z)) [w4,w7,w9,w11,w27,w60,w70,w98,w127] (n (n z [w4,w7,w11,w27,w60,w62,w70,w98,w127] z) [w4,w7,w11,w27,w60,w69,w70,w98,w129] (n z [w4,w7,w11,w27,w60,w70,w98,w100,w127] z))) [w4,w7,w11,w27,w60,w70,w98,w127,w129] (n (n (n z [w4,w7,w11,w27,w60,w70,w98,w129] z) [w4,w9,w11,w27,w60,w69,w70,w98,w127] (n z [w4,w9,w11,w27,w60,w70,w98,w127] z)) [w6,w7,w9,w11,w27,w60,w69,w98,w127] (n (n z [w6,w7,w11,w27,w60,w62,w69,w98,w127] z) [w6,w7,w11,w27,w60,w69,w98,w100,w127] (n z [w6,w9,w11,w27,w60,w69,w98,w127] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbbbb : ReplayTree.all (blocked 7 t7) t8bbbbb = true := by
  decide +kernel
def t8bbbb := (n t8bbbba [w2,w7,w19,w27,w60,w69,w98,w129] t8bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbbb : ReplayTree.all (blocked 7 t7) t8bbbb = true := by
  simp only [t8bbbb, ReplayTree.all, n, ht8bbbba, ht8bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bbb := (n t8bbba [w2,w7,w11,w30,w60,w69,w72,w98,w127] t8bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bbb : ReplayTree.all (blocked 7 t7) t8bbb = true := by
  simp only [t8bbb, ReplayTree.all, n, ht8bbba, ht8bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8bb := (n t8bba [w2,w4,w9,w27,w60,w69,w98,w105,w127] t8bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8bb : ReplayTree.all (blocked 7 t7) t8bb = true := by
  simp only [t8bb, ReplayTree.all, n, ht8bba, ht8bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8b := (n t8ba [w2,w4,w7,w14,w27,w60,w76,w98,w127] t8bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8b : ReplayTree.all (blocked 7 t7) t8b = true := by
  simp only [t8b, ReplayTree.all, n, ht8ba, ht8bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8 := (n t8a [w1,w4,w7,w11,w27,w60,w70,w98,w127] t8b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht8 : ReplayTree.all (blocked 7 t7) t8 = true := by
  simp only [t8, ReplayTree.all, n, ht8a, ht8b, Bool.true_and, Bool.and_true]
  decide +kernel
theorem s8 : sound 8 t8 := layer_sound s7 ht8
def t9aa := (n (n (n (n z [w0,w2,w4,w7,w11,w27,w60,w69,w98,w127] z) [w1,w2,w3,w7,w11,w27,w60,w69,w98,w127] (n z [w1,w2,w4,w7,w10,w27,w60,w69,w98,w127] z)) [w1,w2,w4,w7,w11,w26,w60,w69,w98,w127] (n (n z [w1,w2,w4,w7,w11,w27,w60,w69,w98,w129] z) [w1,w2,w4,w7,w11,w27,w60,w69,w98,w131] (n z [w1,w2,w4,w7,w11,w27,w60,w69,w98,w132] z))) [w1,w2,w4,w7,w11,w27,w60,w69,w101,w127] (n (n (n z [w1,w2,w4,w7,w11,w27,w60,w69,w105,w127] z) [w1,w2,w4,w7,w11,w27,w60,w69,w112,w127] (n z [w1,w2,w4,w7,w11,w27,w60,w70,w98,w127] z)) [w1,w2,w4,w7,w11,w27,w60,w76,w98,w127] (n (n z [w1,w2,w4,w7,w11,w27,w60,w83,w98,w127] z) [w1,w2,w4,w7,w11,w27,w69,w98,w127,w132] (n z [w1,w2,w4,w7,w11,w27,w69,w98,w132] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9aa : ReplayTree.all (blocked 8 t8) t9aa = true := by
  decide +kernel
def t9ab := (n (n (n (n z [w1,w2,w4,w7,w11,w32,w60,w69,w98,w127] z) [w1,w2,w4,w7,w11,w35,w60,w69,w98,w127] (n z [w1,w2,w4,w7,w11,w39,w60,w69,w98,w127] z)) [w1,w2,w4,w7,w11,w45,w60,w69,w98,w127] (n (n z [w1,w2,w4,w7,w11,w60,w69,w83,w98,w127] z) [w1,w2,w4,w7,w11,w60,w69,w98,w112,w127] (n z [w1,w2,w4,w7,w11,w60,w69,w112,w127] z))) [w1,w2,w4,w7,w11,w60,w83,w98,w127] (n (n (n z [w1,w2,w4,w7,w14,w27,w60,w69,w98,w127] z) [w1,w2,w4,w7,w16,w27,w60,w69,w98,w127] (n z [w1,w2,w4,w7,w19,w27,w60,w69,w98,w127] z)) [w1,w2,w4,w7,w23,w27,w60,w69,w98,w127] (n (n z [w1,w2,w4,w7,w27,w45,w60,w69,w98,w127] z) [w1,w2,w4,w7,w27,w60,w69,w76,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9ab : ReplayTree.all (blocked 8 t8) t9ab = true := by
  decide +kernel
def t9a := (n t9aa [w1,w2,w4,w7,w11,w30,w60,w69,w98,w127] t9ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9a : ReplayTree.all (blocked 8 t8) t9a = true := by
  simp only [t9a, ReplayTree.all, n, ht9aa, ht9ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t9ba := (n (n (n (n z [w1,w2,w4,w7,w27,w60,w69,w105,w127] z) [w1,w2,w4,w7,w27,w60,w76,w98,w127] (n z [w1,w2,w4,w7,w45,w60,w69,w98,w127] z)) [w1,w2,w4,w9,w11,w27,w60,w69,w98,w127] (n (n z [w1,w2,w4,w11,w27,w60,w69,w98,w101,w127] z) [w1,w2,w4,w11,w27,w60,w69,w101,w127] (n z [w1,w2,w6,w7,w11,w27,w60,w69,w98,w127] z))) [w1,w2,w7,w11,w19,w27,w60,w69,w98,w127] (n (n (n z [w1,w2,w7,w11,w27,w35,w60,w69,w98,w127] z) [w1,w2,w7,w11,w27,w60,w64,w69,w98,w127] (n z [w1,w2,w7,w11,w27,w60,w69,w72,w98,w127] z)) [w1,w2,w7,w11,w27,w60,w69,w98,w127,w131] (n (n z [w1,w2,w7,w11,w27,w60,w69,w98,w131] z) [w1,w2,w7,w11,w35,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9ba : ReplayTree.all (blocked 8 t8) t9ba = true := by
  decide +kernel
def t9bb := (n (n (n (n z [w1,w4,w6,w7,w11,w27,w60,w69,w98,w127] z) [w1,w4,w7,w11,w27,w60,w69,w70,w98,w127] (n z [w1,w4,w7,w11,w27,w60,w70,w98,w127] z)) [w1,w6,w7,w11,w27,w60,w69,w98,w127] (n (n z [w2,w4,w7,w9,w11,w27,w60,w69,w98,w127] z) [w2,w4,w7,w11,w14,w27,w60,w69,w98,w127] (n z [w2,w4,w7,w11,w27,w30,w60,w69,w98,w127] z))) [w2,w4,w7,w11,w27,w60,w62,w69,w98,w127] (n (n (n z [w2,w4,w7,w11,w27,w60,w69,w98,w100,w127] z) [w2,w4,w7,w11,w27,w60,w69,w98,w127,w129] (n z [w2,w4,w7,w11,w27,w60,w69,w98,w129] z)) [w2,w4,w7,w11,w30,w60,w69,w98,w127] (n (n z [w2,w4,w7,w14,w27,w60,w69,w98,w127] z) [w2,w4,w9,w11,w27,w60,w69,w98,w127] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9bb : ReplayTree.all (blocked 8 t8) t9bb = true := by
  decide +kernel
def t9b := (n t9ba [w1,w2,w7,w19,w27,w60,w69,w98,w127] t9bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9b : ReplayTree.all (blocked 8 t8) t9b = true := by
  simp only [t9b, ReplayTree.all, n, ht9ba, ht9bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t9 := (n t9a [w1,w2,w4,w7,w27,w60,w69,w98,w105,w127] t9b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht9 : ReplayTree.all (blocked 8 t8) t9 = true := by
  simp only [t9, ReplayTree.all, n, ht9a, ht9b, Bool.true_and, Bool.and_true]
  decide +kernel
theorem s9 : sound 9 t9 := layer_sound s8 ht9
def t10 := (n z [w1,w2,w4,w7,w11,w27,w60,w69,w98,w127] z)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ht10 : ReplayTree.all (blocked 9 t9) t10 = true := by
  decide +kernel
theorem s10 : sound 10 t10 := layer_sound s9 ht10
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem initial_cover : inputs.sublists.all (fun l => cuts l != -1 || ReplayTree.find (sortedW l) t10) = true := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 10 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hr' : live basicOps goal 10 l.toFinset := hlS ▸ hl3
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hh := List.all_eq_true.mp initial_cover l hmem
  have hit : ReplayTree.find (sortedW l) t10 = true := by simpa [cuts_full hr'] using hh
  have perm := sorted_perm l
  exact s10 _ hit (perm.nodup_iff.mpr hnd) (by simpa only [List.toFinset_eq_of_perm _ _ perm] using hr')

end PEqualNP.Outside.L_meta_9399

theorem PEqualNP.Outside.L_meta_9399 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3687098 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_9399.no_small C hm hs hr
