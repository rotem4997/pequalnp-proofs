import PEqualNP.Defs

-- The live-set lower-bound framework below (`build`, `live`, `compress`, `live_separates`, the
-- pair encoding with `sep` / `cuts`, the `optimized` search and its completeness proof) is copied
-- from the accepted L-meta-6345 by BastianMIllan (open-goat/pequalnp-proofs, Apache License 2.0).
-- New here: the graph, the width (272 bits: one negative and one positive bit for each of the
-- 136 (positive, negative) one-each input pairs), the search depth, and the split of the long search
-- into pieces checked one at a time.


namespace PEqualNP.Outside.L_meta_9186_aux

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

abbrev W := BitVec 272

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 136 := ((x >>> 136) &&& ~~~x).setWidth 136

def cuts (ws : List W) : BitVec 136 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 136) ++ (0 : BitVec 136)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x3ffffffff00038001c000e000700038001c000e0007, 0xffffffffc00000000001c000e000700038001c000e000700038, 0x1ffff0000000000000000001e000f00078003c001e000f00078003c0, 0x3fffe0000000000000000000001e000f00078003c001e000f00078003c00, 0xffffffffc0000000000000000000000000e000700038001c000e000700038001c000, 0x7fffffffe0000000000000000000000024801240092004900248012400920049, 0xffff8000000000000000000000000000000249012480924049202490124809240492, 0x1ffff2490124809240492024901248092404920, 0x7fffffffe00004900248012400920049002480124009200, 0x1ffffffff80000000000009002480124009200490024801240092004]

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

def differs (i : Fin 136) (w : W) : Prop :=
  w.getLsbD (136 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 136) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (136 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (136 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 136, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 136) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 272 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 136)[j]
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
  z == 0 || z == BitVec.allOnes 272 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 272) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 272) :
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
    · exact ⟨BitVec.allOnes 272, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 272 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 272 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 272 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 272 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 272) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 272 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def A : Fin 5 → Fin 5 → Bool := fun u v : Fin 5 => (3195660 : ℕ).testBit (5 * u.val + v.val)

def posL : List (Fin 5 × Fin 5) :=
  [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (3, 0), (4, 0), (4, 1)]

def negL : List (Fin 5 × Fin 5) :=
  [(0, 0), (0, 1), (0, 4), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4)]

def samp (k : Fin 272) : Fin 5 × Fin 5 :=
  if k.val < 136 then negL.getD (k.val % 17) (0, 0) else posL.getD ((k.val - 136) / 17) (0, 2)

theorem input_rows : ∀ k : Fin 272,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 272, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 272) :
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

-- The sublists whose search is long are checked one first-level pair at a time.
def x0 : W := 0x3ffffffff00038001c000e000700038001c000e0007
def x1 : W := 0xffffffffc00000000001c000e000700038001c000e000700038
def x2 : W := 0x1ffff0000000000000000001e000f00078003c001e000f00078003c0
def x3 : W := 0x3fffe0000000000000000000001e000f00078003c001e000f00078003c00
def x4 : W := 0xffffffffc0000000000000000000000000e000700038001c000e000700038001c000
def x5 : W := 0x7fffffffe0000000000000000000000024801240092004900248012400920049
def x6 : W := 0xffff8000000000000000000000000000000249012480924049202490124809240492
def x7 : W := 0x1ffff2490124809240492024901248092404920
def x8 : W := 0x7fffffffe00004900248012400920049002480124009200
def x9 : W := 0x1ffffffff80000000000009002480124009200490024801240092004

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1 : dispatch 1 (optimized 9) x0 x1 [x2, x3, x4, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t2 : dispatch 1 (optimized 9) x0 x2 [x1, x3, x4, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t3 : dispatch 1 (optimized 9) x0 x3 [x1, x2, x4, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t4 : dispatch 1 (optimized 9) x0 x4 [x1, x2, x3, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t5 : dispatch 1 (optimized 8) (x0 ||| x5) x1 [x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t6 : dispatch 1 (optimized 8) (x0 ||| x5) x2 [x1, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t7 : dispatch 1 (optimized 8) (x0 ||| x5) x3 [x1, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t8 : dispatch 1 (optimized 8) (x0 ||| x5) x4 [x1, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t9 : dispatch 1 (optimized 8) (x0 ||| x5) x6 [x1, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t10 : dispatch 1 (optimized 8) (x0 ||| x5) x7 [x1, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t11 : dispatch 1 (optimized 8) (x0 ||| x5) x8 [x1, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t12 : dispatch 1 (optimized 8) (x0 ||| x5) x9 [x1, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t13 : dispatch 1 (optimized 8) x1 x2 [x0 ||| x5, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t14 : dispatch 1 (optimized 8) x1 x3 [x0 ||| x5, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t15 : dispatch 1 (optimized 8) x1 x4 [x0 ||| x5, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t16 : dispatch 1 (optimized 8) x1 x6 [x0 ||| x5, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t17 : dispatch 1 (optimized 8) x1 x7 [x0 ||| x5, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t18 : dispatch 1 (optimized 8) x1 x8 [x0 ||| x5, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t19 : dispatch 1 (optimized 8) x1 x9 [x0 ||| x5, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t20 : dispatch 1 (optimized 8) x2 x3 [x0 ||| x5, x1, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t21 : dispatch 1 (optimized 8) x2 x4 [x0 ||| x5, x1, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t22 : dispatch 1 (optimized 8) x2 x6 [x0 ||| x5, x1, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t23 : dispatch 1 (optimized 8) x2 x7 [x0 ||| x5, x1, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t24 : dispatch 1 (optimized 8) x2 x8 [x0 ||| x5, x1, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t25 : dispatch 1 (optimized 8) x2 x9 [x0 ||| x5, x1, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t26 : dispatch 1 (optimized 8) x3 x4 [x0 ||| x5, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t27 : dispatch 1 (optimized 8) x3 x6 [x0 ||| x5, x1, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t28 : dispatch 1 (optimized 8) x3 x7 [x0 ||| x5, x1, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t29 : dispatch 1 (optimized 8) x3 x8 [x0 ||| x5, x1, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t30 : dispatch 1 (optimized 8) x3 x9 [x0 ||| x5, x1, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t31 : dispatch 1 (optimized 8) x4 x6 [x0 ||| x5, x1, x2, x3, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t32 : dispatch 1 (optimized 8) x4 x7 [x0 ||| x5, x1, x2, x3, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t33 : dispatch 1 (optimized 8) x4 x8 [x0 ||| x5, x1, x2, x3, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t34 : dispatch 1 (optimized 8) x4 x9 [x0 ||| x5, x1, x2, x3, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t35 : dispatch 1 (optimized 8) x6 x7 [x0 ||| x5, x1, x2, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t36 : dispatch 1 (optimized 8) x6 x8 [x0 ||| x5, x1, x2, x3, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t37 : dispatch 1 (optimized 8) x6 x9 [x0 ||| x5, x1, x2, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t38 : dispatch 1 (optimized 8) x7 x8 [x0 ||| x5, x1, x2, x3, x4, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t39 : dispatch 1 (optimized 8) x7 x9 [x0 ||| x5, x1, x2, x3, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t40 : dispatch 1 (optimized 8) x8 x9 [x0 ||| x5, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t41_pairs : pairs [x0 ||| x5, x1, x2, x3, x4, x6, x7, x8, x9] = [(x0 ||| x5, x1, [x2, x3, x4, x6, x7, x8, x9]), (x0 ||| x5, x2, [x1, x3, x4, x6, x7, x8, x9]), (x0 ||| x5, x3, [x1, x2, x4, x6, x7, x8, x9]), (x0 ||| x5, x4, [x1, x2, x3, x6, x7, x8, x9]), (x0 ||| x5, x6, [x1, x2, x3, x4, x7, x8, x9]), (x0 ||| x5, x7, [x1, x2, x3, x4, x6, x8, x9]), (x0 ||| x5, x8, [x1, x2, x3, x4, x6, x7, x9]), (x0 ||| x5, x9, [x1, x2, x3, x4, x6, x7, x8]), (x1, x2, [x0 ||| x5, x3, x4, x6, x7, x8, x9]), (x1, x3, [x0 ||| x5, x2, x4, x6, x7, x8, x9]), (x1, x4, [x0 ||| x5, x2, x3, x6, x7, x8, x9]), (x1, x6, [x0 ||| x5, x2, x3, x4, x7, x8, x9]), (x1, x7, [x0 ||| x5, x2, x3, x4, x6, x8, x9]), (x1, x8, [x0 ||| x5, x2, x3, x4, x6, x7, x9]), (x1, x9, [x0 ||| x5, x2, x3, x4, x6, x7, x8]), (x2, x3, [x0 ||| x5, x1, x4, x6, x7, x8, x9]), (x2, x4, [x0 ||| x5, x1, x3, x6, x7, x8, x9]), (x2, x6, [x0 ||| x5, x1, x3, x4, x7, x8, x9]), (x2, x7, [x0 ||| x5, x1, x3, x4, x6, x8, x9]), (x2, x8, [x0 ||| x5, x1, x3, x4, x6, x7, x9]), (x2, x9, [x0 ||| x5, x1, x3, x4, x6, x7, x8]), (x3, x4, [x0 ||| x5, x1, x2, x6, x7, x8, x9]), (x3, x6, [x0 ||| x5, x1, x2, x4, x7, x8, x9]), (x3, x7, [x0 ||| x5, x1, x2, x4, x6, x8, x9]), (x3, x8, [x0 ||| x5, x1, x2, x4, x6, x7, x9]), (x3, x9, [x0 ||| x5, x1, x2, x4, x6, x7, x8]), (x4, x6, [x0 ||| x5, x1, x2, x3, x7, x8, x9]), (x4, x7, [x0 ||| x5, x1, x2, x3, x6, x8, x9]), (x4, x8, [x0 ||| x5, x1, x2, x3, x6, x7, x9]), (x4, x9, [x0 ||| x5, x1, x2, x3, x6, x7, x8]), (x6, x7, [x0 ||| x5, x1, x2, x3, x4, x8, x9]), (x6, x8, [x0 ||| x5, x1, x2, x3, x4, x7, x9]), (x6, x9, [x0 ||| x5, x1, x2, x3, x4, x7, x8]), (x7, x8, [x0 ||| x5, x1, x2, x3, x4, x6, x9]), (x7, x9, [x0 ||| x5, x1, x2, x3, x4, x6, x8]), (x8, x9, [x0 ||| x5, x1, x2, x3, x4, x6, x7])] := by
  decide +kernel

theorem t41 : optimized 9 1 [x0 ||| x5, x1, x2, x3, x4, x6, x7, x8, x9] = false := by
  rw [optimized.eq_2, t41_pairs]
  simp only [List.any_cons, List.any_nil, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t42 : optimized 9 0 [x0 ||| x5, x0, x1, x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t43 : optimized 9 0 [x0 ||| x5, x5, x1, x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

theorem t44 : dispatch 1 (optimized 9) x0 x5 [x1, x2, x3, x4, x6, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t41, t42, t43, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t45 : dispatch 1 (optimized 8) (x0 ||| x6) x1 [x2, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t46 : dispatch 1 (optimized 8) (x0 ||| x6) x2 [x1, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t47 : dispatch 1 (optimized 8) (x0 ||| x6) x3 [x1, x2, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t48 : dispatch 1 (optimized 8) (x0 ||| x6) x4 [x1, x2, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t49 : dispatch 1 (optimized 8) (x0 ||| x6) x5 [x1, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t50 : dispatch 1 (optimized 8) (x0 ||| x6) x7 [x1, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t51 : dispatch 1 (optimized 8) (x0 ||| x6) x8 [x1, x2, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t52 : dispatch 1 (optimized 8) (x0 ||| x6) x9 [x1, x2, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t53 : dispatch 1 (optimized 8) x1 x2 [x0 ||| x6, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t54 : dispatch 1 (optimized 8) x1 x3 [x0 ||| x6, x2, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t55 : dispatch 1 (optimized 8) x1 x4 [x0 ||| x6, x2, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t56 : dispatch 1 (optimized 8) x1 x5 [x0 ||| x6, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t57 : dispatch 1 (optimized 8) x1 x7 [x0 ||| x6, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t58 : dispatch 1 (optimized 8) x1 x8 [x0 ||| x6, x2, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t59 : dispatch 1 (optimized 8) x1 x9 [x0 ||| x6, x2, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t60 : dispatch 1 (optimized 8) x2 x3 [x0 ||| x6, x1, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t61 : dispatch 1 (optimized 8) x2 x4 [x0 ||| x6, x1, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t62 : dispatch 1 (optimized 8) x2 x5 [x0 ||| x6, x1, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t63 : dispatch 1 (optimized 8) x2 x7 [x0 ||| x6, x1, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t64 : dispatch 1 (optimized 8) x2 x8 [x0 ||| x6, x1, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t65 : dispatch 1 (optimized 8) x2 x9 [x0 ||| x6, x1, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t66 : dispatch 1 (optimized 8) x3 x4 [x0 ||| x6, x1, x2, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t67 : dispatch 1 (optimized 8) x3 x5 [x0 ||| x6, x1, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t68 : dispatch 1 (optimized 8) x3 x7 [x0 ||| x6, x1, x2, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t69 : dispatch 1 (optimized 8) x3 x8 [x0 ||| x6, x1, x2, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t70 : dispatch 1 (optimized 8) x3 x9 [x0 ||| x6, x1, x2, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t71 : dispatch 1 (optimized 8) x4 x5 [x0 ||| x6, x1, x2, x3, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t72 : dispatch 1 (optimized 8) x4 x7 [x0 ||| x6, x1, x2, x3, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t73 : dispatch 1 (optimized 8) x4 x8 [x0 ||| x6, x1, x2, x3, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t74 : dispatch 1 (optimized 8) x4 x9 [x0 ||| x6, x1, x2, x3, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t75 : dispatch 1 (optimized 8) x5 x7 [x0 ||| x6, x1, x2, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t76 : dispatch 1 (optimized 8) x5 x8 [x0 ||| x6, x1, x2, x3, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t77 : dispatch 1 (optimized 8) x5 x9 [x0 ||| x6, x1, x2, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t78 : dispatch 1 (optimized 8) x7 x8 [x0 ||| x6, x1, x2, x3, x4, x5, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t79 : dispatch 1 (optimized 8) x7 x9 [x0 ||| x6, x1, x2, x3, x4, x5, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t80 : dispatch 1 (optimized 8) x8 x9 [x0 ||| x6, x1, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t81_pairs : pairs [x0 ||| x6, x1, x2, x3, x4, x5, x7, x8, x9] = [(x0 ||| x6, x1, [x2, x3, x4, x5, x7, x8, x9]), (x0 ||| x6, x2, [x1, x3, x4, x5, x7, x8, x9]), (x0 ||| x6, x3, [x1, x2, x4, x5, x7, x8, x9]), (x0 ||| x6, x4, [x1, x2, x3, x5, x7, x8, x9]), (x0 ||| x6, x5, [x1, x2, x3, x4, x7, x8, x9]), (x0 ||| x6, x7, [x1, x2, x3, x4, x5, x8, x9]), (x0 ||| x6, x8, [x1, x2, x3, x4, x5, x7, x9]), (x0 ||| x6, x9, [x1, x2, x3, x4, x5, x7, x8]), (x1, x2, [x0 ||| x6, x3, x4, x5, x7, x8, x9]), (x1, x3, [x0 ||| x6, x2, x4, x5, x7, x8, x9]), (x1, x4, [x0 ||| x6, x2, x3, x5, x7, x8, x9]), (x1, x5, [x0 ||| x6, x2, x3, x4, x7, x8, x9]), (x1, x7, [x0 ||| x6, x2, x3, x4, x5, x8, x9]), (x1, x8, [x0 ||| x6, x2, x3, x4, x5, x7, x9]), (x1, x9, [x0 ||| x6, x2, x3, x4, x5, x7, x8]), (x2, x3, [x0 ||| x6, x1, x4, x5, x7, x8, x9]), (x2, x4, [x0 ||| x6, x1, x3, x5, x7, x8, x9]), (x2, x5, [x0 ||| x6, x1, x3, x4, x7, x8, x9]), (x2, x7, [x0 ||| x6, x1, x3, x4, x5, x8, x9]), (x2, x8, [x0 ||| x6, x1, x3, x4, x5, x7, x9]), (x2, x9, [x0 ||| x6, x1, x3, x4, x5, x7, x8]), (x3, x4, [x0 ||| x6, x1, x2, x5, x7, x8, x9]), (x3, x5, [x0 ||| x6, x1, x2, x4, x7, x8, x9]), (x3, x7, [x0 ||| x6, x1, x2, x4, x5, x8, x9]), (x3, x8, [x0 ||| x6, x1, x2, x4, x5, x7, x9]), (x3, x9, [x0 ||| x6, x1, x2, x4, x5, x7, x8]), (x4, x5, [x0 ||| x6, x1, x2, x3, x7, x8, x9]), (x4, x7, [x0 ||| x6, x1, x2, x3, x5, x8, x9]), (x4, x8, [x0 ||| x6, x1, x2, x3, x5, x7, x9]), (x4, x9, [x0 ||| x6, x1, x2, x3, x5, x7, x8]), (x5, x7, [x0 ||| x6, x1, x2, x3, x4, x8, x9]), (x5, x8, [x0 ||| x6, x1, x2, x3, x4, x7, x9]), (x5, x9, [x0 ||| x6, x1, x2, x3, x4, x7, x8]), (x7, x8, [x0 ||| x6, x1, x2, x3, x4, x5, x9]), (x7, x9, [x0 ||| x6, x1, x2, x3, x4, x5, x8]), (x8, x9, [x0 ||| x6, x1, x2, x3, x4, x5, x7])] := by
  decide +kernel

theorem t81 : optimized 9 1 [x0 ||| x6, x1, x2, x3, x4, x5, x7, x8, x9] = false := by
  rw [optimized.eq_2, t81_pairs]
  simp only [List.any_cons, List.any_nil, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, t76, t77, t78, t79, t80, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t82 : optimized 9 0 [x0 ||| x6, x0, x1, x2, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t83 : optimized 9 0 [x0 ||| x6, x6, x1, x2, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

theorem t84 : dispatch 1 (optimized 9) x0 x6 [x1, x2, x3, x4, x5, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t81, t82, t83, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t85 : dispatch 0 (optimized 8) (x0 &&& x7) x0 [x1, x2, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t86 : dispatch 0 (optimized 8) (x0 &&& x7) x1 [x0, x2, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t87 : dispatch 0 (optimized 8) (x0 &&& x7) x2 [x0, x1, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t88 : dispatch 0 (optimized 8) (x0 &&& x7) x3 [x0, x1, x2, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t89 : dispatch 0 (optimized 8) (x0 &&& x7) x4 [x0, x1, x2, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t90 : dispatch 0 (optimized 8) (x0 &&& x7) x5 [x0, x1, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t91 : dispatch 0 (optimized 8) (x0 &&& x7) x6 [x0, x1, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t92 : dispatch 0 (optimized 8) (x0 &&& x7) x8 [x0, x1, x2, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t93 : dispatch 0 (optimized 8) (x0 &&& x7) x9 [x0, x1, x2, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t94 : dispatch 0 (optimized 8) x0 x1 [x0 &&& x7, x2, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t95 : dispatch 0 (optimized 8) x0 x2 [x0 &&& x7, x1, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t96 : dispatch 0 (optimized 8) x0 x3 [x0 &&& x7, x1, x2, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t97 : dispatch 0 (optimized 8) x0 x4 [x0 &&& x7, x1, x2, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t98 : dispatch 0 (optimized 8) x0 x5 [x0 &&& x7, x1, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t99 : dispatch 0 (optimized 8) x0 x6 [x0 &&& x7, x1, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t100 : dispatch 0 (optimized 8) x0 x8 [x0 &&& x7, x1, x2, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t101 : dispatch 0 (optimized 8) x0 x9 [x0 &&& x7, x1, x2, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t102 : dispatch 0 (optimized 8) x1 x2 [x0 &&& x7, x0, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t103 : dispatch 0 (optimized 8) x1 x3 [x0 &&& x7, x0, x2, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t104 : dispatch 0 (optimized 8) x1 x4 [x0 &&& x7, x0, x2, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t105 : dispatch 0 (optimized 8) x1 x5 [x0 &&& x7, x0, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t106 : dispatch 0 (optimized 8) x1 x6 [x0 &&& x7, x0, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t107 : dispatch 0 (optimized 8) x1 x8 [x0 &&& x7, x0, x2, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t108 : dispatch 0 (optimized 8) x1 x9 [x0 &&& x7, x0, x2, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t109 : dispatch 0 (optimized 8) x2 x3 [x0 &&& x7, x0, x1, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t110 : dispatch 0 (optimized 8) x2 x4 [x0 &&& x7, x0, x1, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t111 : dispatch 0 (optimized 8) x2 x5 [x0 &&& x7, x0, x1, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t112 : dispatch 0 (optimized 8) x2 x6 [x0 &&& x7, x0, x1, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t113 : dispatch 0 (optimized 8) x2 x8 [x0 &&& x7, x0, x1, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t114 : dispatch 0 (optimized 8) x2 x9 [x0 &&& x7, x0, x1, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t115 : dispatch 0 (optimized 8) x3 x4 [x0 &&& x7, x0, x1, x2, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t116 : dispatch 0 (optimized 8) x3 x5 [x0 &&& x7, x0, x1, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t117 : dispatch 0 (optimized 8) x3 x6 [x0 &&& x7, x0, x1, x2, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t118 : dispatch 0 (optimized 8) x3 x8 [x0 &&& x7, x0, x1, x2, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t119 : dispatch 0 (optimized 8) x3 x9 [x0 &&& x7, x0, x1, x2, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t120 : dispatch 0 (optimized 8) x4 x5 [x0 &&& x7, x0, x1, x2, x3, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t121 : dispatch 0 (optimized 8) x4 x6 [x0 &&& x7, x0, x1, x2, x3, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t122 : dispatch 0 (optimized 8) x4 x8 [x0 &&& x7, x0, x1, x2, x3, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t123 : dispatch 0 (optimized 8) x4 x9 [x0 &&& x7, x0, x1, x2, x3, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t124 : dispatch 0 (optimized 8) x5 x6 [x0 &&& x7, x0, x1, x2, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t125 : dispatch 0 (optimized 8) x5 x8 [x0 &&& x7, x0, x1, x2, x3, x4, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t126 : dispatch 0 (optimized 8) x5 x9 [x0 &&& x7, x0, x1, x2, x3, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t127 : dispatch 0 (optimized 8) x6 x8 [x0 &&& x7, x0, x1, x2, x3, x4, x5, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t128 : dispatch 0 (optimized 8) x6 x9 [x0 &&& x7, x0, x1, x2, x3, x4, x5, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t129 : dispatch 0 (optimized 8) x8 x9 [x0 &&& x7, x0, x1, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t130_pairs : pairs [x0 &&& x7, x0, x1, x2, x3, x4, x5, x6, x8, x9] = [(x0 &&& x7, x0, [x1, x2, x3, x4, x5, x6, x8, x9]), (x0 &&& x7, x1, [x0, x2, x3, x4, x5, x6, x8, x9]), (x0 &&& x7, x2, [x0, x1, x3, x4, x5, x6, x8, x9]), (x0 &&& x7, x3, [x0, x1, x2, x4, x5, x6, x8, x9]), (x0 &&& x7, x4, [x0, x1, x2, x3, x5, x6, x8, x9]), (x0 &&& x7, x5, [x0, x1, x2, x3, x4, x6, x8, x9]), (x0 &&& x7, x6, [x0, x1, x2, x3, x4, x5, x8, x9]), (x0 &&& x7, x8, [x0, x1, x2, x3, x4, x5, x6, x9]), (x0 &&& x7, x9, [x0, x1, x2, x3, x4, x5, x6, x8]), (x0, x1, [x0 &&& x7, x2, x3, x4, x5, x6, x8, x9]), (x0, x2, [x0 &&& x7, x1, x3, x4, x5, x6, x8, x9]), (x0, x3, [x0 &&& x7, x1, x2, x4, x5, x6, x8, x9]), (x0, x4, [x0 &&& x7, x1, x2, x3, x5, x6, x8, x9]), (x0, x5, [x0 &&& x7, x1, x2, x3, x4, x6, x8, x9]), (x0, x6, [x0 &&& x7, x1, x2, x3, x4, x5, x8, x9]), (x0, x8, [x0 &&& x7, x1, x2, x3, x4, x5, x6, x9]), (x0, x9, [x0 &&& x7, x1, x2, x3, x4, x5, x6, x8]), (x1, x2, [x0 &&& x7, x0, x3, x4, x5, x6, x8, x9]), (x1, x3, [x0 &&& x7, x0, x2, x4, x5, x6, x8, x9]), (x1, x4, [x0 &&& x7, x0, x2, x3, x5, x6, x8, x9]), (x1, x5, [x0 &&& x7, x0, x2, x3, x4, x6, x8, x9]), (x1, x6, [x0 &&& x7, x0, x2, x3, x4, x5, x8, x9]), (x1, x8, [x0 &&& x7, x0, x2, x3, x4, x5, x6, x9]), (x1, x9, [x0 &&& x7, x0, x2, x3, x4, x5, x6, x8]), (x2, x3, [x0 &&& x7, x0, x1, x4, x5, x6, x8, x9]), (x2, x4, [x0 &&& x7, x0, x1, x3, x5, x6, x8, x9]), (x2, x5, [x0 &&& x7, x0, x1, x3, x4, x6, x8, x9]), (x2, x6, [x0 &&& x7, x0, x1, x3, x4, x5, x8, x9]), (x2, x8, [x0 &&& x7, x0, x1, x3, x4, x5, x6, x9]), (x2, x9, [x0 &&& x7, x0, x1, x3, x4, x5, x6, x8]), (x3, x4, [x0 &&& x7, x0, x1, x2, x5, x6, x8, x9]), (x3, x5, [x0 &&& x7, x0, x1, x2, x4, x6, x8, x9]), (x3, x6, [x0 &&& x7, x0, x1, x2, x4, x5, x8, x9]), (x3, x8, [x0 &&& x7, x0, x1, x2, x4, x5, x6, x9]), (x3, x9, [x0 &&& x7, x0, x1, x2, x4, x5, x6, x8]), (x4, x5, [x0 &&& x7, x0, x1, x2, x3, x6, x8, x9]), (x4, x6, [x0 &&& x7, x0, x1, x2, x3, x5, x8, x9]), (x4, x8, [x0 &&& x7, x0, x1, x2, x3, x5, x6, x9]), (x4, x9, [x0 &&& x7, x0, x1, x2, x3, x5, x6, x8]), (x5, x6, [x0 &&& x7, x0, x1, x2, x3, x4, x8, x9]), (x5, x8, [x0 &&& x7, x0, x1, x2, x3, x4, x6, x9]), (x5, x9, [x0 &&& x7, x0, x1, x2, x3, x4, x6, x8]), (x6, x8, [x0 &&& x7, x0, x1, x2, x3, x4, x5, x9]), (x6, x9, [x0 &&& x7, x0, x1, x2, x3, x4, x5, x8]), (x8, x9, [x0 &&& x7, x0, x1, x2, x3, x4, x5, x6])] := by
  decide +kernel

theorem t130 : optimized 9 0 [x0 &&& x7, x0, x1, x2, x3, x4, x5, x6, x8, x9] = false := by
  rw [optimized.eq_2, t130_pairs]
  simp only [List.any_cons, List.any_nil, t85, t86, t87, t88, t89, t90, t91, t92, t93, t94, t95, t96, t97, t98, t99, t100, t101, t102, t103, t104, t105, t106, t107, t108, t109, t110, t111, t112, t113, t114, t115, t116, t117, t118, t119, t120, t121, t122, t123, t124, t125, t126, t127, t128, t129, Bool.or_false]
  all_goals decide +kernel

theorem t131 : dispatch 1 (optimized 9) x0 x7 [x1, x2, x3, x4, x5, x6, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t130, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t132 : dispatch 1 (optimized 9) x0 x8 [x1, x2, x3, x4, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t133 : dispatch 1 (optimized 8) (x0 ||| x9) x1 [x2, x3, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t134 : dispatch 1 (optimized 8) (x0 ||| x9) x2 [x1, x3, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t135 : dispatch 1 (optimized 8) (x0 ||| x9) x3 [x1, x2, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t136 : dispatch 1 (optimized 8) (x0 ||| x9) x4 [x1, x2, x3, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t137 : dispatch 1 (optimized 8) (x0 ||| x9) x5 [x1, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t138 : dispatch 1 (optimized 8) (x0 ||| x9) x6 [x1, x2, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t139 : dispatch 1 (optimized 8) (x0 ||| x9) x7 [x1, x2, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t140 : dispatch 1 (optimized 8) (x0 ||| x9) x8 [x1, x2, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t141 : dispatch 1 (optimized 8) x1 x2 [x0 ||| x9, x3, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t142 : dispatch 1 (optimized 8) x1 x3 [x0 ||| x9, x2, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t143 : dispatch 1 (optimized 8) x1 x4 [x0 ||| x9, x2, x3, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t144 : dispatch 1 (optimized 8) x1 x5 [x0 ||| x9, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t145 : dispatch 1 (optimized 8) x1 x6 [x0 ||| x9, x2, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t146 : dispatch 1 (optimized 8) x1 x7 [x0 ||| x9, x2, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t147 : dispatch 1 (optimized 8) x1 x8 [x0 ||| x9, x2, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t148 : dispatch 1 (optimized 8) x2 x3 [x0 ||| x9, x1, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t149 : dispatch 1 (optimized 8) x2 x4 [x0 ||| x9, x1, x3, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t150 : dispatch 1 (optimized 8) x2 x5 [x0 ||| x9, x1, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t151 : dispatch 1 (optimized 8) x2 x6 [x0 ||| x9, x1, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t152 : dispatch 1 (optimized 8) x2 x7 [x0 ||| x9, x1, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t153 : dispatch 1 (optimized 8) x2 x8 [x0 ||| x9, x1, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t154 : dispatch 1 (optimized 8) x3 x4 [x0 ||| x9, x1, x2, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t155 : dispatch 1 (optimized 8) x3 x5 [x0 ||| x9, x1, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t156 : dispatch 1 (optimized 8) x3 x6 [x0 ||| x9, x1, x2, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t157 : dispatch 1 (optimized 8) x3 x7 [x0 ||| x9, x1, x2, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t158 : dispatch 1 (optimized 8) x3 x8 [x0 ||| x9, x1, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t159 : dispatch 1 (optimized 8) x4 x5 [x0 ||| x9, x1, x2, x3, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t160 : dispatch 1 (optimized 8) x4 x6 [x0 ||| x9, x1, x2, x3, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t161 : dispatch 1 (optimized 8) x4 x7 [x0 ||| x9, x1, x2, x3, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t162 : dispatch 1 (optimized 8) x4 x8 [x0 ||| x9, x1, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t163 : dispatch 1 (optimized 8) x5 x6 [x0 ||| x9, x1, x2, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t164 : dispatch 1 (optimized 8) x5 x7 [x0 ||| x9, x1, x2, x3, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t165 : dispatch 1 (optimized 8) x5 x8 [x0 ||| x9, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t166 : dispatch 1 (optimized 8) x6 x7 [x0 ||| x9, x1, x2, x3, x4, x5, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t167 : dispatch 1 (optimized 8) x6 x8 [x0 ||| x9, x1, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t168 : dispatch 1 (optimized 8) x7 x8 [x0 ||| x9, x1, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t169_pairs : pairs [x0 ||| x9, x1, x2, x3, x4, x5, x6, x7, x8] = [(x0 ||| x9, x1, [x2, x3, x4, x5, x6, x7, x8]), (x0 ||| x9, x2, [x1, x3, x4, x5, x6, x7, x8]), (x0 ||| x9, x3, [x1, x2, x4, x5, x6, x7, x8]), (x0 ||| x9, x4, [x1, x2, x3, x5, x6, x7, x8]), (x0 ||| x9, x5, [x1, x2, x3, x4, x6, x7, x8]), (x0 ||| x9, x6, [x1, x2, x3, x4, x5, x7, x8]), (x0 ||| x9, x7, [x1, x2, x3, x4, x5, x6, x8]), (x0 ||| x9, x8, [x1, x2, x3, x4, x5, x6, x7]), (x1, x2, [x0 ||| x9, x3, x4, x5, x6, x7, x8]), (x1, x3, [x0 ||| x9, x2, x4, x5, x6, x7, x8]), (x1, x4, [x0 ||| x9, x2, x3, x5, x6, x7, x8]), (x1, x5, [x0 ||| x9, x2, x3, x4, x6, x7, x8]), (x1, x6, [x0 ||| x9, x2, x3, x4, x5, x7, x8]), (x1, x7, [x0 ||| x9, x2, x3, x4, x5, x6, x8]), (x1, x8, [x0 ||| x9, x2, x3, x4, x5, x6, x7]), (x2, x3, [x0 ||| x9, x1, x4, x5, x6, x7, x8]), (x2, x4, [x0 ||| x9, x1, x3, x5, x6, x7, x8]), (x2, x5, [x0 ||| x9, x1, x3, x4, x6, x7, x8]), (x2, x6, [x0 ||| x9, x1, x3, x4, x5, x7, x8]), (x2, x7, [x0 ||| x9, x1, x3, x4, x5, x6, x8]), (x2, x8, [x0 ||| x9, x1, x3, x4, x5, x6, x7]), (x3, x4, [x0 ||| x9, x1, x2, x5, x6, x7, x8]), (x3, x5, [x0 ||| x9, x1, x2, x4, x6, x7, x8]), (x3, x6, [x0 ||| x9, x1, x2, x4, x5, x7, x8]), (x3, x7, [x0 ||| x9, x1, x2, x4, x5, x6, x8]), (x3, x8, [x0 ||| x9, x1, x2, x4, x5, x6, x7]), (x4, x5, [x0 ||| x9, x1, x2, x3, x6, x7, x8]), (x4, x6, [x0 ||| x9, x1, x2, x3, x5, x7, x8]), (x4, x7, [x0 ||| x9, x1, x2, x3, x5, x6, x8]), (x4, x8, [x0 ||| x9, x1, x2, x3, x5, x6, x7]), (x5, x6, [x0 ||| x9, x1, x2, x3, x4, x7, x8]), (x5, x7, [x0 ||| x9, x1, x2, x3, x4, x6, x8]), (x5, x8, [x0 ||| x9, x1, x2, x3, x4, x6, x7]), (x6, x7, [x0 ||| x9, x1, x2, x3, x4, x5, x8]), (x6, x8, [x0 ||| x9, x1, x2, x3, x4, x5, x7]), (x7, x8, [x0 ||| x9, x1, x2, x3, x4, x5, x6])] := by
  decide +kernel

theorem t169 : optimized 9 1 [x0 ||| x9, x1, x2, x3, x4, x5, x6, x7, x8] = false := by
  rw [optimized.eq_2, t169_pairs]
  simp only [List.any_cons, List.any_nil, t133, t134, t135, t136, t137, t138, t139, t140, t141, t142, t143, t144, t145, t146, t147, t148, t149, t150, t151, t152, t153, t154, t155, t156, t157, t158, t159, t160, t161, t162, t163, t164, t165, t166, t167, t168, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t170 : optimized 9 0 [x0 ||| x9, x0, x1, x2, x3, x4, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t171 : optimized 9 0 [x0 ||| x9, x9, x1, x2, x3, x4, x5, x6, x7, x8] = false := by
  decide +kernel

theorem t172 : dispatch 1 (optimized 9) x0 x9 [x1, x2, x3, x4, x5, x6, x7, x8] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t169, t170, t171, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t173 : dispatch 1 (optimized 9) x1 x2 [x0, x3, x4, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t174 : dispatch 1 (optimized 9) x1 x3 [x0, x2, x4, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t175 : dispatch 1 (optimized 9) x1 x4 [x0, x2, x3, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t176 : dispatch 1 (optimized 8) (x1 ||| x5) x0 [x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t177 : dispatch 1 (optimized 8) (x1 ||| x5) x2 [x0, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t178 : dispatch 1 (optimized 8) (x1 ||| x5) x3 [x0, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t179 : dispatch 1 (optimized 8) (x1 ||| x5) x4 [x0, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t180 : dispatch 1 (optimized 8) (x1 ||| x5) x6 [x0, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t181 : dispatch 1 (optimized 8) (x1 ||| x5) x7 [x0, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t182 : dispatch 1 (optimized 8) (x1 ||| x5) x8 [x0, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t183 : dispatch 1 (optimized 8) (x1 ||| x5) x9 [x0, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t184 : dispatch 1 (optimized 8) x0 x2 [x1 ||| x5, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t185 : dispatch 1 (optimized 8) x0 x3 [x1 ||| x5, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t186 : dispatch 1 (optimized 8) x0 x4 [x1 ||| x5, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t187 : dispatch 1 (optimized 8) x0 x6 [x1 ||| x5, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t188 : dispatch 1 (optimized 8) x0 x7 [x1 ||| x5, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t189 : dispatch 1 (optimized 8) x0 x8 [x1 ||| x5, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t190 : dispatch 1 (optimized 8) x0 x9 [x1 ||| x5, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t191 : dispatch 1 (optimized 8) x2 x3 [x1 ||| x5, x0, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t192 : dispatch 1 (optimized 8) x2 x4 [x1 ||| x5, x0, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t193 : dispatch 1 (optimized 8) x2 x6 [x1 ||| x5, x0, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t194 : dispatch 1 (optimized 8) x2 x7 [x1 ||| x5, x0, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t195 : dispatch 1 (optimized 8) x2 x8 [x1 ||| x5, x0, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t196 : dispatch 1 (optimized 8) x2 x9 [x1 ||| x5, x0, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t197 : dispatch 1 (optimized 8) x3 x4 [x1 ||| x5, x0, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t198 : dispatch 1 (optimized 8) x3 x6 [x1 ||| x5, x0, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t199 : dispatch 1 (optimized 8) x3 x7 [x1 ||| x5, x0, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t200 : dispatch 1 (optimized 8) x3 x8 [x1 ||| x5, x0, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t201 : dispatch 1 (optimized 8) x3 x9 [x1 ||| x5, x0, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t202 : dispatch 1 (optimized 8) x4 x6 [x1 ||| x5, x0, x2, x3, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t203 : dispatch 1 (optimized 8) x4 x7 [x1 ||| x5, x0, x2, x3, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t204 : dispatch 1 (optimized 8) x4 x8 [x1 ||| x5, x0, x2, x3, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t205 : dispatch 1 (optimized 8) x4 x9 [x1 ||| x5, x0, x2, x3, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t206 : dispatch 1 (optimized 8) x6 x7 [x1 ||| x5, x0, x2, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t207 : dispatch 1 (optimized 8) x6 x8 [x1 ||| x5, x0, x2, x3, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t208 : dispatch 1 (optimized 8) x6 x9 [x1 ||| x5, x0, x2, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t209 : dispatch 1 (optimized 8) x7 x8 [x1 ||| x5, x0, x2, x3, x4, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t210 : dispatch 1 (optimized 8) x7 x9 [x1 ||| x5, x0, x2, x3, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t211 : dispatch 1 (optimized 8) x8 x9 [x1 ||| x5, x0, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t212_pairs : pairs [x1 ||| x5, x0, x2, x3, x4, x6, x7, x8, x9] = [(x1 ||| x5, x0, [x2, x3, x4, x6, x7, x8, x9]), (x1 ||| x5, x2, [x0, x3, x4, x6, x7, x8, x9]), (x1 ||| x5, x3, [x0, x2, x4, x6, x7, x8, x9]), (x1 ||| x5, x4, [x0, x2, x3, x6, x7, x8, x9]), (x1 ||| x5, x6, [x0, x2, x3, x4, x7, x8, x9]), (x1 ||| x5, x7, [x0, x2, x3, x4, x6, x8, x9]), (x1 ||| x5, x8, [x0, x2, x3, x4, x6, x7, x9]), (x1 ||| x5, x9, [x0, x2, x3, x4, x6, x7, x8]), (x0, x2, [x1 ||| x5, x3, x4, x6, x7, x8, x9]), (x0, x3, [x1 ||| x5, x2, x4, x6, x7, x8, x9]), (x0, x4, [x1 ||| x5, x2, x3, x6, x7, x8, x9]), (x0, x6, [x1 ||| x5, x2, x3, x4, x7, x8, x9]), (x0, x7, [x1 ||| x5, x2, x3, x4, x6, x8, x9]), (x0, x8, [x1 ||| x5, x2, x3, x4, x6, x7, x9]), (x0, x9, [x1 ||| x5, x2, x3, x4, x6, x7, x8]), (x2, x3, [x1 ||| x5, x0, x4, x6, x7, x8, x9]), (x2, x4, [x1 ||| x5, x0, x3, x6, x7, x8, x9]), (x2, x6, [x1 ||| x5, x0, x3, x4, x7, x8, x9]), (x2, x7, [x1 ||| x5, x0, x3, x4, x6, x8, x9]), (x2, x8, [x1 ||| x5, x0, x3, x4, x6, x7, x9]), (x2, x9, [x1 ||| x5, x0, x3, x4, x6, x7, x8]), (x3, x4, [x1 ||| x5, x0, x2, x6, x7, x8, x9]), (x3, x6, [x1 ||| x5, x0, x2, x4, x7, x8, x9]), (x3, x7, [x1 ||| x5, x0, x2, x4, x6, x8, x9]), (x3, x8, [x1 ||| x5, x0, x2, x4, x6, x7, x9]), (x3, x9, [x1 ||| x5, x0, x2, x4, x6, x7, x8]), (x4, x6, [x1 ||| x5, x0, x2, x3, x7, x8, x9]), (x4, x7, [x1 ||| x5, x0, x2, x3, x6, x8, x9]), (x4, x8, [x1 ||| x5, x0, x2, x3, x6, x7, x9]), (x4, x9, [x1 ||| x5, x0, x2, x3, x6, x7, x8]), (x6, x7, [x1 ||| x5, x0, x2, x3, x4, x8, x9]), (x6, x8, [x1 ||| x5, x0, x2, x3, x4, x7, x9]), (x6, x9, [x1 ||| x5, x0, x2, x3, x4, x7, x8]), (x7, x8, [x1 ||| x5, x0, x2, x3, x4, x6, x9]), (x7, x9, [x1 ||| x5, x0, x2, x3, x4, x6, x8]), (x8, x9, [x1 ||| x5, x0, x2, x3, x4, x6, x7])] := by
  decide +kernel

theorem t212 : optimized 9 1 [x1 ||| x5, x0, x2, x3, x4, x6, x7, x8, x9] = false := by
  rw [optimized.eq_2, t212_pairs]
  simp only [List.any_cons, List.any_nil, t176, t177, t178, t179, t180, t181, t182, t183, t184, t185, t186, t187, t188, t189, t190, t191, t192, t193, t194, t195, t196, t197, t198, t199, t200, t201, t202, t203, t204, t205, t206, t207, t208, t209, t210, t211, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t213 : optimized 9 0 [x1 ||| x5, x1, x0, x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t214 : dispatch 0 (optimized 8) (x1 ||| x5) x5 [x0, x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t215 : dispatch 0 (optimized 8) (x1 ||| x5) x0 [x5, x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t216 : dispatch 0 (optimized 8) (x1 ||| x5) x2 [x5, x0, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t217 : dispatch 0 (optimized 8) (x1 ||| x5) x3 [x5, x0, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t218 : dispatch 0 (optimized 8) (x1 ||| x5) x4 [x5, x0, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t219 : dispatch 0 (optimized 8) (x1 ||| x5) x6 [x5, x0, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t220 : dispatch 0 (optimized 8) (x1 ||| x5) x7 [x5, x0, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t221 : dispatch 0 (optimized 8) (x1 ||| x5) x8 [x5, x0, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t222 : dispatch 0 (optimized 8) (x1 ||| x5) x9 [x5, x0, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t223 : dispatch 0 (optimized 8) x5 x0 [x1 ||| x5, x2, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t224 : dispatch 0 (optimized 8) x5 x2 [x1 ||| x5, x0, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t225 : dispatch 0 (optimized 8) x5 x3 [x1 ||| x5, x0, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t226 : dispatch 0 (optimized 8) x5 x4 [x1 ||| x5, x0, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t227 : dispatch 0 (optimized 8) x5 x6 [x1 ||| x5, x0, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t228 : dispatch 0 (optimized 8) x5 x7 [x1 ||| x5, x0, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t229 : dispatch 0 (optimized 8) x5 x8 [x1 ||| x5, x0, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t230 : dispatch 0 (optimized 8) x5 x9 [x1 ||| x5, x0, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t231 : dispatch 0 (optimized 8) x0 x2 [x1 ||| x5, x5, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t232 : dispatch 0 (optimized 8) x0 x3 [x1 ||| x5, x5, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t233 : dispatch 0 (optimized 8) x0 x4 [x1 ||| x5, x5, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t234 : dispatch 0 (optimized 8) x0 x6 [x1 ||| x5, x5, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t235 : dispatch 0 (optimized 8) x0 x7 [x1 ||| x5, x5, x2, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t236 : dispatch 0 (optimized 8) x0 x8 [x1 ||| x5, x5, x2, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t237 : dispatch 0 (optimized 8) x0 x9 [x1 ||| x5, x5, x2, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t238 : dispatch 0 (optimized 8) x2 x3 [x1 ||| x5, x5, x0, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t239 : dispatch 0 (optimized 8) x2 x4 [x1 ||| x5, x5, x0, x3, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t240 : dispatch 0 (optimized 8) x2 x6 [x1 ||| x5, x5, x0, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t241 : dispatch 0 (optimized 8) x2 x7 [x1 ||| x5, x5, x0, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t242 : dispatch 0 (optimized 8) x2 x8 [x1 ||| x5, x5, x0, x3, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t243 : dispatch 0 (optimized 8) x2 x9 [x1 ||| x5, x5, x0, x3, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t244 : dispatch 0 (optimized 8) x3 x4 [x1 ||| x5, x5, x0, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t245 : dispatch 0 (optimized 8) x3 x6 [x1 ||| x5, x5, x0, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t246 : dispatch 0 (optimized 8) x3 x7 [x1 ||| x5, x5, x0, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t247 : dispatch 0 (optimized 8) x3 x8 [x1 ||| x5, x5, x0, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t248 : dispatch 0 (optimized 8) x3 x9 [x1 ||| x5, x5, x0, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t249 : dispatch 0 (optimized 8) x4 x6 [x1 ||| x5, x5, x0, x2, x3, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t250 : dispatch 0 (optimized 8) x4 x7 [x1 ||| x5, x5, x0, x2, x3, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t251 : dispatch 0 (optimized 8) x4 x8 [x1 ||| x5, x5, x0, x2, x3, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t252 : dispatch 0 (optimized 8) x4 x9 [x1 ||| x5, x5, x0, x2, x3, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t253 : dispatch 0 (optimized 8) x6 x7 [x1 ||| x5, x5, x0, x2, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t254 : dispatch 0 (optimized 8) x6 x8 [x1 ||| x5, x5, x0, x2, x3, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t255 : dispatch 0 (optimized 8) x6 x9 [x1 ||| x5, x5, x0, x2, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t256 : dispatch 0 (optimized 8) x7 x8 [x1 ||| x5, x5, x0, x2, x3, x4, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t257 : dispatch 0 (optimized 8) x7 x9 [x1 ||| x5, x5, x0, x2, x3, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t258 : dispatch 0 (optimized 8) x8 x9 [x1 ||| x5, x5, x0, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t259_pairs : pairs [x1 ||| x5, x5, x0, x2, x3, x4, x6, x7, x8, x9] = [(x1 ||| x5, x5, [x0, x2, x3, x4, x6, x7, x8, x9]), (x1 ||| x5, x0, [x5, x2, x3, x4, x6, x7, x8, x9]), (x1 ||| x5, x2, [x5, x0, x3, x4, x6, x7, x8, x9]), (x1 ||| x5, x3, [x5, x0, x2, x4, x6, x7, x8, x9]), (x1 ||| x5, x4, [x5, x0, x2, x3, x6, x7, x8, x9]), (x1 ||| x5, x6, [x5, x0, x2, x3, x4, x7, x8, x9]), (x1 ||| x5, x7, [x5, x0, x2, x3, x4, x6, x8, x9]), (x1 ||| x5, x8, [x5, x0, x2, x3, x4, x6, x7, x9]), (x1 ||| x5, x9, [x5, x0, x2, x3, x4, x6, x7, x8]), (x5, x0, [x1 ||| x5, x2, x3, x4, x6, x7, x8, x9]), (x5, x2, [x1 ||| x5, x0, x3, x4, x6, x7, x8, x9]), (x5, x3, [x1 ||| x5, x0, x2, x4, x6, x7, x8, x9]), (x5, x4, [x1 ||| x5, x0, x2, x3, x6, x7, x8, x9]), (x5, x6, [x1 ||| x5, x0, x2, x3, x4, x7, x8, x9]), (x5, x7, [x1 ||| x5, x0, x2, x3, x4, x6, x8, x9]), (x5, x8, [x1 ||| x5, x0, x2, x3, x4, x6, x7, x9]), (x5, x9, [x1 ||| x5, x0, x2, x3, x4, x6, x7, x8]), (x0, x2, [x1 ||| x5, x5, x3, x4, x6, x7, x8, x9]), (x0, x3, [x1 ||| x5, x5, x2, x4, x6, x7, x8, x9]), (x0, x4, [x1 ||| x5, x5, x2, x3, x6, x7, x8, x9]), (x0, x6, [x1 ||| x5, x5, x2, x3, x4, x7, x8, x9]), (x0, x7, [x1 ||| x5, x5, x2, x3, x4, x6, x8, x9]), (x0, x8, [x1 ||| x5, x5, x2, x3, x4, x6, x7, x9]), (x0, x9, [x1 ||| x5, x5, x2, x3, x4, x6, x7, x8]), (x2, x3, [x1 ||| x5, x5, x0, x4, x6, x7, x8, x9]), (x2, x4, [x1 ||| x5, x5, x0, x3, x6, x7, x8, x9]), (x2, x6, [x1 ||| x5, x5, x0, x3, x4, x7, x8, x9]), (x2, x7, [x1 ||| x5, x5, x0, x3, x4, x6, x8, x9]), (x2, x8, [x1 ||| x5, x5, x0, x3, x4, x6, x7, x9]), (x2, x9, [x1 ||| x5, x5, x0, x3, x4, x6, x7, x8]), (x3, x4, [x1 ||| x5, x5, x0, x2, x6, x7, x8, x9]), (x3, x6, [x1 ||| x5, x5, x0, x2, x4, x7, x8, x9]), (x3, x7, [x1 ||| x5, x5, x0, x2, x4, x6, x8, x9]), (x3, x8, [x1 ||| x5, x5, x0, x2, x4, x6, x7, x9]), (x3, x9, [x1 ||| x5, x5, x0, x2, x4, x6, x7, x8]), (x4, x6, [x1 ||| x5, x5, x0, x2, x3, x7, x8, x9]), (x4, x7, [x1 ||| x5, x5, x0, x2, x3, x6, x8, x9]), (x4, x8, [x1 ||| x5, x5, x0, x2, x3, x6, x7, x9]), (x4, x9, [x1 ||| x5, x5, x0, x2, x3, x6, x7, x8]), (x6, x7, [x1 ||| x5, x5, x0, x2, x3, x4, x8, x9]), (x6, x8, [x1 ||| x5, x5, x0, x2, x3, x4, x7, x9]), (x6, x9, [x1 ||| x5, x5, x0, x2, x3, x4, x7, x8]), (x7, x8, [x1 ||| x5, x5, x0, x2, x3, x4, x6, x9]), (x7, x9, [x1 ||| x5, x5, x0, x2, x3, x4, x6, x8]), (x8, x9, [x1 ||| x5, x5, x0, x2, x3, x4, x6, x7])] := by
  decide +kernel

theorem t259 : optimized 9 0 [x1 ||| x5, x5, x0, x2, x3, x4, x6, x7, x8, x9] = false := by
  rw [optimized.eq_2, t259_pairs]
  simp only [List.any_cons, List.any_nil, t214, t215, t216, t217, t218, t219, t220, t221, t222, t223, t224, t225, t226, t227, t228, t229, t230, t231, t232, t233, t234, t235, t236, t237, t238, t239, t240, t241, t242, t243, t244, t245, t246, t247, t248, t249, t250, t251, t252, t253, t254, t255, t256, t257, t258, Bool.or_false]
  all_goals decide +kernel

theorem t260 : dispatch 1 (optimized 9) x1 x5 [x0, x2, x3, x4, x6, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t212, t213, t259, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t261 : dispatch 1 (optimized 8) (x1 ||| x6) x0 [x2, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t262 : dispatch 1 (optimized 8) (x1 ||| x6) x2 [x0, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t263 : dispatch 1 (optimized 8) (x1 ||| x6) x3 [x0, x2, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t264 : dispatch 1 (optimized 8) (x1 ||| x6) x4 [x0, x2, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t265 : dispatch 1 (optimized 8) (x1 ||| x6) x5 [x0, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t266 : dispatch 1 (optimized 8) (x1 ||| x6) x7 [x0, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t267 : dispatch 1 (optimized 8) (x1 ||| x6) x8 [x0, x2, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t268 : dispatch 1 (optimized 8) (x1 ||| x6) x9 [x0, x2, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t269 : dispatch 1 (optimized 8) x0 x2 [x1 ||| x6, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t270 : dispatch 1 (optimized 8) x0 x3 [x1 ||| x6, x2, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t271 : dispatch 1 (optimized 8) x0 x4 [x1 ||| x6, x2, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t272 : dispatch 1 (optimized 8) x0 x5 [x1 ||| x6, x2, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t273 : dispatch 1 (optimized 8) x0 x7 [x1 ||| x6, x2, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t274 : dispatch 1 (optimized 8) x0 x8 [x1 ||| x6, x2, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t275 : dispatch 1 (optimized 8) x0 x9 [x1 ||| x6, x2, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t276 : dispatch 1 (optimized 8) x2 x3 [x1 ||| x6, x0, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t277 : dispatch 1 (optimized 8) x2 x4 [x1 ||| x6, x0, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t278 : dispatch 1 (optimized 8) x2 x5 [x1 ||| x6, x0, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t279 : dispatch 1 (optimized 8) x2 x7 [x1 ||| x6, x0, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t280 : dispatch 1 (optimized 8) x2 x8 [x1 ||| x6, x0, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t281 : dispatch 1 (optimized 8) x2 x9 [x1 ||| x6, x0, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t282 : dispatch 1 (optimized 8) x3 x4 [x1 ||| x6, x0, x2, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t283 : dispatch 1 (optimized 8) x3 x5 [x1 ||| x6, x0, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t284 : dispatch 1 (optimized 8) x3 x7 [x1 ||| x6, x0, x2, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t285 : dispatch 1 (optimized 8) x3 x8 [x1 ||| x6, x0, x2, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t286 : dispatch 1 (optimized 8) x3 x9 [x1 ||| x6, x0, x2, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t287 : dispatch 1 (optimized 8) x4 x5 [x1 ||| x6, x0, x2, x3, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t288 : dispatch 1 (optimized 8) x4 x7 [x1 ||| x6, x0, x2, x3, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t289 : dispatch 1 (optimized 8) x4 x8 [x1 ||| x6, x0, x2, x3, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t290 : dispatch 1 (optimized 8) x4 x9 [x1 ||| x6, x0, x2, x3, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t291 : dispatch 1 (optimized 8) x5 x7 [x1 ||| x6, x0, x2, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t292 : dispatch 1 (optimized 8) x5 x8 [x1 ||| x6, x0, x2, x3, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t293 : dispatch 1 (optimized 8) x5 x9 [x1 ||| x6, x0, x2, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t294 : dispatch 1 (optimized 8) x7 x8 [x1 ||| x6, x0, x2, x3, x4, x5, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t295 : dispatch 1 (optimized 8) x7 x9 [x1 ||| x6, x0, x2, x3, x4, x5, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t296 : dispatch 1 (optimized 8) x8 x9 [x1 ||| x6, x0, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t297_pairs : pairs [x1 ||| x6, x0, x2, x3, x4, x5, x7, x8, x9] = [(x1 ||| x6, x0, [x2, x3, x4, x5, x7, x8, x9]), (x1 ||| x6, x2, [x0, x3, x4, x5, x7, x8, x9]), (x1 ||| x6, x3, [x0, x2, x4, x5, x7, x8, x9]), (x1 ||| x6, x4, [x0, x2, x3, x5, x7, x8, x9]), (x1 ||| x6, x5, [x0, x2, x3, x4, x7, x8, x9]), (x1 ||| x6, x7, [x0, x2, x3, x4, x5, x8, x9]), (x1 ||| x6, x8, [x0, x2, x3, x4, x5, x7, x9]), (x1 ||| x6, x9, [x0, x2, x3, x4, x5, x7, x8]), (x0, x2, [x1 ||| x6, x3, x4, x5, x7, x8, x9]), (x0, x3, [x1 ||| x6, x2, x4, x5, x7, x8, x9]), (x0, x4, [x1 ||| x6, x2, x3, x5, x7, x8, x9]), (x0, x5, [x1 ||| x6, x2, x3, x4, x7, x8, x9]), (x0, x7, [x1 ||| x6, x2, x3, x4, x5, x8, x9]), (x0, x8, [x1 ||| x6, x2, x3, x4, x5, x7, x9]), (x0, x9, [x1 ||| x6, x2, x3, x4, x5, x7, x8]), (x2, x3, [x1 ||| x6, x0, x4, x5, x7, x8, x9]), (x2, x4, [x1 ||| x6, x0, x3, x5, x7, x8, x9]), (x2, x5, [x1 ||| x6, x0, x3, x4, x7, x8, x9]), (x2, x7, [x1 ||| x6, x0, x3, x4, x5, x8, x9]), (x2, x8, [x1 ||| x6, x0, x3, x4, x5, x7, x9]), (x2, x9, [x1 ||| x6, x0, x3, x4, x5, x7, x8]), (x3, x4, [x1 ||| x6, x0, x2, x5, x7, x8, x9]), (x3, x5, [x1 ||| x6, x0, x2, x4, x7, x8, x9]), (x3, x7, [x1 ||| x6, x0, x2, x4, x5, x8, x9]), (x3, x8, [x1 ||| x6, x0, x2, x4, x5, x7, x9]), (x3, x9, [x1 ||| x6, x0, x2, x4, x5, x7, x8]), (x4, x5, [x1 ||| x6, x0, x2, x3, x7, x8, x9]), (x4, x7, [x1 ||| x6, x0, x2, x3, x5, x8, x9]), (x4, x8, [x1 ||| x6, x0, x2, x3, x5, x7, x9]), (x4, x9, [x1 ||| x6, x0, x2, x3, x5, x7, x8]), (x5, x7, [x1 ||| x6, x0, x2, x3, x4, x8, x9]), (x5, x8, [x1 ||| x6, x0, x2, x3, x4, x7, x9]), (x5, x9, [x1 ||| x6, x0, x2, x3, x4, x7, x8]), (x7, x8, [x1 ||| x6, x0, x2, x3, x4, x5, x9]), (x7, x9, [x1 ||| x6, x0, x2, x3, x4, x5, x8]), (x8, x9, [x1 ||| x6, x0, x2, x3, x4, x5, x7])] := by
  decide +kernel

theorem t297 : optimized 9 1 [x1 ||| x6, x0, x2, x3, x4, x5, x7, x8, x9] = false := by
  rw [optimized.eq_2, t297_pairs]
  simp only [List.any_cons, List.any_nil, t261, t262, t263, t264, t265, t266, t267, t268, t269, t270, t271, t272, t273, t274, t275, t276, t277, t278, t279, t280, t281, t282, t283, t284, t285, t286, t287, t288, t289, t290, t291, t292, t293, t294, t295, t296, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t298 : optimized 9 0 [x1 ||| x6, x1, x0, x2, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t299 : optimized 9 0 [x1 ||| x6, x6, x0, x2, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

theorem t300 : dispatch 1 (optimized 9) x1 x6 [x0, x2, x3, x4, x5, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t297, t298, t299, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t301 : optimized 9 1 [x1 ||| x7, x0, x2, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t302 : optimized 9 0 [x1 ||| x7, x1, x0, x2, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t303 : optimized 9 0 [x1 ||| x7, x7, x0, x2, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

theorem t304 : dispatch 1 (optimized 9) x1 x7 [x0, x2, x3, x4, x5, x6, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t301, t302, t303, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t305 : dispatch 1 (optimized 9) x1 x8 [x0, x2, x3, x4, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t306 : dispatch 1 (optimized 9) x2 x3 [x0, x1, x4, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t307 : dispatch 1 (optimized 9) x2 x4 [x0, x1, x3, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t308 : optimized 9 1 [x2 ||| x5, x0, x1, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t309 : optimized 9 0 [x2 ||| x5, x2, x0, x1, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t310 : optimized 9 0 [x2 ||| x5, x5, x0, x1, x3, x4, x6, x7, x8, x9] = false := by
  decide +kernel

theorem t311 : dispatch 1 (optimized 9) x2 x5 [x0, x1, x3, x4, x6, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t308, t309, t310, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t312 : dispatch 1 (optimized 8) (x2 ||| x6) x0 [x1, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t313 : dispatch 1 (optimized 8) (x2 ||| x6) x1 [x0, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t314 : dispatch 1 (optimized 8) (x2 ||| x6) x3 [x0, x1, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t315 : dispatch 1 (optimized 8) (x2 ||| x6) x4 [x0, x1, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t316 : dispatch 1 (optimized 8) (x2 ||| x6) x5 [x0, x1, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t317 : dispatch 1 (optimized 8) (x2 ||| x6) x7 [x0, x1, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t318 : dispatch 1 (optimized 8) (x2 ||| x6) x8 [x0, x1, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t319 : dispatch 1 (optimized 8) (x2 ||| x6) x9 [x0, x1, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t320 : dispatch 1 (optimized 8) x0 x1 [x2 ||| x6, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t321 : dispatch 1 (optimized 8) x0 x3 [x2 ||| x6, x1, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t322 : dispatch 1 (optimized 8) x0 x4 [x2 ||| x6, x1, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t323 : dispatch 1 (optimized 8) x0 x5 [x2 ||| x6, x1, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t324 : dispatch 1 (optimized 8) x0 x7 [x2 ||| x6, x1, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t325 : dispatch 1 (optimized 8) x0 x8 [x2 ||| x6, x1, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t326 : dispatch 1 (optimized 8) x0 x9 [x2 ||| x6, x1, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t327 : dispatch 1 (optimized 8) x1 x3 [x2 ||| x6, x0, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t328 : dispatch 1 (optimized 8) x1 x4 [x2 ||| x6, x0, x3, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t329 : dispatch 1 (optimized 8) x1 x5 [x2 ||| x6, x0, x3, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t330 : dispatch 1 (optimized 8) x1 x7 [x2 ||| x6, x0, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t331 : dispatch 1 (optimized 8) x1 x8 [x2 ||| x6, x0, x3, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t332 : dispatch 1 (optimized 8) x1 x9 [x2 ||| x6, x0, x3, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t333 : dispatch 1 (optimized 8) x3 x4 [x2 ||| x6, x0, x1, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t334 : dispatch 1 (optimized 8) x3 x5 [x2 ||| x6, x0, x1, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t335 : dispatch 1 (optimized 8) x3 x7 [x2 ||| x6, x0, x1, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t336 : dispatch 1 (optimized 8) x3 x8 [x2 ||| x6, x0, x1, x4, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t337 : dispatch 1 (optimized 8) x3 x9 [x2 ||| x6, x0, x1, x4, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t338 : dispatch 1 (optimized 8) x4 x5 [x2 ||| x6, x0, x1, x3, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t339 : dispatch 1 (optimized 8) x4 x7 [x2 ||| x6, x0, x1, x3, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t340 : dispatch 1 (optimized 8) x4 x8 [x2 ||| x6, x0, x1, x3, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t341 : dispatch 1 (optimized 8) x4 x9 [x2 ||| x6, x0, x1, x3, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t342 : dispatch 1 (optimized 8) x5 x7 [x2 ||| x6, x0, x1, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t343 : dispatch 1 (optimized 8) x5 x8 [x2 ||| x6, x0, x1, x3, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t344 : dispatch 1 (optimized 8) x5 x9 [x2 ||| x6, x0, x1, x3, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t345 : dispatch 1 (optimized 8) x7 x8 [x2 ||| x6, x0, x1, x3, x4, x5, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t346 : dispatch 1 (optimized 8) x7 x9 [x2 ||| x6, x0, x1, x3, x4, x5, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t347 : dispatch 1 (optimized 8) x8 x9 [x2 ||| x6, x0, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t348_pairs : pairs [x2 ||| x6, x0, x1, x3, x4, x5, x7, x8, x9] = [(x2 ||| x6, x0, [x1, x3, x4, x5, x7, x8, x9]), (x2 ||| x6, x1, [x0, x3, x4, x5, x7, x8, x9]), (x2 ||| x6, x3, [x0, x1, x4, x5, x7, x8, x9]), (x2 ||| x6, x4, [x0, x1, x3, x5, x7, x8, x9]), (x2 ||| x6, x5, [x0, x1, x3, x4, x7, x8, x9]), (x2 ||| x6, x7, [x0, x1, x3, x4, x5, x8, x9]), (x2 ||| x6, x8, [x0, x1, x3, x4, x5, x7, x9]), (x2 ||| x6, x9, [x0, x1, x3, x4, x5, x7, x8]), (x0, x1, [x2 ||| x6, x3, x4, x5, x7, x8, x9]), (x0, x3, [x2 ||| x6, x1, x4, x5, x7, x8, x9]), (x0, x4, [x2 ||| x6, x1, x3, x5, x7, x8, x9]), (x0, x5, [x2 ||| x6, x1, x3, x4, x7, x8, x9]), (x0, x7, [x2 ||| x6, x1, x3, x4, x5, x8, x9]), (x0, x8, [x2 ||| x6, x1, x3, x4, x5, x7, x9]), (x0, x9, [x2 ||| x6, x1, x3, x4, x5, x7, x8]), (x1, x3, [x2 ||| x6, x0, x4, x5, x7, x8, x9]), (x1, x4, [x2 ||| x6, x0, x3, x5, x7, x8, x9]), (x1, x5, [x2 ||| x6, x0, x3, x4, x7, x8, x9]), (x1, x7, [x2 ||| x6, x0, x3, x4, x5, x8, x9]), (x1, x8, [x2 ||| x6, x0, x3, x4, x5, x7, x9]), (x1, x9, [x2 ||| x6, x0, x3, x4, x5, x7, x8]), (x3, x4, [x2 ||| x6, x0, x1, x5, x7, x8, x9]), (x3, x5, [x2 ||| x6, x0, x1, x4, x7, x8, x9]), (x3, x7, [x2 ||| x6, x0, x1, x4, x5, x8, x9]), (x3, x8, [x2 ||| x6, x0, x1, x4, x5, x7, x9]), (x3, x9, [x2 ||| x6, x0, x1, x4, x5, x7, x8]), (x4, x5, [x2 ||| x6, x0, x1, x3, x7, x8, x9]), (x4, x7, [x2 ||| x6, x0, x1, x3, x5, x8, x9]), (x4, x8, [x2 ||| x6, x0, x1, x3, x5, x7, x9]), (x4, x9, [x2 ||| x6, x0, x1, x3, x5, x7, x8]), (x5, x7, [x2 ||| x6, x0, x1, x3, x4, x8, x9]), (x5, x8, [x2 ||| x6, x0, x1, x3, x4, x7, x9]), (x5, x9, [x2 ||| x6, x0, x1, x3, x4, x7, x8]), (x7, x8, [x2 ||| x6, x0, x1, x3, x4, x5, x9]), (x7, x9, [x2 ||| x6, x0, x1, x3, x4, x5, x8]), (x8, x9, [x2 ||| x6, x0, x1, x3, x4, x5, x7])] := by
  decide +kernel

theorem t348 : optimized 9 1 [x2 ||| x6, x0, x1, x3, x4, x5, x7, x8, x9] = false := by
  rw [optimized.eq_2, t348_pairs]
  simp only [List.any_cons, List.any_nil, t312, t313, t314, t315, t316, t317, t318, t319, t320, t321, t322, t323, t324, t325, t326, t327, t328, t329, t330, t331, t332, t333, t334, t335, t336, t337, t338, t339, t340, t341, t342, t343, t344, t345, t346, t347, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t349 : optimized 9 0 [x2 ||| x6, x2, x0, x1, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t350 : optimized 9 0 [x2 ||| x6, x6, x0, x1, x3, x4, x5, x7, x8, x9] = false := by
  decide +kernel

theorem t351 : dispatch 1 (optimized 9) x2 x6 [x0, x1, x3, x4, x5, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t348, t349, t350, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t352 : dispatch 1 (optimized 8) (x2 ||| x7) x0 [x1, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t353 : dispatch 1 (optimized 8) (x2 ||| x7) x1 [x0, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t354 : dispatch 1 (optimized 8) (x2 ||| x7) x3 [x0, x1, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t355 : dispatch 1 (optimized 8) (x2 ||| x7) x4 [x0, x1, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t356 : dispatch 1 (optimized 8) (x2 ||| x7) x5 [x0, x1, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t357 : dispatch 1 (optimized 8) (x2 ||| x7) x6 [x0, x1, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t358 : dispatch 1 (optimized 8) (x2 ||| x7) x8 [x0, x1, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t359 : dispatch 1 (optimized 8) (x2 ||| x7) x9 [x0, x1, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t360 : dispatch 1 (optimized 8) x0 x1 [x2 ||| x7, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t361 : dispatch 1 (optimized 8) x0 x3 [x2 ||| x7, x1, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t362 : dispatch 1 (optimized 8) x0 x4 [x2 ||| x7, x1, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t363 : dispatch 1 (optimized 8) x0 x5 [x2 ||| x7, x1, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t364 : dispatch 1 (optimized 8) x0 x6 [x2 ||| x7, x1, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t365 : dispatch 1 (optimized 8) x0 x8 [x2 ||| x7, x1, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t366 : dispatch 1 (optimized 8) x0 x9 [x2 ||| x7, x1, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t367 : dispatch 1 (optimized 8) x1 x3 [x2 ||| x7, x0, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t368 : dispatch 1 (optimized 8) x1 x4 [x2 ||| x7, x0, x3, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t369 : dispatch 1 (optimized 8) x1 x5 [x2 ||| x7, x0, x3, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t370 : dispatch 1 (optimized 8) x1 x6 [x2 ||| x7, x0, x3, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t371 : dispatch 1 (optimized 8) x1 x8 [x2 ||| x7, x0, x3, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t372 : dispatch 1 (optimized 8) x1 x9 [x2 ||| x7, x0, x3, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t373 : dispatch 1 (optimized 8) x3 x4 [x2 ||| x7, x0, x1, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t374 : dispatch 1 (optimized 8) x3 x5 [x2 ||| x7, x0, x1, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t375 : dispatch 1 (optimized 8) x3 x6 [x2 ||| x7, x0, x1, x4, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t376 : dispatch 1 (optimized 8) x3 x8 [x2 ||| x7, x0, x1, x4, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t377 : dispatch 1 (optimized 8) x3 x9 [x2 ||| x7, x0, x1, x4, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t378 : dispatch 1 (optimized 8) x4 x5 [x2 ||| x7, x0, x1, x3, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t379 : dispatch 1 (optimized 8) x4 x6 [x2 ||| x7, x0, x1, x3, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t380 : dispatch 1 (optimized 8) x4 x8 [x2 ||| x7, x0, x1, x3, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t381 : dispatch 1 (optimized 8) x4 x9 [x2 ||| x7, x0, x1, x3, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t382 : dispatch 1 (optimized 8) x5 x6 [x2 ||| x7, x0, x1, x3, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t383 : dispatch 1 (optimized 8) x5 x8 [x2 ||| x7, x0, x1, x3, x4, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t384 : dispatch 1 (optimized 8) x5 x9 [x2 ||| x7, x0, x1, x3, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t385 : dispatch 1 (optimized 8) x6 x8 [x2 ||| x7, x0, x1, x3, x4, x5, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t386 : dispatch 1 (optimized 8) x6 x9 [x2 ||| x7, x0, x1, x3, x4, x5, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t387 : dispatch 1 (optimized 8) x8 x9 [x2 ||| x7, x0, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t388_pairs : pairs [x2 ||| x7, x0, x1, x3, x4, x5, x6, x8, x9] = [(x2 ||| x7, x0, [x1, x3, x4, x5, x6, x8, x9]), (x2 ||| x7, x1, [x0, x3, x4, x5, x6, x8, x9]), (x2 ||| x7, x3, [x0, x1, x4, x5, x6, x8, x9]), (x2 ||| x7, x4, [x0, x1, x3, x5, x6, x8, x9]), (x2 ||| x7, x5, [x0, x1, x3, x4, x6, x8, x9]), (x2 ||| x7, x6, [x0, x1, x3, x4, x5, x8, x9]), (x2 ||| x7, x8, [x0, x1, x3, x4, x5, x6, x9]), (x2 ||| x7, x9, [x0, x1, x3, x4, x5, x6, x8]), (x0, x1, [x2 ||| x7, x3, x4, x5, x6, x8, x9]), (x0, x3, [x2 ||| x7, x1, x4, x5, x6, x8, x9]), (x0, x4, [x2 ||| x7, x1, x3, x5, x6, x8, x9]), (x0, x5, [x2 ||| x7, x1, x3, x4, x6, x8, x9]), (x0, x6, [x2 ||| x7, x1, x3, x4, x5, x8, x9]), (x0, x8, [x2 ||| x7, x1, x3, x4, x5, x6, x9]), (x0, x9, [x2 ||| x7, x1, x3, x4, x5, x6, x8]), (x1, x3, [x2 ||| x7, x0, x4, x5, x6, x8, x9]), (x1, x4, [x2 ||| x7, x0, x3, x5, x6, x8, x9]), (x1, x5, [x2 ||| x7, x0, x3, x4, x6, x8, x9]), (x1, x6, [x2 ||| x7, x0, x3, x4, x5, x8, x9]), (x1, x8, [x2 ||| x7, x0, x3, x4, x5, x6, x9]), (x1, x9, [x2 ||| x7, x0, x3, x4, x5, x6, x8]), (x3, x4, [x2 ||| x7, x0, x1, x5, x6, x8, x9]), (x3, x5, [x2 ||| x7, x0, x1, x4, x6, x8, x9]), (x3, x6, [x2 ||| x7, x0, x1, x4, x5, x8, x9]), (x3, x8, [x2 ||| x7, x0, x1, x4, x5, x6, x9]), (x3, x9, [x2 ||| x7, x0, x1, x4, x5, x6, x8]), (x4, x5, [x2 ||| x7, x0, x1, x3, x6, x8, x9]), (x4, x6, [x2 ||| x7, x0, x1, x3, x5, x8, x9]), (x4, x8, [x2 ||| x7, x0, x1, x3, x5, x6, x9]), (x4, x9, [x2 ||| x7, x0, x1, x3, x5, x6, x8]), (x5, x6, [x2 ||| x7, x0, x1, x3, x4, x8, x9]), (x5, x8, [x2 ||| x7, x0, x1, x3, x4, x6, x9]), (x5, x9, [x2 ||| x7, x0, x1, x3, x4, x6, x8]), (x6, x8, [x2 ||| x7, x0, x1, x3, x4, x5, x9]), (x6, x9, [x2 ||| x7, x0, x1, x3, x4, x5, x8]), (x8, x9, [x2 ||| x7, x0, x1, x3, x4, x5, x6])] := by
  decide +kernel

theorem t388 : optimized 9 1 [x2 ||| x7, x0, x1, x3, x4, x5, x6, x8, x9] = false := by
  rw [optimized.eq_2, t388_pairs]
  simp only [List.any_cons, List.any_nil, t352, t353, t354, t355, t356, t357, t358, t359, t360, t361, t362, t363, t364, t365, t366, t367, t368, t369, t370, t371, t372, t373, t374, t375, t376, t377, t378, t379, t380, t381, t382, t383, t384, t385, t386, t387, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t389 : optimized 9 0 [x2 ||| x7, x2, x0, x1, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t390 : optimized 9 0 [x2 ||| x7, x7, x0, x1, x3, x4, x5, x6, x8, x9] = false := by
  decide +kernel

theorem t391 : dispatch 1 (optimized 9) x2 x7 [x0, x1, x3, x4, x5, x6, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t388, t389, t390, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t392 : dispatch 0 (optimized 8) (x3 ||| x4) x4 [x0, x1, x2, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t393 : dispatch 0 (optimized 8) (x3 ||| x4) x0 [x4, x1, x2, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t394 : dispatch 0 (optimized 8) (x3 ||| x4) x1 [x4, x0, x2, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t395 : dispatch 0 (optimized 8) (x3 ||| x4) x2 [x4, x0, x1, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t396 : dispatch 0 (optimized 8) (x3 ||| x4) x5 [x4, x0, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t397 : dispatch 0 (optimized 8) (x3 ||| x4) x6 [x4, x0, x1, x2, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t398 : dispatch 0 (optimized 8) (x3 ||| x4) x7 [x4, x0, x1, x2, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t399 : dispatch 0 (optimized 8) (x3 ||| x4) x8 [x4, x0, x1, x2, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t400 : dispatch 0 (optimized 8) (x3 ||| x4) x9 [x4, x0, x1, x2, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t401 : dispatch 0 (optimized 8) x4 x0 [x3 ||| x4, x1, x2, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t402 : dispatch 0 (optimized 8) x4 x1 [x3 ||| x4, x0, x2, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t403 : dispatch 0 (optimized 8) x4 x2 [x3 ||| x4, x0, x1, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t404 : dispatch 0 (optimized 8) x4 x5 [x3 ||| x4, x0, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t405 : dispatch 0 (optimized 8) x4 x6 [x3 ||| x4, x0, x1, x2, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t406 : dispatch 0 (optimized 8) x4 x7 [x3 ||| x4, x0, x1, x2, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t407 : dispatch 0 (optimized 8) x4 x8 [x3 ||| x4, x0, x1, x2, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t408 : dispatch 0 (optimized 8) x4 x9 [x3 ||| x4, x0, x1, x2, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t409 : dispatch 0 (optimized 8) x0 x1 [x3 ||| x4, x4, x2, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t410 : dispatch 0 (optimized 8) x0 x2 [x3 ||| x4, x4, x1, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t411 : dispatch 0 (optimized 8) x0 x5 [x3 ||| x4, x4, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t412 : dispatch 0 (optimized 8) x0 x6 [x3 ||| x4, x4, x1, x2, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t413 : dispatch 0 (optimized 8) x0 x7 [x3 ||| x4, x4, x1, x2, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t414 : dispatch 0 (optimized 8) x0 x8 [x3 ||| x4, x4, x1, x2, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t415 : dispatch 0 (optimized 8) x0 x9 [x3 ||| x4, x4, x1, x2, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t416 : dispatch 0 (optimized 8) x1 x2 [x3 ||| x4, x4, x0, x5, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t417 : dispatch 0 (optimized 8) x1 x5 [x3 ||| x4, x4, x0, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t418 : dispatch 0 (optimized 8) x1 x6 [x3 ||| x4, x4, x0, x2, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t419 : dispatch 0 (optimized 8) x1 x7 [x3 ||| x4, x4, x0, x2, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t420 : dispatch 0 (optimized 8) x1 x8 [x3 ||| x4, x4, x0, x2, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t421 : dispatch 0 (optimized 8) x1 x9 [x3 ||| x4, x4, x0, x2, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t422 : dispatch 0 (optimized 8) x2 x5 [x3 ||| x4, x4, x0, x1, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t423 : dispatch 0 (optimized 8) x2 x6 [x3 ||| x4, x4, x0, x1, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t424 : dispatch 0 (optimized 8) x2 x7 [x3 ||| x4, x4, x0, x1, x5, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t425 : dispatch 0 (optimized 8) x2 x8 [x3 ||| x4, x4, x0, x1, x5, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t426 : dispatch 0 (optimized 8) x2 x9 [x3 ||| x4, x4, x0, x1, x5, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t427 : dispatch 0 (optimized 8) x5 x6 [x3 ||| x4, x4, x0, x1, x2, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t428 : dispatch 0 (optimized 8) x5 x7 [x3 ||| x4, x4, x0, x1, x2, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t429 : dispatch 0 (optimized 8) x5 x8 [x3 ||| x4, x4, x0, x1, x2, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t430 : dispatch 0 (optimized 8) x5 x9 [x3 ||| x4, x4, x0, x1, x2, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t431 : dispatch 0 (optimized 8) x6 x7 [x3 ||| x4, x4, x0, x1, x2, x5, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t432 : dispatch 0 (optimized 8) x6 x8 [x3 ||| x4, x4, x0, x1, x2, x5, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t433 : dispatch 0 (optimized 8) x6 x9 [x3 ||| x4, x4, x0, x1, x2, x5, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t434 : dispatch 0 (optimized 8) x7 x8 [x3 ||| x4, x4, x0, x1, x2, x5, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t435 : dispatch 0 (optimized 8) x7 x9 [x3 ||| x4, x4, x0, x1, x2, x5, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t436 : dispatch 0 (optimized 8) x8 x9 [x3 ||| x4, x4, x0, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t437_pairs : pairs [x3 ||| x4, x4, x0, x1, x2, x5, x6, x7, x8, x9] = [(x3 ||| x4, x4, [x0, x1, x2, x5, x6, x7, x8, x9]), (x3 ||| x4, x0, [x4, x1, x2, x5, x6, x7, x8, x9]), (x3 ||| x4, x1, [x4, x0, x2, x5, x6, x7, x8, x9]), (x3 ||| x4, x2, [x4, x0, x1, x5, x6, x7, x8, x9]), (x3 ||| x4, x5, [x4, x0, x1, x2, x6, x7, x8, x9]), (x3 ||| x4, x6, [x4, x0, x1, x2, x5, x7, x8, x9]), (x3 ||| x4, x7, [x4, x0, x1, x2, x5, x6, x8, x9]), (x3 ||| x4, x8, [x4, x0, x1, x2, x5, x6, x7, x9]), (x3 ||| x4, x9, [x4, x0, x1, x2, x5, x6, x7, x8]), (x4, x0, [x3 ||| x4, x1, x2, x5, x6, x7, x8, x9]), (x4, x1, [x3 ||| x4, x0, x2, x5, x6, x7, x8, x9]), (x4, x2, [x3 ||| x4, x0, x1, x5, x6, x7, x8, x9]), (x4, x5, [x3 ||| x4, x0, x1, x2, x6, x7, x8, x9]), (x4, x6, [x3 ||| x4, x0, x1, x2, x5, x7, x8, x9]), (x4, x7, [x3 ||| x4, x0, x1, x2, x5, x6, x8, x9]), (x4, x8, [x3 ||| x4, x0, x1, x2, x5, x6, x7, x9]), (x4, x9, [x3 ||| x4, x0, x1, x2, x5, x6, x7, x8]), (x0, x1, [x3 ||| x4, x4, x2, x5, x6, x7, x8, x9]), (x0, x2, [x3 ||| x4, x4, x1, x5, x6, x7, x8, x9]), (x0, x5, [x3 ||| x4, x4, x1, x2, x6, x7, x8, x9]), (x0, x6, [x3 ||| x4, x4, x1, x2, x5, x7, x8, x9]), (x0, x7, [x3 ||| x4, x4, x1, x2, x5, x6, x8, x9]), (x0, x8, [x3 ||| x4, x4, x1, x2, x5, x6, x7, x9]), (x0, x9, [x3 ||| x4, x4, x1, x2, x5, x6, x7, x8]), (x1, x2, [x3 ||| x4, x4, x0, x5, x6, x7, x8, x9]), (x1, x5, [x3 ||| x4, x4, x0, x2, x6, x7, x8, x9]), (x1, x6, [x3 ||| x4, x4, x0, x2, x5, x7, x8, x9]), (x1, x7, [x3 ||| x4, x4, x0, x2, x5, x6, x8, x9]), (x1, x8, [x3 ||| x4, x4, x0, x2, x5, x6, x7, x9]), (x1, x9, [x3 ||| x4, x4, x0, x2, x5, x6, x7, x8]), (x2, x5, [x3 ||| x4, x4, x0, x1, x6, x7, x8, x9]), (x2, x6, [x3 ||| x4, x4, x0, x1, x5, x7, x8, x9]), (x2, x7, [x3 ||| x4, x4, x0, x1, x5, x6, x8, x9]), (x2, x8, [x3 ||| x4, x4, x0, x1, x5, x6, x7, x9]), (x2, x9, [x3 ||| x4, x4, x0, x1, x5, x6, x7, x8]), (x5, x6, [x3 ||| x4, x4, x0, x1, x2, x7, x8, x9]), (x5, x7, [x3 ||| x4, x4, x0, x1, x2, x6, x8, x9]), (x5, x8, [x3 ||| x4, x4, x0, x1, x2, x6, x7, x9]), (x5, x9, [x3 ||| x4, x4, x0, x1, x2, x6, x7, x8]), (x6, x7, [x3 ||| x4, x4, x0, x1, x2, x5, x8, x9]), (x6, x8, [x3 ||| x4, x4, x0, x1, x2, x5, x7, x9]), (x6, x9, [x3 ||| x4, x4, x0, x1, x2, x5, x7, x8]), (x7, x8, [x3 ||| x4, x4, x0, x1, x2, x5, x6, x9]), (x7, x9, [x3 ||| x4, x4, x0, x1, x2, x5, x6, x8]), (x8, x9, [x3 ||| x4, x4, x0, x1, x2, x5, x6, x7])] := by
  decide +kernel

theorem t437 : optimized 9 0 [x3 ||| x4, x4, x0, x1, x2, x5, x6, x7, x8, x9] = false := by
  rw [optimized.eq_2, t437_pairs]
  simp only [List.any_cons, List.any_nil, t392, t393, t394, t395, t396, t397, t398, t399, t400, t401, t402, t403, t404, t405, t406, t407, t408, t409, t410, t411, t412, t413, t414, t415, t416, t417, t418, t419, t420, t421, t422, t423, t424, t425, t426, t427, t428, t429, t430, t431, t432, t433, t434, t435, t436, Bool.or_false]
  all_goals decide +kernel

theorem t438 : dispatch 1 (optimized 9) x3 x4 [x0, x1, x2, x5, x6, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t437, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t439 : dispatch 0 (optimized 8) (x3 &&& x5) x5 [x0, x1, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t440 : dispatch 0 (optimized 8) (x3 &&& x5) x0 [x5, x1, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t441 : dispatch 0 (optimized 8) (x3 &&& x5) x1 [x5, x0, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t442 : dispatch 0 (optimized 8) (x3 &&& x5) x2 [x5, x0, x1, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t443 : dispatch 0 (optimized 8) (x3 &&& x5) x4 [x5, x0, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t444 : dispatch 0 (optimized 8) (x3 &&& x5) x6 [x5, x0, x1, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t445 : dispatch 0 (optimized 8) (x3 &&& x5) x7 [x5, x0, x1, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t446 : dispatch 0 (optimized 8) (x3 &&& x5) x8 [x5, x0, x1, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t447 : dispatch 0 (optimized 8) (x3 &&& x5) x9 [x5, x0, x1, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t448 : dispatch 0 (optimized 8) x5 x0 [x3 &&& x5, x1, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t449 : dispatch 0 (optimized 8) x5 x1 [x3 &&& x5, x0, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t450 : dispatch 0 (optimized 8) x5 x2 [x3 &&& x5, x0, x1, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t451 : dispatch 0 (optimized 8) x5 x4 [x3 &&& x5, x0, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t452 : dispatch 0 (optimized 8) x5 x6 [x3 &&& x5, x0, x1, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t453 : dispatch 0 (optimized 8) x5 x7 [x3 &&& x5, x0, x1, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t454 : dispatch 0 (optimized 8) x5 x8 [x3 &&& x5, x0, x1, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t455 : dispatch 0 (optimized 8) x5 x9 [x3 &&& x5, x0, x1, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t456 : dispatch 0 (optimized 8) x0 x1 [x3 &&& x5, x5, x2, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t457 : dispatch 0 (optimized 8) x0 x2 [x3 &&& x5, x5, x1, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t458 : dispatch 0 (optimized 8) x0 x4 [x3 &&& x5, x5, x1, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t459 : dispatch 0 (optimized 8) x0 x6 [x3 &&& x5, x5, x1, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t460 : dispatch 0 (optimized 8) x0 x7 [x3 &&& x5, x5, x1, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t461 : dispatch 0 (optimized 8) x0 x8 [x3 &&& x5, x5, x1, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t462 : dispatch 0 (optimized 8) x0 x9 [x3 &&& x5, x5, x1, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t463 : dispatch 0 (optimized 8) x1 x2 [x3 &&& x5, x5, x0, x4, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t464 : dispatch 0 (optimized 8) x1 x4 [x3 &&& x5, x5, x0, x2, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t465 : dispatch 0 (optimized 8) x1 x6 [x3 &&& x5, x5, x0, x2, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t466 : dispatch 0 (optimized 8) x1 x7 [x3 &&& x5, x5, x0, x2, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t467 : dispatch 0 (optimized 8) x1 x8 [x3 &&& x5, x5, x0, x2, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t468 : dispatch 0 (optimized 8) x1 x9 [x3 &&& x5, x5, x0, x2, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t469 : dispatch 0 (optimized 8) x2 x4 [x3 &&& x5, x5, x0, x1, x6, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t470 : dispatch 0 (optimized 8) x2 x6 [x3 &&& x5, x5, x0, x1, x4, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t471 : dispatch 0 (optimized 8) x2 x7 [x3 &&& x5, x5, x0, x1, x4, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t472 : dispatch 0 (optimized 8) x2 x8 [x3 &&& x5, x5, x0, x1, x4, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t473 : dispatch 0 (optimized 8) x2 x9 [x3 &&& x5, x5, x0, x1, x4, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t474 : dispatch 0 (optimized 8) x4 x6 [x3 &&& x5, x5, x0, x1, x2, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t475 : dispatch 0 (optimized 8) x4 x7 [x3 &&& x5, x5, x0, x1, x2, x6, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t476 : dispatch 0 (optimized 8) x4 x8 [x3 &&& x5, x5, x0, x1, x2, x6, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t477 : dispatch 0 (optimized 8) x4 x9 [x3 &&& x5, x5, x0, x1, x2, x6, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t478 : dispatch 0 (optimized 8) x6 x7 [x3 &&& x5, x5, x0, x1, x2, x4, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t479 : dispatch 0 (optimized 8) x6 x8 [x3 &&& x5, x5, x0, x1, x2, x4, x7, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t480 : dispatch 0 (optimized 8) x6 x9 [x3 &&& x5, x5, x0, x1, x2, x4, x7, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t481 : dispatch 0 (optimized 8) x7 x8 [x3 &&& x5, x5, x0, x1, x2, x4, x6, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t482 : dispatch 0 (optimized 8) x7 x9 [x3 &&& x5, x5, x0, x1, x2, x4, x6, x8] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t483 : dispatch 0 (optimized 8) x8 x9 [x3 &&& x5, x5, x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t484_pairs : pairs [x3 &&& x5, x5, x0, x1, x2, x4, x6, x7, x8, x9] = [(x3 &&& x5, x5, [x0, x1, x2, x4, x6, x7, x8, x9]), (x3 &&& x5, x0, [x5, x1, x2, x4, x6, x7, x8, x9]), (x3 &&& x5, x1, [x5, x0, x2, x4, x6, x7, x8, x9]), (x3 &&& x5, x2, [x5, x0, x1, x4, x6, x7, x8, x9]), (x3 &&& x5, x4, [x5, x0, x1, x2, x6, x7, x8, x9]), (x3 &&& x5, x6, [x5, x0, x1, x2, x4, x7, x8, x9]), (x3 &&& x5, x7, [x5, x0, x1, x2, x4, x6, x8, x9]), (x3 &&& x5, x8, [x5, x0, x1, x2, x4, x6, x7, x9]), (x3 &&& x5, x9, [x5, x0, x1, x2, x4, x6, x7, x8]), (x5, x0, [x3 &&& x5, x1, x2, x4, x6, x7, x8, x9]), (x5, x1, [x3 &&& x5, x0, x2, x4, x6, x7, x8, x9]), (x5, x2, [x3 &&& x5, x0, x1, x4, x6, x7, x8, x9]), (x5, x4, [x3 &&& x5, x0, x1, x2, x6, x7, x8, x9]), (x5, x6, [x3 &&& x5, x0, x1, x2, x4, x7, x8, x9]), (x5, x7, [x3 &&& x5, x0, x1, x2, x4, x6, x8, x9]), (x5, x8, [x3 &&& x5, x0, x1, x2, x4, x6, x7, x9]), (x5, x9, [x3 &&& x5, x0, x1, x2, x4, x6, x7, x8]), (x0, x1, [x3 &&& x5, x5, x2, x4, x6, x7, x8, x9]), (x0, x2, [x3 &&& x5, x5, x1, x4, x6, x7, x8, x9]), (x0, x4, [x3 &&& x5, x5, x1, x2, x6, x7, x8, x9]), (x0, x6, [x3 &&& x5, x5, x1, x2, x4, x7, x8, x9]), (x0, x7, [x3 &&& x5, x5, x1, x2, x4, x6, x8, x9]), (x0, x8, [x3 &&& x5, x5, x1, x2, x4, x6, x7, x9]), (x0, x9, [x3 &&& x5, x5, x1, x2, x4, x6, x7, x8]), (x1, x2, [x3 &&& x5, x5, x0, x4, x6, x7, x8, x9]), (x1, x4, [x3 &&& x5, x5, x0, x2, x6, x7, x8, x9]), (x1, x6, [x3 &&& x5, x5, x0, x2, x4, x7, x8, x9]), (x1, x7, [x3 &&& x5, x5, x0, x2, x4, x6, x8, x9]), (x1, x8, [x3 &&& x5, x5, x0, x2, x4, x6, x7, x9]), (x1, x9, [x3 &&& x5, x5, x0, x2, x4, x6, x7, x8]), (x2, x4, [x3 &&& x5, x5, x0, x1, x6, x7, x8, x9]), (x2, x6, [x3 &&& x5, x5, x0, x1, x4, x7, x8, x9]), (x2, x7, [x3 &&& x5, x5, x0, x1, x4, x6, x8, x9]), (x2, x8, [x3 &&& x5, x5, x0, x1, x4, x6, x7, x9]), (x2, x9, [x3 &&& x5, x5, x0, x1, x4, x6, x7, x8]), (x4, x6, [x3 &&& x5, x5, x0, x1, x2, x7, x8, x9]), (x4, x7, [x3 &&& x5, x5, x0, x1, x2, x6, x8, x9]), (x4, x8, [x3 &&& x5, x5, x0, x1, x2, x6, x7, x9]), (x4, x9, [x3 &&& x5, x5, x0, x1, x2, x6, x7, x8]), (x6, x7, [x3 &&& x5, x5, x0, x1, x2, x4, x8, x9]), (x6, x8, [x3 &&& x5, x5, x0, x1, x2, x4, x7, x9]), (x6, x9, [x3 &&& x5, x5, x0, x1, x2, x4, x7, x8]), (x7, x8, [x3 &&& x5, x5, x0, x1, x2, x4, x6, x9]), (x7, x9, [x3 &&& x5, x5, x0, x1, x2, x4, x6, x8]), (x8, x9, [x3 &&& x5, x5, x0, x1, x2, x4, x6, x7])] := by
  decide +kernel

theorem t484 : optimized 9 0 [x3 &&& x5, x5, x0, x1, x2, x4, x6, x7, x8, x9] = false := by
  rw [optimized.eq_2, t484_pairs]
  simp only [List.any_cons, List.any_nil, t439, t440, t441, t442, t443, t444, t445, t446, t447, t448, t449, t450, t451, t452, t453, t454, t455, t456, t457, t458, t459, t460, t461, t462, t463, t464, t465, t466, t467, t468, t469, t470, t471, t472, t473, t474, t475, t476, t477, t478, t479, t480, t481, t482, t483, Bool.or_false]
  all_goals decide +kernel

theorem t485 : dispatch 1 (optimized 9) x3 x5 [x0, x1, x2, x4, x6, x7, x8, x9] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t484, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t486 : dispatch 1 (optimized 9) x3 x6 [x0, x1, x2, x4, x5, x7, x8, x9] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t487 : dispatch 1 (optimized 9) x4 x5 [x0, x1, x2, x3, x6, x7, x8, x9] = false := by
  decide +kernel

def heavy0 : List W := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]

set_option maxRecDepth 8000 in
theorem heavy0_pairs : pairs heavy0 = [(x0, x1, [x2, x3, x4, x5, x6, x7, x8, x9]), (x0, x2, [x1, x3, x4, x5, x6, x7, x8, x9]), (x0, x3, [x1, x2, x4, x5, x6, x7, x8, x9]), (x0, x4, [x1, x2, x3, x5, x6, x7, x8, x9]), (x0, x5, [x1, x2, x3, x4, x6, x7, x8, x9]), (x0, x6, [x1, x2, x3, x4, x5, x7, x8, x9]), (x0, x7, [x1, x2, x3, x4, x5, x6, x8, x9]), (x0, x8, [x1, x2, x3, x4, x5, x6, x7, x9]), (x0, x9, [x1, x2, x3, x4, x5, x6, x7, x8]), (x1, x2, [x0, x3, x4, x5, x6, x7, x8, x9]), (x1, x3, [x0, x2, x4, x5, x6, x7, x8, x9]), (x1, x4, [x0, x2, x3, x5, x6, x7, x8, x9]), (x1, x5, [x0, x2, x3, x4, x6, x7, x8, x9]), (x1, x6, [x0, x2, x3, x4, x5, x7, x8, x9]), (x1, x7, [x0, x2, x3, x4, x5, x6, x8, x9]), (x1, x8, [x0, x2, x3, x4, x5, x6, x7, x9]), (x1, x9, [x0, x2, x3, x4, x5, x6, x7, x8]), (x2, x3, [x0, x1, x4, x5, x6, x7, x8, x9]), (x2, x4, [x0, x1, x3, x5, x6, x7, x8, x9]), (x2, x5, [x0, x1, x3, x4, x6, x7, x8, x9]), (x2, x6, [x0, x1, x3, x4, x5, x7, x8, x9]), (x2, x7, [x0, x1, x3, x4, x5, x6, x8, x9]), (x2, x8, [x0, x1, x3, x4, x5, x6, x7, x9]), (x2, x9, [x0, x1, x3, x4, x5, x6, x7, x8]), (x3, x4, [x0, x1, x2, x5, x6, x7, x8, x9]), (x3, x5, [x0, x1, x2, x4, x6, x7, x8, x9]), (x3, x6, [x0, x1, x2, x4, x5, x7, x8, x9]), (x3, x7, [x0, x1, x2, x4, x5, x6, x8, x9]), (x3, x8, [x0, x1, x2, x4, x5, x6, x7, x9]), (x3, x9, [x0, x1, x2, x4, x5, x6, x7, x8]), (x4, x5, [x0, x1, x2, x3, x6, x7, x8, x9]), (x4, x6, [x0, x1, x2, x3, x5, x7, x8, x9]), (x4, x7, [x0, x1, x2, x3, x5, x6, x8, x9]), (x4, x8, [x0, x1, x2, x3, x5, x6, x7, x9]), (x4, x9, [x0, x1, x2, x3, x5, x6, x7, x8]), (x5, x6, [x0, x1, x2, x3, x4, x7, x8, x9]), (x5, x7, [x0, x1, x2, x3, x4, x6, x8, x9]), (x5, x8, [x0, x1, x2, x3, x4, x6, x7, x9]), (x5, x9, [x0, x1, x2, x3, x4, x6, x7, x8]), (x6, x7, [x0, x1, x2, x3, x4, x5, x8, x9]), (x6, x8, [x0, x1, x2, x3, x4, x5, x7, x9]), (x6, x9, [x0, x1, x2, x3, x4, x5, x7, x8]), (x7, x8, [x0, x1, x2, x3, x4, x5, x6, x9]), (x7, x9, [x0, x1, x2, x3, x4, x5, x6, x8]), (x8, x9, [x0, x1, x2, x3, x4, x5, x6, x7])] := by
  decide +kernel

-- The graph has a side-swapping automorphism: exchanging each left input with its image on the
-- right maps a live run to a live run (`sigma` below permutes the pair slots). So only one first
-- pair of each swapped couple needs the search. `selectRows` and its two lemmas are copied from
-- the accepted L-meta-8463 by k-sandhu (open-goat/pequalnp-proofs, Apache License 2.0).

def selectRows (rows : Fin 272 → Fin 272) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 272 => w[(rows k).val]))).cast List.length_ofFn

theorem selectRows_bit (rows : Fin 272 → Fin 272) (w : W) (j : Fin 272) :
    (selectRows rows w)[j.val] = w[(rows j).val] := by
  rw [← BitVec.getLsbD_eq_getElem j.isLt]
  simp only [selectRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt, dite_eq_left, Option.getD_some]

theorem selectRows_land (rows : Fin 272 → Fin 272) (u v : W) :
    selectRows rows (u &&& v) = (selectRows rows u &&& selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 272 := ⟨j,hj⟩
  change (selectRows rows (u &&& v))[k.val] = (selectRows rows u &&& selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_and]

theorem selectRows_lor (rows : Fin 272 → Fin 272) (u v : W) :
    selectRows rows (u ||| v) = (selectRows rows u ||| selectRows rows v) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 272 := ⟨j,hj⟩
  change (selectRows rows (u ||| v))[k.val] = (selectRows rows u ||| selectRows rows v)[k.val]
  simp only [selectRows_bit, BitVec.getElem_or]

def swapTable : List ℕ := [84, 81, 70, 83, 80, 77, 82, 79, 76, 73, 78, 75, 72, 69, 74, 71, 68, 67, 64, 53, 66, 63, 60, 65, 62, 59, 56, 61, 58, 55, 52, 57, 54, 51, 50, 47, 36, 49, 46, 43, 48, 45, 42, 39, 44, 41, 38, 35, 40, 37, 34, 33, 30, 19, 32, 29, 26, 31, 28, 25, 22, 27, 24, 21, 18, 23, 20, 17, 16, 13, 2, 15, 12, 9, 14, 11, 8, 5, 10, 7, 4, 1, 6, 3, 0, 135, 132, 121, 134, 131, 128, 133, 130, 127, 124, 129, 126, 123, 120, 125, 122, 119, 118, 115, 104, 117, 114, 111, 116, 113, 110, 107, 112, 109, 106, 103, 108, 105, 102, 101, 98, 87, 100, 97, 94, 99, 96, 93, 90, 95, 92, 89, 86, 91, 88, 85, 220, 217, 206, 219, 216, 213, 218, 215, 212, 209, 214, 211, 208, 205, 210, 207, 204, 203, 200, 189, 202, 199, 196, 201, 198, 195, 192, 197, 194, 191, 188, 193, 190, 187, 186, 183, 172, 185, 182, 179, 184, 181, 178, 175, 180, 177, 174, 171, 176, 173, 170, 169, 166, 155, 168, 165, 162, 167, 164, 161, 158, 163, 160, 157, 154, 159, 156, 153, 152, 149, 138, 151, 148, 145, 150, 147, 144, 141, 146, 143, 140, 137, 142, 139, 136, 271, 268, 257, 270, 267, 264, 269, 266, 263, 260, 265, 262, 259, 256, 261, 258, 255, 254, 251, 240, 253, 250, 247, 252, 249, 246, 243, 248, 245, 242, 239, 244, 241, 238, 237, 234, 223, 236, 233, 230, 235, 232, 229, 226, 231, 228, 225, 222, 227, 224, 221]

def swapRows (k : Fin 272) : Fin 272 := ⟨swapTable.getD k.val 0 % 272, Nat.mod_lt _ (by decide)⟩

def sigma (w : W) : W := selectRows swapRows w

set_option maxRecDepth 8000 in
theorem swap_invol : ∀ j : Fin 272, swapRows (swapRows j) = j := by
  decide +kernel

theorem sigma_sigma (w : W) : sigma (sigma w) = w := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  let k : Fin 272 := ⟨j, hj⟩
  change (sigma (sigma w))[k.val] = w[k.val]
  simp only [sigma, selectRows_bit, swap_invol]

theorem sigma_inj : Function.Injective sigma := fun a b h => by
  rw [← sigma_sigma a, h, sigma_sigma]

theorem sigma_ops (a b z : W) (hz : z ∈ basicOps a b) : sigma z ∈ basicOps (sigma a) (sigma b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl
  · exact .inl (selectRows_land _ _ _)
  · exact .inr (selectRows_lor _ _ _)

set_option maxRecDepth 8000 in
theorem sigma_goal : sigma goal = goal := by
  decide +kernel

theorem live_map {g : W} : ∀ {k : ℕ} {s : Finset W},
    live basicOps g k s → live basicOps (sigma g) k (s.image sigma) := by
  intro k
  induction k with
  | zero =>
    intro s h
    change s = {g} at h
    subst h
    exact Finset.image_singleton _ _
  | succ k ih =>
    intro s h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨sigma a, Finset.mem_image_of_mem _ ha, sigma b, Finset.mem_image_of_mem _ hb,
        sigma_inj.ne hab, sigma z, sigma_ops a b z hz, ?_, rest.image sigma, ?_, ?_⟩
      · intro hm
        obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hm
        exact hout (sigma_inj hyz ▸ hy)
      · rw [hs, Finset.image_insert, Finset.image_insert]
      · have h2 := ih tail
        rwa [Finset.image_insert] at h2

/-- The first step of a live run on the list `ws` makes `dispatch` true on a triple of `pairs ws`
whose first two entries are the step's pair (the inner part of `optimized_complete`). -/
theorem first_dispatch (k : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = k + 2) {a b z : W} {needed : Finset W}
    (ha : a ∈ ws.toFinset) (hb : b ∈ ws.toFinset) (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (hout : z ∉ ws.toFinset) (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps goal k (insert z needed)) :
    ∃ t ∈ pairs ws, ((t.1 = a ∧ t.2.1 = b) ∨ (t.1 = b ∧ t.2.1 = a)) ∧
      dispatch extra (optimized k) t.1 t.2.1 t.2.2 = true := by
  obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
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
    apply optimized_complete k _ _ hnd _ hl
    simp; omega
  rcases hm with direct | swap
  · exact ⟨(a, b, r), direct, .inl ⟨rfl, rfl⟩, go hp hs hz⟩
  · exact ⟨(b, a, r), swap, .inr ⟨rfl, rfl⟩,
      go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

set_option maxRecDepth 8000 in
theorem heavy0_nodup : heavy0.Nodup := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx0 : sigma x0 = x9 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx1 : sigma x1 = x8 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx2 : sigma x2 = x7 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx3 : sigma x3 = x6 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx4 : sigma x4 = x5 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx5 : sigma x5 = x4 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx6 : sigma x6 = x3 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx7 : sigma x7 = x2 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx8 : sigma x8 = x1 := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem sx9 : sigma x9 = x0 := by
  decide +kernel

theorem sigma_mem : ∀ w ∈ heavy0, sigma w ∈ heavy0 := by
  intro w hw
  simp only [heavy0, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sx0, sx1, sx2, sx3, sx4, sx5, sx6, sx7, sx8, sx9] <;> simp

theorem heavy_image : heavy0.toFinset.image sigma = heavy0.toFinset := by
  ext w
  simp only [Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact sigma_mem y hy
  · intro hw
    exact ⟨sigma w, sigma_mem w hw, sigma_sigma w⟩

/-- One pair of each swapped couple of first pairs (and every pair the swap fixes). -/
def canonList : List (W × W) := [(x0, x1), (x0, x2), (x0, x3), (x0, x4), (x0, x5), (x0, x6), (x0, x7), (x0, x8), (x0, x9), (x1, x2), (x1, x3), (x1, x4), (x1, x5), (x1, x6), (x1, x7), (x1, x8), (x2, x3), (x2, x4), (x2, x5), (x2, x6), (x2, x7), (x3, x4), (x3, x5), (x3, x6), (x4, x5)]

def canonPair (a b : W) : Bool :=
  canonList.any (fun p => (p.1 == a && p.2 == b) || (p.1 == b && p.2 == a))

theorem canonPair_comm (a b : W) : canonPair a b = canonPair b a := by
  unfold canonPair
  congr 1
  funext p
  rw [Bool.or_comm]

set_option maxRecDepth 8000 in
theorem canon_sigma : ∀ a ∈ heavy0, ∀ b ∈ heavy0, a ≠ b → canonPair a b = false →
    canonPair (sigma a) (sigma b) = true := by
  intro a ha b hb hab hc
  simp only [heavy0, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [sx0, sx1, sx2, sx3, sx4, sx5, sx6, sx7, sx8, sx9] <;>
    first
    | exact absurd rfl hab
    | exact absurd hc (by decide +kernel)
    | decide +kernel

theorem canon_false (t : W × W × List W) (ht : t ∈ pairs heavy0) (hc : canonPair t.1 t.2.1 = true) :
    dispatch 1 (optimized 9) t.1 t.2.1 t.2.2 = false := by
  rw [heavy0_pairs] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact t1
  · exact t2
  · exact t3
  · exact t4
  · exact t44
  · exact t84
  · exact t131
  · exact t132
  · exact t172
  · exact t173
  · exact t174
  · exact t175
  · exact t260
  · exact t300
  · exact t304
  · exact t305
  · exact absurd hc (by decide +kernel)
  · exact t306
  · exact t307
  · exact t311
  · exact t351
  · exact t391
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact t438
  · exact t485
  · exact t486
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact t487
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)
  · exact absurd hc (by decide +kernel)

theorem heavy_root (h : live basicOps goal 10 heavy0.toFinset) : False := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have h8 := List.toFinset_card_of_nodup heavy0_nodup
    rw [done, Finset.card_singleton] at h8
    exact absurd h8 (by decide)
  · have finish : ∀ {a b z : W} {needed : Finset W}, a ∈ heavy0.toFinset → b ∈ heavy0.toFinset →
        a ≠ b → z ∈ basicOps a b → z ∉ heavy0.toFinset →
        heavy0.toFinset = insert a (insert b needed) → live basicOps goal 9 (insert z needed) →
        canonPair a b = true → False := by
      intro a b z needed ha hb hab hz hout hs tail hc
      obtain ⟨t, ht, hab', hd⟩ :=
        first_dispatch 9 heavy0 1 heavy0_nodup (by decide) ha hb hab hz hout hs tail
      have hct : canonPair t.1 t.2.1 = true := by
        rcases hab' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact hc
        · rw [h1, h2, canonPair_comm]; exact hc
      rw [canon_false t ht hct] at hd
      exact Bool.noConfusion hd
    cases hc : canonPair a b
    · have hc' := canon_sigma a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb) hab hc
      have tail' := live_map tail
      rw [sigma_goal, Finset.image_insert] at tail'
      refine finish (a := sigma a) (b := sigma b) (z := sigma z) (needed := needed.image sigma)
        ?_ ?_ (sigma_inj.ne hab) (sigma_ops a b z hz) ?_ ?_ tail' hc'
      · rw [← heavy_image]; exact Finset.mem_image_of_mem _ ha
      · rw [← heavy_image]; exact Finset.mem_image_of_mem _ hb
      · rw [← heavy_image]
        intro hm
        obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hm
        exact hout (sigma_inj hyz ▸ hy)
      · rw [← heavy_image, hs, Finset.image_insert, Finset.image_insert]
    · exact finish ha hb hab hz hout hs tail hc

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem all_front : inputs.sublists.all
    (fun l => (l == heavy0) || decide (11 < l.length) || !(optimized 10 (11 - l.length) l)) = true := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 10 S := extend_live hs hl
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
  have hsearch := optimized_complete 10 l (11 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  by_cases e0 : l = heavy0
  · apply heavy_root
    rw [← e0, hlS]
    exact hl3
  have n0 : (l == heavy0) = false := by simpa using e0
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (11 < l.length) = false := by simp; omega
  rw [n0, h4, hsearch] at hrow
  exact Bool.noConfusion hrow

end PEqualNP.Outside.L_meta_9186_aux

theorem PEqualNP.Outside.L_meta_9186 : ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3195660 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_9186_aux.no_small C hm hs hr
