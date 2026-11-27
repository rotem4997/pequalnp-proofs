import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14668_aux

-- SPDX-License-Identifier: Apache-2.0
-- The finite search checker and circuit semantics adapt L_meta_8639
-- by tacyon52 in open-goat/pequalnp-proofs pull request 12794.
-- The sampled rows and search states below are for this eight-input graph.

-- Adapted from Sam Lentz's L-meta-1423 (PR 3033), Apache-2.0.
-- The live-wire compression argument follows the project proof of L-meta-703.
-- The live-wire reduction and circuit semantics follow the merged L-meta-1429.
-- Each finite search layer below is checked against the next layer of smaller states.
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

-- The upper and lower halves represent opposite target labels on 128 pairs of assignments.
abbrev W := BitVec 256
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : W) : List W → List W
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List W) := ws.foldr insertW []

theorem insertW_perm (v : W) (ws : List W) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

def children (k : ℕ) (ws : List W) : List (List W) := (pairs ws).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z =>
    (keepChoices a b r).filterMap fun kept =>
      if kept.length ≤ k ∧ cuts (z :: kept) = -1 then some (ordered (z :: kept)) else none

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BinaryTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BinaryTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BinaryTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey,Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next e =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BinaryTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 9 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closed_nil (tr : BinaryTree (List W)) (hc : everyKey (fun q => !doneTest q) tr = true) :
    Closed 0 tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  have eq := singleton_list hn h
  rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy

def rowOK (k : Nat) (tr : BinaryTree (List W)) (ws : List W) :=
  !doneTest ws && (children k ws).all (fun child => containsKey child tr)

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

theorem closed_next (k : Nat) (hk : k < 9) (tr next : BinaryTree (List W))
    (hnext : Closed k next) (hc : everyKey (rowOK k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  simp only [rowOK,Bool.and_eq_true,List.all_eq_true] at hy
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hp' := ordered_perm (z :: kept)
      have mem : ordered (z :: kept) ∈ children k ws := by
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
        exact List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ k by omega,cuts_full hg hraw]⟩
      have sz : (ordered (z :: kept)).length ≤ 9 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 9) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd := nd.filter (fun u => decide (u ∈ s))
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have size := live_card hl'
  rw [List.toFinset_card_of_nodup (show ws.Nodup from hnd)] at size
  have sub : ws.Sublist ins := List.filter_sublist ..
  have key := List.all_eq_true.mp hi ws (List.mem_sublists.mpr sub)
  have perm := ordered_perm ws
  apply hc g hg (ordered ws) (perm.nodup_iff.mpr hnd) (by rw [perm.length_eq]; exact sub.length_le.trans small) ?_
  · rwa [perm_set perm]
  · simpa [startOK,size,cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (_nd : ins.Nodup)
    (row : ∀ j : Fin 256, Nat.testBit T (∑ i : Fin 8, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 8) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 8, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 8) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection t ht (lift low run)


-- The sample contains 128 pairs of opposite graph values. A usable set of live
-- wires must distinguish every pair. Each checked layer lists its possible
-- successors under one more AND or OR, allowing complements at no cost.
def v0 : W := 0x0
def v1 : W := 0x11281040a44280820202001660030040012c1410a4028042000600162
def v2 : W := 0x20380080412a0a50c00200088000000000000000000000000000000000
def v3 : W := 0x1103a9084c83a48958008221824001001103a80c4c83248158008221004
def v4 : W := 0x11041940800114081018822242000000000000000000000000000000000
def v5 : W := 0x130691488413b42d1c18a022c800900213029068cc1324251918a063484
def v6 : W := 0x130699488413b42d1c18a222ca00900213029068cc1324251918a063484
def v7 : W := 0x130799488413b4ad1c18a222ca000000000000000000000000000000000
def v8 : W := 0x1307b948cc93b4ad5c18a223ca4091021303b86ccc9324a55918a263484
def v9 : W := 0xc001081000244280420006012200030040012c1410a4028042000600162
def v10 : W := 0x502008008034200220800410c09000000000000000000000000000000000
def v11 : W := 0x2000010090002440800002000000000000000000000000000000000000000
def v12 : W := 0x8010284a0100080210021880a040800000000000000000000000000000000
def v13 : W := 0x80112c5b4180091618121882a242800000000000000000000000000000000
def v14 : W := 0x801200822808080020007844e9008000801200802808080020007840e9008
def v15 : W := 0x87d40002080203102a4088054b2180008b940002080203102a0088014b209
def v16 : W := 0x87d60082080343102a4888454f2980008b940002080203102a0088014b209
def v17 : W := 0x10008110c3048800200036004410020010000010c100080000002000400002
def v18 : W := 0x1000ae006212018002001596040408000000a6000200018002001596040408
def v19 : W := 0x100120388284c9000200118a06140000100120388284c9000200118a061400
def v20 : W := 0x1021005094c041330ac51088243c20001021001284c049320a451088243400
def v21 : W := 0x1021207894c0413b0ad5d08a243ca0001021001284c049320a451088243400
def v22 : W := 0x1021307994c8413b4ad5d18a263ca0091021303b86ccc9324a55918a263484
def v23 : W := 0x18018384e2148880210037884e140a109801a7bcc384c9800200379e4e940a
def v24 : W := 0x489540002008009150a001800a220900009040002000000100a00000000201
def v25 : W := 0x48d12008208834b152a081841ae0990548b960082288b0b152a08f841fb289
def v26 : W := 0x48fd6008208834b152a489845ef2990548b960082288b0b152a08f841fb289
def v27 : W := 0x98038a14e1904100230030984494080098018214c18049000200309844940a
def v28 : W := 0x9803ae14e39241802300359e449408009801a614c38049800200359e44940a
def v29 : W := 0x98238a54f5d041332bc5309864bc280098218216c5c049320a45309864b40a
def v30 : W := 0x100212008028880314284818006308001002120080288803042008180063080
def v31 : W := 0x1007060002208348112000d8405208901003060002208308112000d84052089
def v32 : W := 0x108212008228880b1428487844eb0880108212008028880b0420087840eb088
def v33 : W := 0x220044000800000402000200020032000200400000000004020000000000120
def v34 : W := 0x23020c24064510001000018c0042408420430c24024102101024018d0042409
def v35 : W := 0x23220c000404100000000184004000000000000000000000000000000000000
def v36 : W := 0x2322cc010c1410244280438406412200030040012c1410a4028042000600162
def v37 : W := 0x26c8552c5b4380091f58121882a272942249440403030004121a00000800321
def v38 : W := 0x4000c010280048800200c22006013660030040012c1410a4028042000600162
def v39 : W := 0x4000c011281048a44280c22206013660030040012c1410a4028042000600162
def v40 : W := 0x4000d113a9184ca7e689da228621b66003005103ac1c5ca726815a008621166
def v41 : W := 0x4020c011289048a44280c22206013660030040012c1410a4028042000600162
def v42 : W := 0x440dc4000000034001020080011421104409840002000300110a00800110201
def v43 : W := 0x444801183002c8880d40803000a01471d400035a9020c9080d41887070b0084
def v44 : W := 0x4488d00080080803040a482005ad21004488900080080803040a082001a9200
def v45 : W := 0x4488d011a81848a7468aca2207ad37604788d001ac1c18a7068a4a2007a9362
def v46 : W := 0x448dc40002000348010200e0459c21904489840002000308110a00e04198209
def v47 : W := 0x448dd20080080b43042a482045ad29004488900080080803040a082001a9200
def v48 : W := 0x448dd20082088b4b152a483845af2990548b960082288b0b152a08f841fb289
def v49 : W := 0x448dd40080080b43050a48a005bd21104489940082080b03150a08a001b9201
def v50 : W := 0x448dd40082080b4b050a48e045bd21904489940082080b0b150a08e041b9209
def v51 : W := 0x448fd40002080343112a4088055f2190448b940002080303112a0088015b209
def v52 : W := 0x448fd4000208034b112a40e845df2190448b94000208030b112a00e841db209
def v53 : W := 0x5002c40000200800000040e0045120000000000000000000000000000000000
def v54 : W := 0x5002c411283048a44280c2e206513660030040012c1410a4028042000600162
def v55 : W := 0x5006820080280b42002048e0455d09005482920080288b0b052008f841fb088
def v56 : W := 0x5006c60080280b42002048e0455d29005482920080288b0b052008f841fb088
def v57 : W := 0x5007c60080280b42002248e0455d29000000000000000000000000000000000
def v58 : W := 0x5087d60082280b43102a48e8455f2980548b960082288b0b152a08f841fb289
def v59 : W := 0x54080200802089480500087040b4081054000200802089080500087040b0080
def v60 : W := 0x540fc40000008343150a488001162910540b840002008303150a08800112281
def v61 : W := 0x540fc40000200b40010240e0055521104409840002000300110a00800110201
def v62 : W := 0x540fc40000208b43150a48e005572910540b840002008303150a08800112281
def v63 : W := 0x540fc60080280b42012248e0455d2910548b960082288b0b152a08f841fb289
def v64 : W := 0x540fc60080288b43152a48e0455f2910548b960082288b0b152a08f841fb289
def v65 : W := 0x548ad40002208809150840f804f32090548b960082288b0b152a08f841fb289
def v66 : W := 0x548ed20080280b43042a48e045fd2900548a920080288b0b052a08f841fb288
def v67 : W := 0x548ed60082288b4b152848f845ff2990548b960082288b0b152a08f841fb289
def v68 : W := 0x548fc4000200834b150a48e0459e2990548b84000200830b150a08e0419a289
def v69 : W := 0x548fc40002200b48010240e045dd21904489840002000308110a00e04198209
def v70 : W := 0x548fc60082280b4a012248e045dd2990548b960082288b0b152a08f841fb289
def v71 : W := 0x548fd40002088343152a4888055f2990548b940002088303152a0888015b289
def v72 : W := 0x548fd40002208b49150a40f805f72190548b960082288b0b152a08f841fb289
def v73 : W := 0x548fd40002208b49150a40f845ff2190548b960082288b0b152a08f841fb289
def v74 : W := 0x548fd40002208b4b150a48f805f72990548b960082288b0b152a08f841fb289
def v75 : W := 0x548fd40080088b43150a48a005bf2910548b940082088b03150a08a001bb281
def v76 : W := 0x548fd60082288b4b152a48f845ff2990548b960082288b0b152a08f841fb289
def v77 : W := 0x548fd60382288f5bb5af4cf865ffa990548b960082288b0b152a08f841fb289
def v78 : W := 0x548fd611aa38cbef57aacafa47ff3ff0578bd601ae3c9baf17aa4af847fb3eb
def v79 : W := 0x548fd628ca298b4b173a4af8c5ff6990548b960082288b0b152a08f841fb289
def v80 : W := 0x548fd7049b688b4b152a58f8c7ff6b90548b960082288b0b152a08f841fb289
def v81 : W := 0x548fd70693688f5bb52f5cf8e5ffe990d48b97029268cf1b352f19f8e1fb68d
def v82 : W := 0x548fd72cdb698b4b173a5af8c7ff6b90548b960082288b0b152a08f841fb289
def v83 : W := 0x54afd60182b88b6f55aa48fa45ff2990548b960082288b0b152a08f841fb289
def v84 : W := 0x558fd6038a28cfdb152a49f8e5ff6990558b96038a28cf9b152a09f8e1fb689
def v85 : W := 0x558fdee08629ab5b152a49f965ff6990548b9e6082288b1b152a09f961fb689
def v86 : W := 0x6220c4000080102440008086101034000200400000001024020000000000160
def v87 : W := 0x6220cc1004901024420082e6141034200200400004101024020002000400162
def v88 : W := 0x6220df1695d89437f62d9efeb432fc20920253029478dc3726251b18a4635e6
def v89 : W := 0x778fde24866d9b4b152a49fc45ff699474cb9e2482698b1b152e09fd41fb689
def v90 : W := 0x77afde00862c9b4b152a49fc45ff2990548b960082288b0b152a08f841fb289
def v91 : W := 0x8100010739444490a0851500a200c240810001033844449020855100a200404
def v92 : W := 0x810011073944c491b48d1518a222c240810001033844449020855100a200404
def v93 : W := 0x81001307b94cc493b4ad1d18a222ca4091021303b86ccc9324a55918a263484
def v94 : W := 0x81021107394c4493b0ad5508a243c24081021103384c449320a55108a243404
def v95 : W := 0x90000302b020c88084010c1020200840900003029020c800040108102020084
def v96 : W := 0x9002010431448003b48d5c0002028a409002010030448003248558000202084
def v97 : W := 0x90020306b164c883b48d5c1022228a4090020302b064c803248558102222084
def v98 : W := 0x90020307b14c8413b4ad5c0022028a409002010030448003248558000202084
def v99 : W := 0x9002110439448003b48d5c188222ca409002010030448003248558000202084
def v100 : W := 0x90021107b94ccc83b48d5c0082238a4091021103b84ccc83248558008223084
def v101 : W := 0x90021304b16c8803b4ad5c1802638a4090021300b06c880324a558180263084
def v102 : W := 0x90021306b14c8413b4ad5c18a222ca4090021302b06ccc1324a55918a263484
def v103 : W := 0x910200012824488000804100024102400100000128040080008040000200000
def v104 : W := 0x910201053964c883b48d5d0002438a409102010138448083248558000202084
def v105 : W := 0x910201073944c493b48d5d00a202ca40910201033844c49324855900a202484
def v106 : W := 0x91020203a02c4c92a0a54d002041884091021303b86ccc9324a55918a263484
def v107 : W := 0x910202041064801010240518204248009002020010608010002401182042480
def v108 : W := 0x9102030431648013b4ad5d182242ca40900203003064801324a559182242484
def v109 : W := 0x91020307b16ccc93b4ad5d0022438a4091021303b86ccc9324a55918a263484
def v110 : W := 0x910208112c3448800280436006410260010000012c140080008042000600002
def v111 : W := 0x91020ae41665a018102405596042488090020a6010608018002401596042488
def v112 : W := 0x910211043964c881140851188263424091021303b86ccc9324a55918a263484
def v113 : W := 0x910211043964c883b48d5d188263ca4091021303b86ccc9324a55918a263484
def v114 : W := 0x91021105394c8413b4ad5d088243ca4091021101384c849324a559088243484
def v115 : W := 0x910211073964cc91b48d5518a263c24091021303b86ccc9324a55918a263484
def v116 : W := 0x91021207a96c4c93b0ad5d08a243ca4091021303b86ccc9324a55918a263484
def v117 : W := 0x91021306b96ccc93b42d5d18a263ca4091021303b86ccc9324a55918a263484
def v118 : W := 0x91021307b96ccc93b4ad5d18a263ca4091021303b86ccc9324a55918a263484
def v119 : W := 0x91021b17bd7ccc93b6ad5f78a663ca6091021303bc7ccc9324a55b18a663486
def v120 : W := 0x91021be7bf6dec9bb4ad5d59e263cac091021b63b86ccc9b24a55959e26348c
def v121 : W := 0x91071307b96ccfd3b4af5d18e36fcb4091021303b86ccc9324a55918a263484
def v122 : W := 0x91221307b9fcccb7f4ad5d1aa263ca4091021303b86ccc9324a55918a263484
def v123 : W := 0x91260ac004a43350002405c57050080290260ae010e0a358092425dd7052488
def v124 : W := 0x91821307bb6ccc9bb4ad5d78e6ebcac091821303b86ccc9b24a55978e2eb48c
def v125 : W := 0x9182132ffb6dcc9bb6bd5f18a2e3cac091021303b86ccc9324a55918a263484
def v126 : W := 0x9182193c7f65c8891618537886e342e199821b7bfc7ccc9b24a55b79e6eb48e
def v127 : W := 0x91821b3fff6dcc9bb6bd5f78a6e3cae199821b7bfc7ccc9b24a55b79e6eb48e
def v128 : W := 0x99823ba7ff7dcc93b6bd5f19a66bcac099821b23fc7ccc9324a55b19a66b48e
def v129 : W := 0x99823be7ff7dec9bb6bd5f59e66bcac099821b63fc7ccc9b24a55b59e66b48e
def v130 : W := 0xa32008000484100000000104100000000000000000000000000000000000000
def v131 : W := 0xa32008112c9450a44280830612001660030040012c1410a4028042000600162
def v132 : W := 0xa3400824144510000800010410004004a040086410410010080401053000400
def v133 : W := 0xa7ad1a11ae9cd3ef57aa8b1e53ae1ff0578bd601ae3c9baf17aa4af847fb3eb
def v134 : W := 0xb3020c0004241000000001c4105000000000000000000000000000000000000
def v135 : W := 0xb3220c0004a41000000001c4105000000000000000000000000000000000000
def v136 : W := 0xb3220c0104b41024408001c6105000000000000000000000000000000000000
def v137 : W := 0xb3220e0414e49010102405dc305248009002020010608010002401182042480
def v138 : W := 0xb3220ee006a53018002001dd7050408000000a6000200018002001596040408
def v139 : W := 0xb3220ee416e5b018102405dd7052488090020a6010608018002401596042488
def v140 : W := 0xb3221f07bdecdc93b4ad5ddcb273ca4091021303b86ccc9324a55918a263484
def v141 : W := 0xb3260ec004a43350002405c57050080290260ae010e0a358092425dd7052488
def v142 : W := 0xb3270e0006a49348112001dc505208901003060002208308112000d84052089
def v143 : W := 0xb3420c2416659008190001dc10524094b0430e6412618318192401dd7052489
def v144 : W := 0xb3420e2416659018192405dc30524894b0430e6412618318192401dd7052489
def v145 : W := 0xb3420ee41665b018192001dd70524094b0430e6412618318192401dd7052489
def v146 : W := 0xb3420ee41665b018192405dd70524894b0430e6412618318192401dd7052489
def v147 : W := 0xb3470e2416659348192001dc50524894b0430e6412618318192401dd7052489
def v148 : W := 0xb3620c2416e59008190001dc10524094b0430e6412618318192401dd7052489
def v149 : W := 0xb3660ee416e5b358192405dd70524896b0670ee412e1a358192425dd7052489
def v150 : W := 0xc58dc5073b4447d8a18715e0e79ce3d0c58985033a444798318f51e0e39860d
def v151 : W := 0xd000001020a0488000008062101014600000000000000000000000000000000
def v152 : W := 0xd000c01128b048a44280c26216113660030040012c1410a4028042000600162
def v153 : W := 0xd1021317b9eccc93b4addd7ab273de6091021303b86ccc9324a55918a263484
def v154 : W := 0xd102d707b96ccc93b4ad5df8a673ea4091021303b86ccc9324a55918a263484
def v155 : W := 0xd1069307b96ccfd3b4ad5df8e77fcb40d5829303b86ccf9b25a559f8e3fb48c
def v156 : W := 0xd122881124b458a04080c1e614510460010000012c1410a0008042000600042
def v157 : W := 0xd1229b17bdfcdcb3f4adddfeb673ce6091021303bc7cdcb324a55b18a6634c6
def v158 : W := 0xd44801183022c8880d40807010b01471d400035a9020c9080d41887070b0084
def v159 : W := 0xd448011830a2c8880d40807210b01471d400035a9020c9080d41887070b0084
def v160 : W := 0xd4480318b022c9c80d40887050b41c71d400035a9020c9080d41887070b0084
def v161 : W := 0xd448031ab022c8888d418c7030b01c71d400035a9020c9080d41887070b0084
def v162 : W := 0xd48fd610a2a8cbcb152ac8fa55ff3df0548b960082288b0b152a08f841fb289
def v163 : W := 0xd48fd702b228cbcb952b4cf865ff29d0d48b97029228cb0b152b08f861fb28d
def v164 : W := 0xd4cfd718b22acbcb1d6ac8f855ff3df1d48b975a9228cb0b1d6b88f871fb28d
def v165 : W := 0xd50a1307b96ccddbb5ad5d78e2f7ca50d5021303b86ccd9b25a55978e2f3484
def v166 : W := 0xd54a131fb96ecc9bbdeddd78b2f3de71d502135bb86ccd9b2de5d978f2f3484
def v167 : W := 0xd58fd604926c8b5b152e4df865ff6990d48b960092688b1b152e09f861fb689
def v168 : W := 0xd58fd707bb6ccfdbb5af5df8e7ffebd0d58b9703ba6ccf9b35af59f8e3fb68d
def v169 : W := 0xd58fdee4966dab5b152e4df965ff6990d48b9e6092688b1b152e09f961fb689
def v170 : W := 0xf222c400208410244080c086121036400200400020041024028040000200160
def v171 : W := 0xf302cc102c2458800200c3e416513660030040012c1410a4028042000600162
def v172 : W := 0xf3220c1024a45880000081e6105014600000000000000000000000000000000
def v173 : W := 0xf322cc0004a41800000041e4145120000000000000000000000000000000000
def v174 : W := 0xf322cc102ca458a44200c3e616513660030040012c1410a4028042000600162
def v175 : W := 0xf322cc102ca458a44280c3e616513660030040012c1410a4028042000600162
def v176 : W := 0xf322cc102cb458a44200c3e616513660030040012c1410a4028042000600162
def v177 : W := 0xf322cc1124b458a44080c1e614513460030040012c1410a4028042000600162
def v178 : W := 0xf322cc1124b458a44080c1e616513660030040012c1410a4028042000600162
def v179 : W := 0xf322cc1124b458a44280c3e614513460030040012c1410a4028042000600162
def v180 : W := 0xf322cc112cb458a04280c3e616513660030040012c1410a4028042000600162
def v181 : W := 0xf322cc112cb458a44280c3e616512660030040012c1410a4028042000600162
def v182 : W := 0xf322cc112cb458a44280c3e616513660030040012c1410a4028042000600162
def v183 : W := 0xf322ce13acbc5cb6e2a5cfe63651be60030040012c1410a4028042000600162
def v184 : W := 0xf322dd153df4d8a55688d3fe96737660030040012c1410a4028042000600162
def v185 : W := 0xf322df17bdfcdcb7f6addffeb673fe6093025303bc7cdcb726a55b18a6635e6
def v186 : W := 0xf327ce11acbc5be642a2cbe6575d3f60030040012c1410a4028042000600162
def v187 : W := 0xf3a2dc396eb558ac4290c3fe96f176e0030040012c1410a4028042000600162
def v188 : W := 0xf3a2dd3d7ff5d8ad5698d3fe96f376e0030040012c1410a4028042000600162
def v189 : W := 0xf74a0d183426d8880d4081f410f01471d400035a9020c9080d41887070b0084
def v190 : W := 0xf74a0d3c3667d8881d4081fc10f254f5f4430f7e9261cb181d6589fd70f248d
def v191 : W := 0xf76a0d1834a6d8880d4081f410f01471d400035a9020c9080d41887070b0084
def v192 : W := 0xf78fde00862c9b4b152a49fc55ff2990548b960082288b0b152a08f841fb289
def v193 : W := 0xf7afde0086ac9b4b152a49fc55ff2990548b960082288b0b152a08f841fb289
def v194 : W := 0xf7afde0186bc9b6f55aa49fe55ff2990548b960082288b0b152a08f841fb289
def v195 : W := 0xf7afde0496ec9b5b152e4dfc75ff6990d48b960092688b1b152e09f861fb689
def v196 : W := 0xf7afde10a6acdbcb152ac9fe55ff3df0548b960082288b0b152a08f841fb289
def v197 : W := 0xf7afde11aebcdbef57aacbfe57ff3ff0578bd601ae3c9baf17aa4af847fb3eb
def v198 : W := 0xf7afdee086adbb5b152a49fd75ff6990548b9e6082288b1b152a09f961fb689
def v199 : W := 0xf7afdee496edbb5b152e4dfd75ff6990d48b9e6092688b1b152e09f961fb689
def v200 : W := 0xf7cadc24166598091d0841fc14f36094f4cb9e6492698b1b1d2e09fd71fb689
def v201 : W := 0xf7cfde24966d9b4b1d2a49fc55ff6994f4cb9e6492698b1b1d2e09fd71fb689
def v202 : W := 0xf7cfde24966d9b5b1d2e4dfc75ff6994f4cb9e6492698b1b1d2e09fd71fb689
def v203 : W := 0xf7cfdee4966dbb5b1d2a49fd75ff6994f4cb9e6492698b1b1d2e09fd71fb689
def v204 : W := 0xf7cfdee4966dbb5b1d2e4dfd75ff6994f4cb9e6492698b1b1d2e09fd71fb689
def v205 : W := 0xf7cfdf3cb66fdbcb1d6ac9fc55ff7df5f4cb9f7e9269cb1b1d6f89fd71fb68d
def v206 : W := 0xf7efde2496ed9b4b1d2a49fc55ff6994f4cb9e6492698b1b1d2e09fd71fb689
def v207 : W := 0x10000025a802068880000007060a000210000025a802048080000007060a0000
def v208 : W := 0x1080022c38018241000200001600800000000000000000000000000000000000
def v209 : W := 0x1080022c380182412a0a50c01600888000000000000000000000000000000000
def v210 : W := 0x1082422c380982772e0a50c03610c890a0034208000802040c00024020004810
def v211 : W := 0x1088028f84611200802100261448800a1088008784410000800000261448800a
def v212 : W := 0x108802afac63168880210027164a800a108800a7ac43048080000027164a800a
def v213 : W := 0x108802afbc619241802300261648800a1088008784410000800000261448800a
def v214 : W := 0x10880301bc8184c800210022084a900210980101bcc184c800000022084a9002
def v215 : W := 0x10880311be9184c83a6995a2086a982610980111bec1c4c8324815a2086a9006
def v216 : W := 0x1088032eac209241800300019e0a8408108801a7ac0284c1800200179e0e9408
def v217 : W := 0x1088032eaca09241802300219e0a8408108801a7ac0284c1800200179e0e9408
def v218 : W := 0x1088032ebca19241802300219e0a840800000000000000000000000000000000
def v219 : W := 0x1088032fbca196c9802300239e4a940a109801a7bcc384c9800200379e4e940a
def v220 : W := 0x1088033eed349a41bb43d1c19e0aac88198821b7ad068cc1b24251979e0eb48c
def v221 : W := 0x1088033eedb49a41bb63d1e19e2aaca8198821b7ad068cc1b24251979e0eb48c
def v222 : W := 0x1088033efdb59a41bb6bd1e19e2aaca800000000000000000000000000000000
def v223 : W := 0x1088033fffb59ec9bb6bd5e39e6abcae199821b7bfc7ccc9b24a55b79e6eb48e
def v224 : W := 0x1088038f84e11200802100279c4a840a1088008784410000800000261448800a
def v225 : W := 0x1088038fbce196c8802100261c4a900a10980187bcc184c8800000261c4a900a
def v226 : W := 0x108803af8c63928080230027944e900a108801a78c43808080020027944e900a
def v227 : W := 0x108803afac619241802300279e4a840a108801a7ac4384c1800200379e4e940a
def v228 : W := 0x1090028fb4c11649002100301a00040210900087b4c10449000000301a400402
def v229 : W := 0x109002ad384386c90002001616449002109801a7bcc384c9800200379e4e940a
def v230 : W := 0x109002afb4e31649802300359e04040a109000a7b4c30449800200359e44040a
def v231 : W := 0x1098028f94e3168880210036144c900a1098008794c10008800000261448800a
def v232 : W := 0x1098028fb4e11649802100361e48840a10980087b4c10449800000361e48840a
def v233 : W := 0x109802af8463120180230037964c840a108800a78443000180020037964c840a
def v234 : W := 0x109802afbc6396c980230036164c900a109801a7bcc384c9800200379e4e940a
def v235 : W := 0x1098038f84e31688802100379c4e940a109801a7bcc384c9800200379e4e940a
def v236 : W := 0x1098038f94e19241802300369c4c940a1098018794c18049800200369c4c940a
def v237 : W := 0x1098038fb4e11649802100319a0a040a10900087b4c10449000000301a400402
def v238 : W := 0x1098038fb4e19649002300309a44940a10980187b4c18449000200309a44940a
def v239 : W := 0x1098038fb4e316c9802100379a4e140a109801a7bcc384c9800200379e4e940a
def v240 : W := 0x109803ae3ce19241002300309e4494080098018214c18049000200309844940a
def v241 : W := 0x109803aebce19241802300319e4e9408109801a7bcc384c9800200379e4e940a
def v242 : W := 0x109803af3ce396c9002300369e44940a109801a7bcc384c9800200379e4e940a
def v243 : W := 0x109803aface296c9802300379e4e940a109801a7bcc384c9800200379e4e940a
def v244 : W := 0x109803afbce19649802300319e0a840a109801a7bcc384c9800200379e4e940a
def v245 : W := 0x109803afbce396c9802300379e4e940a109801a7bcc384c9800200379e4e940a
def v246 : W := 0x109803afbce396c9aa2b50f79e4e9c8a109801a7bcc384c9800200379e4e940a
def v247 : W := 0x109803bfbef396c9ba6b95b79e6e9c2e109801b7bec3c4c9b24a15b79e6e940e
def v248 : W := 0x109803bffdf79ec9916381379e6eb42a109801a7bcc384c9800200379e4e940a
def v249 : W := 0x109803bffdf79ec9bb63d1f79e4ebc8a199821b7bdc78cc9b24251b79e4eb48e
def v250 : W := 0x109803bffdf79ec9bb63d1f79e6ebcaa199821b7bdc78cc9b24251b79e4eb48e
def v251 : W := 0x109803bffdf79ec9bb6bd1f79e6ebcaa109801a7bcc384c9800200379e4e940a
def v252 : W := 0x109803bffff79ec9bb6bd5f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v253 : W := 0x109823ae7cf5d2413b2bd5f09e64bca80098218216c5c049320a45309864b40a
def v254 : W := 0x109823affcf7d6c9b32bc5379e6ebc2a109821a7bec7c4c9b20a45379e6eb40a
def v255 : W := 0x109823affcf7d6c9bb2bd5f79e6ebcaa109821a7bec7c4c9b20a45379e6eb40a
def v256 : W := 0x109823befdf5da41bb6bd5f19e6ebca8199821b7bfc7ccc9b24a55b79e6eb48e
def v257 : W := 0x109823bffdf7dec9bb6bd5f79e6ebcaa199821b7bfc7ccc9b24a55b79e6eb48e
def v258 : W := 0x109853afbce396fda02320b79e5ed49a109801a7bcc384c9800200379e4e940a
def v259 : W := 0x109a03afbceb96cbc42b0037be4e940a109801a7bcc384c9800200379e4e940a
def v260 : W := 0x119823afbce39ec9b16384b79e4eb48a119821a7bcc38cc9b04200b79e4eb48a
def v261 : W := 0x12eec77efdbdba77bfffd1e1be3aefb9e227d648403832044d21a24020804b31
def v262 : W := 0x14880f01be8184ca44290c22286a936610b80501bec1c5ca40280422086a9162
def v263 : W := 0x14880f11be9184ca7e699da2286a9b6610b80511bec1c5ca726815a2086a9166
def v264 : W := 0x14d88fafbce396c9b063a4b79e5ed61a14d889a7bcc384c9b042a0b79e5e960a
def v265 : W := 0x1548fd65a8228ebcb152a48f865ff29b1548b965a8228cb0b152a08f861fb289
def v266 : W := 0x15982fefbce396c98023043f9e4f960a109801a7bcc384c9800200379e4e940a
def v267 : W := 0x15986bafbce396fda02304bf9e5fd49a15d829a7bcc38cf9b05200bf9e5fb48a
def v268 : W := 0x15c8ff6c38238af5b152a48f965ff2990548b960082288b0b152a08f841fb289
def v269 : W := 0x15c8ff6c38238af5bb5af4cf965ffa990548b960082288b0b152a08f841fb289
def v270 : W := 0x15c8ff6eac229af5b153a48f9e5ff69915c8b9e7ac228cf1b152a09f9e1fb689
def v271 : W := 0x15c8ff7eed369af5bb53f5cf9e5ffe991dc8b9f7ad268cf1b352f19f9e1fb68d
def v272 : W := 0x15d0fecfb4c11e7d3171a4b81a11669315d0b8c7b4e10c793150a0b81a512683
def v273 : W := 0x15d883afbce39edd807300b79e4fd48b15d801a7bcc38cd9805200b79e4f948a
def v274 : W := 0x15d8ffefbce39efdb173a4bf9e5ff69b15d8b9e7bce38cf9b152a0bf9e5fb68b
def v275 : W := 0x16aa0f7eed3c9b43ff43d9c9ff0bafc819a825b7ad068dc3f26251979e0eb5ec
def v276 : W := 0x1890029ff7d556490a2951701a200c2618900097b7c54449020855301a600406
def v277 : W := 0x1898039ff7f55e499b69d1719a2a2c2e18900097b7c54449020855301a600406
def v278 : W := 0x189803bffff5de49bb6bd1f19e2aacae199821b7bfc7ccc9b24a55b79e6eb48e
def v279 : W := 0x189803bffff7d6c98a2b51779e6e9c2e189801b7bfc7c4c9820a55379e6e940e
def v280 : W := 0x189803bffff7dec99b6bd1779e6ebc2e189801b7bfc7c4c9820a55379e6e940e
def v281 : W := 0x189803bffff7dec9bb6bd1f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v282 : W := 0x1898239ff7f5d6493b2bd5709a64bc2e18982197b7c5c449320a55309a64b40e
def v283 : W := 0x189823bffff7d6c9bb2bd5779e6ebc2e189821b7bfc7c4c9b20a55379e6eb40e
def v284 : W := 0x19000035ab020e88884010c7060a008619000035a9020c8080401087060a0084
def v285 : W := 0x19102135fb96cec9bb4ad5d78e2e3ca619102135bb86ccc9b24a55978e2e3484
def v286 : W := 0x1988229fc7755a00bb69d5e61468a8ae1988209787454800b24855a61468a08e
def v287 : W := 0x199022ad3a43c6c92a0a54d616449886199821b7bfc7ccc9b24a55b79e6eb48e
def v288 : W := 0x1990233c7b97cec93b4ad5d19e26bca4091021303b86ccc9324a55918a263484
def v289 : W := 0x199023bd7bd7cec93b4ad5d79e66bca6199821b7bfc7ccc9b24a55b79e6eb48e
def v290 : W := 0x199023bfffd7dec93b6bd5f19a263ca6199021b7bfc7ccc9324a55b19a663486
def v291 : W := 0x199023bffff7dec9bb6bd5f59e263cae199021b7bfc7ccc9b24a55b59e66348e
def v292 : W := 0x199803bfbfe39ec9886310f79e4e948e199801b7bdc38cc9804210b79e4e948e
def v293 : W := 0x19982331ff97ccc93b6bd5f38a6ebca619982131bfc7ccc9324a55b38a6eb486
def v294 : W := 0x1998233effb6dec9bb4bd5d19e2ebcac199821b7bf86ccc9b24a55979e2eb48c
def v295 : W := 0x1998233effb6dec9bb6bd5f19e2ebcac199821b7bf86ccc9b24a55979e2eb48c
def v296 : W := 0x1998233effb7dec9bb6bd5f19e2ebcac091021303b86ccc9324a55918a263484
def v297 : W := 0x1998233fffb7dec9bb6bd5f39e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v298 : W := 0x1998239ff7f75ec99b69d5779a6e3c2e199821b7bfc7ccc9b24a55b79e6eb48e
def v299 : W := 0x199823af7ef7d6c93b2bd5f69e64bcae199821b7bfc7ccc9b24a55b79e6eb48e
def v300 : W := 0x199823afbee3d6c9802b04379e6e942e109801a7bec3c4c9800a04379e6e940a
def v301 : W := 0x199823afbee3d6c9aa2b54f79e4e9c8e199821b7bfc7ccc9b24a55b79e6eb48e
def v302 : W := 0x199823affde7dec9812340779e4eb48a199821a7bdc78cc9800240379e4eb48a
def v303 : W := 0x199823affef7d6c9bb2bd5f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v304 : W := 0x199823be7ff7dec93b6bd5f19e66bcac099821b23fc7ccc9324a55b19a66b48e
def v305 : W := 0x199823befff7dec9bb6bd5f19e6ebcac199821b7bfc7ccc9b24a55b79e6eb48e
def v306 : W := 0x199823bf7ff7dec93b6bd5f79e66bcae199821b7bfc7ccc9b24a55b79e6eb48e
def v307 : W := 0x199823bfeff6dec9bb63d5f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v308 : W := 0x199823bffff6dec9bb6bd5f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v309 : W := 0x199823bffff7dec93b6bd5f19a66bcae199821b7bfc7ccc9324a55b19a66b48e
def v310 : W := 0x199823bffff7dec9916385379e6eb42e199821b7bfc7ccc9b24a55b79e6eb48e
def v311 : W := 0x199823bffff7dec99b6bd5779e6ebc2e199821b7bfc7ccc9b24a55b79e6eb48e
def v312 : W := 0x199823bffff7dec9bb63d5f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v313 : W := 0x199823bffff7dec9bb6bd5f19a2e3cae199021b7bfc7ccc9324a55b19a663486
def v314 : W := 0x199823bffff7dec9bb6bd5f19e2ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v315 : W := 0x199823bffff7dec9bb6bd5f79a6e3cae199821b7bfc7ccc9b24a55b79e6eb48e
def v316 : W := 0x199823bffff7dec9bb6bd5f79e6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v317 : W := 0x199873bffff7defdbb6bf5f79e7efcbe199821b7bfc7ccc9b24a55b79e6eb48e
def v318 : W := 0x199a23bfffffdecbff6bd5f7be6ebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v319 : W := 0x1bba23efbcebd7c98023003fdf4f940a109801a7bcc384c9800200379e4e940a
def v320 : W := 0x1bba23ffffffdfc9bb6bd5ffdf6fbcae199821b7bfc7ccc9b24a55b79e6eb48e
def v321 : W := 0x1cd0dedff7d5567d0a3971781a314e371cd098d7b7e544790318f5381a710607
def v322 : W := 0x1d0000252a0a069c080018c6270140c6bd400035a90a0e9488d418c7270b4084
def v323 : W := 0x1d448035ab022e8880d40807070b01471d400035a9020c9080d41887070b0084
def v324 : W := 0x1d448035ab022e8888d418c7070b01c71d400035a9020c9080d41887070b0084
def v325 : W := 0x1d448035ab0a2e9c88d418c7270b41c7bd400035a90a0e9488d418c7270b4084
def v326 : W := 0x1d48fd75ab228ebcb952b4cf865ff29f1d48b975a9228cb0b152b08f861fb28d
def v327 : W := 0x1d9803afbeeb96c980230837bf4f954e109801a7bcc384c9800200379e4e940a
def v328 : W := 0x1d9823bfffffdec9bb6bddf7bf6fbdee199821b7bfc7ccc9b24a55b79e6eb48e
def v329 : W := 0x1d982ffffff7dec9bb6bd5ff9e6fbeae199821b7bfc7ccc9b24a55b79e6eb48e
def v330 : W := 0x1d986bbffff7defdbb6bd5ff9e7ffcbe1dd829b7bfc7ccf9b25a55bf9e7fb48e
def v331 : W := 0x1d9a2bafbeebd7cb842b0c3fff4f944e109801a7bec3c5cb800a04379e6e944a
def v332 : W := 0x1d9a2bbfffffdfcbbf6bddffff6fbcee199821b7bfc7cdcbb24a55b79e6eb4ce
def v333 : W := 0x1dd8a3bffff7deddbb7bd5f79e6ffcaf1dd821b7bfc7ccd9b25a55b79e6fb48e
def v334 : W := 0x1dd8fffffff7defdbb7bf5ff9e7ffebf1dd8b9f7bfe7ccf9b35af5bf9e7fb68f
def v335 : W := 0x1ddc83bfbfe3bec980f708379f4f954f1dd801b7bdc38cd980d618b79f4f948e
def v336 : W := 0x1ddca3bffff7fec9bbffddf79f6fbdef1dd821b7bfc7ccd9b2de5db79f6fb48e
def v337 : W := 0x1faa2f6eae28d343c40b0c09ff2b876c10a805a7ae02c5c3c02a04179e2e9568
def v338 : W := 0x1fb22eed3acbc7cb442a0c3e776593660030040012c1410a4028042000600162
def v339 : W := 0x1fb22eed3acbc7cb6e2a5cfe77659be60030040012c1410a4028042000600162
def v340 : W := 0x1fba2fefbeebd7cbc42b0c3fff6f976e10b805a7bec3c5cbc02a04379e6e956a
def v341 : W := 0x1fba2fffffffdfcbff6bddffff6fbfee19b825b7bfc7cdcbf26a55b79e6eb5ee
def v342 : W := 0x29040024010a0a14809000450701008129000024010a0a148090004507010080
def v343 : W := 0x2b3420e6416e5b148190005dc70524896b0430e6412e1a358192405dd7052489
def v344 : W := 0x2b3620e4014a4b148090005d4705008129000024010a0a148090004507010080
def v345 : W := 0x2d448035830a2e9c80d40847070b01c73d400035a90a0e9480d418c7070b0084
def v346 : W := 0x4083520810018063660a62001090881000034208000000000400020000000810
def v347 : W := 0x4229154244b410005121a32088a0262842249440403030004121a00000800321
def v348 : W := 0x4232008a4044510100004210500004004206408a400410010000421050000400
def v349 : W := 0x423270ca4064512101024218d0042408420670ca4024102101024218d0042409
def v350 : W := 0x423270ee406653218102421dd6042408420670ee402610218102421dd6042409
def v351 : W := 0x423a7dca4064d1213102e618d054b618420ef9ca402490213102e218d014b609
def v352 : W := 0x423b3dc254f551025529a738c8e436284234944052f1710a4129a42000e00363
def v353 : W := 0x42b372ca5065d163670a6218d094ac18420772ca4024102105024218d0042c19
def v354 : W := 0x433270ea406659358112421dd4052489430670ea402618318112421dd4052489
def v355 : W := 0x477afdea4866d9b5b152e69fd45ff699474ef9ea482698b1b152e29fd41fb689
def v356 : W := 0x4b3270ca406e51210102421cd1052408420670ca4024102101024218d0042409
def v357 : W := 0x4b3270ea4166592101024259d20424884b0670ea4126182101024219d2042489
def v358 : W := 0x4b3270ee406e53350102425cd70524886b0670ee412e1a358192425dd7052489
def v359 : W := 0x4b3270ee41665b218102425dd60424884b0670ee412618218102421dd6042489
def v360 : W := 0x4b3670ca416659218192421dd10524094b0670ee412618318192421dd7052489
def v361 : W := 0x4dc7d2199303acebe6de6a07119b89571d43423da9020c9084d41a87070b0894
def v362 : W := 0x5083522c380982776e0a72c03690c890a0034208000802040c00024020004810
def v363 : W := 0x5f2915676ebe169c5921bbe6afa166eeff649475e93a3e94c9f5b8c7278b43a5
def v364 : W := 0x6002502c00080235000242401600008020024008000802040000024000000000
def v365 : W := 0x6004502e41241a3581924241960024896b0670ee412e1a358192425dd7052489
def v366 : W := 0x6224104241241800819002018000240942041040402010000100000000000001
def v367 : W := 0x6226504000080134009002084101000162065048402812340190024841010001
def v368 : W := 0x622650ce006813348090020c55010009620650ce402812348190024c55010009
def v369 : W := 0x622651de3af897fcbad8978c5d23182d621651de7aa8d6fcb3d817cc5d23100d
def v370 : W := 0x623270ee406c533501024258d6042488620670ca402c122501024258d0042409
def v371 : W := 0x623670ca406c513501924218d1052409620670ca402c123501924258d1052409
def v372 : W := 0x623670ca4164592181924219d0042409420670ca4024102101024218d0042409
def v373 : W := 0x623670ce406c53358192421cd5052409620670ce402c12358192425cd5052409
def v374 : W := 0x623670ee41645b3581924259d60424896b0670ee412e1a358192425dd7052489
def v375 : W := 0x64045c2f53a51ebfc5ba4e63b66037ef6b3674ee53ef5b3fc1ba467dd76525eb
def v376 : W := 0x676cfd62492698b4b1d2a68f845ff699474cb960482298b0b152a08f841fb289
def v377 : W := 0x6a36008e414c530100804250530004006a06408e410c12050080425053000400
def v378 : W := 0x6a3600ae416e530180824255d70404086a0640ae410e120580824255d7040408
def v379 : W := 0x6a3610ce416c5b0181904251d30024096a0650ce412c12050180425053000401
def v380 : W := 0x6a3650ae414c533500824250570004806a06408e410c12050080425053000400
def v381 : W := 0x6a3650ae416c5b3581924251d70024896b0670ee412e1a358192425dd7052489
def v382 : W := 0x6a3650ce414c533500904258530104016a0650ce412c12350190425853010401
def v383 : W := 0x6a3650ce416c53358090425c570104096a0650ce412c12358190425c57010409
def v384 : W := 0x6a3670ce416c532101824258d30424086a0670ce412c122501824258d3042409
def v385 : W := 0x6b267040410c493401904248410120816b067048412c1a340190424841012081
def v386 : W := 0x6b3270ec004a43350002425c5705008020024008000802040000024000000000
def v387 : W := 0x6b3430c2416659008190021dc10524094b0430e6412618318192401dd7052489
def v388 : W := 0x6b3470ee41665b358192425dd70524896b0670ee412e1a358192425dd7052489
def v389 : W := 0x6b3600ae414e5b1580904255570104816b0640ae410e1a158090425557010480
def v390 : W := 0x6b3620ae414e5b0101824251d30424806b0660ae410e1a0500824251d3042480
def v391 : W := 0x6b3620ae416e5b0181824255d70424886b0660ae410e1a0580824255d7042488
def v392 : W := 0x6b3620ce414e53010080425c530504006a06408e410c12050080425053000400
def v393 : W := 0x6b3620ce416e5b018190425dd30524096b0670ee412e1a358192425dd7052489
def v394 : W := 0x6b3630c2416e59008190021dc105240942041040402010000100000000000001
def v395 : W := 0x6b3660ae414e53350082425c570504806b0660ae410e1a358092425dd7052488
def v396 : W := 0x6b3670c0004a41340090021c4105000162065048402812340190024841010001
def v397 : W := 0x6b3670c0414e49340190425c410520816b067048412c1a340190424841012081
def v398 : W := 0x6b3670c2416e59348190021dc10524096b0670ee412e1a358192425dd7052489
def v399 : W := 0x6b3670c2416e59348190425dc10524896b0670ee412e1a358192425dd7052489
def v400 : W := 0x6b3670ca416c593501924258d10524896b0670ca412c1a3501924258d1052489
def v401 : W := 0x6b3670ce006a53348090021c55050009620650ce402812348190024c55010009
def v402 : W := 0x6b3670ce414c5b3501904258530124816b0670ce412c1a350190425853012481
def v403 : W := 0x6b3670ce416e5b348190021dd50524096b0670ee412e1a358192425dd7052489
def v404 : W := 0x6b3670ec004a43350092425c570500816b0670ee412e1a358192425dd7052489
def v405 : W := 0x6b3670ec414e4b350192425c570520816b0670ee412e1a358192425dd7052489
def v406 : W := 0x6b3670ee006a53358092425c570500896b0670ee412e1a358192425dd7052489
def v407 : W := 0x6b3670ee416e5b358192425dd70524896b0670ee412e1a358192425dd7052489
def v408 : W := 0x6b3670ee496edb35a19262ddd715e4996b0670ee412e1a358192425dd7052489
def v409 : W := 0x6b3670ee516f5b37c59a425df70524896b0670ee412e1a358192425dd7052489
def v410 : W := 0x6b3670ee796edb75ab9a52ddd7052c896b0670ee412e1a358192425dd7052489
def v411 : W := 0x6b3670fe6b6e5fbd89d252ddd707248d6b0670fe692e1eb581d252ddd707248d
def v412 : W := 0x6b3671ee496edbb5b1d2c6ddd70734896b0671ee492e9ab5b1d242ddd7073489
def v413 : W := 0x6b3671fe41fe5b3591d2c35ddf2724a96b0670ee412e1a358192425dd7052489
def v414 : W := 0x6b3671fe697edb75bbd2d3dddf072c896b0671fe692e9ef5b3d253dddf07348d
def v415 : W := 0x6b3671fe7bfedffdbbdad7dddf273cad6b1671fe7baedefdb3da57dddf27348d
def v416 : W := 0x6b3e71ee496edbb58192425fd74fb4896b0e71ee492e9ab58192425fd70fb489
def v417 : W := 0x6b3e71ee496edbb5b1d2c6dfd74fb4896b0e71ee492e9ab5b1d242dfd70fb489
def v418 : W := 0x6b3e71eec5ee5b3581b3427ddf0f24896b0670ee412e1a358192425dd7052489
def v419 : W := 0x6b3e71fec5fe5b3591f3c37ddf2f24a96b0670ee412e1a358192425dd7052489
def v420 : W := 0x6b3e7dee416edb35b192e65dd755b6996b0ef9ee412e9a35b192e25dd715b689
def v421 : W := 0x6b7ef1ee496edb35b1d2e2ddd71fe4996f4ef9ee492e9ab5b1d2e2dfd71fb689
def v422 : W := 0x6b7ef5ee416e5b3591d2e25dd70f26896b06f0ee412e1a358192e25dd7052689
def v423 : W := 0x6bb772ee516fdb77e79a625dd795ac996b0772ee412e1a358592425dd7052c99
def v424 : W := 0x6e7e8d8e494cd38130c0e6d2535ad6106e4ec98e490c928530c0e2d2531a9600
def v425 : W := 0x6f3670ef436e5fbd81924a5ff70525cf6b0670ee412e1a358192425dd7052489
def v426 : W := 0x6f3678ee496edbb5a19246dfd755f4996f4e79ee492e9ab5b1d242dfd71fb489
def v427 : W := 0x6f367cee416e5bb58192465fd74536896b0670ee412e1a358192425dd7052489
def v428 : W := 0x6f367cef53ef5fbfc5ba4e7ff76537ef6b3674ee53ef5b3fc1ba467dd76525eb
def v429 : W := 0x6f76f0ee496e5bb581d242dfd70f64896f4670ee492e1ab581d242dfd70f2489
def v430 : W := 0x6f76f0ffc36e7fbd81d64a5fd70f25cf7f4670ffe92e1eb581d65adfd70f248d
def v431 : W := 0x6f76fcee416e5b358192625dd71566996f46f8ee412e1a358192e25dd7152689
def v432 : W := 0x6f76fcee416e5b35b1d2e6ddd71566996f46f8ee412e1a35b1d2e2ddd7152689
def v433 : W := 0x6f7cfde24966d9b4b1d2a69fc55ff6994f4cb9e6492698b1b1d2e09fd71fb689
def v434 : W := 0x6f7efcee416e5b358192625fd75de6996f4ef8ee412e1a358192e25fd71da689
def v435 : W := 0x6f7efde2496ed9b4b1d2a69fc55ff699474cb960482298b0b152a08f841fb289
def v436 : W := 0x6f7efdee416e5bb591d2c65fd74f36896f4ef9ee492e9ab5b1d2e2dfd71fb689
def v437 : W := 0x6f7efdee496edbb5b1d2e6dfd75ff6996f4ef9ee492e9ab5b1d2e2dfd71fb689
def v438 : W := 0x72ae5351be9985fc3af997aa496b9827729e5159fee9d6fc33d817ea496b9007
def v439 : W := 0x7b3670efe96e5fbd8192425fd70f248b7b0670efe92e1eb58192425fd70f2489
def v440 : W := 0x7b3670ffeb6e5fbd89d252dfd70f248f7b0670ffe92e1eb581d252dfd70f248d
def v441 : W := 0x7bae7341fd8dcdfc01b1426a494bb0837b9e7149fded9efc0190426a494bb083
def v442 : W := 0x7bb672ee796fdb758192425dd705a4896b0670ee412e1a358192425dd7052489
def v443 : W := 0x7bb672ee796fdb75ab9a52ddd705ac896b0670ee412e1a358192425dd7052489
def v444 : W := 0x7bb672ee796fdb77af9a52ddf715ec99eb0772ee412e1a358d92425df7056c99
def v445 : W := 0x7bbe73eeed6edb758193425ddf0fa4897b8e71efed2e9ef58192425fdf0fb489
def v446 : W := 0x7bbe73effdefdffd81b3427fdf4fb48b7b9e71effdef9efd8192427fdf4fb48b
def v447 : W := 0x7bbe73feed7edb75bbd3d3dddf0fac897b8e71ffed2e9ef5b3d253dfdf0fb48d
def v448 : W := 0x7bbe73ffffffdffdbbfbd7ffdf6fbcaf7b9e71ffffefdefdb3da57ffdf6fb48f
def v449 : W := 0x7f3670ef6b6e5fbd89925adff70564cfff4670ffe92e1eb589d65adff70f648d
def v450 : W := 0x80498510849020005065a12008aa032000208400001020004021a00000800320
def v451 : W := 0x84498d119691248a546dad2228ea13660030840012d1610a4029a42000e00362
def v452 : W := 0x895be5bc84da63355067e17c5faf03a02922e4ae011e2a35c0b3e25dd78527a8
def v453 : W := 0x90810200380180426e0830802090c81080010200000000000c00000020004810
def v454 : W := 0x94408011aa00248808441882200a414694400011a800048008441882200a4004
def v455 : W := 0x94408c11ba81248a4c6c1ca2206a536694700411bac1458a486c1ca2206a4166
def v456 : W := 0x94810e013a8184ca6e283ca220f0db768031060012c1410a4c28042020604972
def v457 : W := 0x94d883bfbee3b6c9886718b7be4ed54e94d801b7bcc384c9884618b7be4ed40e
def v458 : W := 0x9bb522c27967d942ef98309de195ec19cb0532e6412618318d92401df7056c99
def v459 : W := 0x9d448011ab022c8888d41887210b41479d400035a9020c9088d41887270b4084
def v460 : W := 0xa04480108100280080d40001000a010100000000000000000000000000000000
def v461 : W := 0xa4448000000820140094080021014141a4400000000802140894084021014000
def v462 : W := 0xa4dca38a54fdf05533bfcd30b965fd69a4d8218216cdc25d3a9e4d70b965f40a
def v463 : W := 0xa54cfd708922a8b4b1d6a48f845ff3990548b960082288b0b152a08f841fb289
def v464 : W := 0xa954a130fb96ecc9bbded5d18a2e3da5091021303b86ccc9324a55918a263484
def v465 : W := 0xad448001020a249c0094080621014147a4400000000802140894084021014000
def v466 : W := 0xad4480100308281408d418c0210141c5ad40001001080a1408d418c021014084
def v467 : W := 0xad448011030a2c9c08d418c6210141c7ad40001001080a1408d418c021014084
def v468 : W := 0xad44801183022c8880d40807010b01471d400035a9020c9080d41887070b0084
def v469 : W := 0xad448011830a2c8880d40807210b014700000000000000000000000000000000
def v470 : W := 0xad448011830a2c9c80d40807210b4147bd400035a90a0e9488d418c7270b4084
def v471 : W := 0xad448011830a2c9c88d418c7210b41c7bd400035a90a0e9488d418c7270b4084
def v472 : W := 0xaddc839a17e9b85508f718f0b945d5cdadd8019215c98a5d08d618f0b945d48e
def v473 : W := 0xaf76acd193cb6d8ac4fc0c3f616f13670030040012c1410a4028042000600162
def v474 : W := 0xb000002428080214080010c026004080a0000000000802040800004020004000
def v475 : W := 0xb0448034a9002a1488d410c1060a4081bd400035a90a0e9488d418c7270b4084
def v476 : W := 0xb0dc83bfbde3bec980f700379e4e950b109801a7bcc384c9800200379e4e940a
def v477 : W := 0xb276acf4b9c16b16ccfc14f9466e52a1bd700435bbcb4f9ec8fc1ce7276b41e6
def v478 : W := 0xb4448005800822148094080625094143b4400005800802148894084625094000
def v479 : W := 0xb4448011aa08249c08d41882210b4147b4400011a808069408d418c2210b4004
def v480 : W := 0xb4448011ab002c8888d41883200a414794400011a800048008441882200a4004
def v481 : W := 0xb4448015aa08269c88d41886250b4147b4400015a808069488d418c6250b4004
def v482 : W := 0xb4448035ab002e9c88d418c3260a41c7bd400035a90a0e9488d418c7270b4084
def v483 : W := 0xb454a105d09ce255b39ecd16ad2d7d63b4502105928cc25dba9e4d56ad2d7400
def v484 : W := 0xb8040015a30826080884184023000146b8000015a10806040884184023004004
def v485 : W := 0xb80c7d55a328a6283986bc48a354b35eb808b955a12886243986b848a314f20d
def v486 : W := 0xb8448015a3082e0888d41841230a0147b8000015a10806040884184023004004
def v487 : W := 0xb8448035ab082e1c88d418c1270a41c7bd400035a90a0e9488d418c7270b4084
def v488 : W := 0xb9dca3bffff7fec9bbffd5f79e6ebdaf199821b7bfc7ccc9b24a55b79e6eb48e
def v489 : W := 0xbc448015a308261c0894184023014147bc400015a10806140894184023014004
def v490 : W := 0xbc448015a308261c8894184627094147bc400015a10806148894184627094004
def v491 : W := 0xbd448005820a269c8094080625094147b4400005800802148894084625094000
def v492 : W := 0xbd448011ab082c9c08d418c2210b41c7bd400011a9080e9408d418c2210b4084
def v493 : W := 0xbd448015830a2e9c80d40807250b4147bd400035a90a0e9488d418c7270b4084
def v494 : W := 0xbd448015a3082e1c08d418c0230141c7bd400015a1080e1408d418c023014084
def v495 : W := 0xbd448015a30a2e8888d41847230b0147bd400035a90a0e9488d418c7270b4084
def v496 : W := 0xbd4480252a0a269c089418c6270141c7bd400035a90a0e9488d418c7270b4084
def v497 : W := 0xbd448025aa0a269c889418c6270941c7bd400035a90a0e9488d418c7270b4084
def v498 : W := 0xbd4480352b0a2e9c08d418c6270141c7bd400035a90a0e9488d418c7270b4084
def v499 : W := 0xbd448035ab022e9c88d418c7070b41c7bd400035a90a0e9488d418c7270b4084
def v500 : W := 0xbd448035ab0a2e9c88d418c7270b41c7bd400035a90a0e9488d418c7270b4084
def v501 : W := 0xbd448035bb0aaeddaade58c7270b49c7bd400035a90a0e9488d418c7270b4084
def v502 : W := 0xbd448135eb1eaeddbbd6d9c7af0b6dc7bd402135a90e8ed5bad659d7af0f7484
def v503 : W := 0xbd448135eb9e2e9c99d499c7af2b65e7bd400035a90a0e9488d418c7270b4084
def v504 : W := 0xbd448c35bb8b2e9eccfc1ce7276b53e7bd700435bbcb4f9ec8fc1ce7276b41e6
def v505 : W := 0xbd44a135ab0aae9cb9d69cc7a70f71c7bd402135a90a8e94b8d618c7a70f7084
def v506 : W := 0xbd44ac75ab0a2e9c88d41ccf274f53c7bd400035a90a0e9488d418c7270b4084
def v507 : W := 0xbd44d035ab0aaebca8d638c7271bc1d7bd400035a90a0e9488d418c7270b4084
def v508 : W := 0xbd44e835ab0aaebca8d61ccf275fd1d7bd482935a90a8eb4b8d618cfa71ff08c
def v509 : W := 0xbd468035bb0b2e9eccdc18c7270b41c7bd400035a90a0e9488d418c7270b4084
def v510 : W := 0xbd4c8135ab2aae9c88d618c7a74fd1cfbd480135a90a8e9488d618c7a70fd08c
def v511 : W := 0xbd4c8137afaa3e9c88f518e7af0b45cfbd400035a90a0e9488d418c7270b4084
def v512 : W := 0xbd4c8137efbe3e9c99f599e7af2b65efbd400035a90a0e9488d418c7270b4084
def v513 : W := 0xbd4ca135ab2aae9cb9d69cc7a74ff1cfbd482135a90a8e94b8d618c7a70ff08c
def v514 : W := 0xbd4cfd75ab2aaebcb9d6bccfa75ff3dfbd48b975a92a8eb4b9d6b8cfa71ff28d
def v515 : W := 0xbd5480bfab6a3e9d88d618d7b70f45cfbd4000b7a90a0e9588d618d7b70f448c
def v516 : W := 0xbd54a035eb0e6e9d89d658d7a70f65c7bd402035a90e0e9588d658d7a70f6484
def v517 : W := 0xbd54a0bfeb6e7e9d89d658d7b70f65cfbd4020b7a90e0e9588d658d7b70f648c
def v518 : W := 0xbd54a135fb9eeeddbbdeddd7af2f7de7bd502135bb8eceddbade5dd7af2f7484
def v519 : W := 0xbd56e0bdab4a6fbd88d658df770f41c7bd4260bfa90e0eb588d65adff70f648c
def v520 : W := 0xbdc4823dbb0baedd88d618c7370bc1c7bd400035a90a0e9488d418c7270b4084
def v521 : W := 0xbdc4823dbb0baeddaade58c7370bc9c7bd400035a90a0e9488d418c7270b4084
def v522 : W := 0xbdc58235bb0baedeeedc38c7279bc9d7bd410235a90a0e948cd418c7270b4894
def v523 : W := 0xbdc6c23dbb0baeffaede58c7371bc9d7bd43423da90a0e948cd41ac7270b4894
def v524 : W := 0xbdcc833faf2abedd88d718c7bf0bc5cfbdc801b7ad0a8ed588d618d7bf0fd48c
def v525 : W := 0xbdcc833fef3ebeddbbd7d9c7bf0bedcfbdc821b7ad0e8ed5bad659d7bf0ff48c
def v526 : W := 0xbddc83bfbfebbedd88f718f7bf4fd5cfbdd801b7bdcb8edd88d618f7bf4fd48e
def v527 : W := 0xbddca3bffffffeddbbffddf7bf6ffdefbdd821b7bfcfceddbade5df7bf6ff48e
def v528 : W := 0xbf74a0f5ab4a6f9c88d418df670f41c7bd400035a90a0e9488d418c7270b4084
def v529 : W := 0xbf74a0f7eb6e7f9c89d418dfe70f65cfff4430f7e92e1eb589d658dff70f648d
def v530 : W := 0xbf7680b5ab4a6f9c88d418d7670b41c7bd400035a90a0e9488d418c7270b4084
def v531 : W := 0xbf76a0f5ab4a6f9c88d418df670f41c7bd400035a90a0e9488d418c7270b4084
def v532 : W := 0xbf76a0f5bb4b6f9eccdc18df670f41c7bd400035a90a0e9488d418c7270b4084
def v533 : W := 0xbf76a0f5eb4e6f9d89d658dfe70f65c7bd402035a90e0e9588d658d7a70f6484
def v534 : W := 0xbf76a0ffab6a7f9d88d618dff70f45cfbd4000b7a90a0e9588d618d7b70f448c
def v535 : W := 0xbf76a0ffeb6e7f9d89d658dff70f65cfbd4020b7a90e0e9588d658d7b70f648c
def v536 : W := 0xbf76acf5ab4a6f9c88d41cdf674f53c7bd400035a90a0e9488d418c7270b4084
def v537 : W := 0xbf76acf5bbcb6f9eccfc1cff676f53e7bd700435bbcb4f9ec8fc1ce7276b41e6
def v538 : W := 0xbf76e0fdab4a6fbd88d658df770f41c7bd4260bfa90e0eb588d65adff70f648c
def v539 : W := 0xd672f0dbea6475a909465a9af00e654ed64670dbe82414a109465a9af00e640d
def v540 : W := 0xe001100000000000400022000080000000000000000000000000000000000000
def v541 : W := 0xe0035000000800364400220020904010a0034208000802040c00024020004810
def v542 : W := 0xe0035000000800366e0872c020904890a0034208000802040c00024020004810
def v543 : W := 0xe01b518384ea14beee2972f7a8de5c9ab09b43afbccb86cd8c020277be4edc1a
def v544 : W := 0xe04d9112c534380091d5a301888a240942049040403030000101a00000800201
def v545 : W := 0xe04d9112c5b4380091f5a32188aa242942049040403030000101a00000800201
def v546 : W := 0xe04d9512c5b43800d1f5a32188aa272942249440403030004121a00000800321
def v547 : W := 0xe2250012c594300040a5032008a0052042240400401030004021000000800120
def v548 : W := 0xe265944000002000409422000080030142249440403030004121a00000800321
def v549 : W := 0xe26594504114280051d4a30000a0232142249440403030004121a00000800321
def v550 : W := 0xe267d440000820364494220020904311e227d648403832044d21a24020804b31
def v551 : W := 0xe267d450411c28367fdcf3c020b06bb1e227d648403832044d21a24020804b31
def v552 : W := 0xe26d8552c5b43800d1f5832188aa272942249440403030004121a00000800321
def v553 : W := 0xe26d9112c5b43800d1f5a32188aa252942249440403030004121a00000800321
def v554 : W := 0xe26d944284203000c0b522200088030942249440403030004121a00000800321
def v555 : W := 0xe26d9552c5b4380091f5a32188aa272942249440403030004121a00000800321
def v556 : W := 0xe26d9552c5b43800d1f5a32188aa262942249440403030004121a00000800321
def v557 : W := 0xe26d9552c5b43800d1f5a32188aa272942249440403030004121a00000800321
def v558 : W := 0xe26d9572fdb4b841fbfff3e18aaa2fa942249440403030004121a00000800321
def v559 : W := 0xe26dd572cdb4b834f1f7a3a18cbae7b942249440403030004121a00000800321
def v560 : W := 0xe26f9552d5bd3802d5fda321a8aa272942249440403030004121a00000800321
def v561 : W := 0xe549fd60082288b4f152a68f84dff2990548b960082288b0b152a08f841fb289
def v562 : W := 0xe54dfd72cd36b8b4b1d7a78f8cdff699474cb9604832b8b0b153a08f849fb289
def v563 : W := 0xe66f9d52c5bc3902d5f5ab29e9ab276942249440403031024121a00000800361
def v564 : W := 0xe7256832cd96b0b460a707ae0cf5d5b0476c2d204812b8b0f073008f849fb1a8
def v565 : W := 0xe76dbd52c5b63880d1f5a72f88ef372942249440403030004121a00000800321
def v566 : W := 0xe76dfd72cdb6b8b4f1f7a7af8cfff7b9476cbd604832b8b0f173a08f849fb3a9
def v567 : W := 0xe91131307b96ccc97b4af7d18aa63ca4091021303b86ccc9324a55918a263484
def v568 : W := 0xe91b7193c7fe5cbed561a737a8fe743eb99b63bfbfcfcecdbe4a57f7be6efc9e
def v569 : W := 0xeb3770ee416e5b35c192625dd78524896b0670ee412e1a358192425dd7052489
def v570 : W := 0xeb3770ee416e5b37c592625df7956499eb0772ee412e1a358d92425df7056c99
def v571 : W := 0xeb3770ee416e5b37ef9a72ddf7956c99eb0772ee412e1a358d92425df7056c99
def v572 : W := 0xeb76f0fec16e7b3581d6425dd70f25896b0670ee412e1a358192425dd7052489
def v573 : W := 0xeb7db462be22f4c9eabf76f0028c1b8d4b34b5707bb6fcc9736bf5918aa637a5
def v574 : W := 0xeb7db572ffb6fcc9fbfff7f18aae3fad4b34b5707bb6fcc9736bf5918aa637a5
def v575 : W := 0xeb7fb5d2c5fe7900d1f5a33dc9af272942249440403030004121a00000800321
def v576 : W := 0xeb7ff1fec57e7b3591d7e35ddf8f24896b06f0ee413e3a358193e25dd7852689
def v577 : W := 0xeb7ff5fec5fe7b35d1f7e37ddfaf27a96b26f4ee413e3a35c1b3e25dd78527a9
def v578 : W := 0xed5fb993d77f7d8a95ddaf1fe9cf344f4214904052f1710a0109a42000e00243
def v579 : W := 0xef333cc112cb458a44282e3e61e513660030040012c1410a4028042000600162
def v580 : W := 0xef6d9553c7be3c88d1f5ab27a9ab276f42249440403030004121a00000800321
def v581 : W := 0xef76f0ee416e7b3581964a5df70565c9ef4670ee412e1a3589964a5df7056489
def v582 : W := 0xef76f0fe436e7b3589d65addf70565cdef4670fe412e1a3589d65addf705648d
def v583 : W := 0xef7fbdd3d7ff7d8ad5fdaf3fe9ef376f4234944052f1710a4129a42000e00363
def v584 : W := 0xf081522c280082752a0272c01690c890a0034208000802040c00024020004810
def v585 : W := 0xf081522c380182776e0a72c03690c890a0034208000802040c00024020004810
def v586 : W := 0xf083020c300902434e08524032800800a0034208000802040c00024020004810
def v587 : W := 0xf083020d3289064b4e285a6032a00966a033460812c9430e4c28066020604972
def v588 : W := 0xf083520c00090236440022003490c010a0034208000802040c00024020004810
def v589 : W := 0xf083522c380182776e0a72c01690c890a0034208000802040c00024020004810
def v590 : W := 0xf083522c380982776e0a72c03690c890a0034208000802040c00024020004810
def v591 : W := 0xf083533c799d8a777f4af3c1beb2ecb0a0034208000802040c00024020004810
def v592 : W := 0xf08b532ebca99277ee2b72e1be9acc98a0034208000802040c00024020004810
def v593 : W := 0xf08b533efdbd9a77ff6bf3e1bebaecb8a0034208000802040c00024020004810
def v594 : W := 0xf09913afbce396c9c02322379ece940a109801a7bcc384c9800200379e4e940a
def v595 : W := 0xf09b53afbceb96ffee2b72f7bededc9ab09b43afbccb86cd8c020277be4edc1a
def v596 : W := 0xf0c7d23cb909aa77eede72c1369ac991a0034208000802040c00024020004810
def v597 : W := 0xf2b372ec3849c3776e0a72d87694c890a0034208000802040c00024020004810
def v598 : W := 0xf2b372ee786dd3776f0a72d8f694ec98e20772ca402c12250d024258f0046c19
def v599 : W := 0xf2ed977efdb5ba41d1f7a3219eaaa72942249440403030004121a00000800321
def v600 : W := 0xf2ed977efdb5ba41fbfff3e19eaaafa942249440403030004121a00000800321
def v601 : W := 0xf2efd64e84293236c4b522203498c319e227d648403832044d21a24020804b31
def v602 : W := 0xf2efd77efdbdba77fffff3e1bebaefb9e227d648403832044d21a24020804b31
def v603 : W := 0xf2f596fd7957aec951d6a31616e4b32352bc95e7fcf3b4c9c123a0379ece972b
def v604 : W := 0xf2fd97fffdf7bec9d1f7a3379eeeb72b52bc95e7fcf3b4c9c123a0379ece972b
def v605 : W := 0xf4835e2d3a8986ff6e2a7ee236f0dbf6a033460812c9430e4c28066020604972
def v606 : W := 0xf5837e6c380b82f76e0a76ce36d5da90a0034208000802040c00024020004810
def v607 : W := 0xf5cbaf4c302b0ac3df58d64fb2cf3a09a54bfb68082a8ab4bd52a2cfa41ffa99
def v608 : W := 0xf5cbff6c382b8af7ff5af6cfb6dffa99a54bfb68082a8ab4bd52a2cfa41ffa99
def v609 : W := 0xf993731c439f4ebe5540a711bcb6f434a91363383b8ececd3e4a57d1aa267c94
def v610 : W := 0xf993733c7b9fceff7f4af7d1beb6fcb4a91363383b8ececd3e4a57d1aa267c94
def v611 : W := 0xf99933bffff7dec9fb6bf7f79eeebcae199821b7bfc7ccc9b24a55b79e6eb48e
def v612 : W := 0xf99b73bfffffdeffff6bf7f7befefcbeb99b63bfbfcfcecdbe4a57f7be6efc9e
def v613 : W := 0xfa36009fe34c770908845a5073000546fa06409fe10c160508845a5073004404
def v614 : W := 0xfab3028d32c9474b4e285a7073a00966a033460812c9430e4c28066020604972
def v615 : W := 0xfab352ac3849c3776e0a72d07790c890a0034208000802040c00024020004810
def v616 : W := 0xfab7028e714d53434e88525073800c00ea07428e410c12050c80425073004c10
def v617 : W := 0xfab752ae794dd3776e8a72d07790cc90ea07428e410c12050c80425073004c10
def v618 : W := 0xfb3670ee696e5b35899252ddf7056489eb0670ee412e1a358992425df7056489
def v619 : W := 0xfb3670ffe36e7f3d89965a5df70525cffb0670ffe12e1e3589965a5df705648d
def v620 : W := 0xfb76f0fee96e7b3589d652ddd70f6489ff4670ffe92e1eb589d65adff70f648d
def v621 : W := 0xfbb372ec384bc3776e0a72dc7795c890a0034208000802040c00024020004810
def v622 : W := 0xfbb772ee416f5b37c592625df795e499eb0772ee412e1a358d92425df7056c99
def v623 : W := 0xfbb772ee696edb75ab9272ddd795ec99eb0772ee412e1a358d92425df7056c99
def v624 : W := 0xfbb772ee716f5b77cf9a525df7852c89eb0772ee412e1a358d92425df7056c99
def v625 : W := 0xfbb772ee796fdb77ef9a72ddf795ec99eb0772ee412e1a358d92425df7056c99
def v626 : W := 0xfbf5b6ed3a43e6c96a9e76d616c49b875bbcb5f7fff7fcc9f36bf5b79eeeb7af
def v627 : W := 0xfbfdb7fffff7fec9fbfff7f79eeebfaf5bbcb5f7fff7fcc9f36bf5b79eeeb7af
def v628 : W := 0xfd459035ab0a2e9cc8d43ac7278b41c7bd400035a90a0e9488d418c7270b4084
def v629 : W := 0xfd46d03dab0a2ebd88d65ac7370b41c7bd42403da90a0e9488d41ac7270b4084
def v630 : W := 0xfd47d035ab0a2ebeccd43ac7279b41d7bd43423da90a0e948cd41ac7270b4894
def v631 : W := 0xfd47d035ab0a2ebeeedc7ac7279b49d7bd43423da90a0e948cd41ac7270b4894
def v632 : W := 0xfd83522d3a0b86ff6e0a7ac63791c9d6a0034208000802040c00024020004810
def v633 : W := 0xfdc5d23dab0aaefdaad67ac7379bc9d7bd43423da90a0e948cd41ac7270b4894
def v634 : W := 0xfdc7823dbb0b2edfcedc5ac7378b49c7bd43423da90a0e948cd41ac7270b4894
def v635 : W := 0xfdc7d23dab0b2ebeccd43ac7379bc1d7bd43423da90a0e948cd41ac7270b4894
def v636 : W := 0xfdc7d23dbb0baeffeede7ac7379bc9d7a0034208000802040c00024020004810
def v637 : W := 0xfdc7d23dbb0baeffeede7ac7379bc9d7bd43423da90a0e948cd41ac7270b4894
def v638 : W := 0xff6d9577efbe3e9cd9f5bbe7afab67efff649475e93a3e94c9f5b8c7278b43a5
def v639 : W := 0xff7680bfeb4e7f9d88d45ad7770b45c7ff4640bfe90e1e9588d45ad7770b4484
def v640 : W := 0xff76f0efc16e7b3581964a5ff70d65cbff4670efc12e1a3589964a5ff70d6489
def v641 : W := 0xff76f0fdab4a6fbd88d65adf770f41c7bd42403da90a0e9488d41ac7270b4084
def v642 : W := 0xff76f0ffeb6e7fbd89d65adff70f65cfff4670ffe92e1eb589d65adff70f648d
def v643 : W := 0xff7efdffeb6effbdb9d6fedff75ff7dfff4ef9ffe92e9eb5b9d6fadff71ff68d
def v644 : W := 0xffb17eed2ac2c7fd2a227efe57f5dbf6a033460812c9430e4c28066020604972
def v645 : W := 0xffb372ed3a4bc7ff6e0a7ade7795c9d6a0034208000802040c00024020004810
def v646 : W := 0xffb37eec384bc3f76e0a76de77d5da90a0034208000802040c00024020004810
def v647 : W := 0xffb37eed3acbc7ff6e2a7efe77f5dbf6a033460812c9430e4c28066020604972
def v648 : W := 0xfff7f2fdbb4befffeede7adf779fc9d7bd43423da90a0e948cd41ac7270b4894
def v649 : W := 0xfff7f2fffb6fffffefde7adff79feddfff4772ffe92e1eb58dd65adff70f6c9d
def v650 : W := 0xffffffee796fdbf7ffdaf6dff7dffe99ef4ffbee492e9ab5bdd2e2dff71ffe99

def ins : List W := [v500, v245, v118, v76, v407, v557, v182, v590]
theorem sampled : ∀ j : Fin 256, Nat.testBit 0xfffffffffffffffffffffffffffcfffcfffffffeffffffaafefefefe00000000 (∑ i : Fin 8, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def level0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level0_ok : everyKey (fun q => !doneTest q) level0 = true := by decide +kernel
theorem closed0 : Closed 0 level0 := closed_nil level0 level0_ok
def level1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level1_ok : everyKey (rowOK 0 level0) level1 = true := by decide +kernel
theorem closed1 : Closed 1 level1 := closed_next 0 (by decide) level1 level0 closed0 level1_ok
def level2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level2_ok : everyKey (rowOK 1 level1) level2 = true := by decide +kernel
theorem closed2 : Closed 2 level2 := closed_next 1 (by decide) level2 level1 closed1 level2_ok
def level3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
def level4 : BinaryTree (List W) := (.node [v197, v316, v500, v557, v646] (.node [v194, v316, v500, v557, v647] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
def level5lllll : BinaryTree (List W) := (.node [v48, v182, v316, v500, v557, v621] (.node [v43, v76, v182, v316, v557, v621] .nil .nil) (.node [v48, v182, v316, v531, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllll_ok : everyKey (rowOK 4 level4) level5lllll = true := by decide +kernel
def level5llllr : BinaryTree (List W) := (.node [v76, v172, v316, v537, v557, v590] (.node [v76, v158, v182, v316, v557, v621] .nil .nil) (.node [v76, v182, v189, v316, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llllr_ok : everyKey (rowOK 4 level4) level5llllr = true := by decide +kernel
def level5llll : BinaryTree (List W) := .node [v76, v136, v316, v500, v557, v647] level5lllll level5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llll_ok : everyKey (rowOK 4 level4) level5llll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllll && everyKey (rowOK 4 level4) level5llllr) = true
  rw [level5lllll_ok, level5llllr_ok]
  decide +kernel
def level5lllrl : BinaryTree (List W) := (.node [v76, v182, v223, v500, v557, v621] (.node [v76, v182, v191, v316, v557, v590] .nil .nil) (.node [v76, v182, v223, v531, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrl_ok : everyKey (rowOK 4 level4) level5lllrl = true := by decide +kernel
def level5lllrr : BinaryTree (List W) := (.node [v76, v182, v261, v316, v407, v500] (.node [v76, v182, v252, v531, v557, v590] .nil .nil) (.node [v76, v182, v297, v500, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllrr_ok : everyKey (rowOK 4 level4) level5lllrr = true := by decide +kernel
def level5lllr : BinaryTree (List W) := .node [v76, v182, v252, v500, v557, v621] level5lllrl level5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lllr_ok : everyKey (rowOK 4 level4) level5lllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lllrl && everyKey (rowOK 4 level4) level5lllrr) = true
  rw [level5lllrl_ok, level5lllrr_ok]
  decide +kernel
def level5lll : BinaryTree (List W) := .node [v76, v182, v190, v316, v557, v637] level5llll level5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lll_ok : everyKey (rowOK 4 level4) level5lll = true := by
  change (_ && everyKey (rowOK 4 level4) level5llll && everyKey (rowOK 4 level4) level5lllr) = true
  rw [level5llll_ok, level5lllr_ok]
  decide +kernel
def level5llrll : BinaryTree (List W) := (.node [v76, v182, v316, v363, v407, v590] (.node [v76, v182, v316, v361, v407, v557] .nil .nil) (.node [v76, v182, v316, v407, v557, v636] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrll_ok : everyKey (rowOK 4 level4) level5llrll = true := by decide +kernel
def level5llrlr : BinaryTree (List W) := (.node [v76, v182, v316, v482, v557, v621] (.node [v76, v182, v316, v458, v500, v557] .nil .nil) (.node [v76, v182, v316, v500, v546, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrlr_ok : everyKey (rowOK 4 level4) level5llrlr = true := by decide +kernel
def level5llrl : BinaryTree (List W) := .node [v76, v182, v316, v452, v500, v590] level5llrll level5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrl_ok : everyKey (rowOK 4 level4) level5llrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrll && everyKey (rowOK 4 level4) level5llrlr) = true
  rw [level5llrll_ok, level5llrlr_ok]
  decide +kernel
def level5llrr : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v646] (.node [v76, v182, v316, v500, v557, v621] (.node [v76, v182, v316, v500, v557, v615] .nil .nil) (.node [v76, v182, v316, v500, v557, v645] .nil .nil)) (.node [v76, v182, v316, v528, v557, v590] (.node [v76, v182, v316, v500, v575, v621] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llrr_ok : everyKey (rowOK 4 level4) level5llrr = true := by decide +kernel
def level5llr : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v597] level5llrl level5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5llr_ok : everyKey (rowOK 4 level4) level5llr = true := by
  change (_ && everyKey (rowOK 4 level4) level5llrl && everyKey (rowOK 4 level4) level5llrr) = true
  rw [level5llrl_ok, level5llrr_ok]
  decide +kernel
def level5ll : BinaryTree (List W) := .node [v76, v182, v297, v531, v557, v590] level5lll level5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5ll_ok : everyKey (rowOK 4 level4) level5ll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lll && everyKey (rowOK 4 level4) level5llr) = true
  rw [level5lll_ok, level5llr_ok]
  decide +kernel
def level5lrlll : BinaryTree (List W) := (.node [v76, v182, v316, v531, v557, v585] (.node [v76, v182, v316, v531, v546, v590] .nil .nil) (.node [v76, v182, v316, v531, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlll_ok : everyKey (rowOK 4 level4) level5lrlll = true := by decide +kernel
def level5lrllr : BinaryTree (List W) := (.node [v76, v182, v316, v532, v557, v590] (.node [v76, v182, v316, v531, v575, v590] .nil .nil) (.node [v76, v182, v316, v533, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrllr_ok : everyKey (rowOK 4 level4) level5lrllr = true := by decide +kernel
def level5lrll : BinaryTree (List W) := .node [v76, v182, v316, v531, v557, v621] level5lrlll level5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrll_ok : everyKey (rowOK 4 level4) level5lrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlll && everyKey (rowOK 4 level4) level5lrllr) = true
  rw [level5lrlll_ok, level5lrllr_ok]
  decide +kernel
def level5lrlrl : BinaryTree (List W) := (.node [v76, v182, v316, v536, v557, v590] (.node [v76, v182, v316, v535, v557, v590] .nil .nil) (.node [v76, v182, v316, v538, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrl_ok : everyKey (rowOK 4 level4) level5lrlrl = true := by decide +kernel
def level5lrlrr : BinaryTree (List W) := (.node [v76, v182, v316, v557, v590, v648] (.node [v76, v182, v316, v557, v590, v641] .nil .nil) (.node [v76, v182, v316, v557, v596, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlrr_ok : everyKey (rowOK 4 level4) level5lrlrr = true := by decide +kernel
def level5lrlr : BinaryTree (List W) := .node [v76, v182, v316, v539, v557, v590] level5lrlrl level5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrlr_ok : everyKey (rowOK 4 level4) level5lrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrlrl && everyKey (rowOK 4 level4) level5lrlrr) = true
  rw [level5lrlrl_ok, level5lrlrr_ok]
  decide +kernel
def level5lrl : BinaryTree (List W) := .node [v76, v182, v316, v534, v557, v590] level5lrll level5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrl_ok : everyKey (rowOK 4 level4) level5lrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrll && everyKey (rowOK 4 level4) level5lrlr) = true
  rw [level5lrll_ok, level5lrlr_ok]
  decide +kernel
def level5lrrll : BinaryTree (List W) := (.node [v76, v182, v316, v557, v621, v637] (.node [v76, v182, v316, v557, v605, v637] .nil .nil) (.node [v76, v182, v316, v557, v621, v648] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrll_ok : everyKey (rowOK 4 level4) level5lrrll = true := by decide +kernel
def level5lrrlr : BinaryTree (List W) := (.node [v76, v182, v320, v531, v557, v590] (.node [v76, v182, v320, v500, v575, v590] .nil .nil) (.node [v76, v182, v336, v430, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrlr_ok : everyKey (rowOK 4 level4) level5lrrlr = true := by decide +kernel
def level5lrrl : BinaryTree (List W) := .node [v76, v182, v320, v500, v557, v621] level5lrrll level5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrl_ok : everyKey (rowOK 4 level4) level5lrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrll && everyKey (rowOK 4 level4) level5lrrlr) = true
  rw [level5lrrll_ok, level5lrrlr_ok]
  decide +kernel
def level5lrrr : BinaryTree (List W) := (.node [v76, v182, v407, v500, v593, v627] (.node [v76, v182, v407, v500, v557, v568] (.node [v76, v182, v407, v462, v557, v590] .nil .nil) (.node [v76, v182, v407, v500, v590, v626] .nil .nil)) (.node [v76, v182, v407, v500, v602, v611] (.node [v76, v182, v407, v500, v600, v612] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrrr_ok : everyKey (rowOK 4 level4) level5lrrr = true := by decide +kernel
def level5lrr : BinaryTree (List W) := .node [v76, v182, v336, v557, v590, v642] level5lrrl level5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lrr_ok : everyKey (rowOK 4 level4) level5lrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrrl && everyKey (rowOK 4 level4) level5lrrr) = true
  rw [level5lrrl_ok, level5lrrr_ok]
  decide +kernel
def level5lr : BinaryTree (List W) := .node [v76, v182, v316, v557, v598, v637] level5lrl level5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5lr_ok : everyKey (rowOK 4 level4) level5lr = true := by
  change (_ && everyKey (rowOK 4 level4) level5lrl && everyKey (rowOK 4 level4) level5lrr) = true
  rw [level5lrl_ok, level5lrr_ok]
  decide +kernel
def level5l : BinaryTree (List W) := .node [v76, v182, v316, v530, v557, v590] level5ll level5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5l_ok : everyKey (rowOK 4 level4) level5l = true := by
  change (_ && everyKey (rowOK 4 level4) level5ll && everyKey (rowOK 4 level4) level5lr) = true
  rw [level5ll_ok, level5lr_ok]
  decide +kernel
def level5rllll : BinaryTree (List W) := (.node [v76, v275, v407, v500, v557, v590] (.node [v76, v182, v488, v557, v590, v642] .nil .nil) (.node [v76, v316, v375, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllll_ok : everyKey (rowOK 4 level4) level5rllll = true := by decide +kernel
def level5rlllr : BinaryTree (List W) := (.node [v76, v316, v407, v500, v578, v590] (.node [v76, v316, v407, v500, v557, v644] .nil .nil) (.node [v76, v316, v473, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlllr_ok : everyKey (rowOK 4 level4) level5rlllr = true := by decide +kernel
def level5rlll : BinaryTree (List W) := .node [v76, v316, v407, v477, v557, v590] level5rllll level5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlll_ok : everyKey (rowOK 4 level4) level5rlll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllll && everyKey (rowOK 4 level4) level5rlllr) = true
  rw [level5rllll_ok, level5rlllr_ok]
  decide +kernel
def level5rllrl : BinaryTree (List W) := (.node [v89, v182, v316, v557, v590, v637] (.node [v89, v182, v316, v500, v557, v590] .nil .nil) (.node [v90, v182, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrl_ok : everyKey (rowOK 4 level4) level5rllrl = true := by decide +kernel
def level5rllrr : BinaryTree (List W) := (.node [v133, v316, v407, v500, v557, v590] (.node [v118, v197, v245, v500, v557, v646] .nil .nil) (.node [v158, v182, v193, v316, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllrr_ok : everyKey (rowOK 4 level4) level5rllrr = true := by decide +kernel
def level5rllr : BinaryTree (List W) := .node [v118, v194, v245, v500, v557, v647] level5rllrl level5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rllr_ok : everyKey (rowOK 4 level4) level5rllr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rllrl && everyKey (rowOK 4 level4) level5rllrr) = true
  rw [level5rllrl_ok, level5rllrr_ok]
  decide +kernel
def level5rll : BinaryTree (List W) := .node [v83, v316, v407, v500, v557, v647] level5rlll level5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rll_ok : everyKey (rowOK 4 level4) level5rll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlll && everyKey (rowOK 4 level4) level5rllr) = true
  rw [level5rlll_ok, level5rllr_ok]
  decide +kernel
def level5rlrll : BinaryTree (List W) := (.node [v173, v197, v316, v500, v557, v590] (.node [v164, v182, v336, v407, v557, v590] .nil .nil) (.node [v182, v192, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrll_ok : everyKey (rowOK 4 level4) level5rlrll = true := by decide +kernel
def level5rlrlr : BinaryTree (List W) := (.node [v182, v193, v297, v500, v557, v590] (.node [v182, v193, v252, v500, v557, v590] .nil .nil) (.node [v182, v193, v316, v482, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrlr_ok : everyKey (rowOK 4 level4) level5rlrlr = true := by decide +kernel
def level5rlrl : BinaryTree (List W) := .node [v182, v193, v223, v500, v557, v590] level5rlrll level5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrl_ok : everyKey (rowOK 4 level4) level5rlrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrll && everyKey (rowOK 4 level4) level5rlrlr) = true
  rw [level5rlrll_ok, level5rlrlr_ok]
  decide +kernel
def level5rlrr : BinaryTree (List W) := (.node [v182, v193, v316, v500, v575, v590] (.node [v182, v193, v316, v500, v557, v590] (.node [v182, v193, v316, v500, v557, v585] .nil .nil) (.node [v182, v193, v316, v500, v557, v621] .nil .nil)) (.node [v182, v193, v316, v557, v590, v637] (.node [v182, v193, v316, v531, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlrr_ok : everyKey (rowOK 4 level4) level5rlrr = true := by decide +kernel
def level5rlr : BinaryTree (List W) := .node [v182, v193, v316, v500, v546, v590] level5rlrl level5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rlr_ok : everyKey (rowOK 4 level4) level5rlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rlrl && everyKey (rowOK 4 level4) level5rlrr) = true
  rw [level5rlrl_ok, level5rlrr_ok]
  decide +kernel
def level5rl : BinaryTree (List W) := .node [v158, v182, v201, v316, v557, v590] level5rll level5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rl_ok : everyKey (rowOK 4 level4) level5rl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rll && everyKey (rowOK 4 level4) level5rlr) = true
  rw [level5rll_ok, level5rlr_ok]
  decide +kernel
def level5rrlll : BinaryTree (List W) := (.node [v182, v195, v316, v500, v557, v590] (.node [v182, v194, v316, v500, v557, v590] .nil .nil) (.node [v182, v196, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlll_ok : everyKey (rowOK 4 level4) level5rrlll = true := by decide +kernel
def level5rrllr : BinaryTree (List W) := (.node [v182, v200, v316, v500, v557, v586] (.node [v182, v199, v316, v500, v557, v590] .nil .nil) (.node [v182, v201, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrllr_ok : everyKey (rowOK 4 level4) level5rrllr = true := by decide +kernel
def level5rrll : BinaryTree (List W) := .node [v182, v198, v316, v500, v557, v590] level5rrlll level5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrll_ok : everyKey (rowOK 4 level4) level5rrll = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlll && everyKey (rowOK 4 level4) level5rrllr) = true
  rw [level5rrlll_ok, level5rrllr_ok]
  decide +kernel
def level5rrlrl : BinaryTree (List W) := (.node [v182, v203, v316, v500, v557, v590] (.node [v182, v202, v316, v500, v557, v590] .nil .nil) (.node [v182, v204, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrl_ok : everyKey (rowOK 4 level4) level5rrlrl = true := by decide +kernel
def level5rrlrr : BinaryTree (List W) := (.node [v182, v316, v407, v485, v557, v590] (.node [v182, v206, v316, v500, v557, v590] .nil .nil) (.node [v182, v316, v407, v500, v557, v607] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlrr_ok : everyKey (rowOK 4 level4) level5rrlrr = true := by decide +kernel
def level5rrlr : BinaryTree (List W) := .node [v182, v205, v316, v500, v557, v590] level5rrlrl level5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrlr_ok : everyKey (rowOK 4 level4) level5rrlr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrlrl && everyKey (rowOK 4 level4) level5rrlrr) = true
  rw [level5rrlrl_ok, level5rrlrr_ok]
  decide +kernel
def level5rrl : BinaryTree (List W) := .node [v182, v201, v316, v557, v590, v637] level5rrll level5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrl_ok : everyKey (rowOK 4 level4) level5rrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrll && everyKey (rowOK 4 level4) level5rrlr) = true
  rw [level5rrll_ok, level5rrlr_ok]
  decide +kernel
def level5rrrll : BinaryTree (List W) := (.node [v182, v316, v433, v500, v557, v590] (.node [v182, v316, v424, v500, v557, v590] .nil .nil) (.node [v182, v316, v435, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrll_ok : everyKey (rowOK 4 level4) level5rrrll = true := by decide +kernel
def level5rrrlr : BinaryTree (List W) := (.node [v182, v317, v437, v500, v557, v590] (.node [v182, v316, v500, v557, v587, v590] .nil .nil) (.node [v182, v321, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrlr_ok : everyKey (rowOK 4 level4) level5rrrlr = true := by decide +kernel
def level5rrrl : BinaryTree (List W) := .node [v182, v316, v437, v500, v559, v590] level5rrrll level5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrl_ok : everyKey (rowOK 4 level4) level5rrrl = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrll && everyKey (rowOK 4 level4) level5rrrlr) = true
  rw [level5rrrll_ok, level5rrrlr_ok]
  decide +kernel
def level5rrrr : BinaryTree (List W) := (.node [v186, v316, v407, v500, v557, v608] (.node [v182, v333, v407, v514, v557, v590] (.node [v182, v330, v437, v500, v557, v590] .nil .nil) (.node [v182, v334, v407, v513, v557, v590] .nil .nil)) (.node [v197, v316, v407, v500, v557, v606] (.node [v186, v316, v437, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrrr_ok : everyKey (rowOK 4 level4) level5rrrr = true := by decide +kernel
def level5rrr : BinaryTree (List W) := .node [v182, v326, v407, v527, v557, v590] level5rrrl level5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rrr_ok : everyKey (rowOK 4 level4) level5rrr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrrl && everyKey (rowOK 4 level4) level5rrrr) = true
  rw [level5rrrl_ok, level5rrrr_ok]
  decide +kernel
def level5rr : BinaryTree (List W) := .node [v182, v316, v407, v500, v564, v590] level5rrl level5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5rr_ok : everyKey (rowOK 4 level4) level5rr = true := by
  change (_ && everyKey (rowOK 4 level4) level5rrl && everyKey (rowOK 4 level4) level5rrr) = true
  rw [level5rrl_ok, level5rrr_ok]
  decide +kernel
def level5r : BinaryTree (List W) := .node [v182, v193, v320, v500, v557, v590] level5rl level5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5r_ok : everyKey (rowOK 4 level4) level5r = true := by
  change (_ && everyKey (rowOK 4 level4) level5rl && everyKey (rowOK 4 level4) level5rr) = true
  rw [level5rl_ok, level5rr_ok]
  decide +kernel
def level5 : BinaryTree (List W) := .node [v76, v182, v438, v500, v557, v590] level5l level5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  change (_ && everyKey (rowOK 4 level4) level5l && everyKey (rowOK 4 level4) level5r) = true
  rw [level5l_ok, level5r_ok]
  decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
def level6lllllll : BinaryTree (List W) := (.node [v8, v76, v182, v245, v531, v557, v590] (.node [v8, v76, v182, v245, v500, v557, v621] (.node [v1, v76, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v8, v182, v193, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllllll_ok : everyKey (rowOK 5 level5) level6lllllll = true := by decide +kernel
def level6llllllr : BinaryTree (List W) := (.node [v11, v76, v316, v407, v500, v557, v647] (.node [v10, v182, v316, v437, v500, v557, v590] (.node [v10, v182, v316, v407, v500, v557, v608] .nil .nil) .nil) (.node [v13, v76, v182, v407, v500, v590, v627] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllllr_ok : everyKey (rowOK 5 level5) level6llllllr = true := by decide +kernel
def level6llllll : BinaryTree (List W) := .node [v9, v76, v182, v316, v500, v557, v590] level6lllllll level6llllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllll_ok : everyKey (rowOK 5 level5) level6llllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllllll && everyKey (rowOK 5 level5) level6llllllr) = true
  rw [level6lllllll_ok, level6llllllr_ok]
  decide +kernel
def level6lllllrl : BinaryTree (List W) := (.node [v24, v182, v316, v407, v500, v566, v590] (.node [v16, v182, v316, v407, v500, v557, v590] (.node [v16, v158, v182, v316, v407, v557, v590] .nil .nil) .nil) (.node [v25, v131, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllllrl_ok : everyKey (rowOK 5 level5) level6lllllrl = true := by decide +kernel
def level6lllllrr : BinaryTree (List W) := (.node [v31, v182, v316, v437, v500, v557, v590] (.node [v29, v76, v182, v407, v461, v557, v590] (.node [v26, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v32, v182, v334, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllllrr_ok : everyKey (rowOK 5 level5) level6lllllrr = true := by decide +kernel
def level6lllllr : BinaryTree (List W) := .node [v25, v182, v316, v437, v500, v557, v590] level6lllllrl level6lllllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllllr_ok : everyKey (rowOK 5 level5) level6lllllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllllrl && everyKey (rowOK 5 level5) level6lllllrr) = true
  rw [level6lllllrl_ok, level6lllllrr_ok]
  decide +kernel
def level6lllll : BinaryTree (List W) := .node [v15, v182, v316, v407, v484, v557, v590] level6llllll level6lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllll_ok : everyKey (rowOK 5 level5) level6lllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llllll && everyKey (rowOK 5 level5) level6lllllr) = true
  rw [level6llllll_ok, level6lllllr_ok]
  decide +kernel
def level6llllrll : BinaryTree (List W) := (.node [v35, v76, v182, v316, v500, v557, v590] (.node [v34, v76, v182, v316, v557, v590, v637] (.node [v34, v76, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v36, v76, v316, v407, v475, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrll_ok : everyKey (rowOK 5 level5) level6llllrll = true := by decide +kernel
def level6llllrlr : BinaryTree (List W) := (.node [v39, v76, v158, v182, v316, v557, v590] (.node [v39, v76, v135, v316, v500, v557, v590] (.node [v38, v76, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v39, v76, v182, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrlr_ok : everyKey (rowOK 5 level5) level6llllrlr = true := by decide +kernel
def level6llllrl : BinaryTree (List W) := .node [v37, v76, v182, v210, v316, v407, v500] level6llllrll level6llllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrl_ok : everyKey (rowOK 5 level5) level6llllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llllrll && everyKey (rowOK 5 level5) level6llllrlr) = true
  rw [level6llllrll_ok, level6llllrlr_ok]
  decide +kernel
def level6llllrrl : BinaryTree (List W) := (.node [v41, v76, v182, v316, v500, v557, v590] (.node [v40, v76, v182, v316, v500, v557, v590] (.node [v39, v76, v316, v365, v500, v557, v590] .nil .nil) .nil) (.node [v42, v182, v276, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrrl_ok : everyKey (rowOK 5 level5) level6llllrrl = true := by decide +kernel
def level6llllrrr : BinaryTree (List W) := (.node [v45, v76, v182, v316, v500, v557, v590] (.node [v44, v182, v316, v377, v500, v557, v590] (.node [v43, v76, v118, v182, v245, v557, v621] .nil .nil) .nil) (.node [v46, v182, v279, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrrr_ok : everyKey (rowOK 5 level5) level6llllrrr = true := by decide +kernel
def level6llllrr : BinaryTree (List W) := .node [v42, v182, v316, v437, v500, v557, v590] level6llllrrl level6llllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllrr_ok : everyKey (rowOK 5 level5) level6llllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llllrrl && everyKey (rowOK 5 level5) level6llllrrr) = true
  rw [level6llllrrl_ok, level6llllrrr_ok]
  decide +kernel
def level6llllr : BinaryTree (List W) := .node [v39, v76, v182, v316, v557, v590, v637] level6llllrl level6llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llllr_ok : everyKey (rowOK 5 level5) level6llllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llllrl && everyKey (rowOK 5 level5) level6llllrr) = true
  rw [level6llllrl_ok, level6llllrr_ok]
  decide +kernel
def level6llll : BinaryTree (List W) := .node [v33, v76, v316, v407, v500, v583, v590] level6lllll level6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llll_ok : everyKey (rowOK 5 level5) level6llll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllll && everyKey (rowOK 5 level5) level6llllr) = true
  rw [level6lllll_ok, level6llllr_ok]
  decide +kernel
def level6lllrlll : BinaryTree (List W) := (.node [v48, v118, v182, v245, v500, v557, v621] (.node [v47, v182, v316, v407, v500, v557, v590] (.node [v47, v143, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v48, v118, v182, v245, v531, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrlll_ok : everyKey (rowOK 5 level5) level6lllrlll = true := by decide +kernel
def level6lllrllr : BinaryTree (List W) := (.node [v50, v182, v316, v407, v500, v557, v590] (.node [v49, v182, v316, v407, v500, v557, v590] (.node [v48, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v51, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrllr_ok : everyKey (rowOK 5 level5) level6lllrllr = true := by decide +kernel
def level6lllrll : BinaryTree (List W) := .node [v48, v135, v182, v316, v500, v557, v590] level6lllrlll level6lllrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrll_ok : everyKey (rowOK 5 level5) level6lllrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrlll && everyKey (rowOK 5 level5) level6lllrllr) = true
  rw [level6lllrlll_ok, level6lllrllr_ok]
  decide +kernel
def level6lllrlrl : BinaryTree (List W) := (.node [v55, v182, v316, v407, v500, v547, v590] (.node [v54, v76, v182, v316, v500, v557, v590] (.node [v53, v197, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v55, v182, v316, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrlrl_ok : everyKey (rowOK 5 level5) level6lllrlrl = true := by decide +kernel
def level6lllrlrr : BinaryTree (List W) := (.node [v59, v182, v316, v407, v514, v557, v590] (.node [v58, v182, v316, v407, v500, v557, v590] (.node [v57, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v60, v182, v290, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrlrr_ok : everyKey (rowOK 5 level5) level6lllrlrr = true := by decide +kernel
def level6lllrlr : BinaryTree (List W) := .node [v56, v182, v316, v407, v500, v557, v590] level6lllrlrl level6lllrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrlr_ok : everyKey (rowOK 5 level5) level6lllrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrlrl && everyKey (rowOK 5 level5) level6lllrlrr) = true
  rw [level6lllrlrl_ok, level6lllrlrr_ok]
  decide +kernel
def level6lllrl : BinaryTree (List W) := .node [v52, v182, v316, v407, v500, v557, v590] level6lllrll level6lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrl_ok : everyKey (rowOK 5 level5) level6lllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrll && everyKey (rowOK 5 level5) level6lllrlr) = true
  rw [level6lllrll_ok, level6lllrlr_ok]
  decide +kernel
def level6lllrrll : BinaryTree (List W) := (.node [v63, v182, v316, v407, v500, v557, v590] (.node [v62, v182, v316, v407, v500, v557, v590] (.node [v61, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v64, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrll_ok : everyKey (rowOK 5 level5) level6lllrrll = true := by decide +kernel
def level6lllrrlr : BinaryTree (List W) := (.node [v68, v182, v316, v407, v500, v557, v590] (.node [v67, v182, v316, v407, v500, v557, v590] (.node [v66, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v69, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrlr_ok : everyKey (rowOK 5 level5) level6lllrrlr = true := by decide +kernel
def level6lllrrl : BinaryTree (List W) := .node [v65, v182, v316, v407, v500, v557, v586] level6lllrrll level6lllrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrl_ok : everyKey (rowOK 5 level5) level6lllrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrrll && everyKey (rowOK 5 level5) level6lllrrlr) = true
  rw [level6lllrrll_ok, level6lllrrlr_ok]
  decide +kernel
def level6lllrrrl : BinaryTree (List W) := (.node [v73, v182, v316, v407, v500, v557, v590] (.node [v72, v182, v316, v407, v500, v557, v590] (.node [v71, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v74, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrrl_ok : everyKey (rowOK 5 level5) level6lllrrrl = true := by decide +kernel
def level6lllrrrr : BinaryTree (List W) := (.node [v76, v88, v245, v407, v500, v557, v590] (.node [v76, v86, v220, v407, v500, v557, v590] (.node [v76, v78, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v96, v182, v245, v500, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrrr_ok : everyKey (rowOK 5 level5) level6lllrrrr = true := by decide +kernel
def level6lllrrr : BinaryTree (List W) := .node [v75, v182, v316, v407, v500, v557, v590] level6lllrrrl level6lllrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrrr_ok : everyKey (rowOK 5 level5) level6lllrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrrrl && everyKey (rowOK 5 level5) level6lllrrrr) = true
  rw [level6lllrrrl_ok, level6lllrrrr_ok]
  decide +kernel
def level6lllrr : BinaryTree (List W) := .node [v70, v182, v316, v407, v500, v557, v590] level6lllrrl level6lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllrr_ok : everyKey (rowOK 5 level5) level6lllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrrl && everyKey (rowOK 5 level5) level6lllrrr) = true
  rw [level6lllrrl_ok, level6lllrrr_ok]
  decide +kernel
def level6lllr : BinaryTree (List W) := .node [v60, v182, v316, v437, v500, v557, v590] level6lllrl level6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lllr_ok : everyKey (rowOK 5 level5) level6lllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lllrl && everyKey (rowOK 5 level5) level6lllrr) = true
  rw [level6lllrl_ok, level6lllrr_ok]
  decide +kernel
def level6lll : BinaryTree (List W) := .node [v46, v182, v316, v437, v500, v557, v590] level6llll level6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lll_ok : everyKey (rowOK 5 level5) level6lll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llll && everyKey (rowOK 5 level5) level6lllr) = true
  rw [level6llll_ok, level6lllr_ok]
  decide +kernel
def level6llrllll : BinaryTree (List W) := (.node [v76, v118, v136, v245, v500, v557, v647] (.node [v76, v111, v182, v448, v500, v557, v590] (.node [v76, v110, v341, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v158, v182, v245, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrllll_ok : everyKey (rowOK 5 level5) level6llrllll = true := by decide +kernel
def level6llrlllr : BinaryTree (List W) := (.node [v76, v118, v182, v191, v245, v557, v590] (.node [v76, v118, v182, v190, v245, v557, v637] (.node [v76, v118, v182, v189, v245, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v211, v500, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlllr_ok : everyKey (rowOK 5 level5) level6llrlllr = true := by decide +kernel
def level6llrlll : BinaryTree (List W) := .node [v76, v118, v172, v245, v537, v557, v590] level6llrllll level6llrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlll_ok : everyKey (rowOK 5 level5) level6llrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrllll && everyKey (rowOK 5 level5) level6llrlllr) = true
  rw [level6llrllll_ok, level6llrlllr_ok]
  decide +kernel
def level6llrllrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v261, v407, v500] (.node [v76, v118, v182, v219, v531, v557, v590] (.node [v76, v118, v182, v219, v500, v557, v621] .nil .nil) .nil) (.node [v76, v118, v182, v245, v361, v407, v557] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrllrl_ok : everyKey (rowOK 5 level5) level6llrllrl = true := by decide +kernel
def level6llrllrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v458, v500, v557] (.node [v76, v118, v182, v245, v452, v500, v590] (.node [v76, v118, v182, v245, v407, v557, v636] .nil .nil) .nil) (.node [v76, v118, v182, v245, v482, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrllrr_ok : everyKey (rowOK 5 level5) level6llrllrr = true := by decide +kernel
def level6llrllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v363, v407, v590] level6llrllrl level6llrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrllr_ok : everyKey (rowOK 5 level5) level6llrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrllrl && everyKey (rowOK 5 level5) level6llrllrr) = true
  rw [level6llrllrl_ok, level6llrllrr_ok]
  decide +kernel
def level6llrll : BinaryTree (List W) := .node [v76, v118, v182, v211, v531, v557, v590] level6llrlll level6llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrll_ok : everyKey (rowOK 5 level5) level6llrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrlll && everyKey (rowOK 5 level5) level6llrllr) = true
  rw [level6llrlll_ok, level6llrllr_ok]
  decide +kernel
def level6llrlrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v557, v621] (.node [v76, v118, v182, v245, v500, v557, v615] (.node [v76, v118, v182, v245, v500, v557, v597] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v557, v645] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrll_ok : everyKey (rowOK 5 level5) level6llrlrll = true := by decide +kernel
def level6llrlrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v530, v557, v590] (.node [v76, v118, v182, v245, v528, v557, v590] (.node [v76, v118, v182, v245, v500, v575, v621] .nil .nil) .nil) (.node [v76, v118, v182, v245, v531, v546, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrlr_ok : everyKey (rowOK 5 level5) level6llrlrlr = true := by decide +kernel
def level6llrlrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v646] level6llrlrll level6llrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrl_ok : everyKey (rowOK 5 level5) level6llrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrlrll && everyKey (rowOK 5 level5) level6llrlrlr) = true
  rw [level6llrlrll_ok, level6llrlrlr_ok]
  decide +kernel
def level6llrlrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v531, v575, v590] (.node [v76, v118, v182, v245, v531, v557, v621] (.node [v76, v118, v182, v245, v531, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v532, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrrl_ok : everyKey (rowOK 5 level5) level6llrlrrl = true := by decide +kernel
def level6llrlrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v538, v557, v590] (.node [v76, v118, v182, v245, v536, v557, v590] (.node [v76, v118, v182, v245, v534, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v539, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrrr_ok : everyKey (rowOK 5 level5) level6llrlrrr = true := by decide +kernel
def level6llrlrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v533, v557, v590] level6llrlrrl level6llrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlrr_ok : everyKey (rowOK 5 level5) level6llrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrlrrl && everyKey (rowOK 5 level5) level6llrlrrr) = true
  rw [level6llrlrrl_ok, level6llrlrrr_ok]
  decide +kernel
def level6llrlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v531, v557, v585] level6llrlrl level6llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrlr_ok : everyKey (rowOK 5 level5) level6llrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrlrl && everyKey (rowOK 5 level5) level6llrlrr) = true
  rw [level6llrlrl_ok, level6llrlrr_ok]
  decide +kernel
def level6llrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v546, v621] level6llrll level6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrl_ok : everyKey (rowOK 5 level5) level6llrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrll && everyKey (rowOK 5 level5) level6llrlr) = true
  rw [level6llrll_ok, level6llrlr_ok]
  decide +kernel
def level6llrrlll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v557, v598, v637] (.node [v76, v118, v182, v245, v557, v596, v642] (.node [v76, v118, v182, v245, v557, v590, v648] .nil .nil) .nil) (.node [v76, v118, v182, v245, v557, v605, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrlll_ok : everyKey (rowOK 5 level5) level6llrrlll = true := by decide +kernel
def level6llrrllr : BinaryTree (List W) := (.node [v76, v118, v182, v316, v531, v557, v590] (.node [v76, v118, v182, v316, v500, v557, v621] (.node [v76, v118, v182, v245, v557, v621, v648] .nil .nil) .nil) (.node [v76, v118, v182, v319, v500, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrllr_ok : everyKey (rowOK 5 level5) level6llrrllr = true := by decide +kernel
def level6llrrll : BinaryTree (List W) := .node [v76, v118, v182, v245, v557, v621, v637] level6llrrlll level6llrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrll_ok : everyKey (rowOK 5 level5) level6llrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrlll && everyKey (rowOK 5 level5) level6llrrllr) = true
  rw [level6llrrlll_ok, level6llrrllr_ok]
  decide +kernel
def level6llrrlrl : BinaryTree (List W) := (.node [v76, v118, v182, v335, v557, v590, v642] (.node [v76, v118, v182, v335, v430, v557, v590] (.node [v76, v118, v182, v319, v531, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v407, v472, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrlrl_ok : everyKey (rowOK 5 level5) level6llrrlrl = true := by decide +kernel
def level6llrrlrr : BinaryTree (List W) := (.node [v76, v118, v182, v407, v500, v594, v602] (.node [v76, v118, v182, v407, v500, v592, v604] (.node [v76, v118, v182, v407, v500, v590, v603] .nil .nil) .nil) (.node [v76, v118, v182, v407, v500, v595, v599] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrlrr_ok : everyKey (rowOK 5 level5) level6llrrlrr = true := by decide +kernel
def level6llrrlr : BinaryTree (List W) := .node [v76, v118, v182, v407, v500, v543, v557] level6llrrlrl level6llrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrlr_ok : everyKey (rowOK 5 level5) level6llrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrlrl && everyKey (rowOK 5 level5) level6llrrlrr) = true
  rw [level6llrrlrl_ok, level6llrrlrr_ok]
  decide +kernel
def level6llrrl : BinaryTree (List W) := .node [v76, v118, v182, v319, v500, v575, v590] level6llrrll level6llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrl_ok : everyKey (rowOK 5 level5) level6llrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrll && everyKey (rowOK 5 level5) level6llrrlr) = true
  rw [level6llrrll_ok, level6llrrlr_ok]
  decide +kernel
def level6llrrrll : BinaryTree (List W) := (.node [v76, v118, v245, v407, v477, v557, v590] (.node [v76, v118, v245, v375, v500, v557, v590] (.node [v76, v118, v182, v476, v557, v590, v642] .nil .nil) .nil) (.node [v76, v118, v245, v407, v500, v557, v644] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrll_ok : everyKey (rowOK 5 level5) level6llrrrll = true := by decide +kernel
def level6llrrrlr : BinaryTree (List W) := (.node [v76, v123, v182, v316, v450, v500, v590] (.node [v76, v118, v337, v407, v500, v557, v590] (.node [v76, v118, v245, v473, v557, v590, v642] .nil .nil) .nil) (.node [v76, v126, v182, v407, v500, v541, v557] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrlr_ok : everyKey (rowOK 5 level5) level6llrrrlr = true := by decide +kernel
def level6llrrrl : BinaryTree (List W) := .node [v76, v118, v245, v407, v500, v578, v590] level6llrrrll level6llrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrl_ok : everyKey (rowOK 5 level5) level6llrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrrll && everyKey (rowOK 5 level5) level6llrrrlr) = true
  rw [level6llrrrll_ok, level6llrrrlr_ok]
  decide +kernel
def level6llrrrrl : BinaryTree (List W) := (.node [v76, v134, v182, v316, v500, v557, v590] (.node [v76, v132, v182, v316, v500, v557, v590] (.node [v76, v130, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v135, v158, v182, v316, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrrl_ok : everyKey (rowOK 5 level5) level6llrrrrl = true := by decide +kernel
def level6llrrrrr : BinaryTree (List W) := (.node [v76, v135, v182, v297, v500, v557, v590] (.node [v76, v135, v182, v252, v500, v557, v590] .nil .nil) (.node [v76, v135, v182, v316, v482, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrrr_ok : everyKey (rowOK 5 level5) level6llrrrrr = true := by decide +kernel
def level6llrrrr : BinaryTree (List W) := .node [v76, v135, v182, v223, v500, v557, v590] level6llrrrrl level6llrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrrr_ok : everyKey (rowOK 5 level5) level6llrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrrrl && everyKey (rowOK 5 level5) level6llrrrrr) = true
  rw [level6llrrrrl_ok, level6llrrrrr_ok]
  decide +kernel
def level6llrrr : BinaryTree (List W) := .node [v76, v129, v182, v407, v500, v557, v590] level6llrrrl level6llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrrr_ok : everyKey (rowOK 5 level5) level6llrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrrl && everyKey (rowOK 5 level5) level6llrrrr) = true
  rw [level6llrrrl_ok, level6llrrrr_ok]
  decide +kernel
def level6llrr : BinaryTree (List W) := .node [v76, v118, v182, v441, v500, v557, v590] level6llrrl level6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llrr_ok : everyKey (rowOK 5 level5) level6llrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrrl && everyKey (rowOK 5 level5) level6llrrr) = true
  rw [level6llrrl_ok, level6llrrr_ok]
  decide +kernel
def level6llr : BinaryTree (List W) := .node [v76, v118, v182, v245, v557, v590, v641] level6llrl level6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6llr_ok : everyKey (rowOK 5 level5) level6llr = true := by
  change (_ && everyKey (rowOK 5 level5) level6llrl && everyKey (rowOK 5 level5) level6llrr) = true
  rw [level6llrl_ok, level6llrr_ok]
  decide +kernel
def level6ll : BinaryTree (List W) := .node [v76, v96, v182, v245, v531, v557, v590] level6lll level6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6ll_ok : everyKey (rowOK 5 level5) level6ll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lll && everyKey (rowOK 5 level5) level6llr) = true
  rw [level6lll_ok, level6llr_ok]
  decide +kernel
def level6lrlllll : BinaryTree (List W) := (.node [v76, v135, v182, v316, v500, v557, v621] (.node [v76, v135, v182, v316, v500, v557, v590] (.node [v76, v135, v182, v316, v500, v557, v585] .nil .nil) .nil) (.node [v76, v135, v182, v316, v500, v575, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlllll_ok : everyKey (rowOK 5 level5) level6lrlllll = true := by decide +kernel
def level6lrllllr : BinaryTree (List W) := (.node [v76, v135, v316, v428, v500, v557, v590] (.node [v76, v135, v182, v320, v500, v557, v590] (.node [v76, v135, v182, v316, v557, v590, v637] .nil .nil) .nil) (.node [v76, v136, v182, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllllr_ok : everyKey (rowOK 5 level5) level6lrllllr = true := by decide +kernel
def level6lrllll : BinaryTree (List W) := .node [v76, v135, v182, v316, v531, v557, v590] level6lrlllll level6lrllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllll_ok : everyKey (rowOK 5 level5) level6lrllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlllll && everyKey (rowOK 5 level5) level6lrllllr) = true
  rw [level6lrlllll_ok, level6lrllllr_ok]
  decide +kernel
def level6lrlllrl : BinaryTree (List W) := (.node [v76, v140, v182, v245, v500, v557, v621] (.node [v76, v139, v182, v316, v500, v557, v590] (.node [v76, v138, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v140, v182, v245, v500, v575, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlllrl_ok : everyKey (rowOK 5 level5) level6lrlllrl = true := by decide +kernel
def level6lrlllrr : BinaryTree (List W) := (.node [v76, v143, v158, v182, v316, v557, v590] (.node [v76, v142, v182, v316, v500, v557, v590] (.node [v76, v141, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v143, v182, v316, v453, v500, v557] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlllrr_ok : everyKey (rowOK 5 level5) level6lrlllrr = true := by decide +kernel
def level6lrlllr : BinaryTree (List W) := .node [v76, v140, v182, v245, v531, v557, v590] level6lrlllrl level6lrlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlllr_ok : everyKey (rowOK 5 level5) level6lrlllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlllrl && everyKey (rowOK 5 level5) level6lrlllrr) = true
  rw [level6lrlllrl_ok, level6lrlllrr_ok]
  decide +kernel
def level6lrlll : BinaryTree (List W) := .node [v76, v137, v182, v316, v500, v557, v590] level6lrllll level6lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlll_ok : everyKey (rowOK 5 level5) level6lrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrllll && everyKey (rowOK 5 level5) level6lrlllr) = true
  rw [level6lrllll_ok, level6lrlllr_ok]
  decide +kernel
def level6lrllrll : BinaryTree (List W) := (.node [v76, v144, v182, v316, v500, v557, v590] (.node [v76, v143, v182, v316, v557, v590, v637] (.node [v76, v143, v182, v316, v500, v557, v625] .nil .nil) .nil) (.node [v76, v145, v182, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrll_ok : everyKey (rowOK 5 level5) level6lrllrll = true := by decide +kernel
def level6lrllrlr : BinaryTree (List W) := (.node [v76, v149, v182, v316, v500, v557, v590] (.node [v76, v148, v182, v316, v500, v557, v590] (.node [v76, v147, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v151, v316, v407, v537, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrlr_ok : everyKey (rowOK 5 level5) level6lrllrlr = true := by decide +kernel
def level6lrllrl : BinaryTree (List W) := .node [v76, v146, v182, v316, v500, v557, v590] level6lrllrll level6lrllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrl_ok : everyKey (rowOK 5 level5) level6lrllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrllrll && everyKey (rowOK 5 level5) level6lrllrlr) = true
  rw [level6lrllrll_ok, level6lrllrlr_ok]
  decide +kernel
def level6lrllrrl : BinaryTree (List W) := (.node [v76, v158, v182, v255, v407, v557, v590] (.node [v76, v158, v182, v253, v407, v557, v590] (.node [v76, v156, v316, v407, v500, v544, v590] .nil .nil) .nil) (.node [v76, v158, v182, v304, v407, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrrl_ok : everyKey (rowOK 5 level5) level6lrllrrl = true := by decide +kernel
def level6lrllrrr : BinaryTree (List W) := (.node [v76, v158, v182, v316, v377, v557, v590] (.node [v76, v158, v182, v316, v370, v557, v590] (.node [v76, v158, v182, v316, v349, v557, v590] .nil .nil) .nil) (.node [v76, v158, v182, v316, v407, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrrr_ok : everyKey (rowOK 5 level5) level6lrllrrr = true := by decide +kernel
def level6lrllrr : BinaryTree (List W) := .node [v76, v158, v182, v316, v346, v407, v557] level6lrllrrl level6lrllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllrr_ok : everyKey (rowOK 5 level5) level6lrllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrllrrl && everyKey (rowOK 5 level5) level6lrllrrr) = true
  rw [level6lrllrrl_ok, level6lrllrrr_ok]
  decide +kernel
def level6lrllr : BinaryTree (List W) := .node [v76, v152, v182, v316, v500, v557, v590] level6lrllrl level6lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrllr_ok : everyKey (rowOK 5 level5) level6lrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrllrl && everyKey (rowOK 5 level5) level6lrllrr) = true
  rw [level6lrllrl_ok, level6lrllrr_ok]
  decide +kernel
def level6lrll : BinaryTree (List W) := .node [v76, v143, v182, v316, v500, v557, v590] level6lrlll level6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrll_ok : everyKey (rowOK 5 level5) level6lrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlll && everyKey (rowOK 5 level5) level6lrllr) = true
  rw [level6lrlll_ok, level6lrllr_ok]
  decide +kernel
def level6lrlrlll : BinaryTree (List W) := (.node [v76, v158, v182, v316, v557, v590, v625] (.node [v76, v158, v182, v316, v437, v557, v590] (.node [v76, v158, v182, v316, v430, v557, v590] .nil .nil) .nil) (.node [v76, v158, v182, v316, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrlll_ok : everyKey (rowOK 5 level5) level6lrlrlll = true := by decide +kernel
def level6lrlrllr : BinaryTree (List W) := (.node [v76, v161, v182, v316, v407, v557, v590] (.node [v76, v160, v182, v316, v407, v557, v590] (.node [v76, v159, v182, v316, v407, v557, v590] .nil .nil) .nil) (.node [v76, v166, v182, v245, v430, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrllr_ok : everyKey (rowOK 5 level5) level6lrlrllr = true := by decide +kernel
def level6lrlrll : BinaryTree (List W) := .node [v76, v158, v182, v336, v407, v557, v590] level6lrlrlll level6lrlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrll_ok : everyKey (rowOK 5 level5) level6lrlrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrlll && everyKey (rowOK 5 level5) level6lrlrllr) = true
  rw [level6lrlrlll_ok, level6lrlrllr_ok]
  decide +kernel
def level6lrlrlrl : BinaryTree (List W) := (.node [v76, v173, v182, v316, v500, v557, v590] (.node [v76, v172, v182, v316, v500, v557, v590] (.node [v76, v171, v316, v407, v500, v557, v584] .nil .nil) .nil) (.node [v76, v174, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrlrl_ok : everyKey (rowOK 5 level5) level6lrlrlrl = true := by decide +kernel
def level6lrlrlrr : BinaryTree (List W) := (.node [v76, v178, v316, v407, v500, v557, v590] (.node [v76, v177, v316, v407, v500, v557, v590] (.node [v76, v176, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v179, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrlrr_ok : everyKey (rowOK 5 level5) level6lrlrlrr = true := by decide +kernel
def level6lrlrlr : BinaryTree (List W) := .node [v76, v175, v316, v407, v500, v557, v590] level6lrlrlrl level6lrlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrlr_ok : everyKey (rowOK 5 level5) level6lrlrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrlrl && everyKey (rowOK 5 level5) level6lrlrlrr) = true
  rw [level6lrlrlrl_ok, level6lrlrlrr_ok]
  decide +kernel
def level6lrlrl : BinaryTree (List W) := .node [v76, v166, v182, v245, v557, v590, v642] level6lrlrll level6lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrl_ok : everyKey (rowOK 5 level5) level6lrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrll && everyKey (rowOK 5 level5) level6lrlrlr) = true
  rw [level6lrlrll_ok, level6lrlrlr_ok]
  decide +kernel
def level6lrlrrll : BinaryTree (List W) := (.node [v76, v182, v193, v316, v500, v557, v590] (.node [v76, v182, v190, v316, v500, v557, v590] (.node [v76, v181, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v200, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrll_ok : everyKey (rowOK 5 level5) level6lrlrrll = true := by decide +kernel
def level6lrlrrlr : BinaryTree (List W) := (.node [v76, v182, v215, v367, v500, v557, v590] (.node [v76, v182, v210, v316, v407, v557, v637] (.node [v76, v182, v209, v407, v500, v557, v612] .nil .nil) .nil) (.node [v76, v182, v221, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrlr_ok : everyKey (rowOK 5 level5) level6lrlrrlr = true := by decide +kernel
def level6lrlrrl : BinaryTree (List W) := .node [v76, v182, v201, v316, v500, v557, v590] level6lrlrrll level6lrlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrl_ok : everyKey (rowOK 5 level5) level6lrlrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrrll && everyKey (rowOK 5 level5) level6lrlrrlr) = true
  rw [level6lrlrrll_ok, level6lrlrrlr_ok]
  decide +kernel
def level6lrlrrrl : BinaryTree (List W) := (.node [v76, v182, v245, v316, v531, v557, v590] (.node [v76, v182, v245, v316, v500, v557, v621] (.node [v76, v182, v223, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v245, v369, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrrl_ok : everyKey (rowOK 5 level5) level6lrlrrrl = true := by decide +kernel
def level6lrlrrrr : BinaryTree (List W) := (.node [v76, v182, v245, v407, v500, v558, v610] (.node [v76, v182, v245, v407, v500, v557, v609] .nil .nil) (.node [v76, v182, v245, v407, v500, v567, v602] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrrr_ok : everyKey (rowOK 5 level5) level6lrlrrrr = true := by decide +kernel
def level6lrlrrr : BinaryTree (List W) := .node [v76, v182, v245, v407, v483, v557, v590] level6lrlrrrl level6lrlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrrr_ok : everyKey (rowOK 5 level5) level6lrlrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrrrl && everyKey (rowOK 5 level5) level6lrlrrrr) = true
  rw [level6lrlrrrl_ok, level6lrlrrrr_ok]
  decide +kernel
def level6lrlrr : BinaryTree (List W) := .node [v76, v182, v222, v407, v500, v557, v590] level6lrlrrl level6lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlrr_ok : everyKey (rowOK 5 level5) level6lrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrrl && everyKey (rowOK 5 level5) level6lrlrrr) = true
  rw [level6lrlrrl_ok, level6lrlrrr_ok]
  decide +kernel
def level6lrlr : BinaryTree (List W) := .node [v76, v180, v316, v407, v500, v557, v590] level6lrlrl level6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrlr_ok : everyKey (rowOK 5 level5) level6lrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrlrl && everyKey (rowOK 5 level5) level6lrlrr) = true
  rw [level6lrlrl_ok, level6lrlrr_ok]
  decide +kernel
def level6lrl : BinaryTree (List W) := .node [v76, v158, v182, v316, v407, v557, v637] level6lrll level6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrl_ok : everyKey (rowOK 5 level5) level6lrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrll && everyKey (rowOK 5 level5) level6lrlr) = true
  rw [level6lrll_ok, level6lrlr_ok]
  decide +kernel
def level6lrrllll : BinaryTree (List W) := (.node [v76, v182, v250, v407, v500, v557, v590] (.node [v76, v182, v245, v464, v557, v590, v642] (.node [v76, v182, v245, v407, v500, v574, v591] .nil .nil) .nil) (.node [v76, v182, v251, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrllll_ok : everyKey (rowOK 5 level5) level6lrrllll = true := by decide +kernel
def level6lrrlllr : BinaryTree (List W) := (.node [v76, v182, v256, v407, v500, v557, v590] (.node [v76, v182, v255, v407, v500, v557, v590] (.node [v76, v182, v253, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v257, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlllr_ok : everyKey (rowOK 5 level5) level6lrrlllr = true := by decide +kernel
def level6lrrlll : BinaryTree (List W) := .node [v76, v182, v252, v407, v500, v557, v590] level6lrrllll level6lrrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlll_ok : everyKey (rowOK 5 level5) level6lrrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrllll && everyKey (rowOK 5 level5) level6lrrlllr) = true
  rw [level6lrrllll_ok, level6lrrlllr_ok]
  decide +kernel
def level6lrrllrl : BinaryTree (List W) := (.node [v76, v182, v278, v407, v500, v557, v590] (.node [v76, v182, v277, v407, v500, v557, v590] (.node [v76, v182, v263, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v280, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrllrl_ok : everyKey (rowOK 5 level5) level6lrrllrl = true := by decide +kernel
def level6lrrllrr : BinaryTree (List W) := (.node [v76, v182, v284, v407, v527, v557, v590] (.node [v76, v182, v283, v407, v500, v557, v590] (.node [v76, v182, v282, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v286, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrllrr_ok : everyKey (rowOK 5 level5) level6lrrllrr = true := by decide +kernel
def level6lrrllr : BinaryTree (List W) := .node [v76, v182, v281, v407, v500, v557, v590] level6lrrllrl level6lrrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrllr_ok : everyKey (rowOK 5 level5) level6lrrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrllrl && everyKey (rowOK 5 level5) level6lrrllrr) = true
  rw [level6lrrllrl_ok, level6lrrllrr_ok]
  decide +kernel
def level6lrrll : BinaryTree (List W) := .node [v76, v182, v262, v316, v500, v557, v590] level6lrrlll level6lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrll_ok : everyKey (rowOK 5 level5) level6lrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrlll && everyKey (rowOK 5 level5) level6lrrllr) = true
  rw [level6lrrlll_ok, level6lrrllr_ok]
  decide +kernel
def level6lrrlrll : BinaryTree (List W) := (.node [v76, v182, v296, v407, v500, v557, v590] (.node [v76, v182, v295, v407, v500, v557, v590] (.node [v76, v182, v291, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v297, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrll_ok : everyKey (rowOK 5 level5) level6lrrlrll = true := by decide +kernel
def level6lrrlrlr : BinaryTree (List W) := (.node [v76, v182, v304, v407, v500, v557, v590] (.node [v76, v182, v303, v407, v500, v557, v590] (.node [v76, v182, v299, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v305, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrlr_ok : everyKey (rowOK 5 level5) level6lrrlrlr = true := by decide +kernel
def level6lrrlrl : BinaryTree (List W) := .node [v76, v182, v298, v407, v500, v557, v590] level6lrrlrll level6lrrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrl_ok : everyKey (rowOK 5 level5) level6lrrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrlrll && everyKey (rowOK 5 level5) level6lrrlrlr) = true
  rw [level6lrrlrll_ok, level6lrrlrlr_ok]
  decide +kernel
def level6lrrlrrl : BinaryTree (List W) := (.node [v76, v182, v309, v407, v500, v557, v590] (.node [v76, v182, v308, v407, v500, v557, v590] (.node [v76, v182, v307, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v311, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrrl_ok : everyKey (rowOK 5 level5) level6lrrlrrl = true := by decide +kernel
def level6lrrlrrr : BinaryTree (List W) := (.node [v76, v182, v315, v407, v500, v557, v590] (.node [v76, v182, v314, v407, v500, v557, v590] (.node [v76, v182, v313, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v322, v347, v407, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrrr_ok : everyKey (rowOK 5 level5) level6lrrlrrr = true := by decide +kernel
def level6lrrlrr : BinaryTree (List W) := .node [v76, v182, v312, v407, v500, v557, v590] level6lrrlrrl level6lrrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlrr_ok : everyKey (rowOK 5 level5) level6lrrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrlrrl && everyKey (rowOK 5 level5) level6lrrlrrr) = true
  rw [level6lrrlrrl_ok, level6lrrlrrr_ok]
  decide +kernel
def level6lrrlr : BinaryTree (List W) := .node [v76, v182, v306, v407, v500, v557, v590] level6lrrlrl level6lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrlr_ok : everyKey (rowOK 5 level5) level6lrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrlrl && everyKey (rowOK 5 level5) level6lrrlrr) = true
  rw [level6lrrlrl_ok, level6lrrlrr_ok]
  decide +kernel
def level6lrrl : BinaryTree (List W) := .node [v76, v182, v287, v407, v500, v548, v590] level6lrrll level6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrl_ok : everyKey (rowOK 5 level5) level6lrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrll && everyKey (rowOK 5 level5) level6lrrlr) = true
  rw [level6lrrll_ok, level6lrrlr_ok]
  decide +kernel
def level6lrrrlll : BinaryTree (List W) := (.node [v76, v182, v316, v342, v557, v590, v642] (.node [v76, v182, v316, v325, v407, v557, v590] (.node [v76, v182, v316, v324, v407, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v343, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrlll_ok : everyKey (rowOK 5 level5) level6lrrrlll = true := by decide +kernel
def level6lrrrllr : BinaryTree (List W) := (.node [v76, v182, v316, v348, v500, v557, v590] (.node [v76, v182, v316, v347, v557, v590, v642] (.node [v76, v182, v316, v345, v407, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v349, v454, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrllr_ok : everyKey (rowOK 5 level5) level6lrrrllr = true := by decide +kernel
def level6lrrrll : BinaryTree (List W) := .node [v76, v182, v316, v344, v500, v557, v590] level6lrrrlll level6lrrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrll_ok : everyKey (rowOK 5 level5) level6lrrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrlll && everyKey (rowOK 5 level5) level6lrrrllr) = true
  rw [level6lrrrlll_ok, level6lrrrllr_ok]
  decide +kernel
def level6lrrrlrl : BinaryTree (List W) := (.node [v76, v182, v316, v350, v500, v557, v590] (.node [v76, v182, v316, v349, v557, v590, v642] (.node [v76, v182, v316, v349, v557, v590, v637] .nil .nil) .nil) (.node [v76, v182, v316, v351, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrlrl_ok : everyKey (rowOK 5 level5) level6lrrrlrl = true := by decide +kernel
def level6lrrrlrr : BinaryTree (List W) := (.node [v76, v182, v316, v355, v500, v557, v590] (.node [v76, v182, v316, v354, v500, v557, v590] (.node [v76, v182, v316, v353, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v356, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrlrr_ok : everyKey (rowOK 5 level5) level6lrrrlrr = true := by decide +kernel
def level6lrrrlr : BinaryTree (List W) := .node [v76, v182, v316, v352, v407, v557, v590] level6lrrrlrl level6lrrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrlr_ok : everyKey (rowOK 5 level5) level6lrrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrlrl && everyKey (rowOK 5 level5) level6lrrrlrr) = true
  rw [level6lrrrlrl_ok, level6lrrrlrr_ok]
  decide +kernel
def level6lrrrl : BinaryTree (List W) := .node [v76, v182, v316, v349, v500, v557, v590] level6lrrrll level6lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrl_ok : everyKey (rowOK 5 level5) level6lrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrll && everyKey (rowOK 5 level5) level6lrrrlr) = true
  rw [level6lrrrll_ok, level6lrrrlr_ok]
  decide +kernel
def level6lrrrrll : BinaryTree (List W) := (.node [v76, v182, v316, v360, v500, v557, v590] (.node [v76, v182, v316, v359, v500, v557, v590] (.node [v76, v182, v316, v358, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v362, v407, v500, v557] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrll_ok : everyKey (rowOK 5 level5) level6lrrrrll = true := by decide +kernel
def level6lrrrrlr : BinaryTree (List W) := (.node [v76, v182, v316, v371, v500, v557, v590] (.node [v76, v182, v316, v370, v500, v557, v590] (.node [v76, v182, v316, v366, v500, v577, v590] .nil .nil) .nil) (.node [v76, v182, v316, v372, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrlr_ok : everyKey (rowOK 5 level5) level6lrrrrlr = true := by decide +kernel
def level6lrrrrl : BinaryTree (List W) := .node [v76, v182, v316, v364, v500, v557, v625] level6lrrrrll level6lrrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrl_ok : everyKey (rowOK 5 level5) level6lrrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrrll && everyKey (rowOK 5 level5) level6lrrrrlr) = true
  rw [level6lrrrrll_ok, level6lrrrrlr_ok]
  decide +kernel
def level6lrrrrrl : BinaryTree (List W) := (.node [v76, v182, v316, v377, v557, v590, v637] (.node [v76, v182, v316, v377, v500, v557, v590] (.node [v76, v182, v316, v374, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v378, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrrl_ok : everyKey (rowOK 5 level5) level6lrrrrrl = true := by decide +kernel
def level6lrrrrrr : BinaryTree (List W) := (.node [v76, v182, v316, v381, v500, v557, v590] (.node [v76, v182, v316, v380, v500, v557, v590] .nil .nil) (.node [v76, v182, v316, v382, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrrr_ok : everyKey (rowOK 5 level5) level6lrrrrrr = true := by decide +kernel
def level6lrrrrr : BinaryTree (List W) := .node [v76, v182, v316, v379, v500, v557, v590] level6lrrrrrl level6lrrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrrr_ok : everyKey (rowOK 5 level5) level6lrrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrrrl && everyKey (rowOK 5 level5) level6lrrrrrr) = true
  rw [level6lrrrrrl_ok, level6lrrrrrr_ok]
  decide +kernel
def level6lrrrr : BinaryTree (List W) := .node [v76, v182, v316, v373, v500, v557, v590] level6lrrrrl level6lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrrr_ok : everyKey (rowOK 5 level5) level6lrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrrl && everyKey (rowOK 5 level5) level6lrrrrr) = true
  rw [level6lrrrrl_ok, level6lrrrrr_ok]
  decide +kernel
def level6lrrr : BinaryTree (List W) := .node [v76, v182, v316, v357, v500, v557, v590] level6lrrrl level6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrrr_ok : everyKey (rowOK 5 level5) level6lrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrrl && everyKey (rowOK 5 level5) level6lrrrr) = true
  rw [level6lrrrl_ok, level6lrrrr_ok]
  decide +kernel
def level6lrr : BinaryTree (List W) := .node [v76, v182, v316, v323, v407, v557, v590] level6lrrl level6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lrr_ok : everyKey (rowOK 5 level5) level6lrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrrl && everyKey (rowOK 5 level5) level6lrrr) = true
  rw [level6lrrl_ok, level6lrrr_ok]
  decide +kernel
def level6lr : BinaryTree (List W) := .node [v76, v182, v245, v407, v500, v573, v590] level6lrl level6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6lr_ok : everyKey (rowOK 5 level5) level6lr = true := by
  change (_ && everyKey (rowOK 5 level5) level6lrl && everyKey (rowOK 5 level5) level6lrr) = true
  rw [level6lrl_ok, level6lrr_ok]
  decide +kernel
def level6l : BinaryTree (List W) := .node [v76, v135, v182, v316, v500, v546, v590] level6ll level6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6l_ok : everyKey (rowOK 5 level5) level6l = true := by
  change (_ && everyKey (rowOK 5 level5) level6ll && everyKey (rowOK 5 level5) level6lr) = true
  rw [level6ll_ok, level6lr_ok]
  decide +kernel
def level6rllllll : BinaryTree (List W) := (.node [v76, v182, v316, v387, v500, v557, v590] (.node [v76, v182, v316, v386, v500, v557, v590] (.node [v76, v182, v316, v384, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v388, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllllll_ok : everyKey (rowOK 5 level5) level6rllllll = true := by decide +kernel
def level6rlllllr : BinaryTree (List W) := (.node [v76, v182, v316, v392, v500, v557, v590] (.node [v76, v182, v316, v391, v500, v557, v590] (.node [v76, v182, v316, v390, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v393, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllllr_ok : everyKey (rowOK 5 level5) level6rlllllr = true := by decide +kernel
def level6rlllll : BinaryTree (List W) := .node [v76, v182, v316, v389, v500, v557, v590] level6rllllll level6rlllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllll_ok : everyKey (rowOK 5 level5) level6rlllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllllll && everyKey (rowOK 5 level5) level6rlllllr) = true
  rw [level6rllllll_ok, level6rlllllr_ok]
  decide +kernel
def level6rllllrl : BinaryTree (List W) := (.node [v76, v182, v316, v397, v500, v557, v590] (.node [v76, v182, v316, v396, v500, v557, v590] (.node [v76, v182, v316, v395, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v398, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllllrl_ok : everyKey (rowOK 5 level5) level6rllllrl = true := by decide +kernel
def level6rllllrr : BinaryTree (List W) := (.node [v76, v182, v316, v402, v500, v557, v590] (.node [v76, v182, v316, v401, v500, v557, v590] (.node [v76, v182, v316, v400, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v403, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllllrr_ok : everyKey (rowOK 5 level5) level6rllllrr = true := by decide +kernel
def level6rllllr : BinaryTree (List W) := .node [v76, v182, v316, v399, v500, v557, v590] level6rllllrl level6rllllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllllr_ok : everyKey (rowOK 5 level5) level6rllllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllllrl && everyKey (rowOK 5 level5) level6rllllrr) = true
  rw [level6rllllrl_ok, level6rllllrr_ok]
  decide +kernel
def level6rllll : BinaryTree (List W) := .node [v76, v182, v316, v394, v500, v557, v590] level6rlllll level6rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllll_ok : everyKey (rowOK 5 level5) level6rllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlllll && everyKey (rowOK 5 level5) level6rllllr) = true
  rw [level6rlllll_ok, level6rllllr_ok]
  decide +kernel
def level6rlllrll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v459, v557, v590] (.node [v76, v182, v316, v406, v500, v557, v590] (.node [v76, v182, v316, v405, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v460, v590, v638] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrll_ok : everyKey (rowOK 5 level5) level6rlllrll = true := by decide +kernel
def level6rlllrlr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v469, v557, v590] (.node [v76, v182, v316, v407, v468, v557, v590] (.node [v76, v182, v316, v407, v467, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v470, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrlr_ok : everyKey (rowOK 5 level5) level6rlllrlr = true := by decide +kernel
def level6rlllrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v465, v557, v590] level6rlllrll level6rlllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrl_ok : everyKey (rowOK 5 level5) level6rlllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlllrll && everyKey (rowOK 5 level5) level6rlllrlr) = true
  rw [level6rlllrll_ok, level6rlllrlr_ok]
  decide +kernel
def level6rlllrrl : BinaryTree (List W) := (.node [v76, v182, v316, v407, v480, v557, v590] (.node [v76, v182, v316, v407, v479, v557, v590] (.node [v76, v182, v316, v407, v474, v557, v637] .nil .nil) .nil) (.node [v76, v182, v316, v407, v481, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrrl_ok : everyKey (rowOK 5 level5) level6rlllrrl = true := by decide +kernel
def level6rlllrrr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v489, v557, v590] (.node [v76, v182, v316, v407, v487, v557, v590] (.node [v76, v182, v316, v407, v486, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v490, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrrr_ok : everyKey (rowOK 5 level5) level6rlllrrr = true := by decide +kernel
def level6rlllrr : BinaryTree (List W) := .node [v76, v182, v316, v407, v482, v557, v590] level6rlllrrl level6rlllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllrr_ok : everyKey (rowOK 5 level5) level6rlllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlllrrl && everyKey (rowOK 5 level5) level6rlllrrr) = true
  rw [level6rlllrrl_ok, level6rlllrrr_ok]
  decide +kernel
def level6rlllr : BinaryTree (List W) := .node [v76, v182, v316, v407, v471, v557, v590] level6rlllrl level6rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlllr_ok : everyKey (rowOK 5 level5) level6rlllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlllrl && everyKey (rowOK 5 level5) level6rlllrr) = true
  rw [level6rlllrl_ok, level6rlllrr_ok]
  decide +kernel
def level6rlll : BinaryTree (List W) := .node [v76, v182, v316, v404, v500, v557, v590] level6rllll level6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlll_ok : everyKey (rowOK 5 level5) level6rlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllll && everyKey (rowOK 5 level5) level6rlllr) = true
  rw [level6rllll_ok, level6rlllr_ok]
  decide +kernel
def level6rllrlll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v494, v557, v590] (.node [v76, v182, v316, v407, v493, v557, v590] (.node [v76, v182, v316, v407, v492, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v495, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrlll_ok : everyKey (rowOK 5 level5) level6rllrlll = true := by decide +kernel
def level6rllrllr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v499, v557, v590] (.node [v76, v182, v316, v407, v498, v557, v590] (.node [v76, v182, v316, v407, v497, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v540, v602] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrllr_ok : everyKey (rowOK 5 level5) level6rllrllr = true := by decide +kernel
def level6rllrll : BinaryTree (List W) := .node [v76, v182, v316, v407, v496, v557, v590] level6rllrlll level6rllrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrll_ok : everyKey (rowOK 5 level5) level6rllrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrlll && everyKey (rowOK 5 level5) level6rllrllr) = true
  rw [level6rllrlll_ok, level6rllrllr_ok]
  decide +kernel
def level6rllrlrl : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v553, v590] (.node [v76, v182, v316, v407, v500, v552, v590] (.node [v76, v182, v316, v407, v500, v546, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v555, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrlrl_ok : everyKey (rowOK 5 level5) level6rllrlrl = true := by decide +kernel
def level6rllrlrr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v557, v590] (.node [v76, v182, v316, v407, v500, v557, v589] (.node [v76, v182, v316, v407, v500, v557, v585] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v557, v591] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrlrr_ok : everyKey (rowOK 5 level5) level6rllrlrr = true := by decide +kernel
def level6rllrlr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v556, v590] level6rllrlrl level6rllrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrlr_ok : everyKey (rowOK 5 level5) level6rllrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrlrl && everyKey (rowOK 5 level5) level6rllrlrr) = true
  rw [level6rllrlrl_ok, level6rllrlrr_ok]
  decide +kernel
def level6rllrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v545, v590] level6rllrll level6rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrl_ok : everyKey (rowOK 5 level5) level6rllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrll && everyKey (rowOK 5 level5) level6rllrlr) = true
  rw [level6rllrll_ok, level6rllrlr_ok]
  decide +kernel
def level6rllrrll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v557, v606] (.node [v76, v182, v316, v407, v500, v557, v596] (.node [v76, v182, v316, v407, v500, v557, v593] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrll_ok : everyKey (rowOK 5 level5) level6rllrrll = true := by decide +kernel
def level6rllrrlr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v560, v590] (.node [v76, v182, v316, v407, v500, v559, v590] (.node [v76, v182, v316, v407, v500, v558, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v563, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrlr_ok : everyKey (rowOK 5 level5) level6rllrrlr = true := by decide +kernel
def level6rllrrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v557, v632] level6rllrrll level6rllrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrl_ok : everyKey (rowOK 5 level5) level6rllrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrrll && everyKey (rowOK 5 level5) level6rllrrlr) = true
  rw [level6rllrrll_ok, level6rllrrlr_ok]
  decide +kernel
def level6rllrrrl : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v590, v599] (.node [v76, v182, v316, v407, v500, v580, v590] (.node [v76, v182, v316, v407, v500, v575, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v590, v600] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrrl_ok : everyKey (rowOK 5 level5) level6rllrrrl = true := by decide +kernel
def level6rllrrrr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v503, v557, v590] (.node [v76, v182, v316, v407, v502, v557, v590] .nil .nil) (.node [v76, v182, v316, v407, v505, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrrr_ok : everyKey (rowOK 5 level5) level6rllrrrr = true := by decide +kernel
def level6rllrrr : BinaryTree (List W) := .node [v76, v182, v316, v407, v501, v557, v590] level6rllrrrl level6rllrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrrr_ok : everyKey (rowOK 5 level5) level6rllrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrrrl && everyKey (rowOK 5 level5) level6rllrrrr) = true
  rw [level6rllrrrl_ok, level6rllrrrr_ok]
  decide +kernel
def level6rllrr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v565, v590] level6rllrrl level6rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllrr_ok : everyKey (rowOK 5 level5) level6rllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrrl && everyKey (rowOK 5 level5) level6rllrrr) = true
  rw [level6rllrrl_ok, level6rllrrr_ok]
  decide +kernel
def level6rllr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v557, v592] level6rllrl level6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rllr_ok : everyKey (rowOK 5 level5) level6rllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rllrl && everyKey (rowOK 5 level5) level6rllrr) = true
  rw [level6rllrl_ok, level6rllrr_ok]
  decide +kernel
def level6rll : BinaryTree (List W) := .node [v76, v182, v316, v407, v491, v557, v590] level6rlll level6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rll_ok : everyKey (rowOK 5 level5) level6rll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlll && everyKey (rowOK 5 level5) level6rllr) = true
  rw [level6rlll_ok, level6rllr_ok]
  decide +kernel
def level6rlrllll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v509, v557, v590] (.node [v76, v182, v316, v407, v508, v557, v590] (.node [v76, v182, v316, v407, v507, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v510, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrllll_ok : everyKey (rowOK 5 level5) level6rlrllll = true := by decide +kernel
def level6rlrlllr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v515, v557, v590] (.node [v76, v182, v316, v407, v513, v557, v590] (.node [v76, v182, v316, v407, v512, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v516, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlllr_ok : everyKey (rowOK 5 level5) level6rlrlllr = true := by decide +kernel
def level6rlrlll : BinaryTree (List W) := .node [v76, v182, v316, v407, v511, v557, v590] level6rlrllll level6rlrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlll_ok : everyKey (rowOK 5 level5) level6rlrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrllll && everyKey (rowOK 5 level5) level6rlrlllr) = true
  rw [level6rlrllll_ok, level6rlrlllr_ok]
  decide +kernel
def level6rlrllrl : BinaryTree (List W) := (.node [v76, v182, v316, v407, v521, v557, v590] (.node [v76, v182, v316, v407, v520, v557, v590] (.node [v76, v182, v316, v407, v519, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v522, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrllrl_ok : everyKey (rowOK 5 level5) level6rlrllrl = true := by decide +kernel
def level6rlrllrr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v531, v557, v590] (.node [v76, v182, v316, v407, v525, v557, v590] (.node [v76, v182, v316, v407, v524, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v557, v584, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrllrr_ok : everyKey (rowOK 5 level5) level6rlrllrr = true := by decide +kernel
def level6rlrllr : BinaryTree (List W) := .node [v76, v182, v316, v407, v523, v557, v590] level6rlrllrl level6rlrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrllr_ok : everyKey (rowOK 5 level5) level6rlrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrllrl && everyKey (rowOK 5 level5) level6rlrllrr) = true
  rw [level6rlrllrl_ok, level6rlrllrr_ok]
  decide +kernel
def level6rlrll : BinaryTree (List W) := .node [v76, v182, v316, v407, v517, v557, v590] level6rlrlll level6rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrll_ok : everyKey (rowOK 5 level5) level6rlrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrlll && everyKey (rowOK 5 level5) level6rlrllr) = true
  rw [level6rlrlll_ok, level6rlrllr_ok]
  decide +kernel
def level6rlrlrll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v557, v590, v631] (.node [v76, v182, v316, v407, v557, v590, v630] (.node [v76, v182, v316, v407, v557, v590, v629] .nil .nil) .nil) (.node [v76, v182, v316, v407, v557, v590, v633] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrll_ok : everyKey (rowOK 5 level5) level6rlrlrll = true := by decide +kernel
def level6rlrlrlr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v557, v602, v637] (.node [v76, v182, v316, v407, v557, v590, v637] (.node [v76, v182, v316, v407, v557, v590, v635] .nil .nil) .nil) (.node [v76, v182, v316, v407, v557, v637, v647] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrlr_ok : everyKey (rowOK 5 level5) level6rlrlrlr = true := by decide +kernel
def level6rlrlrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v557, v590, v634] level6rlrlrll level6rlrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrl_ok : everyKey (rowOK 5 level5) level6rlrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrlrll && everyKey (rowOK 5 level5) level6rlrlrlr) = true
  rw [level6rlrlrll_ok, level6rlrlrlr_ok]
  decide +kernel
def level6rlrlrrl : BinaryTree (List W) := (.node [v76, v182, v316, v411, v500, v557, v590] (.node [v76, v182, v316, v410, v500, v557, v590] (.node [v76, v182, v316, v409, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v412, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrrl_ok : everyKey (rowOK 5 level5) level6rlrlrrl = true := by decide +kernel
def level6rlrlrrr : BinaryTree (List W) := (.node [v76, v182, v316, v417, v500, v557, v590] (.node [v76, v182, v316, v416, v500, v557, v590] (.node [v76, v182, v316, v414, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v418, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrrr_ok : everyKey (rowOK 5 level5) level6rlrlrrr = true := by decide +kernel
def level6rlrlrr : BinaryTree (List W) := .node [v76, v182, v316, v413, v500, v557, v590] level6rlrlrrl level6rlrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlrr_ok : everyKey (rowOK 5 level5) level6rlrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrlrrl && everyKey (rowOK 5 level5) level6rlrlrrr) = true
  rw [level6rlrlrrl_ok, level6rlrlrrr_ok]
  decide +kernel
def level6rlrlr : BinaryTree (List W) := .node [v76, v182, v316, v408, v500, v557, v590] level6rlrlrl level6rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrlr_ok : everyKey (rowOK 5 level5) level6rlrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrlrl && everyKey (rowOK 5 level5) level6rlrlrr) = true
  rw [level6rlrlrl_ok, level6rlrlrr_ok]
  decide +kernel
def level6rlrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v557, v590, v628] level6rlrll level6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrl_ok : everyKey (rowOK 5 level5) level6rlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrll && everyKey (rowOK 5 level5) level6rlrlr) = true
  rw [level6rlrll_ok, level6rlrlr_ok]
  decide +kernel
def level6rlrrlll : BinaryTree (List W) := (.node [v76, v182, v316, v422, v500, v557, v590] (.node [v76, v182, v316, v421, v500, v557, v590] (.node [v76, v182, v316, v420, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v423, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrlll_ok : everyKey (rowOK 5 level5) level6rlrrlll = true := by decide +kernel
def level6rlrrllr : BinaryTree (List W) := (.node [v76, v182, v316, v429, v500, v557, v590] (.node [v76, v182, v316, v427, v500, v557, v590] (.node [v76, v182, v316, v426, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v430, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrllr_ok : everyKey (rowOK 5 level5) level6rlrrllr = true := by decide +kernel
def level6rlrrll : BinaryTree (List W) := .node [v76, v182, v316, v425, v500, v557, v590] level6rlrrlll level6rlrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrll_ok : everyKey (rowOK 5 level5) level6rlrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrlll && everyKey (rowOK 5 level5) level6rlrrllr) = true
  rw [level6rlrrlll_ok, level6rlrrllr_ok]
  decide +kernel
def level6rlrrlrl : BinaryTree (List W) := (.node [v76, v182, v316, v436, v500, v557, v590] (.node [v76, v182, v316, v434, v500, v557, v590] (.node [v76, v182, v316, v432, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrlrl_ok : everyKey (rowOK 5 level5) level6rlrrlrl = true := by decide +kernel
def level6rlrrlrr : BinaryTree (List W) := (.node [v76, v182, v316, v442, v500, v557, v590] (.node [v76, v182, v316, v440, v500, v557, v590] (.node [v76, v182, v316, v439, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v443, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrlrr_ok : everyKey (rowOK 5 level5) level6rlrrlrr = true := by decide +kernel
def level6rlrrlr : BinaryTree (List W) := .node [v76, v182, v316, v437, v557, v590, v637] level6rlrrlrl level6rlrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrlr_ok : everyKey (rowOK 5 level5) level6rlrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrlrl && everyKey (rowOK 5 level5) level6rlrrlrr) = true
  rw [level6rlrrlrl_ok, level6rlrrlrr_ok]
  decide +kernel
def level6rlrrl : BinaryTree (List W) := .node [v76, v182, v316, v431, v500, v557, v590] level6rlrrll level6rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrl_ok : everyKey (rowOK 5 level5) level6rlrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrll && everyKey (rowOK 5 level5) level6rlrrlr) = true
  rw [level6rlrrll_ok, level6rlrrlr_ok]
  decide +kernel
def level6rlrrrll : BinaryTree (List W) := (.node [v76, v182, v316, v449, v500, v557, v590] (.node [v76, v182, v316, v447, v500, v557, v590] (.node [v76, v182, v316, v445, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v451, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrll_ok : everyKey (rowOK 5 level5) level6rlrrrll = true := by decide +kernel
def level6rlrrrlr : BinaryTree (List W) := (.node [v76, v182, v316, v461, v557, v590, v642] (.node [v76, v182, v316, v460, v557, v590, v642] (.node [v76, v182, v316, v456, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v466, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrlr_ok : everyKey (rowOK 5 level5) level6rlrrrlr = true := by decide +kernel
def level6rlrrrl : BinaryTree (List W) := .node [v76, v182, v316, v455, v500, v557, v590] level6rlrrrll level6rlrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrl_ok : everyKey (rowOK 5 level5) level6rlrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrrll && everyKey (rowOK 5 level5) level6rlrrrlr) = true
  rw [level6rlrrrll_ok, level6rlrrrlr_ok]
  decide +kernel
def level6rlrrrrl : BinaryTree (List W) := (.node [v76, v182, v316, v500, v529, v557, v590] (.node [v76, v182, v316, v500, v504, v557, v590] (.node [v76, v182, v316, v478, v557, v590, v642] .nil .nil) .nil) (.node [v76, v182, v316, v500, v531, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrrl_ok : everyKey (rowOK 5 level5) level6rlrrrrl = true := by decide +kernel
def level6rlrrrrr : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v571, v590] (.node [v76, v182, v316, v500, v557, v570, v590] .nil .nil) (.node [v76, v182, v316, v500, v557, v572, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrrr_ok : everyKey (rowOK 5 level5) level6rlrrrrr = true := by decide +kernel
def level6rlrrrr : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v569, v590] level6rlrrrrl level6rlrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrrr_ok : everyKey (rowOK 5 level5) level6rlrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrrrl && everyKey (rowOK 5 level5) level6rlrrrrr) = true
  rw [level6rlrrrrl_ok, level6rlrrrrr_ok]
  decide +kernel
def level6rlrrr : BinaryTree (List W) := .node [v76, v182, v316, v475, v557, v590, v642] level6rlrrrl level6rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrrr_ok : everyKey (rowOK 5 level5) level6rlrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrrl && everyKey (rowOK 5 level5) level6rlrrrr) = true
  rw [level6rlrrrl_ok, level6rlrrrr_ok]
  decide +kernel
def level6rlrr : BinaryTree (List W) := .node [v76, v182, v316, v444, v500, v557, v590] level6rlrrl level6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlrr_ok : everyKey (rowOK 5 level5) level6rlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrrl && everyKey (rowOK 5 level5) level6rlrrr) = true
  rw [level6rlrrl_ok, level6rlrrr_ok]
  decide +kernel
def level6rlr : BinaryTree (List W) := .node [v76, v182, v316, v419, v500, v557, v590] level6rlrl level6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rlr_ok : everyKey (rowOK 5 level5) level6rlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rlrl && everyKey (rowOK 5 level5) level6rlrr) = true
  rw [level6rlrl_ok, level6rlrr_ok]
  decide +kernel
def level6rl : BinaryTree (List W) := .node [v76, v182, v316, v407, v506, v557, v590] level6rll level6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rl_ok : everyKey (rowOK 5 level5) level6rl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rll && everyKey (rowOK 5 level5) level6rlr) = true
  rw [level6rll_ok, level6rlr_ok]
  decide +kernel
def level6rrlllll : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v584, v625] (.node [v76, v182, v316, v500, v557, v582, v590] (.node [v76, v182, v316, v500, v557, v581, v590] .nil .nil) .nil) (.node [v76, v182, v316, v500, v557, v590, v598] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlllll_ok : everyKey (rowOK 5 level5) level6rrlllll = true := by decide +kernel
def level6rrllllr : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v590, v617] (.node [v76, v182, v316, v500, v557, v590, v616] (.node [v76, v182, v316, v500, v557, v590, v613] .nil .nil) .nil) (.node [v76, v182, v316, v500, v557, v590, v618] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllllr_ok : everyKey (rowOK 5 level5) level6rrllllr = true := by decide +kernel
def level6rrllll : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v590, v605] level6rrlllll level6rrllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllll_ok : everyKey (rowOK 5 level5) level6rrllll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlllll && everyKey (rowOK 5 level5) level6rrllllr) = true
  rw [level6rrlllll_ok, level6rrllllr_ok]
  decide +kernel
def level6rrlllrl : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v590, v622] (.node [v76, v182, v316, v500, v557, v590, v621] (.node [v76, v182, v316, v500, v557, v590, v620] .nil .nil) .nil) (.node [v76, v182, v316, v500, v557, v590, v623] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlllrl_ok : everyKey (rowOK 5 level5) level6rrlllrl = true := by decide +kernel
def level6rrlllrr : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v590, v640] (.node [v76, v182, v316, v500, v557, v590, v639] (.node [v76, v182, v316, v500, v557, v590, v625] .nil .nil) .nil) (.node [v76, v182, v316, v500, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlllrr_ok : everyKey (rowOK 5 level5) level6rrlllrr = true := by decide +kernel
def level6rrlllr : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v590, v624] level6rrlllrl level6rrlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlllr_ok : everyKey (rowOK 5 level5) level6rrlllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlllrl && everyKey (rowOK 5 level5) level6rrlllrr) = true
  rw [level6rrlllrl_ok, level6rrlllrr_ok]
  decide +kernel
def level6rrlll : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v590, v619] level6rrllll level6rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlll_ok : everyKey (rowOK 5 level5) level6rrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrllll && everyKey (rowOK 5 level5) level6rrlllr) = true
  rw [level6rrllll_ok, level6rrlllr_ok]
  decide +kernel
def level6rrllrll : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v621] (.node [v76, v182, v316, v500, v557, v590, v650] (.node [v76, v182, v316, v500, v557, v590, v649] .nil .nil) .nil) (.node [v76, v182, v316, v500, v557, v625, v647] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrll_ok : everyKey (rowOK 5 level5) level6rrllrll = true := by decide +kernel
def level6rrllrlr : BinaryTree (List W) := (.node [v76, v182, v316, v531, v557, v590] (.node [v76, v182, v316, v527, v557, v590, v642] (.node [v76, v182, v316, v526, v557, v590, v642] .nil .nil) .nil) (.node [v76, v182, v316, v537, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrlr_ok : everyKey (rowOK 5 level5) level6rrllrlr = true := by decide +kernel
def level6rrllrl : BinaryTree (List W) := .node [v76, v182, v316, v518, v557, v590, v642] level6rrllrll level6rrllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrl_ok : everyKey (rowOK 5 level5) level6rrllrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrllrll && everyKey (rowOK 5 level5) level6rrllrlr) = true
  rw [level6rrllrll_ok, level6rrllrlr_ok]
  decide +kernel
def level6rrllrrl : BinaryTree (List W) := (.node [v76, v182, v317, v407, v500, v557, v590] (.node [v76, v182, v316, v557, v590, v637, v649] (.node [v76, v182, v316, v557, v590, v637, v642] .nil .nil) .nil) (.node [v76, v182, v318, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrrl_ok : everyKey (rowOK 5 level5) level6rrllrrl = true := by decide +kernel
def level6rrllrrr : BinaryTree (List W) := (.node [v76, v182, v330, v407, v500, v557, v590] (.node [v76, v182, v329, v407, v500, v557, v590] (.node [v76, v182, v328, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v332, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrrr_ok : everyKey (rowOK 5 level5) level6rrllrrr = true := by decide +kernel
def level6rrllrr : BinaryTree (List W) := .node [v76, v182, v320, v407, v500, v557, v590] level6rrllrrl level6rrllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllrr_ok : everyKey (rowOK 5 level5) level6rrllrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrllrrl && everyKey (rowOK 5 level5) level6rrllrrr) = true
  rw [level6rrllrrl_ok, level6rrllrrr_ok]
  decide +kernel
def level6rrllr : BinaryTree (List W) := .node [v76, v182, v316, v557, v590, v625, v637] level6rrllrl level6rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrllr_ok : everyKey (rowOK 5 level5) level6rrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrllrl && everyKey (rowOK 5 level5) level6rrllrr) = true
  rw [level6rrllrl_ok, level6rrllrr_ok]
  decide +kernel
def level6rrll : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v590, v643] level6rrlll level6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrll_ok : everyKey (rowOK 5 level5) level6rrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlll && everyKey (rowOK 5 level5) level6rrllr) = true
  rw [level6rrlll_ok, level6rrllr_ok]
  decide +kernel
def level6rrlrlll : BinaryTree (List W) := (.node [v76, v182, v407, v500, v550, v557, v590] (.node [v76, v182, v407, v488, v500, v557, v590] (.node [v76, v182, v336, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v407, v500, v557, v590, v611] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrlll_ok : everyKey (rowOK 5 level5) level6rrlrlll = true := by decide +kernel
def level6rrlrllr : BinaryTree (List W) := (.node [v76, v187, v316, v407, v500, v557, v590] (.node [v76, v186, v316, v407, v500, v557, v590] (.node [v76, v184, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v188, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrllr_ok : everyKey (rowOK 5 level5) level6rrlrllr = true := by decide +kernel
def level6rrlrll : BinaryTree (List W) := .node [v76, v183, v316, v407, v500, v557, v590] level6rrlrlll level6rrlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrll_ok : everyKey (rowOK 5 level5) level6rrlrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrlll && everyKey (rowOK 5 level5) level6rrlrllr) = true
  rw [level6rrlrlll_ok, level6rrlrllr_ok]
  decide +kernel
def level6rrlrlrl : BinaryTree (List W) := (.node [v76, v316, v407, v500, v557, v579, v590] (.node [v76, v316, v407, v473, v500, v557, v590] (.node [v76, v316, v339, v407, v500, v557, v590] .nil .nil) .nil) (.node [v77, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrlrl_ok : everyKey (rowOK 5 level5) level6rrlrlrl = true := by decide +kernel
def level6rrlrlrr : BinaryTree (List W) := (.node [v82, v182, v316, v407, v500, v557, v590] (.node [v81, v182, v316, v407, v500, v557, v590] (.node [v80, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v83, v118, v245, v407, v500, v557, v647] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrlrr_ok : everyKey (rowOK 5 level5) level6rrlrlrr = true := by decide +kernel
def level6rrlrlr : BinaryTree (List W) := .node [v79, v182, v316, v407, v500, v557, v590] level6rrlrlrl level6rrlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrlr_ok : everyKey (rowOK 5 level5) level6rrlrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrlrl && everyKey (rowOK 5 level5) level6rrlrlrr) = true
  rw [level6rrlrlrl_ok, level6rrlrlrr_ok]
  decide +kernel
def level6rrlrl : BinaryTree (List W) := .node [v76, v316, v338, v407, v500, v557, v590] level6rrlrll level6rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrl_ok : everyKey (rowOK 5 level5) level6rrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrll && everyKey (rowOK 5 level5) level6rrlrlr) = true
  rw [level6rrlrll_ok, level6rrlrlr_ok]
  decide +kernel
def level6rrlrrll : BinaryTree (List W) := (.node [v89, v118, v182, v245, v500, v557, v590] (.node [v85, v182, v316, v407, v500, v557, v590] (.node [v84, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v89, v118, v182, v245, v557, v590, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrll_ok : everyKey (rowOK 5 level5) level6rrlrrll = true := by decide +kernel
def level6rrlrrlr : BinaryTree (List W) := (.node [v118, v133, v245, v407, v500, v557, v590] (.node [v96, v182, v201, v245, v500, v557, v590] (.node [v96, v182, v193, v245, v500, v557, v590] .nil .nil) .nil) (.node [v118, v158, v182, v193, v245, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrlr_ok : everyKey (rowOK 5 level5) level6rrlrrlr = true := by decide +kernel
def level6rrlrrl : BinaryTree (List W) := .node [v90, v118, v182, v245, v500, v557, v590] level6rrlrrll level6rrlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrl_ok : everyKey (rowOK 5 level5) level6rrlrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrrll && everyKey (rowOK 5 level5) level6rrlrrlr) = true
  rw [level6rrlrrll_ok, level6rrlrrlr_ok]
  decide +kernel
def level6rrlrrrl : BinaryTree (List W) := (.node [v118, v182, v192, v245, v500, v557, v590] (.node [v118, v173, v197, v245, v500, v557, v590] (.node [v118, v164, v182, v335, v407, v557, v590] .nil .nil) .nil) (.node [v118, v182, v193, v211, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrrl_ok : everyKey (rowOK 5 level5) level6rrlrrrl = true := by decide +kernel
def level6rrlrrrr : BinaryTree (List W) := (.node [v118, v182, v193, v245, v500, v546, v590] (.node [v118, v182, v193, v245, v482, v557, v590] .nil .nil) (.node [v118, v182, v193, v245, v500, v557, v585] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrrr_ok : everyKey (rowOK 5 level5) level6rrlrrrr = true := by decide +kernel
def level6rrlrrr : BinaryTree (List W) := .node [v118, v182, v193, v219, v500, v557, v590] level6rrlrrrl level6rrlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrrr_ok : everyKey (rowOK 5 level5) level6rrlrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrrrl && everyKey (rowOK 5 level5) level6rrlrrrr) = true
  rw [level6rrlrrrl_ok, level6rrlrrrr_ok]
  decide +kernel
def level6rrlrr : BinaryTree (List W) := .node [v118, v158, v182, v201, v245, v557, v590] level6rrlrrl level6rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlrr_ok : everyKey (rowOK 5 level5) level6rrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrrl && everyKey (rowOK 5 level5) level6rrlrrr) = true
  rw [level6rrlrrl_ok, level6rrlrrr_ok]
  decide +kernel
def level6rrlr : BinaryTree (List W) := .node [v83, v182, v316, v407, v500, v557, v590] level6rrlrl level6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrlr_ok : everyKey (rowOK 5 level5) level6rrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrlrl && everyKey (rowOK 5 level5) level6rrlrr) = true
  rw [level6rrlrl_ok, level6rrlrr_ok]
  decide +kernel
def level6rrl : BinaryTree (List W) := .node [v76, v182, v333, v407, v500, v557, v590] level6rrll level6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrl_ok : everyKey (rowOK 5 level5) level6rrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrll && everyKey (rowOK 5 level5) level6rrlr) = true
  rw [level6rrll_ok, level6rrlr_ok]
  decide +kernel
def level6rrrllll : BinaryTree (List W) := (.node [v118, v182, v193, v245, v531, v557, v590] (.node [v118, v182, v193, v245, v500, v575, v590] (.node [v118, v182, v193, v245, v500, v557, v621] .nil .nil) .nil) (.node [v118, v182, v193, v245, v557, v590, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrllll_ok : everyKey (rowOK 5 level5) level6rrrllll = true := by decide +kernel
def level6rrrlllr : BinaryTree (List W) := (.node [v118, v182, v195, v245, v500, v557, v590] (.node [v118, v182, v194, v245, v500, v557, v590] (.node [v118, v182, v193, v319, v500, v557, v590] .nil .nil) .nil) (.node [v118, v182, v196, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlllr_ok : everyKey (rowOK 5 level5) level6rrrlllr = true := by decide +kernel
def level6rrrlll : BinaryTree (List W) := .node [v118, v182, v193, v316, v500, v557, v590] level6rrrllll level6rrrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlll_ok : everyKey (rowOK 5 level5) level6rrrlll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrllll && everyKey (rowOK 5 level5) level6rrrlllr) = true
  rw [level6rrrllll_ok, level6rrrlllr_ok]
  decide +kernel
def level6rrrllrl : BinaryTree (List W) := (.node [v118, v182, v201, v245, v500, v557, v590] (.node [v118, v182, v201, v211, v500, v557, v590] (.node [v118, v182, v200, v245, v500, v557, v586] .nil .nil) .nil) (.node [v118, v182, v201, v245, v557, v590, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrllrl_ok : everyKey (rowOK 5 level5) level6rrrllrl = true := by decide +kernel
def level6rrrllrr : BinaryTree (List W) := (.node [v118, v182, v205, v245, v500, v557, v590] (.node [v118, v182, v203, v245, v500, v557, v590] (.node [v118, v182, v202, v245, v500, v557, v590] .nil .nil) .nil) (.node [v118, v182, v206, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrllrr_ok : everyKey (rowOK 5 level5) level6rrrllrr = true := by decide +kernel
def level6rrrllr : BinaryTree (List W) := .node [v118, v182, v201, v316, v500, v557, v590] level6rrrllrl level6rrrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrllr_ok : everyKey (rowOK 5 level5) level6rrrllr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrllrl && everyKey (rowOK 5 level5) level6rrrllrr) = true
  rw [level6rrrllrl_ok, level6rrrllrr_ok]
  decide +kernel
def level6rrrll : BinaryTree (List W) := .node [v118, v182, v198, v245, v500, v557, v590] level6rrrlll level6rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrll_ok : everyKey (rowOK 5 level5) level6rrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrlll && everyKey (rowOK 5 level5) level6rrrllr) = true
  rw [level6rrrlll_ok, level6rrrllr_ok]
  decide +kernel
def level6rrrlrll : BinaryTree (List W) := (.node [v118, v182, v245, v424, v500, v557, v590] (.node [v118, v182, v245, v407, v500, v564, v590] (.node [v118, v182, v245, v407, v500, v557, v607] .nil .nil) .nil) (.node [v118, v182, v245, v433, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrll_ok : everyKey (rowOK 5 level5) level6rrrlrll = true := by decide +kernel
def level6rrrlrlr : BinaryTree (List W) := (.node [v118, v182, v258, v437, v500, v557, v590] (.node [v118, v182, v245, v500, v557, v587, v590] (.node [v118, v182, v245, v437, v500, v559, v590] .nil .nil) .nil) (.node [v118, v182, v265, v407, v526, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrlr_ok : everyKey (rowOK 5 level5) level6rrrlrlr = true := by decide +kernel
def level6rrrlrl : BinaryTree (List W) := .node [v118, v182, v245, v435, v500, v557, v590] level6rrrlrll level6rrrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrl_ok : everyKey (rowOK 5 level5) level6rrrlrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrlrll && everyKey (rowOK 5 level5) level6rrrlrlr) = true
  rw [level6rrrlrll_ok, level6rrrlrlr_ok]
  decide +kernel
def level6rrrlrrl : BinaryTree (List W) := (.node [v118, v182, v274, v407, v510, v557, v590] (.node [v118, v182, v273, v407, v514, v557, v590] (.node [v118, v182, v272, v407, v500, v557, v590] .nil .nil) .nil) (.node [v118, v186, v245, v407, v500, v557, v608] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrrl_ok : everyKey (rowOK 5 level5) level6rrrlrrl = true := by decide +kernel
def level6rrrlrrr : BinaryTree (List W) := (.node [v124, v182, v274, v407, v500, v557, v590] (.node [v121, v182, v245, v437, v500, v557, v590] (.node [v118, v197, v245, v407, v500, v557, v606] .nil .nil) .nil) (.node [v135, v182, v193, v316, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrrr_ok : everyKey (rowOK 5 level5) level6rrrlrrr = true := by decide +kernel
def level6rrrlrr : BinaryTree (List W) := .node [v118, v186, v245, v437, v500, v557, v590] level6rrrlrrl level6rrrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlrr_ok : everyKey (rowOK 5 level5) level6rrrlrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrlrrl && everyKey (rowOK 5 level5) level6rrrlrrr) = true
  rw [level6rrrlrrl_ok, level6rrrlrrr_ok]
  decide +kernel
def level6rrrlr : BinaryTree (List W) := .node [v118, v182, v267, v437, v500, v557, v590] level6rrrlrl level6rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrlr_ok : everyKey (rowOK 5 level5) level6rrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrlrl && everyKey (rowOK 5 level5) level6rrrlrr) = true
  rw [level6rrrlrl_ok, level6rrrlrr_ok]
  decide +kernel
def level6rrrl : BinaryTree (List W) := .node [v118, v182, v245, v407, v485, v557, v590] level6rrrll level6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrl_ok : everyKey (rowOK 5 level5) level6rrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrll && everyKey (rowOK 5 level5) level6rrrlr) = true
  rw [level6rrrll_ok, level6rrrlr_ok]
  decide +kernel
def level6rrrrlll : BinaryTree (List W) := (.node [v155, v182, v245, v437, v500, v557, v590] (.node [v150, v182, v245, v407, v500, v557, v590] (.node [v143, v182, v201, v316, v500, v557, v590] .nil .nil) .nil) (.node [v158, v164, v182, v316, v407, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrlll_ok : everyKey (rowOK 5 level5) level6rrrrlll = true := by decide +kernel
def level6rrrrllr : BinaryTree (List W) := (.node [v164, v166, v182, v245, v407, v557, v590] (.node [v163, v182, v316, v407, v500, v557, v590] (.node [v163, v182, v245, v407, v518, v557, v590] .nil .nil) .nil) (.node [v164, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrllr_ok : everyKey (rowOK 5 level5) level6rrrrllr = true := by decide +kernel
def level6rrrrll : BinaryTree (List W) := .node [v162, v182, v316, v407, v500, v557, v590] level6rrrrlll level6rrrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrll_ok : everyKey (rowOK 5 level5) level6rrrrll = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrlll && everyKey (rowOK 5 level5) level6rrrrllr) = true
  rw [level6rrrrlll_ok, level6rrrrllr_ok]
  decide +kernel
def level6rrrrlrl : BinaryTree (List W) := (.node [v168, v182, v260, v407, v500, v557, v590] (.node [v168, v182, v245, v407, v505, v557, v590] (.node [v167, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v168, v182, v316, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrlrl_ok : everyKey (rowOK 5 level5) level6rrrrlrl = true := by decide +kernel
def level6rrrrlrr : BinaryTree (List W) := (.node [v182, v193, v316, v500, v557, v590] (.node [v182, v193, v316, v407, v500, v557, v590] (.node [v182, v193, v245, v316, v500, v557, v590] .nil .nil) .nil) (.node [v182, v197, v316, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrlrr_ok : everyKey (rowOK 5 level5) level6rrrrlrr = true := by decide +kernel
def level6rrrrlr : BinaryTree (List W) := .node [v169, v182, v316, v407, v500, v557, v590] level6rrrrlrl level6rrrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrlr_ok : everyKey (rowOK 5 level5) level6rrrrlr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrlrl && everyKey (rowOK 5 level5) level6rrrrlrr) = true
  rw [level6rrrrlrl_ok, level6rrrrlrr_ok]
  decide +kernel
def level6rrrrl : BinaryTree (List W) := .node [v165, v182, v245, v407, v514, v557, v590] level6rrrrll level6rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrl_ok : everyKey (rowOK 5 level5) level6rrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrll && everyKey (rowOK 5 level5) level6rrrrlr) = true
  rw [level6rrrrll_ok, level6rrrrlr_ok]
  decide +kernel
def level6rrrrrll : BinaryTree (List W) := (.node [v182, v265, v316, v407, v500, v557, v590] (.node [v182, v201, v316, v500, v557, v590] (.node [v182, v201, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v182, v268, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrll_ok : everyKey (rowOK 5 level5) level6rrrrrll = true := by decide +kernel
def level6rrrrrlr : BinaryTree (List W) := (.node [v182, v274, v316, v437, v500, v557, v590] (.node [v182, v271, v316, v407, v500, v557, v590] (.node [v182, v270, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v182, v316, v326, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrlr_ok : everyKey (rowOK 5 level5) level6rrrrrlr = true := by decide +kernel
def level6rrrrrl : BinaryTree (List W) := .node [v182, v269, v316, v407, v500, v557, v590] level6rrrrrll level6rrrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrl_ok : everyKey (rowOK 5 level5) level6rrrrrl = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrrll && everyKey (rowOK 5 level5) level6rrrrrlr) = true
  rw [level6rrrrrll_ok, level6rrrrrlr_ok]
  decide +kernel
def level6rrrrrrl : BinaryTree (List W) := (.node [v182, v316, v407, v463, v500, v557, v590] (.node [v182, v316, v377, v437, v500, v557, v590] (.node [v182, v316, v376, v407, v500, v557, v590] .nil .nil) .nil) (.node [v182, v316, v407, v500, v557, v561, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrrl_ok : everyKey (rowOK 5 level5) level6rrrrrrl = true := by decide +kernel
def level6rrrrrrr : BinaryTree (List W) := (.node [v182, v316, v437, v500, v557, v566, v590] (.node [v182, v316, v407, v500, v557, v590, v614] .nil .nil) (.node [v182, v316, v437, v500, v557, v586, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrrr_ok : everyKey (rowOK 5 level5) level6rrrrrrr = true := by decide +kernel
def level6rrrrrr : BinaryTree (List W) := .node [v182, v316, v407, v500, v557, v562, v590] level6rrrrrrl level6rrrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrrr_ok : everyKey (rowOK 5 level5) level6rrrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrrrl && everyKey (rowOK 5 level5) level6rrrrrrr) = true
  rw [level6rrrrrrl_ok, level6rrrrrrr_ok]
  decide +kernel
def level6rrrrr : BinaryTree (List W) := .node [v182, v316, v334, v437, v500, v557, v590] level6rrrrrl level6rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrrr_ok : everyKey (rowOK 5 level5) level6rrrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrrl && everyKey (rowOK 5 level5) level6rrrrrr) = true
  rw [level6rrrrrl_ok, level6rrrrrr_ok]
  decide +kernel
def level6rrrr : BinaryTree (List W) := .node [v182, v201, v245, v316, v500, v557, v590] level6rrrrl level6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrrr_ok : everyKey (rowOK 5 level5) level6rrrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrrl && everyKey (rowOK 5 level5) level6rrrrr) = true
  rw [level6rrrrl_ok, level6rrrrr_ok]
  decide +kernel
def level6rrr : BinaryTree (List W) := .node [v140, v182, v193, v245, v500, v557, v590] level6rrrl level6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rrr_ok : everyKey (rowOK 5 level5) level6rrr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrrl && everyKey (rowOK 5 level5) level6rrrr) = true
  rw [level6rrrl_ok, level6rrrr_ok]
  decide +kernel
def level6rr : BinaryTree (List W) := .node [v118, v182, v193, v245, v500, v557, v590] level6rrl level6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6rr_ok : everyKey (rowOK 5 level5) level6rr = true := by
  change (_ && everyKey (rowOK 5 level5) level6rrl && everyKey (rowOK 5 level5) level6rrr) = true
  rw [level6rrl_ok, level6rrr_ok]
  decide +kernel
def level6r : BinaryTree (List W) := .node [v76, v182, v316, v500, v557, v576, v590] level6rl level6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6r_ok : everyKey (rowOK 5 level5) level6r = true := by
  change (_ && everyKey (rowOK 5 level5) level6rl && everyKey (rowOK 5 level5) level6rr) = true
  rw [level6rl_ok, level6rr_ok]
  decide +kernel
def level6 : BinaryTree (List W) := .node [v76, v182, v316, v383, v500, v557, v590] level6l level6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  change (_ && everyKey (rowOK 5 level5) level6l && everyKey (rowOK 5 level5) level6r) = true
  rw [level6l_ok, level6r_ok]
  decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
def level7lllllll : BinaryTree (List W) := (.node [v2, v76, v182, v245, v407, v500, v557, v610] (.node [v1, v76, v118, v182, v245, v500, v557, v590] (.node [v0, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v3, v76, v182, v245, v368, v500, v557, v590] (.node [v2, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllllll_ok : everyKey (rowOK 6 level6) level7lllllll = true := by decide +kernel
def level7llllllr : BinaryTree (List W) := (.node [v5, v76, v87, v245, v407, v500, v557, v590] (.node [v4, v76, v182, v316, v407, v500, v557, v590] (.node [v4, v76, v182, v245, v407, v500, v574, v590] .nil .nil) .nil) (.node [v5, v76, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllllr_ok : everyKey (rowOK 6 level6) level7llllllr = true := by decide +kernel
def level7llllll : BinaryTree (List W) := .node [v3, v76, v182, v316, v407, v500, v557, v590] level7lllllll level7llllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllll_ok : everyKey (rowOK 6 level6) level7llllll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllllll && everyKey (rowOK 6 level6) level7llllllr) = true
  rw [level7lllllll_ok, level7llllllr_ok]
  decide +kernel
def level7lllllrl : BinaryTree (List W) := (.node [v8, v76, v182, v245, v407, v500, v557, v590] (.node [v8, v76, v135, v182, v245, v500, v557, v590] (.node [v7, v76, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v10, v76, v182, v316, v407, v500, v557, v590] (.node [v9, v76, v118, v182, v245, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllllrl_ok : everyKey (rowOK 6 level6) level7lllllrl = true := by decide +kernel
def level7lllllrr : BinaryTree (List W) := (.node [v11, v76, v182, v316, v407, v500, v557, v590] (.node [v11, v76, v118, v245, v407, v500, v557, v647] (.node [v10, v118, v182, v245, v437, v500, v557, v590] .nil .nil) .nil) (.node [v12, v76, v118, v182, v407, v500, v590, v604] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllllrr_ok : everyKey (rowOK 6 level6) level7lllllrr = true := by decide +kernel
def level7lllllr : BinaryTree (List W) := .node [v10, v118, v182, v245, v407, v500, v557, v608] level7lllllrl level7lllllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllllr_ok : everyKey (rowOK 6 level6) level7lllllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllllrl && everyKey (rowOK 6 level6) level7lllllrr) = true
  rw [level7lllllrl_ok, level7lllllrr_ok]
  decide +kernel
def level7lllll : BinaryTree (List W) := .node [v6, v76, v182, v245, v407, v500, v557, v590] level7llllll level7lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllll_ok : everyKey (rowOK 6 level6) level7lllll = true := by
  change (_ && everyKey (rowOK 6 level6) level7llllll && everyKey (rowOK 6 level6) level7lllllr) = true
  rw [level7llllll_ok, level7lllllr_ok]
  decide +kernel
def level7llllrll : BinaryTree (List W) := (.node [v14, v118, v182, v274, v407, v500, v557, v590] (.node [v14, v76, v182, v316, v407, v500, v557, v590] (.node [v13, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v15, v118, v182, v245, v407, v484, v557, v590] (.node [v15, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllrll_ok : everyKey (rowOK 6 level6) level7llllrll = true := by decide +kernel
def level7llllrlr : BinaryTree (List W) := (.node [v17, v76, v182, v316, v407, v500, v557, v590] (.node [v17, v76, v118, v340, v407, v500, v557, v590] (.node [v16, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v18, v76, v118, v182, v446, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllrlr_ok : everyKey (rowOK 6 level6) level7llllrlr = true := by decide +kernel
def level7llllrl : BinaryTree (List W) := .node [v16, v118, v158, v182, v245, v407, v557, v590] level7llllrll level7llllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllrl_ok : everyKey (rowOK 6 level6) level7llllrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7llllrll && everyKey (rowOK 6 level6) level7llllrlr) = true
  rw [level7llllrll_ok, level7llllrlr_ok]
  decide +kernel
def level7llllrrl : BinaryTree (List W) := (.node [v20, v76, v182, v316, v407, v500, v557, v590] (.node [v20, v76, v182, v245, v407, v478, v557, v590] (.node [v19, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v21, v76, v158, v182, v245, v407, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllrrl_ok : everyKey (rowOK 6 level6) level7llllrrl = true := by decide +kernel
def level7llllrrr : BinaryTree (List W) := (.node [v23, v76, v182, v316, v407, v500, v557, v590] (.node [v23, v76, v118, v182, v407, v500, v542, v557] (.node [v22, v76, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v24, v76, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllrrr_ok : everyKey (rowOK 6 level6) level7llllrrr = true := by decide +kernel
def level7llllrr : BinaryTree (List W) := .node [v21, v76, v182, v245, v407, v500, v557, v590] level7llllrrl level7llllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllrr_ok : everyKey (rowOK 6 level6) level7llllrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llllrrl && everyKey (rowOK 6 level6) level7llllrrr) = true
  rw [level7llllrrl_ok, level7llllrrr_ok]
  decide +kernel
def level7llllr : BinaryTree (List W) := .node [v18, v76, v182, v316, v407, v500, v557, v590] level7llllrl level7llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llllr_ok : everyKey (rowOK 6 level6) level7llllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llllrl && everyKey (rowOK 6 level6) level7llllrr) = true
  rw [level7llllrl_ok, level7llllrr_ok]
  decide +kernel
def level7llll : BinaryTree (List W) := .node [v12, v76, v182, v316, v407, v500, v557, v590] level7lllll level7llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llll_ok : everyKey (rowOK 6 level6) level7llll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllll && everyKey (rowOK 6 level6) level7llllr) = true
  rw [level7lllll_ok, level7llllr_ok]
  decide +kernel
def level7lllrlll : BinaryTree (List W) := (.node [v25, v118, v182, v245, v437, v500, v557, v590] (.node [v25, v118, v131, v245, v407, v500, v557, v590] (.node [v25, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v27, v76, v118, v182, v407, v466, v557, v590] (.node [v26, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrlll_ok : everyKey (rowOK 6 level6) level7lllrlll = true := by decide +kernel
def level7lllrllr : BinaryTree (List W) := (.node [v30, v76, v182, v316, v407, v500, v557, v590] (.node [v29, v76, v182, v316, v407, v500, v557, v590] (.node [v28, v76, v118, v182, v407, v500, v557, v590] .nil .nil) .nil) (.node [v30, v168, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrllr_ok : everyKey (rowOK 6 level6) level7lllrllr = true := by decide +kernel
def level7lllrll : BinaryTree (List W) := .node [v27, v76, v182, v316, v407, v500, v557, v590] level7lllrlll level7lllrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrll_ok : everyKey (rowOK 6 level6) level7lllrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrlll && everyKey (rowOK 6 level6) level7lllrllr) = true
  rw [level7lllrlll_ok, level7lllrllr_ok]
  decide +kernel
def level7lllrlrl : BinaryTree (List W) := (.node [v33, v76, v118, v245, v407, v500, v583, v590] (.node [v32, v76, v182, v316, v407, v500, v557, v590] (.node [v31, v118, v182, v245, v437, v500, v557, v590] .nil .nil) .nil) (.node [v33, v76, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrlrl_ok : everyKey (rowOK 6 level6) level7lllrlrl = true := by decide +kernel
def level7lllrlrr : BinaryTree (List W) := (.node [v36, v76, v118, v245, v407, v475, v557, v590] (.node [v35, v76, v118, v182, v245, v500, v557, v590] (.node [v34, v76, v118, v182, v245, v557, v590, v637] .nil .nil) .nil) (.node [v36, v76, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrlrr_ok : everyKey (rowOK 6 level6) level7lllrlrr = true := by decide +kernel
def level7lllrlr : BinaryTree (List W) := .node [v34, v76, v118, v182, v245, v500, v557, v590] level7lllrlrl level7lllrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrlr_ok : everyKey (rowOK 6 level6) level7lllrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrlrl && everyKey (rowOK 6 level6) level7lllrlrr) = true
  rw [level7lllrlrl_ok, level7lllrlrr_ok]
  decide +kernel
def level7lllrl : BinaryTree (List W) := .node [v31, v76, v182, v316, v407, v500, v557, v590] level7lllrll level7lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrl_ok : everyKey (rowOK 6 level6) level7lllrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrll && everyKey (rowOK 6 level6) level7lllrlr) = true
  rw [level7lllrll_ok, level7lllrlr_ok]
  decide +kernel
def level7lllrrll : BinaryTree (List W) := (.node [v39, v76, v96, v182, v245, v500, v557, v590] (.node [v38, v76, v118, v182, v245, v500, v557, v590] (.node [v37, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v39, v76, v118, v158, v182, v245, v557, v590] (.node [v39, v76, v118, v135, v245, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrrll_ok : everyKey (rowOK 6 level6) level7lllrrll = true := by decide +kernel
def level7lllrrlr : BinaryTree (List W) := (.node [v39, v76, v118, v182, v316, v500, v557, v590] (.node [v39, v76, v118, v182, v245, v557, v590, v637] (.node [v39, v76, v118, v182, v245, v500, v557, v590] .nil .nil) .nil) (.node [v39, v76, v118, v245, v365, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrrlr_ok : everyKey (rowOK 6 level6) level7lllrrlr = true := by decide +kernel
def level7lllrrl : BinaryTree (List W) := .node [v39, v76, v118, v182, v211, v500, v557, v590] level7lllrrll level7lllrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrrl_ok : everyKey (rowOK 6 level6) level7lllrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrrll && everyKey (rowOK 6 level6) level7lllrrlr) = true
  rw [level7lllrrll_ok, level7lllrrlr_ok]
  decide +kernel
def level7lllrrrl : BinaryTree (List W) := (.node [v40, v76, v118, v182, v245, v500, v557, v590] (.node [v39, v76, v182, v316, v500, v557, v590] (.node [v39, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v41, v76, v118, v182, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrrrl_ok : everyKey (rowOK 6 level6) level7lllrrrl = true := by decide +kernel
def level7lllrrrr : BinaryTree (List W) := (.node [v45, v76, v118, v182, v245, v500, v557, v590] (.node [v44, v118, v182, v245, v377, v500, v557, v590] (.node [v44, v76, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v46, v76, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrrrr_ok : everyKey (rowOK 6 level6) level7lllrrrr = true := by decide +kernel
def level7lllrrr : BinaryTree (List W) := .node [v42, v76, v182, v316, v407, v500, v557, v590] level7lllrrrl level7lllrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrrr_ok : everyKey (rowOK 6 level6) level7lllrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrrrl && everyKey (rowOK 6 level6) level7lllrrrr) = true
  rw [level7lllrrrl_ok, level7lllrrrr_ok]
  decide +kernel
def level7lllrr : BinaryTree (List W) := .node [v39, v76, v182, v245, v316, v500, v557, v590] level7lllrrl level7lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllrr_ok : everyKey (rowOK 6 level6) level7lllrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrrl && everyKey (rowOK 6 level6) level7lllrrr) = true
  rw [level7lllrrl_ok, level7lllrrr_ok]
  decide +kernel
def level7lllr : BinaryTree (List W) := .node [v37, v76, v118, v182, v210, v245, v407, v500] level7lllrl level7lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lllr_ok : everyKey (rowOK 6 level6) level7lllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lllrl && everyKey (rowOK 6 level6) level7lllrr) = true
  rw [level7lllrl_ok, level7lllrr_ok]
  decide +kernel
def level7lll : BinaryTree (List W) := .node [v24, v118, v182, v245, v407, v500, v566, v590] level7llll level7lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lll_ok : everyKey (rowOK 6 level6) level7lll = true := by
  change (_ && everyKey (rowOK 6 level6) level7llll && everyKey (rowOK 6 level6) level7lllr) = true
  rw [level7llll_ok, level7lllr_ok]
  decide +kernel
def level7llrllll : BinaryTree (List W) := (.node [v47, v118, v182, v245, v407, v500, v557, v590] (.node [v47, v118, v143, v182, v245, v500, v557, v590] (.node [v46, v118, v182, v245, v437, v500, v557, v590] .nil .nil) .nil) (.node [v48, v118, v182, v245, v407, v500, v557, v590] (.node [v48, v118, v135, v182, v245, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrllll_ok : everyKey (rowOK 6 level6) level7llrllll = true := by decide +kernel
def level7llrlllr : BinaryTree (List W) := (.node [v53, v118, v197, v245, v407, v500, v557, v590] (.node [v53, v76, v182, v316, v407, v500, v557, v590] (.node [v52, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v54, v76, v118, v182, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlllr_ok : everyKey (rowOK 6 level6) level7llrlllr = true := by decide +kernel
def level7llrlll : BinaryTree (List W) := .node [v50, v118, v182, v245, v407, v500, v557, v590] level7llrllll level7llrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlll_ok : everyKey (rowOK 6 level6) level7llrlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrllll && everyKey (rowOK 6 level6) level7llrlllr) = true
  rw [level7llrllll_ok, level7llrlllr_ok]
  decide +kernel
def level7llrllrl : BinaryTree (List W) := (.node [v56, v118, v182, v245, v407, v500, v557, v590] (.node [v55, v118, v182, v245, v437, v500, v557, v590] (.node [v55, v118, v182, v245, v407, v500, v547, v590] .nil .nil) .nil) (.node [v58, v118, v182, v245, v407, v500, v557, v590] (.node [v57, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrllrl_ok : everyKey (rowOK 6 level6) level7llrllrl = true := by decide +kernel
def level7llrllrr : BinaryTree (List W) := (.node [v60, v118, v182, v228, v407, v500, v557, v590] (.node [v60, v76, v182, v316, v407, v500, v557, v590] (.node [v59, v118, v182, v245, v407, v514, v557, v590] .nil .nil) .nil) (.node [v60, v118, v182, v245, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrllrr_ok : everyKey (rowOK 6 level6) level7llrllrr = true := by decide +kernel
def level7llrllr : BinaryTree (List W) := .node [v59, v76, v182, v316, v407, v500, v557, v590] level7llrllrl level7llrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrllr_ok : everyKey (rowOK 6 level6) level7llrllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrllrl && everyKey (rowOK 6 level6) level7llrllrr) = true
  rw [level7llrllrl_ok, level7llrllrr_ok]
  decide +kernel
def level7llrll : BinaryTree (List W) := .node [v55, v76, v182, v316, v407, v500, v557, v590] level7llrlll level7llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrll_ok : everyKey (rowOK 6 level6) level7llrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrlll && everyKey (rowOK 6 level6) level7llrllr) = true
  rw [level7llrlll_ok, level7llrllr_ok]
  decide +kernel
def level7llrlrll : BinaryTree (List W) := (.node [v65, v118, v182, v245, v407, v500, v557, v586] (.node [v65, v76, v182, v316, v407, v500, v557, v590] (.node [v64, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v67, v118, v182, v245, v407, v500, v557, v590] (.node [v66, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlrll_ok : everyKey (rowOK 6 level6) level7llrlrll = true := by decide +kernel
def level7llrlrlr : BinaryTree (List W) := (.node [v71, v118, v182, v245, v407, v500, v557, v590] (.node [v70, v118, v182, v245, v407, v500, v557, v590] (.node [v69, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v73, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlrlr_ok : everyKey (rowOK 6 level6) level7llrlrlr = true := by decide +kernel
def level7llrlrl : BinaryTree (List W) := .node [v68, v118, v182, v245, v407, v500, v557, v590] level7llrlrll level7llrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlrl_ok : everyKey (rowOK 6 level6) level7llrlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrlrll && everyKey (rowOK 6 level6) level7llrlrlr) = true
  rw [level7llrlrll_ok, level7llrlrlr_ok]
  decide +kernel
def level7llrlrrl : BinaryTree (List W) := (.node [v76, v86, v182, v316, v407, v500, v557, v590] (.node [v76, v78, v118, v182, v245, v500, v557, v590] (.node [v75, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v87, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlrrl_ok : everyKey (rowOK 6 level6) level7llrlrrl = true := by decide +kernel
def level7llrlrrr : BinaryTree (List W) := (.node [v76, v94, v182, v245, v407, v500, v557, v590] (.node [v76, v93, v182, v245, v407, v500, v557, v590] (.node [v76, v92, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v95, v182, v245, v407, v518, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlrrr_ok : everyKey (rowOK 6 level6) level7llrlrrr = true := by decide +kernel
def level7llrlrr : BinaryTree (List W) := .node [v76, v91, v182, v316, v407, v500, v557, v590] level7llrlrrl level7llrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlrr_ok : everyKey (rowOK 6 level6) level7llrlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrlrrl && everyKey (rowOK 6 level6) level7llrlrrr) = true
  rw [level7llrlrrl_ok, level7llrlrrr_ok]
  decide +kernel
def level7llrlr : BinaryTree (List W) := .node [v74, v118, v182, v245, v407, v500, v557, v590] level7llrlrl level7llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrlr_ok : everyKey (rowOK 6 level6) level7llrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrlrl && everyKey (rowOK 6 level6) level7llrlrr) = true
  rw [level7llrlrl_ok, level7llrlrr_ok]
  decide +kernel
def level7llrl : BinaryTree (List W) := .node [v62, v118, v182, v245, v407, v500, v557, v590] level7llrll level7llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrl_ok : everyKey (rowOK 6 level6) level7llrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrll && everyKey (rowOK 6 level6) level7llrlr) = true
  rw [level7llrll_ok, level7llrlr_ok]
  decide +kernel
def level7llrrlll : BinaryTree (List W) := (.node [v76, v96, v158, v182, v245, v407, v557, v590] (.node [v76, v96, v143, v182, v245, v500, v557, v590] (.node [v76, v96, v135, v182, v245, v500, v557, v590] .nil .nil) .nil) (.node [v76, v96, v182, v245, v349, v500, v557, v590] (.node [v76, v96, v182, v211, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrlll_ok : everyKey (rowOK 6 level6) level7llrrlll = true := by decide +kernel
def level7llrrllr : BinaryTree (List W) := (.node [v76, v96, v182, v245, v437, v500, v557, v590] (.node [v76, v96, v182, v245, v407, v557, v590, v637] (.node [v76, v96, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v96, v182, v245, v500, v557, v590, v625] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrllr_ok : everyKey (rowOK 6 level6) level7llrrllr = true := by decide +kernel
def level7llrrll : BinaryTree (List W) := .node [v76, v96, v182, v245, v377, v500, v557, v590] level7llrrlll level7llrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrll_ok : everyKey (rowOK 6 level6) level7llrrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrlll && everyKey (rowOK 6 level6) level7llrrllr) = true
  rw [level7llrrlll_ok, level7llrrllr_ok]
  decide +kernel
def level7llrrlrl : BinaryTree (List W) := (.node [v76, v98, v182, v245, v407, v500, v557, v590] (.node [v76, v97, v182, v245, v407, v500, v557, v590] (.node [v76, v96, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v99, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrlrl_ok : everyKey (rowOK 6 level6) level7llrrlrl = true := by decide +kernel
def level7llrrlrr : BinaryTree (List W) := (.node [v76, v103, v182, v316, v407, v500, v557, v590] (.node [v76, v102, v182, v245, v407, v500, v557, v590] (.node [v76, v101, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v103, v185, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrlrr_ok : everyKey (rowOK 6 level6) level7llrrlrr = true := by decide +kernel
def level7llrrlr : BinaryTree (List W) := .node [v76, v100, v182, v245, v407, v500, v557, v590] level7llrrlrl level7llrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrlr_ok : everyKey (rowOK 6 level6) level7llrrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrlrl && everyKey (rowOK 6 level6) level7llrrlrr) = true
  rw [level7llrrlrl_ok, level7llrrlrr_ok]
  decide +kernel
def level7llrrl : BinaryTree (List W) := .node [v76, v96, v182, v245, v500, v557, v590, v642] level7llrrll level7llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrl_ok : everyKey (rowOK 6 level6) level7llrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrll && everyKey (rowOK 6 level6) level7llrrlr) = true
  rw [level7llrrll_ok, level7llrrlr_ok]
  decide +kernel
def level7llrrrll : BinaryTree (List W) := (.node [v76, v106, v182, v316, v407, v500, v557, v590] (.node [v76, v106, v182, v245, v407, v500, v554, v590] (.node [v76, v105, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v107, v182, v316, v407, v500, v557, v590] (.node [v76, v107, v182, v245, v415, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrrll_ok : everyKey (rowOK 6 level6) level7llrrrll = true := by decide +kernel
def level7llrrrlr : BinaryTree (List W) := (.node [v76, v111, v182, v316, v407, v500, v557, v590] (.node [v76, v110, v182, v316, v407, v500, v557, v590] (.node [v76, v109, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v112, v182, v245, v407, v500, v557, v588] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrrlr_ok : everyKey (rowOK 6 level6) level7llrrrlr = true := by decide +kernel
def level7llrrrl : BinaryTree (List W) := .node [v76, v108, v182, v245, v407, v500, v557, v590] level7llrrrll level7llrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrrl_ok : everyKey (rowOK 6 level6) level7llrrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrrll && everyKey (rowOK 6 level6) level7llrrrlr) = true
  rw [level7llrrrll_ok, level7llrrrlr_ok]
  decide +kernel
def level7llrrrrl : BinaryTree (List W) := (.node [v76, v115, v182, v245, v407, v500, v557, v590] (.node [v76, v114, v182, v245, v407, v500, v557, v590] (.node [v76, v113, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v116, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrrrl_ok : everyKey (rowOK 6 level6) level7llrrrrl = true := by decide +kernel
def level7llrrrrr : BinaryTree (List W) := (.node [v76, v118, v132, v182, v245, v500, v557, v590] (.node [v76, v118, v130, v182, v245, v500, v557, v590] (.node [v76, v118, v123, v182, v245, v450, v500, v590] .nil .nil) .nil) (.node [v76, v118, v134, v182, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrrrr_ok : everyKey (rowOK 6 level6) level7llrrrrr = true := by decide +kernel
def level7llrrrr : BinaryTree (List W) := .node [v76, v117, v182, v245, v407, v500, v557, v590] level7llrrrrl level7llrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrrr_ok : everyKey (rowOK 6 level6) level7llrrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrrrl && everyKey (rowOK 6 level6) level7llrrrrr) = true
  rw [level7llrrrrl_ok, level7llrrrrr_ok]
  decide +kernel
def level7llrrr : BinaryTree (List W) := .node [v76, v112, v182, v316, v407, v500, v557, v590] level7llrrrl level7llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrrr_ok : everyKey (rowOK 6 level6) level7llrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrrl && everyKey (rowOK 6 level6) level7llrrrr) = true
  rw [level7llrrrl_ok, level7llrrrr_ok]
  decide +kernel
def level7llrr : BinaryTree (List W) := .node [v76, v104, v182, v245, v407, v500, v557, v590] level7llrrl level7llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llrr_ok : everyKey (rowOK 6 level6) level7llrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrrl && everyKey (rowOK 6 level6) level7llrrr) = true
  rw [level7llrrl_ok, level7llrrr_ok]
  decide +kernel
def level7llr : BinaryTree (List W) := .node [v76, v95, v182, v316, v407, v500, v557, v590] level7llrl level7llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7llr_ok : everyKey (rowOK 6 level6) level7llr = true := by
  change (_ && everyKey (rowOK 6 level6) level7llrl && everyKey (rowOK 6 level6) level7llrr) = true
  rw [level7llrl_ok, level7llrr_ok]
  decide +kernel
def level7ll : BinaryTree (List W) := .node [v46, v91, v182, v245, v407, v500, v557, v590] level7lll level7llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7ll_ok : everyKey (rowOK 6 level6) level7ll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lll && everyKey (rowOK 6 level6) level7llr) = true
  rw [level7lll_ok, level7llr_ok]
  decide +kernel
def level7lrlllll : BinaryTree (List W) := (.node [v76, v118, v135, v182, v245, v482, v557, v590] (.node [v76, v118, v135, v182, v219, v500, v557, v590] (.node [v76, v118, v135, v182, v211, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v135, v182, v245, v500, v557, v585] (.node [v76, v118, v135, v182, v245, v500, v546, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlllll_ok : everyKey (rowOK 6 level6) level7lrlllll = true := by decide +kernel
def level7lrllllr : BinaryTree (List W) := (.node [v76, v118, v135, v182, v245, v531, v557, v590] (.node [v76, v118, v135, v182, v245, v500, v575, v590] (.node [v76, v118, v135, v182, v245, v500, v557, v621] .nil .nil) .nil) (.node [v76, v118, v135, v182, v245, v557, v590, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllllr_ok : everyKey (rowOK 6 level6) level7lrllllr = true := by decide +kernel
def level7lrllll : BinaryTree (List W) := .node [v76, v118, v135, v182, v245, v500, v557, v590] level7lrlllll level7lrllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllll_ok : everyKey (rowOK 6 level6) level7lrllll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlllll && everyKey (rowOK 6 level6) level7lrllllr) = true
  rw [level7lrlllll_ok, level7lrllllr_ok]
  decide +kernel
def level7lrlllrl : BinaryTree (List W) := (.node [v76, v118, v136, v182, v245, v500, v557, v590] (.node [v76, v118, v135, v245, v428, v500, v557, v590] (.node [v76, v118, v135, v182, v319, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v138, v182, v245, v500, v557, v590] (.node [v76, v118, v137, v182, v245, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlllrl_ok : everyKey (rowOK 6 level6) level7lrlllrl = true := by decide +kernel
def level7lrlllrr : BinaryTree (List W) := (.node [v76, v118, v143, v182, v211, v500, v557, v590] (.node [v76, v118, v143, v158, v182, v245, v557, v590] (.node [v76, v118, v142, v182, v245, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v143, v182, v245, v453, v500, v557] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlllrr_ok : everyKey (rowOK 6 level6) level7lrlllrr = true := by decide +kernel
def level7lrlllr : BinaryTree (List W) := .node [v76, v118, v141, v182, v245, v500, v557, v590] level7lrlllrl level7lrlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlllr_ok : everyKey (rowOK 6 level6) level7lrlllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlllrl && everyKey (rowOK 6 level6) level7lrlllrr) = true
  rw [level7lrlllrl_ok, level7lrlllrr_ok]
  decide +kernel
def level7lrlll : BinaryTree (List W) := .node [v76, v118, v135, v182, v316, v500, v557, v590] level7lrllll level7lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlll_ok : everyKey (rowOK 6 level6) level7lrlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrllll && everyKey (rowOK 6 level6) level7lrlllr) = true
  rw [level7lrllll_ok, level7lrlllr_ok]
  decide +kernel
def level7lrllrll : BinaryTree (List W) := (.node [v76, v118, v143, v182, v316, v500, v557, v590] (.node [v76, v118, v143, v182, v245, v557, v590, v637] (.node [v76, v118, v143, v182, v245, v500, v557, v625] .nil .nil) .nil) (.node [v76, v118, v145, v182, v245, v500, v557, v590] (.node [v76, v118, v144, v182, v245, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllrll_ok : everyKey (rowOK 6 level6) level7lrllrll = true := by decide +kernel
def level7lrllrlr : BinaryTree (List W) := (.node [v76, v118, v151, v245, v407, v537, v557, v590] (.node [v76, v118, v149, v182, v245, v500, v557, v590] (.node [v76, v118, v148, v182, v245, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v152, v182, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllrlr_ok : everyKey (rowOK 6 level6) level7lrllrlr = true := by decide +kernel
def level7lrllrl : BinaryTree (List W) := .node [v76, v118, v147, v182, v245, v500, v557, v590] level7lrllrll level7lrllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllrl_ok : everyKey (rowOK 6 level6) level7lrllrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrllrll && everyKey (rowOK 6 level6) level7lrllrlr) = true
  rw [level7lrllrll_ok, level7lrllrlr_ok]
  decide +kernel
def level7lrllrrl : BinaryTree (List W) := (.node [v76, v118, v158, v182, v245, v346, v407, v557] (.node [v76, v118, v158, v182, v240, v407, v557, v590] (.node [v76, v118, v158, v182, v211, v407, v557, v590] .nil .nil) .nil) (.node [v76, v118, v158, v182, v245, v349, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllrrl_ok : everyKey (rowOK 6 level6) level7lrllrrl = true := by decide +kernel
def level7lrllrrr : BinaryTree (List W) := (.node [v76, v118, v158, v182, v245, v407, v557, v637] (.node [v76, v118, v158, v182, v245, v407, v557, v590] (.node [v76, v118, v158, v182, v245, v377, v557, v590] .nil .nil) .nil) (.node [v76, v118, v158, v182, v245, v430, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllrrr_ok : everyKey (rowOK 6 level6) level7lrllrrr = true := by decide +kernel
def level7lrllrr : BinaryTree (List W) := .node [v76, v118, v158, v182, v245, v370, v557, v590] level7lrllrrl level7lrllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllrr_ok : everyKey (rowOK 6 level6) level7lrllrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrllrrl && everyKey (rowOK 6 level6) level7lrllrrr) = true
  rw [level7lrllrrl_ok, level7lrllrrr_ok]
  decide +kernel
def level7lrllr : BinaryTree (List W) := .node [v76, v118, v156, v245, v407, v500, v544, v590] level7lrllrl level7lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrllr_ok : everyKey (rowOK 6 level6) level7lrllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrllrl && everyKey (rowOK 6 level6) level7lrllrr) = true
  rw [level7lrllrl_ok, level7lrllrr_ok]
  decide +kernel
def level7lrll : BinaryTree (List W) := .node [v76, v118, v143, v182, v245, v500, v557, v590] level7lrlll level7lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrll_ok : everyKey (rowOK 6 level6) level7lrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlll && everyKey (rowOK 6 level6) level7lrllr) = true
  rw [level7lrlll_ok, level7lrllr_ok]
  decide +kernel
def level7lrlrlll : BinaryTree (List W) := (.node [v76, v118, v158, v182, v316, v407, v557, v590] (.node [v76, v118, v158, v182, v245, v557, v590, v642] (.node [v76, v118, v158, v182, v245, v557, v590, v625] .nil .nil) .nil) (.node [v76, v118, v159, v182, v245, v407, v557, v590] (.node [v76, v118, v158, v182, v335, v407, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrlll_ok : everyKey (rowOK 6 level6) level7lrlrlll = true := by decide +kernel
def level7lrlrllr : BinaryTree (List W) := (.node [v76, v118, v171, v245, v407, v500, v557, v584] (.node [v76, v118, v170, v216, v407, v500, v557, v590] (.node [v76, v118, v161, v182, v245, v407, v557, v590] .nil .nil) .nil) (.node [v76, v118, v172, v182, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrllr_ok : everyKey (rowOK 6 level6) level7lrlrllr = true := by decide +kernel
def level7lrlrll : BinaryTree (List W) := .node [v76, v118, v160, v182, v245, v407, v557, v590] level7lrlrlll level7lrlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrll_ok : everyKey (rowOK 6 level6) level7lrlrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrlll && everyKey (rowOK 6 level6) level7lrlrllr) = true
  rw [level7lrlrlll_ok, level7lrlrllr_ok]
  decide +kernel
def level7lrlrlrl : BinaryTree (List W) := (.node [v76, v118, v178, v245, v407, v500, v557, v590] (.node [v76, v118, v176, v245, v407, v500, v557, v590] (.node [v76, v118, v175, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v179, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrlrl_ok : everyKey (rowOK 6 level6) level7lrlrlrl = true := by decide +kernel
def level7lrlrlrr : BinaryTree (List W) := (.node [v76, v118, v182, v193, v245, v500, v557, v590] (.node [v76, v118, v182, v190, v245, v500, v557, v590] (.node [v76, v118, v181, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v200, v245, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrlrr_ok : everyKey (rowOK 6 level6) level7lrlrlrr = true := by decide +kernel
def level7lrlrlr : BinaryTree (List W) := .node [v76, v118, v180, v245, v407, v500, v557, v590] level7lrlrlrl level7lrlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrlr_ok : everyKey (rowOK 6 level6) level7lrlrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrlrl && everyKey (rowOK 6 level6) level7lrlrlrr) = true
  rw [level7lrlrlrl_ok, level7lrlrlrr_ok]
  decide +kernel
def level7lrlrl : BinaryTree (List W) := .node [v76, v118, v173, v182, v245, v500, v557, v590] level7lrlrll level7lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrl_ok : everyKey (rowOK 6 level6) level7lrlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrll && everyKey (rowOK 6 level6) level7lrlrlr) = true
  rw [level7lrlrll_ok, level7lrlrlr_ok]
  decide +kernel
def level7lrlrrll : BinaryTree (List W) := (.node [v76, v118, v182, v210, v245, v407, v557, v637] (.node [v76, v118, v182, v208, v407, v500, v557, v595] (.node [v76, v118, v182, v207, v407, v526, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v211, v377, v500, v557, v590] (.node [v76, v118, v182, v211, v349, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrrll_ok : everyKey (rowOK 6 level6) level7lrlrrll = true := by decide +kernel
def level7lrlrrlr : BinaryTree (List W) := (.node [v76, v118, v182, v211, v500, v557, v590, v625] (.node [v76, v118, v182, v211, v437, v500, v557, v590] (.node [v76, v118, v182, v211, v407, v557, v590, v637] .nil .nil) .nil) (.node [v76, v118, v182, v211, v500, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrrlr_ok : everyKey (rowOK 6 level6) level7lrlrrlr = true := by decide +kernel
def level7lrlrrl : BinaryTree (List W) := .node [v76, v118, v182, v211, v407, v500, v557, v590] level7lrlrrll level7lrlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrrl_ok : everyKey (rowOK 6 level6) level7lrlrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrrll && everyKey (rowOK 6 level6) level7lrlrrlr) = true
  rw [level7lrlrrll_ok, level7lrlrrlr_ok]
  decide +kernel
def level7lrlrrrl : BinaryTree (List W) := (.node [v76, v118, v182, v217, v407, v500, v557, v590] (.node [v76, v118, v182, v214, v385, v500, v557, v590] (.node [v76, v118, v182, v213, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v218, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrrrl_ok : everyKey (rowOK 6 level6) level7lrlrrrl = true := by decide +kernel
def level7lrlrrrr : BinaryTree (List W) := (.node [v76, v118, v182, v226, v407, v500, v557, v590] (.node [v76, v118, v182, v225, v407, v500, v557, v590] (.node [v76, v118, v182, v224, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v227, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrrrr_ok : everyKey (rowOK 6 level6) level7lrlrrrr = true := by decide +kernel
def level7lrlrrr : BinaryTree (List W) := .node [v76, v118, v182, v219, v407, v500, v557, v590] level7lrlrrrl level7lrlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrrr_ok : everyKey (rowOK 6 level6) level7lrlrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrrrl && everyKey (rowOK 6 level6) level7lrlrrrr) = true
  rw [level7lrlrrrl_ok, level7lrlrrrr_ok]
  decide +kernel
def level7lrlrr : BinaryTree (List W) := .node [v76, v118, v182, v212, v407, v500, v557, v590] level7lrlrrl level7lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlrr_ok : everyKey (rowOK 6 level6) level7lrlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrrl && everyKey (rowOK 6 level6) level7lrlrrr) = true
  rw [level7lrlrrl_ok, level7lrlrrr_ok]
  decide +kernel
def level7lrlr : BinaryTree (List W) := .node [v76, v118, v182, v201, v245, v500, v557, v590] level7lrlrl level7lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrlr_ok : everyKey (rowOK 6 level6) level7lrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrlrl && everyKey (rowOK 6 level6) level7lrlrr) = true
  rw [level7lrlrl_ok, level7lrlrr_ok]
  decide +kernel
def level7lrl : BinaryTree (List W) := .node [v76, v118, v158, v182, v245, v437, v557, v590] level7lrll level7lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrl_ok : everyKey (rowOK 6 level6) level7lrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrll && everyKey (rowOK 6 level6) level7lrlr) = true
  rw [level7lrll_ok, level7lrlr_ok]
  decide +kernel
def level7lrrllll : BinaryTree (List W) := (.node [v76, v118, v182, v232, v407, v500, v557, v590] (.node [v76, v118, v182, v231, v407, v500, v557, v590] (.node [v76, v118, v182, v230, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v234, v407, v500, v557, v590] (.node [v76, v118, v182, v233, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrllll_ok : everyKey (rowOK 6 level6) level7lrrllll = true := by decide +kernel
def level7lrrlllr : BinaryTree (List W) := (.node [v76, v118, v182, v238, v407, v500, v557, v590] (.node [v76, v118, v182, v237, v407, v500, v557, v590] (.node [v76, v118, v182, v236, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v239, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlllr_ok : everyKey (rowOK 6 level6) level7lrrlllr = true := by decide +kernel
def level7lrrlll : BinaryTree (List W) := .node [v76, v118, v182, v235, v407, v500, v557, v590] level7lrrllll level7lrrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlll_ok : everyKey (rowOK 6 level6) level7lrrlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrllll && everyKey (rowOK 6 level6) level7lrrlllr) = true
  rw [level7lrrllll_ok, level7lrrlllr_ok]
  decide +kernel
def level7lrrllrl : BinaryTree (List W) := (.node [v76, v118, v182, v243, v407, v500, v557, v590] (.node [v76, v118, v182, v242, v407, v500, v557, v590] (.node [v76, v118, v182, v241, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v262, v500, v557, v590] (.node [v76, v118, v182, v244, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrllrl_ok : everyKey (rowOK 6 level6) level7lrrllrl = true := by decide +kernel
def level7lrrllrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v342, v557, v590, v642] (.node [v76, v118, v182, v245, v325, v407, v557, v590] (.node [v76, v118, v182, v245, v323, v407, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v343, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrllrr_ok : everyKey (rowOK 6 level6) level7lrrllrr = true := by decide +kernel
def level7lrrllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v322, v347, v407, v590] level7lrrllrl level7lrrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrllr_ok : everyKey (rowOK 6 level6) level7lrrllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrllrl && everyKey (rowOK 6 level6) level7lrrllrr) = true
  rw [level7lrrllrl_ok, level7lrrllrr_ok]
  decide +kernel
def level7lrrll : BinaryTree (List W) := .node [v76, v118, v182, v240, v407, v500, v557, v590] level7lrrlll level7lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrll_ok : everyKey (rowOK 6 level6) level7lrrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrlll && everyKey (rowOK 6 level6) level7lrrllr) = true
  rw [level7lrrlll_ok, level7lrrllr_ok]
  decide +kernel
def level7lrrlrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v348, v500, v557, v590] (.node [v76, v118, v182, v245, v347, v557, v590, v642] (.node [v76, v118, v182, v245, v345, v407, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v349, v500, v557, v590] (.node [v76, v118, v182, v245, v349, v454, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlrll_ok : everyKey (rowOK 6 level6) level7lrrlrll = true := by decide +kernel
def level7lrrlrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v351, v500, v557, v590] (.node [v76, v118, v182, v245, v350, v500, v557, v590] (.node [v76, v118, v182, v245, v349, v557, v590, v642] .nil .nil) .nil) (.node [v76, v118, v182, v245, v352, v407, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlrlr_ok : everyKey (rowOK 6 level6) level7lrrlrlr = true := by decide +kernel
def level7lrrlrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v349, v557, v590, v637] level7lrrlrll level7lrrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlrl_ok : everyKey (rowOK 6 level6) level7lrrlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrlrll && everyKey (rowOK 6 level6) level7lrrlrlr) = true
  rw [level7lrrlrll_ok, level7lrrlrlr_ok]
  decide +kernel
def level7lrrlrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v356, v500, v557, v590] (.node [v76, v118, v182, v245, v355, v500, v557, v590] (.node [v76, v118, v182, v245, v354, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v357, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlrrl_ok : everyKey (rowOK 6 level6) level7lrrlrrl = true := by decide +kernel
def level7lrrlrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v364, v500, v557, v625] (.node [v76, v118, v182, v245, v362, v407, v500, v557] (.node [v76, v118, v182, v245, v360, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v366, v500, v577, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlrrr_ok : everyKey (rowOK 6 level6) level7lrrlrrr = true := by decide +kernel
def level7lrrlrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v358, v500, v557, v590] level7lrrlrrl level7lrrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlrr_ok : everyKey (rowOK 6 level6) level7lrrlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrlrrl && everyKey (rowOK 6 level6) level7lrrlrrr) = true
  rw [level7lrrlrrl_ok, level7lrrlrrr_ok]
  decide +kernel
def level7lrrlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v353, v500, v557, v590] level7lrrlrl level7lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrlr_ok : everyKey (rowOK 6 level6) level7lrrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrlrl && everyKey (rowOK 6 level6) level7lrrlrr) = true
  rw [level7lrrlrl_ok, level7lrrlrr_ok]
  decide +kernel
def level7lrrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v344, v500, v557, v590] level7lrrll level7lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrl_ok : everyKey (rowOK 6 level6) level7lrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrll && everyKey (rowOK 6 level6) level7lrrlr) = true
  rw [level7lrrll_ok, level7lrrlr_ok]
  decide +kernel
def level7lrrrlll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v374, v500, v557, v590] (.node [v76, v118, v182, v245, v373, v500, v557, v590] (.node [v76, v118, v182, v245, v372, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v377, v557, v590, v637] (.node [v76, v118, v182, v245, v377, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrlll_ok : everyKey (rowOK 6 level6) level7lrrrlll = true := by decide +kernel
def level7lrrrllr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v381, v500, v557, v590] (.node [v76, v118, v182, v245, v380, v500, v557, v590] (.node [v76, v118, v182, v245, v379, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v383, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrllr_ok : everyKey (rowOK 6 level6) level7lrrrllr = true := by decide +kernel
def level7lrrrll : BinaryTree (List W) := .node [v76, v118, v182, v245, v378, v500, v557, v590] level7lrrrlll level7lrrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrll_ok : everyKey (rowOK 6 level6) level7lrrrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrlll && everyKey (rowOK 6 level6) level7lrrrllr) = true
  rw [level7lrrrlll_ok, level7lrrrllr_ok]
  decide +kernel
def level7lrrrlrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v388, v500, v557, v590] (.node [v76, v118, v182, v245, v387, v500, v557, v590] (.node [v76, v118, v182, v245, v386, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v389, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrlrl_ok : everyKey (rowOK 6 level6) level7lrrrlrl = true := by decide +kernel
def level7lrrrlrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v394, v500, v557, v590] (.node [v76, v118, v182, v245, v393, v500, v557, v590] (.node [v76, v118, v182, v245, v392, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v395, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrlrr_ok : everyKey (rowOK 6 level6) level7lrrrlrr = true := by decide +kernel
def level7lrrrlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v390, v500, v557, v590] level7lrrrlrl level7lrrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrlr_ok : everyKey (rowOK 6 level6) level7lrrrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrlrl && everyKey (rowOK 6 level6) level7lrrrlrr) = true
  rw [level7lrrrlrl_ok, level7lrrrlrr_ok]
  decide +kernel
def level7lrrrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v384, v500, v557, v590] level7lrrrll level7lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrl_ok : everyKey (rowOK 6 level6) level7lrrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrll && everyKey (rowOK 6 level6) level7lrrrlr) = true
  rw [level7lrrrll_ok, level7lrrrlr_ok]
  decide +kernel
def level7lrrrrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v401, v500, v557, v590] (.node [v76, v118, v182, v245, v400, v500, v557, v590] (.node [v76, v118, v182, v245, v399, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v403, v500, v557, v590] (.node [v76, v118, v182, v245, v402, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrrll_ok : everyKey (rowOK 6 level6) level7lrrrrll = true := by decide +kernel
def level7lrrrrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v460, v590, v638] (.node [v76, v118, v182, v245, v407, v459, v557, v590] (.node [v76, v118, v182, v245, v406, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v467, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrrlr_ok : everyKey (rowOK 6 level6) level7lrrrrlr = true := by decide +kernel
def level7lrrrrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v405, v500, v557, v590] level7lrrrrll level7lrrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrrl_ok : everyKey (rowOK 6 level6) level7lrrrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrrll && everyKey (rowOK 6 level6) level7lrrrrlr) = true
  rw [level7lrrrrll_ok, level7lrrrrlr_ok]
  decide +kernel
def level7lrrrrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v474, v557, v637] (.node [v76, v118, v182, v245, v407, v471, v557, v590] (.node [v76, v118, v182, v245, v407, v469, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v480, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrrrl_ok : everyKey (rowOK 6 level6) level7lrrrrrl = true := by decide +kernel
def level7lrrrrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v487, v557, v590] (.node [v76, v118, v182, v245, v407, v486, v557, v590] (.node [v76, v118, v182, v245, v407, v482, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v490, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrrrr_ok : everyKey (rowOK 6 level6) level7lrrrrrr = true := by decide +kernel
def level7lrrrrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v481, v557, v590] level7lrrrrrl level7lrrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrrr_ok : everyKey (rowOK 6 level6) level7lrrrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrrrl && everyKey (rowOK 6 level6) level7lrrrrrr) = true
  rw [level7lrrrrrl_ok, level7lrrrrrr_ok]
  decide +kernel
def level7lrrrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v468, v557, v590] level7lrrrrl level7lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrrr_ok : everyKey (rowOK 6 level6) level7lrrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrrl && everyKey (rowOK 6 level6) level7lrrrrr) = true
  rw [level7lrrrrl_ok, level7lrrrrr_ok]
  decide +kernel
def level7lrrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v397, v500, v557, v590] level7lrrrl level7lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrrr_ok : everyKey (rowOK 6 level6) level7lrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrrl && everyKey (rowOK 6 level6) level7lrrrr) = true
  rw [level7lrrrl_ok, level7lrrrr_ok]
  decide +kernel
def level7lrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v370, v500, v557, v590] level7lrrl level7lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lrr_ok : everyKey (rowOK 6 level6) level7lrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrrl && everyKey (rowOK 6 level6) level7lrrr) = true
  rw [level7lrrl_ok, level7lrrr_ok]
  decide +kernel
def level7lr : BinaryTree (List W) := .node [v76, v118, v182, v229, v407, v500, v549, v590] level7lrl level7lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7lr_ok : everyKey (rowOK 6 level6) level7lr = true := by
  change (_ && everyKey (rowOK 6 level6) level7lrl && everyKey (rowOK 6 level6) level7lrr) = true
  rw [level7lrl_ok, level7lrr_ok]
  decide +kernel
def level7l : BinaryTree (List W) := .node [v76, v118, v135, v158, v182, v245, v557, v590] level7ll level7lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7l_ok : everyKey (rowOK 6 level6) level7l = true := by
  change (_ && everyKey (rowOK 6 level6) level7ll && everyKey (rowOK 6 level6) level7lr) = true
  rw [level7ll_ok, level7lr_ok]
  decide +kernel
def level7rllllll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v494, v557, v590] (.node [v76, v118, v182, v245, v407, v493, v557, v590] (.node [v76, v118, v182, v245, v407, v492, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v497, v557, v590] (.node [v76, v118, v182, v245, v407, v495, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllllll_ok : everyKey (rowOK 6 level6) level7rllllll = true := by decide +kernel
def level7rlllllr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v546, v590] (.node [v76, v118, v182, v245, v407, v500, v540, v602] (.node [v76, v118, v182, v245, v407, v499, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v500, v552, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllllr_ok : everyKey (rowOK 6 level6) level7rlllllr = true := by decide +kernel
def level7rlllll : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v498, v557, v590] level7rllllll level7rlllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllll_ok : everyKey (rowOK 6 level6) level7rlllll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllllll && everyKey (rowOK 6 level6) level7rlllllr) = true
  rw [level7rllllll_ok, level7rlllllr_ok]
  decide +kernel
def level7rllllrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v585] (.node [v76, v118, v182, v245, v407, v500, v556, v590] (.node [v76, v118, v182, v245, v407, v500, v555, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v500, v557, v590] (.node [v76, v118, v182, v245, v407, v500, v557, v589] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllllrl_ok : everyKey (rowOK 6 level6) level7rllllrl = true := by decide +kernel
def level7rllllrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v606] (.node [v76, v118, v182, v245, v407, v500, v557, v596] (.node [v76, v118, v182, v245, v407, v500, v557, v592] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v500, v557, v621] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllllrr_ok : everyKey (rowOK 6 level6) level7rllllrr = true := by decide +kernel
def level7rllllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v591] level7rllllrl level7rllllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllllr_ok : everyKey (rowOK 6 level6) level7rllllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllllrl && everyKey (rowOK 6 level6) level7rllllrr) = true
  rw [level7rllllrl_ok, level7rllllrr_ok]
  decide +kernel
def level7rllll : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v553, v590] level7rlllll level7rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllll_ok : everyKey (rowOK 6 level6) level7rllll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlllll && everyKey (rowOK 6 level6) level7rllllr) = true
  rw [level7rlllll_ok, level7rllllr_ok]
  decide +kernel
def level7rlllrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v560, v590] (.node [v76, v118, v182, v245, v407, v500, v559, v590] (.node [v76, v118, v182, v245, v407, v500, v558, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v500, v575, v590] (.node [v76, v118, v182, v245, v407, v500, v565, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllrll_ok : everyKey (rowOK 6 level6) level7rlllrll = true := by decide +kernel
def level7rlllrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v502, v557, v590] (.node [v76, v118, v182, v245, v407, v501, v557, v590] (.node [v76, v118, v182, v245, v407, v500, v590, v599] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v503, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllrlr_ok : everyKey (rowOK 6 level6) level7rlllrlr = true := by decide +kernel
def level7rlllrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v580, v590] level7rlllrll level7rlllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllrl_ok : everyKey (rowOK 6 level6) level7rlllrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlllrll && everyKey (rowOK 6 level6) level7rlllrlr) = true
  rw [level7rlllrll_ok, level7rlllrlr_ok]
  decide +kernel
def level7rlllrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v508, v557, v590] (.node [v76, v118, v182, v245, v407, v507, v557, v590] (.node [v76, v118, v182, v245, v407, v506, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v509, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllrrl_ok : everyKey (rowOK 6 level6) level7rlllrrl = true := by decide +kernel
def level7rlllrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v516, v557, v590] (.node [v76, v118, v182, v245, v407, v515, v557, v590] (.node [v76, v118, v182, v245, v407, v511, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v519, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllrrr_ok : everyKey (rowOK 6 level6) level7rlllrrr = true := by decide +kernel
def level7rlllrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v510, v557, v590] level7rlllrrl level7rlllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllrr_ok : everyKey (rowOK 6 level6) level7rlllrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlllrrl && everyKey (rowOK 6 level6) level7rlllrrr) = true
  rw [level7rlllrrl_ok, level7rlllrrr_ok]
  decide +kernel
def level7rlllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v505, v557, v590] level7rlllrl level7rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlllr_ok : everyKey (rowOK 6 level6) level7rlllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlllrl && everyKey (rowOK 6 level6) level7rlllrr) = true
  rw [level7rlllrl_ok, level7rlllrr_ok]
  decide +kernel
def level7rlll : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v632] level7rllll level7rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlll_ok : everyKey (rowOK 6 level6) level7rlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllll && everyKey (rowOK 6 level6) level7rlllr) = true
  rw [level7rllll_ok, level7rlllr_ok]
  decide +kernel
def level7rllrlll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v524, v557, v590] (.node [v76, v118, v182, v245, v407, v523, v557, v590] (.node [v76, v118, v182, v245, v407, v522, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v557, v584, v637] (.node [v76, v118, v182, v245, v407, v531, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrlll_ok : everyKey (rowOK 6 level6) level7rllrlll = true := by decide +kernel
def level7rllrllr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v557, v590, v633] (.node [v76, v118, v182, v245, v407, v557, v590, v631] (.node [v76, v118, v182, v245, v407, v557, v590, v629] .nil .nil) .nil) (.node [v76, v118, v182, v245, v407, v557, v590, v634] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrllr_ok : everyKey (rowOK 6 level6) level7rllrllr = true := by decide +kernel
def level7rllrll : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v557, v590, v628] level7rllrlll level7rllrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrll_ok : everyKey (rowOK 6 level6) level7rllrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrlll && everyKey (rowOK 6 level6) level7rllrllr) = true
  rw [level7rllrlll_ok, level7rllrllr_ok]
  decide +kernel
def level7rllrlrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v557, v637, v647] (.node [v76, v118, v182, v245, v407, v557, v602, v637] (.node [v76, v118, v182, v245, v407, v557, v590, v637] .nil .nil) .nil) (.node [v76, v118, v182, v245, v408, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrlrl_ok : everyKey (rowOK 6 level6) level7rllrlrl = true := by decide +kernel
def level7rllrlrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v412, v500, v557, v590] (.node [v76, v118, v182, v245, v411, v500, v557, v590] (.node [v76, v118, v182, v245, v410, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v413, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrlrr_ok : everyKey (rowOK 6 level6) level7rllrlrr = true := by decide +kernel
def level7rllrlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v409, v500, v557, v590] level7rllrlrl level7rllrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrlr_ok : everyKey (rowOK 6 level6) level7rllrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrlrl && everyKey (rowOK 6 level6) level7rllrlrr) = true
  rw [level7rllrlrl_ok, level7rllrlrr_ok]
  decide +kernel
def level7rllrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v557, v590, v635] level7rllrll level7rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrl_ok : everyKey (rowOK 6 level6) level7rllrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrll && everyKey (rowOK 6 level6) level7rllrlr) = true
  rw [level7rllrll_ok, level7rllrlr_ok]
  decide +kernel
def level7rllrrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v420, v500, v557, v590] (.node [v76, v118, v182, v245, v418, v500, v557, v590] (.node [v76, v118, v182, v245, v416, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v422, v500, v557, v590] (.node [v76, v118, v182, v245, v421, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrrll_ok : everyKey (rowOK 6 level6) level7rllrrll = true := by decide +kernel
def level7rllrrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v427, v500, v557, v590] (.node [v76, v118, v182, v245, v426, v500, v557, v590] (.node [v76, v118, v182, v245, v425, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v429, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrrlr_ok : everyKey (rowOK 6 level6) level7rllrrlr = true := by decide +kernel
def level7rllrrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v423, v500, v557, v590] level7rllrrll level7rllrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrrl_ok : everyKey (rowOK 6 level6) level7rllrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrrll && everyKey (rowOK 6 level6) level7rllrrlr) = true
  rw [level7rllrrll_ok, level7rllrrlr_ok]
  decide +kernel
def level7rllrrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v436, v500, v557, v590] (.node [v76, v118, v182, v245, v434, v500, v557, v590] (.node [v76, v118, v182, v245, v432, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrrrl_ok : everyKey (rowOK 6 level6) level7rllrrrl = true := by decide +kernel
def level7rllrrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v444, v500, v557, v590] (.node [v76, v118, v182, v245, v442, v500, v557, v590] (.node [v76, v118, v182, v245, v439, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v445, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrrrr_ok : everyKey (rowOK 6 level6) level7rllrrrr = true := by decide +kernel
def level7rllrrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v437, v557, v590, v637] level7rllrrrl level7rllrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrrr_ok : everyKey (rowOK 6 level6) level7rllrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrrrl && everyKey (rowOK 6 level6) level7rllrrrr) = true
  rw [level7rllrrrl_ok, level7rllrrrr_ok]
  decide +kernel
def level7rllrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v430, v500, v557, v590] level7rllrrl level7rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllrr_ok : everyKey (rowOK 6 level6) level7rllrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrrl && everyKey (rowOK 6 level6) level7rllrrr) = true
  rw [level7rllrrl_ok, level7rllrrr_ok]
  decide +kernel
def level7rllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v414, v500, v557, v590] level7rllrl level7rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rllr_ok : everyKey (rowOK 6 level6) level7rllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rllrl && everyKey (rowOK 6 level6) level7rllrr) = true
  rw [level7rllrl_ok, level7rllrr_ok]
  decide +kernel
def level7rll : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v520, v557, v590] level7rlll level7rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rll_ok : everyKey (rowOK 6 level6) level7rll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlll && everyKey (rowOK 6 level6) level7rllr) = true
  rw [level7rlll_ok, level7rllr_ok]
  decide +kernel
def level7rlrllll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v456, v500, v557, v590] (.node [v76, v118, v182, v245, v455, v500, v557, v590] (.node [v76, v118, v182, v245, v451, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v466, v557, v590, v642] (.node [v76, v118, v182, v245, v460, v557, v590, v642] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrllll_ok : everyKey (rowOK 6 level6) level7rlrllll = true := by decide +kernel
def level7rlrlllr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v529, v557, v590] (.node [v76, v118, v182, v245, v500, v504, v557, v590] (.node [v76, v118, v182, v245, v478, v557, v590, v642] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v531, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlllr_ok : everyKey (rowOK 6 level6) level7rlrlllr = true := by decide +kernel
def level7rlrlll : BinaryTree (List W) := .node [v76, v118, v182, v245, v475, v557, v590, v642] level7rlrllll level7rlrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlll_ok : everyKey (rowOK 6 level6) level7rlrlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrllll && everyKey (rowOK 6 level6) level7rlrlllr) = true
  rw [level7rlrllll_ok, level7rlrlllr_ok]
  decide +kernel
def level7rlrllrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v557, v576, v590] (.node [v76, v118, v182, v245, v500, v557, v572, v590] (.node [v76, v118, v182, v245, v500, v557, v571, v590] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v557, v584, v625] (.node [v76, v118, v182, v245, v500, v557, v582, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrllrl_ok : everyKey (rowOK 6 level6) level7rlrllrl = true := by decide +kernel
def level7rlrllrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v557, v590, v616] (.node [v76, v118, v182, v245, v500, v557, v590, v613] (.node [v76, v118, v182, v245, v500, v557, v590, v605] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v557, v590, v617] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrllrr_ok : everyKey (rowOK 6 level6) level7rlrllrr = true := by decide +kernel
def level7rlrllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v590, v598] level7rlrllrl level7rlrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrllr_ok : everyKey (rowOK 6 level6) level7rlrllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrllrl && everyKey (rowOK 6 level6) level7rlrllrr) = true
  rw [level7rlrllrl_ok, level7rlrllrr_ok]
  decide +kernel
def level7rlrll : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v569, v590] level7rlrlll level7rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrll_ok : everyKey (rowOK 6 level6) level7rlrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrlll && everyKey (rowOK 6 level6) level7rlrllr) = true
  rw [level7rlrlll_ok, level7rlrllr_ok]
  decide +kernel
def level7rlrlrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v557, v590, v621] (.node [v76, v118, v182, v245, v500, v557, v590, v620] (.node [v76, v118, v182, v245, v500, v557, v590, v619] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v557, v590, v623] (.node [v76, v118, v182, v245, v500, v557, v590, v622] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlrll_ok : everyKey (rowOK 6 level6) level7rlrlrll = true := by decide +kernel
def level7rlrlrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v557, v590, v640] (.node [v76, v118, v182, v245, v500, v557, v590, v639] (.node [v76, v118, v182, v245, v500, v557, v590, v625] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlrlr_ok : everyKey (rowOK 6 level6) level7rlrlrlr = true := by decide +kernel
def level7rlrlrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v590, v624] level7rlrlrll level7rlrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlrl_ok : everyKey (rowOK 6 level6) level7rlrlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrlrll && everyKey (rowOK 6 level6) level7rlrlrlr) = true
  rw [level7rlrlrll_ok, level7rlrlrlr_ok]
  decide +kernel
def level7rlrlrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v500, v557, v621] (.node [v76, v118, v182, v245, v500, v557, v590, v650] (.node [v76, v118, v182, v245, v500, v557, v590, v649] .nil .nil) .nil) (.node [v76, v118, v182, v245, v500, v557, v625, v647] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlrrl_ok : everyKey (rowOK 6 level6) level7rlrlrrl = true := by decide +kernel
def level7rlrlrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v537, v557, v590, v642] (.node [v76, v118, v182, v245, v531, v557, v590] (.node [v76, v118, v182, v245, v526, v557, v590, v642] .nil .nil) .nil) (.node [v76, v118, v182, v245, v557, v590, v625, v637] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlrrr_ok : everyKey (rowOK 6 level6) level7rlrlrrr = true := by decide +kernel
def level7rlrlrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v518, v557, v590, v642] level7rlrlrrl level7rlrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlrr_ok : everyKey (rowOK 6 level6) level7rlrlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrlrrl && everyKey (rowOK 6 level6) level7rlrlrrr) = true
  rw [level7rlrlrrl_ok, level7rlrlrrr_ok]
  decide +kernel
def level7rlrlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v590, v643] level7rlrlrl level7rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrlr_ok : everyKey (rowOK 6 level6) level7rlrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrlrl && everyKey (rowOK 6 level6) level7rlrlrr) = true
  rw [level7rlrlrl_ok, level7rlrlrr_ok]
  decide +kernel
def level7rlrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v590, v618] level7rlrll level7rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrl_ok : everyKey (rowOK 6 level6) level7rlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrll && everyKey (rowOK 6 level6) level7rlrlr) = true
  rw [level7rlrll_ok, level7rlrlr_ok]
  decide +kernel
def level7rlrrlll : BinaryTree (List W) := (.node [v76, v118, v182, v247, v407, v500, v557, v590] (.node [v76, v118, v182, v246, v407, v500, v557, v590] (.node [v76, v118, v182, v245, v557, v590, v637, v649] .nil .nil) .nil) (.node [v76, v118, v182, v249, v407, v500, v557, v590] (.node [v76, v118, v182, v248, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrlll_ok : everyKey (rowOK 6 level6) level7rlrrlll = true := by decide +kernel
def level7rlrrllr : BinaryTree (List W) := (.node [v76, v118, v182, v260, v407, v500, v557, v590] (.node [v76, v118, v182, v259, v407, v500, v557, v590] (.node [v76, v118, v182, v258, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v264, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrllr_ok : everyKey (rowOK 6 level6) level7rlrrllr = true := by decide +kernel
def level7rlrrll : BinaryTree (List W) := .node [v76, v118, v182, v254, v407, v500, v557, v590] level7rlrrlll level7rlrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrll_ok : everyKey (rowOK 6 level6) level7rlrrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrlll && everyKey (rowOK 6 level6) level7rlrrllr) = true
  rw [level7rlrrlll_ok, level7rlrrllr_ok]
  decide +kernel
def level7rlrrlrl : BinaryTree (List W) := (.node [v76, v118, v182, v279, v407, v500, v557, v590] (.node [v76, v118, v182, v273, v407, v500, v557, v590] (.node [v76, v118, v182, v267, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v292, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrlrl_ok : everyKey (rowOK 6 level6) level7rlrrlrl = true := by decide +kernel
def level7rlrrlrr : BinaryTree (List W) := (.node [v76, v118, v182, v310, v407, v500, v557, v590] (.node [v76, v118, v182, v302, v407, v500, v557, v590] (.node [v76, v118, v182, v301, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v316, v349, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrlrr_ok : everyKey (rowOK 6 level6) level7rlrrlrr = true := by decide +kernel
def level7rlrrlr : BinaryTree (List W) := .node [v76, v118, v182, v300, v407, v500, v557, v590] level7rlrrlrl level7rlrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrlr_ok : everyKey (rowOK 6 level6) level7rlrrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrlrl && everyKey (rowOK 6 level6) level7rlrrlrr) = true
  rw [level7rlrrlrl_ok, level7rlrrlrr_ok]
  decide +kernel
def level7rlrrl : BinaryTree (List W) := .node [v76, v118, v182, v266, v407, v500, v557, v590] level7rlrrll level7rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrl_ok : everyKey (rowOK 6 level6) level7rlrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrll && everyKey (rowOK 6 level6) level7rlrrlr) = true
  rw [level7rlrrll_ok, level7rlrrlr_ok]
  decide +kernel
def level7rlrrrll : BinaryTree (List W) := (.node [v76, v118, v182, v316, v437, v500, v557, v590] (.node [v76, v118, v182, v316, v407, v557, v590, v637] (.node [v76, v118, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v316, v500, v557, v590, v642] (.node [v76, v118, v182, v316, v500, v557, v590, v625] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrrll_ok : everyKey (rowOK 6 level6) level7rlrrrll = true := by decide +kernel
def level7rlrrrlr : BinaryTree (List W) := (.node [v76, v118, v182, v335, v407, v500, v557, v590] (.node [v76, v118, v182, v331, v407, v500, v557, v590] (.node [v76, v118, v182, v327, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v182, v407, v457, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrrlr_ok : everyKey (rowOK 6 level6) level7rlrrrlr = true := by decide +kernel
def level7rlrrrl : BinaryTree (List W) := .node [v76, v118, v182, v319, v407, v500, v557, v590] level7rlrrrll level7rlrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrrl_ok : everyKey (rowOK 6 level6) level7rlrrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrrll && everyKey (rowOK 6 level6) level7rlrrrlr) = true
  rw [level7rlrrrll_ok, level7rlrrrlr_ok]
  decide +kernel
def level7rlrrrrl : BinaryTree (List W) := (.node [v76, v118, v183, v245, v407, v500, v557, v590] (.node [v76, v118, v182, v407, v500, v557, v590, v594] (.node [v76, v118, v182, v407, v500, v551, v557, v590] .nil .nil) .nil) (.node [v76, v118, v184, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrrrl_ok : everyKey (rowOK 6 level6) level7rlrrrrl = true := by decide +kernel
def level7rlrrrrr : BinaryTree (List W) := (.node [v76, v118, v245, v407, v473, v500, v557, v590] (.node [v76, v118, v245, v338, v407, v500, v557, v590] (.node [v76, v118, v187, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v118, v245, v407, v500, v557, v579, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrrrr_ok : everyKey (rowOK 6 level6) level7rlrrrrr = true := by decide +kernel
def level7rlrrrr : BinaryTree (List W) := .node [v76, v118, v186, v245, v407, v500, v557, v590] level7rlrrrrl level7rlrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrrr_ok : everyKey (rowOK 6 level6) level7rlrrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrrrl && everyKey (rowOK 6 level6) level7rlrrrrr) = true
  rw [level7rlrrrrl_ok, level7rlrrrrr_ok]
  decide +kernel
def level7rlrrr : BinaryTree (List W) := .node [v76, v118, v182, v407, v476, v500, v557, v590] level7rlrrrl level7rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrrr_ok : everyKey (rowOK 6 level6) level7rlrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrrl && everyKey (rowOK 6 level6) level7rlrrrr) = true
  rw [level7rlrrrl_ok, level7rlrrrr_ok]
  decide +kernel
def level7rlrr : BinaryTree (List W) := .node [v76, v118, v182, v316, v377, v500, v557, v590] level7rlrrl level7rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlrr_ok : everyKey (rowOK 6 level6) level7rlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrrl && everyKey (rowOK 6 level6) level7rlrrr) = true
  rw [level7rlrrl_ok, level7rlrrr_ok]
  decide +kernel
def level7rlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v557, v590, v637, v642] level7rlrl level7rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rlr_ok : everyKey (rowOK 6 level6) level7rlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rlrl && everyKey (rowOK 6 level6) level7rlrr) = true
  rw [level7rlrl_ok, level7rlrr_ok]
  decide +kernel
def level7rl : BinaryTree (List W) := .node [v76, v118, v182, v245, v449, v500, v557, v590] level7rll level7rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rl_ok : everyKey (rowOK 6 level6) level7rl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rll && everyKey (rowOK 6 level6) level7rlr) = true
  rw [level7rll_ok, level7rlr_ok]
  decide +kernel
def level7rrlllll : BinaryTree (List W) := (.node [v76, v122, v182, v245, v407, v500, v557, v590] (.node [v76, v121, v182, v245, v407, v500, v557, v590] (.node [v76, v120, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v124, v182, v245, v407, v500, v557, v590] (.node [v76, v123, v182, v316, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlllll_ok : everyKey (rowOK 6 level6) level7rrlllll = true := by decide +kernel
def level7rrllllr : BinaryTree (List W) := (.node [v76, v128, v182, v245, v407, v500, v557, v590] (.node [v76, v127, v182, v245, v407, v500, v557, v590] (.node [v76, v126, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v131, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllllr_ok : everyKey (rowOK 6 level6) level7rrllllr = true := by decide +kernel
def level7rrllll : BinaryTree (List W) := .node [v76, v125, v182, v245, v407, v500, v557, v590] level7rrlllll level7rrllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllll_ok : everyKey (rowOK 6 level6) level7rrllll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlllll && everyKey (rowOK 6 level6) level7rrllllr) = true
  rw [level7rrlllll_ok, level7rrllllr_ok]
  decide +kernel
def level7rrlllrl : BinaryTree (List W) := (.node [v76, v135, v182, v316, v500, v557, v590] (.node [v76, v135, v182, v316, v407, v500, v557, v590] (.node [v76, v135, v182, v245, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v143, v182, v245, v316, v500, v557, v590] (.node [v76, v140, v182, v245, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlllrl_ok : everyKey (rowOK 6 level6) level7rrlllrl = true := by decide +kernel
def level7rrlllrr : BinaryTree (List W) := (.node [v76, v153, v182, v245, v407, v500, v557, v590] (.node [v76, v151, v182, v316, v407, v500, v557, v590] (.node [v76, v143, v182, v316, v500, v557, v590] .nil .nil) .nil) (.node [v76, v154, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlllrr_ok : everyKey (rowOK 6 level6) level7rrlllrr = true := by decide +kernel
def level7rrlllr : BinaryTree (List W) := .node [v76, v143, v182, v316, v407, v500, v557, v590] level7rrlllrl level7rrlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlllr_ok : everyKey (rowOK 6 level6) level7rrlllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlllrl && everyKey (rowOK 6 level6) level7rrlllrr) = true
  rw [level7rrlllrl_ok, level7rrlllrr_ok]
  decide +kernel
def level7rrlll : BinaryTree (List W) := .node [v76, v135, v140, v182, v245, v500, v557, v590] level7rrllll level7rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlll_ok : everyKey (rowOK 6 level6) level7rrlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrllll && everyKey (rowOK 6 level6) level7rrlllr) = true
  rw [level7rrllll_ok, level7rrlllr_ok]
  decide +kernel
def level7rrllrll : BinaryTree (List W) := (.node [v76, v158, v166, v182, v245, v407, v557, v590] (.node [v76, v157, v182, v245, v407, v500, v557, v590] (.node [v76, v156, v182, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v158, v182, v316, v407, v500, v557, v590] (.node [v76, v158, v182, v245, v316, v407, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllrll_ok : everyKey (rowOK 6 level6) level7rrllrll = true := by decide +kernel
def level7rrllrlr : BinaryTree (List W) := (.node [v76, v168, v182, v316, v407, v500, v557, v590] (.node [v76, v166, v182, v245, v407, v500, v557, v590] (.node [v76, v165, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v170, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllrlr_ok : everyKey (rowOK 6 level6) level7rrllrlr = true := by decide +kernel
def level7rrllrl : BinaryTree (List W) := .node [v76, v158, v182, v316, v407, v557, v590] level7rrllrll level7rrllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllrl_ok : everyKey (rowOK 6 level6) level7rrllrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrllrll && everyKey (rowOK 6 level6) level7rrllrlr) = true
  rw [level7rrllrll_ok, level7rrllrlr_ok]
  decide +kernel
def level7rrllrrl : BinaryTree (List W) := (.node [v76, v182, v207, v316, v407, v500, v557, v590] (.node [v76, v182, v197, v316, v407, v500, v557, v590] (.node [v76, v182, v185, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v208, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllrrl_ok : everyKey (rowOK 6 level6) level7rrllrrl = true := by decide +kernel
def level7rrllrrr : BinaryTree (List W) := (.node [v76, v182, v214, v316, v407, v500, v557, v590] (.node [v76, v182, v211, v316, v407, v500, v557, v590] (.node [v76, v182, v210, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v215, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllrrr_ok : everyKey (rowOK 6 level6) level7rrllrrr = true := by decide +kernel
def level7rrllrr : BinaryTree (List W) := .node [v76, v182, v209, v316, v407, v500, v557, v590] level7rrllrrl level7rrllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllrr_ok : everyKey (rowOK 6 level6) level7rrllrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrllrrl && everyKey (rowOK 6 level6) level7rrllrrr) = true
  rw [level7rrllrrl_ok, level7rrllrrr_ok]
  decide +kernel
def level7rrllr : BinaryTree (List W) := .node [v76, v171, v182, v316, v407, v500, v557, v590] level7rrllrl level7rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrllr_ok : everyKey (rowOK 6 level6) level7rrllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrllrl && everyKey (rowOK 6 level6) level7rrllrr) = true
  rw [level7rrllrl_ok, level7rrllrr_ok]
  decide +kernel
def level7rrll : BinaryTree (List W) := .node [v76, v155, v182, v245, v407, v500, v557, v590] level7rrlll level7rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrll_ok : everyKey (rowOK 6 level6) level7rrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlll && everyKey (rowOK 6 level6) level7rrllr) = true
  rw [level7rrlll_ok, level7rrllr_ok]
  decide +kernel
def level7rrlrlll : BinaryTree (List W) := (.node [v76, v182, v229, v316, v407, v500, v557, v590] (.node [v76, v182, v228, v316, v407, v500, v557, v590] (.node [v76, v182, v220, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v245, v288, v407, v500, v557, v590] (.node [v76, v182, v245, v285, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrlll_ok : everyKey (rowOK 6 level6) level7rrlrlll = true := by decide +kernel
def level7rrlrllr : BinaryTree (List W) := (.node [v76, v182, v245, v294, v407, v500, v557, v590] (.node [v76, v182, v245, v293, v407, v500, v557, v590] (.node [v76, v182, v245, v290, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v245, v316, v349, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrllr_ok : everyKey (rowOK 6 level6) level7rrlrllr = true := by decide +kernel
def level7rrlrll : BinaryTree (List W) := .node [v76, v182, v245, v289, v407, v500, v557, v590] level7rrlrlll level7rrlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrll_ok : everyKey (rowOK 6 level6) level7rrlrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrlll && everyKey (rowOK 6 level6) level7rrlrllr) = true
  rw [level7rrlrlll_ok, level7rrlrllr_ok]
  decide +kernel
def level7rrlrlrl : BinaryTree (List W) := (.node [v76, v182, v245, v316, v437, v500, v557, v590] (.node [v76, v182, v245, v316, v407, v557, v590, v637] (.node [v76, v182, v245, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v245, v316, v500, v557, v590, v625] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrlrl_ok : everyKey (rowOK 6 level6) level7rrlrlrl = true := by decide +kernel
def level7rrlrlrr : BinaryTree (List W) := (.node [v76, v182, v245, v407, v500, v557, v590, v601] (.node [v76, v182, v245, v407, v500, v557, v567, v590] (.node [v76, v182, v245, v407, v464, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v274, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrlrr_ok : everyKey (rowOK 6 level6) level7rrlrlrr = true := by decide +kernel
def level7rrlrlr : BinaryTree (List W) := .node [v76, v182, v245, v316, v500, v557, v590, v642] level7rrlrlrl level7rrlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrlr_ok : everyKey (rowOK 6 level6) level7rrlrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrlrl && everyKey (rowOK 6 level6) level7rrlrlrr) = true
  rw [level7rrlrlrl_ok, level7rrlrlrr_ok]
  decide +kernel
def level7rrlrl : BinaryTree (List W) := .node [v76, v182, v245, v316, v377, v500, v557, v590] level7rrlrll level7rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrl_ok : everyKey (rowOK 6 level6) level7rrlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrll && everyKey (rowOK 6 level6) level7rrlrlr) = true
  rw [level7rrlrll_ok, level7rrlrlr_ok]
  decide +kernel
def level7rrlrrll : BinaryTree (List W) := (.node [v76, v182, v316, v316, v407, v500, v557, v590] (.node [v76, v182, v287, v316, v407, v500, v557, v590] (.node [v76, v182, v284, v316, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v334, v407, v500, v557, v590] (.node [v76, v182, v316, v322, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrrll_ok : everyKey (rowOK 6 level6) level7rrlrrll = true := by decide +kernel
def level7rrlrrlr : BinaryTree (List W) := (.node [v76, v182, v316, v346, v407, v500, v557, v590] (.node [v76, v182, v316, v342, v407, v500, v557, v590] (.node [v76, v182, v316, v341, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v347, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrrlr_ok : everyKey (rowOK 6 level6) level7rrlrrlr = true := by decide +kernel
def level7rrlrrl : BinaryTree (List W) := .node [v76, v182, v316, v340, v407, v500, v557, v590] level7rrlrrll level7rrlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrrl_ok : everyKey (rowOK 6 level6) level7rrlrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrrll && everyKey (rowOK 6 level6) level7rrlrrlr) = true
  rw [level7rrlrrll_ok, level7rrlrrlr_ok]
  decide +kernel
def level7rrlrrrl : BinaryTree (List W) := (.node [v76, v182, v316, v365, v407, v500, v557, v590] (.node [v76, v182, v316, v364, v407, v500, v557, v590] (.node [v76, v182, v316, v349, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v366, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrrrl_ok : everyKey (rowOK 6 level6) level7rrlrrrl = true := by decide +kernel
def level7rrlrrrr : BinaryTree (List W) := (.node [v76, v182, v316, v377, v500, v557, v590] (.node [v76, v182, v316, v377, v407, v500, v557, v590] (.node [v76, v182, v316, v368, v407, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v385, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrrrr_ok : everyKey (rowOK 6 level6) level7rrlrrrr = true := by decide +kernel
def level7rrlrrr : BinaryTree (List W) := .node [v76, v182, v316, v367, v407, v500, v557, v590] level7rrlrrrl level7rrlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrrr_ok : everyKey (rowOK 6 level6) level7rrlrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrrrl && everyKey (rowOK 6 level6) level7rrlrrrr) = true
  rw [level7rrlrrrl_ok, level7rrlrrrr_ok]
  decide +kernel
def level7rrlrr : BinaryTree (List W) := .node [v76, v182, v316, v349, v407, v500, v557, v590] level7rrlrrl level7rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlrr_ok : everyKey (rowOK 6 level6) level7rrlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrrl && everyKey (rowOK 6 level6) level7rrlrrr) = true
  rw [level7rrlrrl_ok, level7rrlrrr_ok]
  decide +kernel
def level7rrlr : BinaryTree (List W) := .node [v76, v182, v276, v316, v407, v500, v557, v590] level7rrlrl level7rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrlr_ok : everyKey (rowOK 6 level6) level7rrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrlrl && everyKey (rowOK 6 level6) level7rrlrr) = true
  rw [level7rrlrl_ok, level7rrlrr_ok]
  decide +kernel
def level7rrl : BinaryTree (List W) := .node [v76, v182, v216, v316, v407, v500, v557, v590] level7rrll level7rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrl_ok : everyKey (rowOK 6 level6) level7rrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrll && everyKey (rowOK 6 level6) level7rrlr) = true
  rw [level7rrll_ok, level7rrlr_ok]
  decide +kernel
def level7rrrllll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v446, v500, v557, v590] (.node [v76, v182, v316, v407, v437, v500, v557, v590] (.node [v76, v182, v316, v407, v428, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v450, v500, v557, v590] (.node [v76, v182, v316, v407, v448, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrllll_ok : everyKey (rowOK 6 level6) level7rrrllll = true := by decide +kernel
def level7rrrlllr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v461, v500, v557, v590] (.node [v76, v182, v316, v407, v460, v500, v557, v590] (.node [v76, v182, v316, v407, v454, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v466, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlllr_ok : everyKey (rowOK 6 level6) level7rrrlllr = true := by decide +kernel
def level7rrrlll : BinaryTree (List W) := .node [v76, v182, v316, v407, v453, v500, v557, v590] level7rrrllll level7rrrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlll_ok : everyKey (rowOK 6 level6) level7rrrlll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrllll && everyKey (rowOK 6 level6) level7rrrlllr) = true
  rw [level7rrrllll_ok, level7rrrlllr_ok]
  decide +kernel
def level7rrrllrl : BinaryTree (List W) := (.node [v76, v182, v316, v407, v484, v500, v557, v590] (.node [v76, v182, v316, v407, v478, v500, v557, v590] (.node [v76, v182, v316, v407, v475, v500, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v514, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrllrl_ok : everyKey (rowOK 6 level6) level7rrrllrl = true := by decide +kernel
def level7rrrllrr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v537, v557, v590] (.node [v76, v182, v316, v407, v500, v527, v557, v590] (.node [v76, v182, v316, v407, v500, v526, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v540, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrllrr_ok : everyKey (rowOK 6 level6) level7rrrllrr = true := by decide +kernel
def level7rrrllr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v518, v557, v590] level7rrrllrl level7rrrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrllr_ok : everyKey (rowOK 6 level6) level7rrrllr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrllrl && everyKey (rowOK 6 level6) level7rrrllrr) = true
  rw [level7rrrllrl_ok, level7rrrllrr_ok]
  decide +kernel
def level7rrrll : BinaryTree (List W) := .node [v76, v182, v316, v407, v474, v500, v557, v590] level7rrrlll level7rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrll_ok : everyKey (rowOK 6 level6) level7rrrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrlll && everyKey (rowOK 6 level6) level7rrrllr) = true
  rw [level7rrrlll_ok, level7rrrllr_ok]
  decide +kernel
def level7rrrlrll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v547, v557, v590] (.node [v76, v182, v316, v407, v500, v544, v557, v590] (.node [v76, v182, v316, v407, v500, v542, v557, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v549, v557, v590] (.node [v76, v182, v316, v407, v500, v548, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlrll_ok : everyKey (rowOK 6 level6) level7rrrlrll = true := by decide +kernel
def level7rrrlrlr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v557, v577, v590] (.node [v76, v182, v316, v407, v500, v557, v574, v590] (.node [v76, v182, v316, v407, v500, v557, v566, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v557, v583, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlrlr_ok : everyKey (rowOK 6 level6) level7rrrlrlr = true := by decide +kernel
def level7rrrlrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v554, v557, v590] level7rrrlrll level7rrrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlrl_ok : everyKey (rowOK 6 level6) level7rrrlrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrlrll && everyKey (rowOK 6 level6) level7rrrlrlr) = true
  rw [level7rrrlrll_ok, level7rrrlrlr_ok]
  decide +kernel
def level7rrrlrrl : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v557, v590] (.node [v76, v182, v316, v407, v500, v557, v588, v590] (.node [v76, v182, v316, v407, v500, v557, v586, v590] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v557, v590, v595] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlrrl_ok : everyKey (rowOK 6 level6) level7rrrlrrl = true := by decide +kernel
def level7rrrlrrr : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v557, v590, v610] (.node [v76, v182, v316, v407, v500, v557, v590, v608] (.node [v76, v182, v316, v407, v500, v557, v590, v604] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v557, v590, v612] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlrrr_ok : everyKey (rowOK 6 level6) level7rrrlrrr = true := by decide +kernel
def level7rrrlrr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v557, v590, v602] level7rrrlrrl level7rrrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlrr_ok : everyKey (rowOK 6 level6) level7rrrlrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrlrrl && everyKey (rowOK 6 level6) level7rrrlrrr) = true
  rw [level7rrrlrrl_ok, level7rrrlrrr_ok]
  decide +kernel
def level7rrrlr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v557, v584, v590] level7rrrlrl level7rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrlr_ok : everyKey (rowOK 6 level6) level7rrrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrlrl && everyKey (rowOK 6 level6) level7rrrlrr) = true
  rw [level7rrrlrl_ok, level7rrrlrr_ok]
  decide +kernel
def level7rrrl : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v541, v557, v590] level7rrrll level7rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrl_ok : everyKey (rowOK 6 level6) level7rrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrll && everyKey (rowOK 6 level6) level7rrrlr) = true
  rw [level7rrrll_ok, level7rrrlr_ok]
  decide +kernel
def level7rrrrlll : BinaryTree (List W) := (.node [v76, v182, v316, v407, v500, v557, v590, v638] (.node [v76, v182, v316, v407, v500, v557, v590, v637] (.node [v76, v182, v316, v407, v500, v557, v590, v627] .nil .nil) .nil) (.node [v76, v182, v316, v407, v500, v557, v590, v647] (.node [v76, v182, v316, v407, v500, v557, v590, v642] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrlll_ok : everyKey (rowOK 6 level6) level7rrrrlll = true := by decide +kernel
def level7rrrrllr : BinaryTree (List W) := (.node [v76, v182, v316, v500, v557, v590, v642] (.node [v76, v182, v316, v500, v557, v590, v625] (.node [v76, v182, v316, v437, v500, v557, v590] .nil .nil) .nil) (.node [v77, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrllr_ok : everyKey (rowOK 6 level6) level7rrrrllr = true := by decide +kernel
def level7rrrrll : BinaryTree (List W) := .node [v76, v182, v316, v407, v557, v590, v637] level7rrrrlll level7rrrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrll_ok : everyKey (rowOK 6 level6) level7rrrrll = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrlll && everyKey (rowOK 6 level6) level7rrrrllr) = true
  rw [level7rrrrlll_ok, level7rrrrllr_ok]
  decide +kernel
def level7rrrrlrl : BinaryTree (List W) := (.node [v83, v118, v182, v245, v407, v500, v557, v590] (.node [v81, v118, v182, v245, v407, v500, v557, v590] (.node [v80, v118, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v84, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrlrl_ok : everyKey (rowOK 6 level6) level7rrrrlrl = true := by decide +kernel
def level7rrrrlrr : BinaryTree (List W) := (.node [v118, v158, v164, v182, v245, v407, v557, v590] (.node [v118, v143, v182, v201, v245, v500, v557, v590] (.node [v118, v135, v182, v193, v245, v500, v557, v590] .nil .nil) .nil) (.node [v118, v162, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrlrr_ok : everyKey (rowOK 6 level6) level7rrrrlrr = true := by decide +kernel
def level7rrrrlr : BinaryTree (List W) := .node [v85, v118, v182, v245, v407, v500, v557, v590] level7rrrrlrl level7rrrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrlr_ok : everyKey (rowOK 6 level6) level7rrrrlr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrlrl && everyKey (rowOK 6 level6) level7rrrrlrr) = true
  rw [level7rrrrlrl_ok, level7rrrrlrr_ok]
  decide +kernel
def level7rrrrl : BinaryTree (List W) := .node [v79, v118, v182, v245, v407, v500, v557, v590] level7rrrrll level7rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrl_ok : everyKey (rowOK 6 level6) level7rrrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrll && everyKey (rowOK 6 level6) level7rrrrlr) = true
  rw [level7rrrrll_ok, level7rrrrlr_ok]
  decide +kernel
def level7rrrrrll : BinaryTree (List W) := (.node [v118, v168, v182, v245, v437, v500, v557, v590] (.node [v118, v167, v182, v245, v407, v500, v557, v590] (.node [v118, v164, v182, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v118, v182, v193, v245, v500, v557, v590] (.node [v118, v182, v193, v245, v407, v500, v557, v590] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrrll_ok : everyKey (rowOK 6 level6) level7rrrrrll = true := by decide +kernel
def level7rrrrrlr : BinaryTree (List W) := (.node [v118, v182, v245, v265, v407, v500, v557, v590] (.node [v118, v182, v201, v245, v500, v557, v590] (.node [v118, v182, v201, v245, v407, v500, v557, v590] .nil .nil) .nil) (.node [v118, v182, v245, v268, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrrlr_ok : everyKey (rowOK 6 level6) level7rrrrrlr = true := by decide +kernel
def level7rrrrrl : BinaryTree (List W) := .node [v118, v182, v197, v245, v437, v500, v557, v590] level7rrrrrll level7rrrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrrl_ok : everyKey (rowOK 6 level6) level7rrrrrl = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrrll && everyKey (rowOK 6 level6) level7rrrrrlr) = true
  rw [level7rrrrrll_ok, level7rrrrrlr_ok]
  decide +kernel
def level7rrrrrrl : BinaryTree (List W) := (.node [v118, v182, v245, v377, v437, v500, v557, v590] (.node [v118, v182, v245, v376, v407, v500, v557, v590] (.node [v118, v182, v245, v274, v437, v500, v557, v590] .nil .nil) .nil) (.node [v118, v182, v245, v407, v463, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrrrl_ok : everyKey (rowOK 6 level6) level7rrrrrrl = true := by decide +kernel
def level7rrrrrrr : BinaryTree (List W) := (.node [v118, v182, v245, v437, v500, v557, v566, v590] (.node [v118, v182, v245, v407, v500, v557, v590, v614] (.node [v118, v182, v245, v407, v500, v557, v562, v590] .nil .nil) .nil) (.node [v118, v182, v245, v437, v500, v557, v586, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrrrr_ok : everyKey (rowOK 6 level6) level7rrrrrrr = true := by decide +kernel
def level7rrrrrr : BinaryTree (List W) := .node [v118, v182, v245, v407, v500, v557, v561, v590] level7rrrrrrl level7rrrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrrr_ok : everyKey (rowOK 6 level6) level7rrrrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrrrl && everyKey (rowOK 6 level6) level7rrrrrrr) = true
  rw [level7rrrrrrl_ok, level7rrrrrrr_ok]
  decide +kernel
def level7rrrrr : BinaryTree (List W) := .node [v118, v182, v245, v270, v407, v500, v557, v590] level7rrrrrl level7rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrrr_ok : everyKey (rowOK 6 level6) level7rrrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrrl && everyKey (rowOK 6 level6) level7rrrrrr) = true
  rw [level7rrrrrl_ok, level7rrrrrr_ok]
  decide +kernel
def level7rrrr : BinaryTree (List W) := .node [v118, v163, v182, v245, v407, v500, v557, v590] level7rrrrl level7rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrrr_ok : everyKey (rowOK 6 level6) level7rrrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrrl && everyKey (rowOK 6 level6) level7rrrrr) = true
  rw [level7rrrrl_ok, level7rrrrr_ok]
  decide +kernel
def level7rrr : BinaryTree (List W) := .node [v76, v182, v316, v407, v500, v557, v590, v625] level7rrrl level7rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rrr_ok : everyKey (rowOK 6 level6) level7rrr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrrl && everyKey (rowOK 6 level6) level7rrrr) = true
  rw [level7rrrl_ok, level7rrrr_ok]
  decide +kernel
def level7rr : BinaryTree (List W) := .node [v76, v182, v316, v407, v415, v500, v557, v590] level7rrl level7rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7rr_ok : everyKey (rowOK 6 level6) level7rr = true := by
  change (_ && everyKey (rowOK 6 level6) level7rrl && everyKey (rowOK 6 level6) level7rrr) = true
  rw [level7rrl_ok, level7rrr_ok]
  decide +kernel
def level7r : BinaryTree (List W) := .node [v76, v119, v182, v245, v407, v500, v557, v590] level7rl level7rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7r_ok : everyKey (rowOK 6 level6) level7r = true := by
  change (_ && everyKey (rowOK 6 level6) level7rl && everyKey (rowOK 6 level6) level7rr) = true
  rw [level7rl_ok, level7rr_ok]
  decide +kernel
def level7 : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v491, v557, v590] level7l level7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by
  change (_ && everyKey (rowOK 6 level6) level7l && everyKey (rowOK 6 level6) level7r) = true
  rw [level7l_ok, level7r_ok]
  decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok
def level8lllll : BinaryTree (List W) := (.node [v3, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v2, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v4, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lllll_ok : everyKey (rowOK 7 level7) level8lllll = true := by decide +kernel
def level8llllr : BinaryTree (List W) := (.node [v11, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v10, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v12, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llllr_ok : everyKey (rowOK 7 level7) level8llllr = true := by decide +kernel
def level8llll : BinaryTree (List W) := .node [v5, v76, v118, v182, v245, v407, v500, v557, v590] level8lllll level8llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llll_ok : everyKey (rowOK 7 level7) level8llll = true := by
  change (_ && everyKey (rowOK 7 level7) level8lllll && everyKey (rowOK 7 level7) level8llllr) = true
  rw [level8lllll_ok, level8llllr_ok]
  decide +kernel
def level8lllrl : BinaryTree (List W) := (.node [v17, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v15, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v18, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lllrl_ok : everyKey (rowOK 7 level7) level8lllrl = true := by decide +kernel
def level8lllrr : BinaryTree (List W) := (.node [v23, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v20, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v24, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lllrr_ok : everyKey (rowOK 7 level7) level8lllrr = true := by decide +kernel
def level8lllr : BinaryTree (List W) := .node [v19, v76, v118, v182, v245, v407, v500, v557, v590] level8lllrl level8lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lllr_ok : everyKey (rowOK 7 level7) level8lllr = true := by
  change (_ && everyKey (rowOK 7 level7) level8lllrl && everyKey (rowOK 7 level7) level8lllrr) = true
  rw [level8lllrl_ok, level8lllrr_ok]
  decide +kernel
def level8lll : BinaryTree (List W) := .node [v14, v76, v118, v182, v245, v407, v500, v557, v590] level8llll level8lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lll_ok : everyKey (rowOK 7 level7) level8lll = true := by
  change (_ && everyKey (rowOK 7 level7) level8llll && everyKey (rowOK 7 level7) level8lllr) = true
  rw [level8llll_ok, level8lllr_ok]
  decide +kernel
def level8llrll : BinaryTree (List W) := (.node [v30, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v27, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v31, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llrll_ok : everyKey (rowOK 7 level7) level8llrll = true := by decide +kernel
def level8llrlr : BinaryTree (List W) := (.node [v37, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v36, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v39, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llrlr_ok : everyKey (rowOK 7 level7) level8llrlr = true := by decide +kernel
def level8llrl : BinaryTree (List W) := .node [v33, v76, v118, v182, v245, v407, v500, v557, v590] level8llrll level8llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llrl_ok : everyKey (rowOK 7 level7) level8llrl = true := by
  change (_ && everyKey (rowOK 7 level7) level8llrll && everyKey (rowOK 7 level7) level8llrlr) = true
  rw [level8llrll_ok, level8llrlr_ok]
  decide +kernel
def level8llrrl : BinaryTree (List W) := (.node [v46, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v44, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v53, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llrrl_ok : everyKey (rowOK 7 level7) level8llrrl = true := by decide +kernel
def level8llrrr : BinaryTree (List W) := (.node [v60, v76, v118, v182, v245, v407, v500, v557, v590] (.node [v59, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v65, v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llrrr_ok : everyKey (rowOK 7 level7) level8llrrr = true := by decide +kernel
def level8llrr : BinaryTree (List W) := .node [v55, v76, v118, v182, v245, v407, v500, v557, v590] level8llrrl level8llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llrr_ok : everyKey (rowOK 7 level7) level8llrr = true := by
  change (_ && everyKey (rowOK 7 level7) level8llrrl && everyKey (rowOK 7 level7) level8llrrr) = true
  rw [level8llrrl_ok, level8llrrr_ok]
  decide +kernel
def level8llr : BinaryTree (List W) := .node [v39, v76, v118, v182, v245, v500, v557, v590] level8llrl level8llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8llr_ok : everyKey (rowOK 7 level7) level8llr = true := by
  change (_ && everyKey (rowOK 7 level7) level8llrl && everyKey (rowOK 7 level7) level8llrr) = true
  rw [level8llrl_ok, level8llrr_ok]
  decide +kernel
def level8ll : BinaryTree (List W) := .node [v25, v76, v118, v182, v245, v407, v500, v557, v590] level8lll level8llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8ll_ok : everyKey (rowOK 7 level7) level8ll = true := by
  change (_ && everyKey (rowOK 7 level7) level8lll && everyKey (rowOK 7 level7) level8llr) = true
  rw [level8lll_ok, level8llr_ok]
  decide +kernel
def level8lrlll : BinaryTree (List W) := (.node [v76, v95, v118, v182, v245, v407, v500, v557, v590] (.node [v76, v91, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v96, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrlll_ok : everyKey (rowOK 7 level7) level8lrlll = true := by decide +kernel
def level8lrllr : BinaryTree (List W) := (.node [v76, v106, v118, v182, v245, v407, v500, v557, v590] (.node [v76, v103, v118, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v107, v118, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrllr_ok : everyKey (rowOK 7 level7) level8lrllr = true := by decide +kernel
def level8lrll : BinaryTree (List W) := .node [v76, v96, v182, v245, v407, v500, v557, v590] level8lrlll level8lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrll_ok : everyKey (rowOK 7 level7) level8lrll = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrlll && everyKey (rowOK 7 level7) level8lrllr) = true
  rw [level8lrlll_ok, level8lrllr_ok]
  decide +kernel
def level8lrlrl : BinaryTree (List W) := (.node [v76, v118, v131, v182, v245, v407, v500, v557, v590] (.node [v76, v118, v123, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v135, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrlrl_ok : everyKey (rowOK 7 level7) level8lrlrl = true := by decide +kernel
def level8lrlrr : BinaryTree (List W) := (.node [v76, v118, v143, v182, v245, v500, v557, v590] (.node [v76, v118, v143, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v151, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrlrr_ok : everyKey (rowOK 7 level7) level8lrlrr = true := by decide +kernel
def level8lrlr : BinaryTree (List W) := .node [v76, v118, v135, v182, v245, v500, v557, v590] level8lrlrl level8lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrlr_ok : everyKey (rowOK 7 level7) level8lrlr = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrlrl && everyKey (rowOK 7 level7) level8lrlrr) = true
  rw [level8lrlrl_ok, level8lrlrr_ok]
  decide +kernel
def level8lrl : BinaryTree (List W) := .node [v76, v112, v118, v182, v245, v407, v500, v557, v590] level8lrll level8lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrl_ok : everyKey (rowOK 7 level7) level8lrl = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrll && everyKey (rowOK 7 level7) level8lrlr) = true
  rw [level8lrll_ok, level8lrlr_ok]
  decide +kernel
def level8lrrll : BinaryTree (List W) := (.node [v76, v118, v158, v182, v245, v407, v557, v590] (.node [v76, v118, v158, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v168, v182, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrrll_ok : everyKey (rowOK 7 level7) level8lrrll = true := by decide +kernel
def level8lrrlr : BinaryTree (List W) := (.node [v76, v118, v182, v185, v245, v407, v500, v557, v590] (.node [v76, v118, v171, v182, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v197, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrrlr_ok : everyKey (rowOK 7 level7) level8lrrlr = true := by decide +kernel
def level8lrrl : BinaryTree (List W) := .node [v76, v118, v170, v182, v245, v407, v500, v557, v590] level8lrrll level8lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrrl_ok : everyKey (rowOK 7 level7) level8lrrl = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrrll && everyKey (rowOK 7 level7) level8lrrlr) = true
  rw [level8lrrll_ok, level8lrrlr_ok]
  decide +kernel
def level8lrrrl : BinaryTree (List W) := (.node [v76, v118, v182, v210, v245, v407, v500, v557, v590] (.node [v76, v118, v182, v208, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v211, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrrrl_ok : everyKey (rowOK 7 level7) level8lrrrl = true := by decide +kernel
def level8lrrrr : BinaryTree (List W) := (.node [v76, v118, v182, v216, v245, v407, v500, v557, v590] (.node [v76, v118, v182, v214, v245, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v228, v245, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrrrr_ok : everyKey (rowOK 7 level7) level8lrrrr = true := by decide +kernel
def level8lrrr : BinaryTree (List W) := .node [v76, v118, v182, v211, v407, v500, v557, v590] level8lrrrl level8lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrrr_ok : everyKey (rowOK 7 level7) level8lrrr = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrrrl && everyKey (rowOK 7 level7) level8lrrrr) = true
  rw [level8lrrrl_ok, level8lrrrr_ok]
  decide +kernel
def level8lrr : BinaryTree (List W) := .node [v76, v118, v182, v207, v245, v407, v500, v557, v590] level8lrrl level8lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lrr_ok : everyKey (rowOK 7 level7) level8lrr = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrrl && everyKey (rowOK 7 level7) level8lrrr) = true
  rw [level8lrrl_ok, level8lrrr_ok]
  decide +kernel
def level8lr : BinaryTree (List W) := .node [v76, v118, v156, v182, v245, v407, v500, v557, v590] level8lrl level8lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8lr_ok : everyKey (rowOK 7 level7) level8lr = true := by
  change (_ && everyKey (rowOK 7 level7) level8lrl && everyKey (rowOK 7 level7) level8lrr) = true
  rw [level8lrl_ok, level8lrr_ok]
  decide +kernel
def level8l : BinaryTree (List W) := .node [v76, v87, v118, v182, v245, v407, v500, v557, v590] level8ll level8lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8l_ok : everyKey (rowOK 7 level7) level8l = true := by
  change (_ && everyKey (rowOK 7 level7) level8ll && everyKey (rowOK 7 level7) level8lr) = true
  rw [level8ll_ok, level8lr_ok]
  decide +kernel
def level8rllll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v316, v407, v500, v557, v590] (.node [v76, v118, v182, v245, v274, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v322, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rllll_ok : everyKey (rowOK 7 level7) level8rllll = true := by decide +kernel
def level8rlllr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v346, v407, v500, v557, v590] (.node [v76, v118, v182, v245, v342, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v347, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlllr_ok : everyKey (rowOK 7 level7) level8rlllr = true := by decide +kernel
def level8rlll : BinaryTree (List W) := .node [v76, v118, v182, v245, v340, v407, v500, v557, v590] level8rllll level8rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlll_ok : everyKey (rowOK 7 level7) level8rlll = true := by
  change (_ && everyKey (rowOK 7 level7) level8rllll && everyKey (rowOK 7 level7) level8rlllr) = true
  rw [level8rllll_ok, level8rlllr_ok]
  decide +kernel
def level8rllrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v364, v407, v500, v557, v590] (.node [v76, v118, v182, v245, v349, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v365, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rllrl_ok : everyKey (rowOK 7 level7) level8rllrl = true := by decide +kernel
def level8rllrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v377, v407, v500, v557, v590] (.node [v76, v118, v182, v245, v368, v407, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v377, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rllrr_ok : everyKey (rowOK 7 level7) level8rllrr = true := by decide +kernel
def level8rllr : BinaryTree (List W) := .node [v76, v118, v182, v245, v366, v407, v500, v557, v590] level8rllrl level8rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rllr_ok : everyKey (rowOK 7 level7) level8rllr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rllrl && everyKey (rowOK 7 level7) level8rllrr) = true
  rw [level8rllrl_ok, level8rllrr_ok]
  decide +kernel
def level8rll : BinaryTree (List W) := .node [v76, v118, v182, v245, v349, v407, v500, v557, v590] level8rlll level8rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rll_ok : everyKey (rowOK 7 level7) level8rll = true := by
  change (_ && everyKey (rowOK 7 level7) level8rlll && everyKey (rowOK 7 level7) level8rllr) = true
  rw [level8rlll_ok, level8rllr_ok]
  decide +kernel
def level8rlrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v428, v500, v557, v590] (.node [v76, v118, v182, v245, v407, v415, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v437, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlrll_ok : everyKey (rowOK 7 level7) level8rlrll = true := by decide +kernel
def level8rlrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v453, v500, v557, v590] (.node [v76, v118, v182, v245, v407, v450, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v454, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlrlr_ok : everyKey (rowOK 7 level7) level8rlrlr = true := by decide +kernel
def level8rlrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v446, v500, v557, v590] level8rlrll level8rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlrl_ok : everyKey (rowOK 7 level7) level8rlrl = true := by
  change (_ && everyKey (rowOK 7 level7) level8rlrll && everyKey (rowOK 7 level7) level8rlrlr) = true
  rw [level8rlrll_ok, level8rlrlr_ok]
  decide +kernel
def level8rlrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v474, v500, v557, v590] (.node [v76, v118, v182, v245, v407, v466, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v475, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlrrl_ok : everyKey (rowOK 7 level7) level8rlrrl = true := by decide +kernel
def level8rlrrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v514, v557, v590] (.node [v76, v118, v182, v245, v407, v484, v500, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v518, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlrrr_ok : everyKey (rowOK 7 level7) level8rlrrr = true := by decide +kernel
def level8rlrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v478, v500, v557, v590] level8rlrrl level8rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlrr_ok : everyKey (rowOK 7 level7) level8rlrr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rlrrl && everyKey (rowOK 7 level7) level8rlrrr) = true
  rw [level8rlrrl_ok, level8rlrrr_ok]
  decide +kernel
def level8rlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v460, v500, v557, v590] level8rlrl level8rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rlr_ok : everyKey (rowOK 7 level7) level8rlr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rlrl && everyKey (rowOK 7 level7) level8rlrr) = true
  rw [level8rlrl_ok, level8rlrr_ok]
  decide +kernel
def level8rl : BinaryTree (List W) := .node [v76, v118, v182, v245, v385, v407, v500, v557, v590] level8rll level8rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rl_ok : everyKey (rowOK 7 level7) level8rl = true := by
  change (_ && everyKey (rowOK 7 level7) level8rll && everyKey (rowOK 7 level7) level8rlr) = true
  rw [level8rll_ok, level8rlr_ok]
  decide +kernel
def level8rrlll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v540, v557, v590] (.node [v76, v118, v182, v245, v407, v500, v537, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v542, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrlll_ok : everyKey (rowOK 7 level7) level8rrlll = true := by decide +kernel
def level8rrllr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v549, v557, v590] (.node [v76, v118, v182, v245, v407, v500, v547, v557, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v554, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrllr_ok : everyKey (rowOK 7 level7) level8rrllr = true := by decide +kernel
def level8rrll : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v544, v557, v590] level8rrlll level8rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrll_ok : everyKey (rowOK 7 level7) level8rrll = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrlll && everyKey (rowOK 7 level7) level8rrllr) = true
  rw [level8rrlll_ok, level8rrllr_ok]
  decide +kernel
def level8rrlrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v577, v590] (.node [v76, v118, v182, v245, v407, v500, v557, v574, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v557, v583, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrlrl_ok : everyKey (rowOK 7 level7) level8rrlrl = true := by decide +kernel
def level8rrlrr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v588, v590] (.node [v76, v118, v182, v245, v407, v500, v557, v586, v590] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v557, v590, v595] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrlrr_ok : everyKey (rowOK 7 level7) level8rrlrr = true := by decide +kernel
def level8rrlr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v584, v590] level8rrlrl level8rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrlr_ok : everyKey (rowOK 7 level7) level8rrlr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrlrl && everyKey (rowOK 7 level7) level8rrlrr) = true
  rw [level8rrlrl_ok, level8rrlrr_ok]
  decide +kernel
def level8rrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v566, v590] level8rrll level8rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrl_ok : everyKey (rowOK 7 level7) level8rrl = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrll && everyKey (rowOK 7 level7) level8rrlr) = true
  rw [level8rrll_ok, level8rrlr_ok]
  decide +kernel
def level8rrrll : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v590, v608] (.node [v76, v118, v182, v245, v407, v500, v557, v590, v604] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v557, v590, v610] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrrll_ok : everyKey (rowOK 7 level7) level8rrrll = true := by decide +kernel
def level8rrrlr : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v590, v638] (.node [v76, v118, v182, v245, v407, v500, v557, v590, v637] .nil .nil) (.node [v76, v118, v182, v245, v407, v500, v557, v590, v642] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrrlr_ok : everyKey (rowOK 7 level7) level8rrrlr = true := by decide +kernel
def level8rrrl : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v590, v625] level8rrrll level8rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrrl_ok : everyKey (rowOK 7 level7) level8rrrl = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrrll && everyKey (rowOK 7 level7) level8rrrlr) = true
  rw [level8rrrll_ok, level8rrrlr_ok]
  decide +kernel
def level8rrrrl : BinaryTree (List W) := (.node [v76, v118, v182, v245, v437, v500, v557, v590] (.node [v76, v118, v182, v245, v407, v557, v590, v637] .nil .nil) (.node [v76, v118, v182, v245, v500, v557, v590, v625] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrrrl_ok : everyKey (rowOK 7 level7) level8rrrrl = true := by decide +kernel
def level8rrrrr : BinaryTree (List W) := (.node [v76, v182, v245, v316, v407, v500, v557, v590] (.node [v76, v118, v182, v316, v407, v500, v557, v590] .nil .nil) (.node [v76, v182, v316, v407, v500, v557, v590] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrrrr_ok : everyKey (rowOK 7 level7) level8rrrrr = true := by decide +kernel
def level8rrrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v500, v557, v590, v642] level8rrrrl level8rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrrr_ok : everyKey (rowOK 7 level7) level8rrrr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrrrl && everyKey (rowOK 7 level7) level8rrrrr) = true
  rw [level8rrrrl_ok, level8rrrrr_ok]
  decide +kernel
def level8rrr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v590, v647] level8rrrl level8rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rrr_ok : everyKey (rowOK 7 level7) level8rrr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrrl && everyKey (rowOK 7 level7) level8rrrr) = true
  rw [level8rrrl_ok, level8rrrr_ok]
  decide +kernel
def level8rr : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v557, v590, v602] level8rrl level8rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8rr_ok : everyKey (rowOK 7 level7) level8rr = true := by
  change (_ && everyKey (rowOK 7 level7) level8rrl && everyKey (rowOK 7 level7) level8rrr) = true
  rw [level8rrl_ok, level8rrr_ok]
  decide +kernel
def level8r : BinaryTree (List W) := .node [v76, v118, v182, v245, v407, v500, v526, v557, v590] level8rl level8rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8r_ok : everyKey (rowOK 7 level7) level8r = true := by
  change (_ && everyKey (rowOK 7 level7) level8rl && everyKey (rowOK 7 level7) level8rr) = true
  rw [level8rl_ok, level8rr_ok]
  decide +kernel
def level8 : BinaryTree (List W) := .node [v76, v118, v182, v229, v245, v407, v500, v557, v590] level8l level8r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level8_ok : everyKey (rowOK 7 level7) level8 = true := by
  change (_ && everyKey (rowOK 7 level7) level8l && everyKey (rowOK 7 level7) level8r) = true
  rw [level8l_ok, level8r_ok]
  decide +kernel
theorem closed8 : Closed 8 level8 := closed_next 7 (by decide) level8 level7 closed7 level8_ok
def level9 : BinaryTree (List W) := (.node [v76, v118, v182, v245, v407, v500, v557, v590] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem level9_ok : everyKey (rowOK 8 level8) level9 = true := by decide +kernel
theorem closed9 : Closed 9 level9 := closed_next 8 (by decide) level9 level8 closed8 level9_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 9 ins.toFinset :=
  @no_build 9 level9 ins (by decide +kernel) (by decide) closed9 (by decide +kernel)

def target (x : Fin 8 → Bool) : Bool :=
  Nat.testBit 0xfffffffffffffffffffffffffffcfffcfffffffeffffffaafefefefe00000000 (∑ i : Fin 8, if x i then 2 ^ (i : ℕ) else 0)

def edges : List ℕ :=
  [0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7]

def edgeFunction (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edges.length / 2,
    (List.ofFn x).getD (edges.getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (edges.getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem same : ∀ x, target x = edgeFunction x := by
  decide +kernel

theorem binary_lower (gates : List Gate) (o : ℕ) (hlegal : ∀ g ∈ gates, legal g)
    (h : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target x) :
    10 ≤ binaryCost gates := by
  exact Nat.succ_le_of_lt (bound_from_search 0xfffffffffffffffffffffffffffcfffcfffffffeffffffaafefefefe00000000 9 ins (by decide +kernel)
    sampled rfl lower gates o hlegal h)

-- Inputs 1 and 2 share an OR, as do inputs 0 and 7.
def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [8, 9]⟩,
    ⟨.and, [10, 7]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [3, 4]⟩,
    ⟨.or, [15, 9]⟩, ⟨.and, [6, 16]⟩, ⟨.or, [17, 14]⟩], 18⟩

theorem witness_mono :
    ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem witness_size : witness.gates.length = 11 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_correct : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_14668_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_14668_aux in
theorem PEqualNP.Outside.L_meta_14668 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hlegal _ hcomp
  by_cases present : ∃ g ∈ gates, g.op = .not
  · obtain ⟨g, hg, hn⟩ := present
    have htarget x : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target x :=
      (hcomp x).trans (same x).symm
    have lower_bound := binary_lower gates o hlegal htarget
    have hcost : binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, hg, by simp [isBinary, hn]⟩
    exact ⟨witness.gates, witness.output, witness_mono, by rw [witness_size]; omega,
      fun x => (witness_correct x).trans (same x)⟩
  · refine ⟨gates, o, ?_, le_rfl, hcomp⟩
    intro g hg
    obtain ⟨hop, cap⟩ := hlegal g hg
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g, hg, eq⟩).elim)), cap⟩
