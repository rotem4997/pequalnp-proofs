import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13733_aux

-- SPDX-License-Identifier: Apache-2.0
-- The signed live-wire checker adapts tacyon52’s L_meta_8639 (PR 12794).
-- The sample and the first-layer symmetry certificate are for this truth table.

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

-- The upper and lower halves represent opposite target labels on 54 pairs of assignments.
abbrev W := BitVec 108
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 54 := ((x >>> 54) ^^^ x).setWidth 54
def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 54) ++ (0 : BitVec 54)
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

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 54+i.val < 108 := by omega
  have hi' : i.val < 108 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 54) :
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
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
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
  · change reachable av (BitVec.allOnes 108 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 108)
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

private def bit (k : Fin 108) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 108) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 108) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#108)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

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
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
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
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 108, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 108) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 6) : Bool := bit k (ins.getD i.val 0)
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

-- Coordinate packing used in the symmetry transport.
def bitTable : (n : ℕ) → (ℕ → Bool) → BitVec n
  | 0, _ => 0
  | n+1, f => BitVec.cons (f n) (bitTable n f)

@[simp] theorem bitTable_get (n : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < n) :
    (bitTable n f)[i] = f i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [bitTable, BitVec.getElem_cons]
    split
    next h => rw [h]
    next h => exact ih i (by omega)

def wordMap {n : ℕ} (p : Fin n → Fin n) (x : BitVec n) : BitVec n :=
  bitTable n (fun i => if hi : i < n then x[(p ⟨i,hi⟩).val] else false)

@[simp] theorem wordMap_get {n : ℕ} (p : Fin n → Fin n) (x : BitVec n)
    (i : ℕ) (hi : i < n) : (wordMap p x)[i] = x[(p ⟨i,hi⟩).val] := by
  simp [wordMap, hi]

theorem wordMap_and (p : Fin 108 → Fin 108) (a b : W) :
    wordMap p (a &&& b) = wordMap p a &&& wordMap p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [wordMap_get]

theorem wordMap_or (p : Fin 108 → Fin 108) (a b : W) :
    wordMap p (a ||| b) = wordMap p a ||| wordMap p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [wordMap_get]

theorem wordMap_not (p : Fin 108 → Fin 108) (a : W) :
    wordMap p (~~~a) = ~~~(wordMap p a) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [wordMap_get]

theorem wordMap_injective (p : Fin 108 → Fin 108) (hp : Function.Surjective p) :
    Function.Injective (wordMap p) := by
  intro a b h
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨j, hj⟩ := hp ⟨i, hi⟩
  have eq := congrArg (fun w : W => w[j.val]) h
  simpa [wordMap_get, hj] using eq

theorem wordMap_basic (p : Fin 108 → Fin 108) {a b z : W} (h : z ∈ basicOps a b) :
    wordMap p z ∈ basicOps (wordMap p a) (wordMap p b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp [wordMap_and, wordMap_or, wordMap_not]

theorem live_wordMap (p : Fin 108 → Fin 108) (hp : Function.Surjective p) {g : W}
    {k : ℕ} {s : Finset W} (h : live basicOps g k s) :
    live basicOps (wordMap p g) k (s.image (wordMap p)) := by
  have hInj := wordMap_injective p hp
  induction k generalizing s with
  | zero =>
    change s = {g} at h
    simp [live, h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hnew, l, he, htail⟩
    · exact Or.inl (ih skip)
    · right
      refine ⟨wordMap p a, Finset.mem_image_of_mem _ ha,
        wordMap p b, Finset.mem_image_of_mem _ hb, fun e => hab (hInj e),
        wordMap p z, wordMap_basic p hz, ?_, l.image (wordMap p), ?_, ?_⟩
      · intro hz
        obtain ⟨u, hu, eq⟩ := Finset.mem_image.mp hz
        exact hnew (hInj eq ▸ hu)
      · simpa [Finset.image_insert] using congrArg (Finset.image (wordMap p)) he
      · simpa [Finset.image_insert] using ih htail

def orbitCovered (maps : List (Fin 108 → Fin 108)) (tr : BinaryTree (List W))
    (ws : List W) : Bool :=
  maps.any fun p => containsKey (ordered (ws.map (wordMap p))) tr

theorem closed_cover (k : ℕ) (original reps : BinaryTree (List W))
    (maps : List (Fin 108 → Fin 108))
    (valid : ∀ p ∈ maps, Function.Surjective p ∧ wordMap p goal = goal)
    (covered : everyKey (orbitCovered maps reps) original = true)
    (closed : Closed k reps) : Closed k original := by
  intro g hg ws hn hlen hm alive
  have hw := every_at original covered hm
  unfold orbitCovered at hw
  obtain ⟨p, hp, hmem⟩ := List.any_eq_true.mp hw
  obtain ⟨surj, fixGoal⟩ := valid p hp
  have transported := live_wordMap p surj alive
  have goalPolarity : wordMap p g = goal ∨ wordMap p g = ~~~goal := by
    rcases hg with rfl | rfl
    · exact Or.inl fixGoal
    · exact Or.inr (by rw [wordMap_not, fixGoal])
  have order := ordered_perm (ws.map (wordMap p))
  have noDup := order.nodup_iff.mpr (hn.map (wordMap_injective p surj))
  have size : (ordered (ws.map (wordMap p))).length ≤ 9 := by
    simpa only [order.length_eq, List.length_map] using hlen
  apply closed (wordMap p g) goalPolarity _ noDup size hmem
  have image_eq : (ws.map (wordMap p)).toFinset = ws.toFinset.image (wordMap p) := by
    ext w
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
  simpa only [perm_set order, image_eq] using transported


-- A balanced tree built from a short sorted block.
def blockTreeAux (rows : Array (List W)) : ℕ → ℕ → ℕ → BinaryTree (List W)
  | 0, _, _ => .nil
  | f+1, lo, hi =>
    if lo < hi then
      let m := (lo + hi) / 2
      .node rows[m]! (blockTreeAux rows f lo m) (blockTreeAux rows f (m+1) hi)
    else .nil

def blockTree (rows : Array (List W)) := blockTreeAux rows 8 0 rows.size

theorem every_node {f : List W → Bool} {v : List W} {l r : BinaryTree (List W)}
    (hv : f v = true) (hl : everyKey f l = true) (hr : everyKey f r = true) :
    everyKey f (.node v l r) = true := by simp [everyKey,hv,hl,hr]

def word (hi lo : W) : W := (hi <<< 64) + lo
def va : W := 0x0
def vb : W := 0x1c0000000000007000
def vc : W := 0x2c411000000000771dd
def vd : W := 0x6448100000000387e1e
def ve : W := 0x6e499000000003f8000
def vf : W := word 0x16008 0x22000000038071dd
def vg : W := word 0x2040d 0x8000000000007e00
def vh : W := word 0x23009 0x280000000007e1e
def vi : W := word 0xa1c01 0x8080000000380e02
def vj : W := word 0x1c0c20 0x8800000060388000
def vk : W := word 0x202008 0x200000000000000
def vl : W := word 0x202240 0x30000038387001d
def vm : W := word 0x20224c 0x30000000000701c
def vn : W := word 0x280a40 0x1000003e03f8000
def vo : W := word 0x280e44 0x8100000000380000
def vp : W := word 0x283800 0x2800003e3c00000
def vq : W := word 0x283a40 0x38000000038001e
def vr : W := word 0x2a3809 0x280000000000000
def vs : W := word 0x2a3e4d 0x8380000000387e1e
def vt : W := word 0x400084 0x1000000000000000
def vu : W := word 0x414080 0x30000003838701c1
def vv : W := word 0x41408c 0x30000000000071c0
def vw : W := word 0x5400a0 0x18000003e0078000
def vx : W := word 0x5404a4 0x9800000000000000
def vy : W := word 0x5744ad 0xb80000001c007fe0
def vz : W := word 0x6002c4 0x1100000380070000
def vA : W := word 0x616008 0x2200000383800000
def vB : W := word 0x6162cc 0x33000003838771dd
def vC : W := word 0x6b7ecd 0xb380000383bf7fdf
def vD : W := word 0x7766ed 0xbb0000039f877ffd
def vE : W := word 0x7c0800 0x3e0000000
def vF : W := word 0x7c0ee4 0x99000003e03f8000
def vG : W := word 0x7d6eec 0xbb000003e3bff1dd
def vH : W := word 0x7f4eed 0xb9000003fc3fffe0
def vI : W := word 0x7f6eed 0xbb000003ffbffffd
def vJ : W := word 0x7f7809 0x22800003ffc00000
def vK : W := word 0x7f7ecd 0xb3800003ffff7fdf
def vL : W := word 0x7f7eed 0xbb8000039fbf7fff
def vM : W := word 0x7f7eed 0xbb800003e3bfffdf
def vN : W := word 0x7f7eed 0xbb800003ffff8000
def vO : W := word 0x2002018 0x60000000000701c
def vP : W := word 0x13000010 0x44400000000071dd
def vQ : W := word 0x26000012 0x400003800007e1e
def vR : W := word 0x34000012 0x400001c000007fe0
def vS : W := word 0x37000012 0x444001fc00000000
def vT : W := word 0x200200244 0x100000000000000
def vU : W := word 0x202000010 0x400000000000000
def vV : W := word 0x202000254 0x50000000000701c
def vW : W := word 0x202202240 0x70000000000001c
def vX : W := word 0x20220225c 0x70000000000701c
def vY : W := word 0x280000340 0x1003e00003f8000
def vZ : W := word 0x2800003c4 0x1100000000070000
def v0 : W := word 0x283000340 0x54000000007001d
def v1 : W := word 0x293000110 0x4440000000000000
def v2 : W := word 0x2930003d4 0x55400000000771dd
def v3 : W := word 0x5740004b6 0xd80001c000007fe0
def v4 : W := word 0x626000656 0x8500383800387e1e
def v5 : W := word 0x6260006d6 0x95003838003f7fdf
def v6 : W := word 0x6b70007d6 0xd5403838003f7fdf
def v7 : W := word 0x7c00007e4 0x99003e00003f8000
def v8 : W := word 0x7d30007f4 0xdd403e00003ff1dd
def v9 : W := word 0x7f40007f6 0xd9003fc0003fffe0
def vaa : W := word 0x7f60007f6 0xdd003ff8003ffffe
def vab : W := word 0x7f7000112 0x44403ffc00000000
def vac : W := word 0x7f70007d6 0xd5403ffc003f7fdf
def vad : W := word 0x7f70007f6 0xdd4039f8003f7fff
def vae : W := word 0x7f70007f6 0xdd403e38003fffdf
def vaf : W := word 0x100300a000 0x64000000380001d
def vag : W := word 0x200a003000 0x68000380000001e
def vah : W := word 0x300800b000 0x280c00003c00000
def vai : W := word 0x300b008000 0x440c03c00000000
def vaj : W := word 0x4010000010 0x4000000000000000
def vak : W := word 0x401041409c 0x70000000000071c0
def val : W := word 0x42126162dc 0x77000000000071dc
def vam : W := word 0x42934143dc 0x75400000000771dd
def van : W := word 0x5013008010 0x4440000000000000
def vao : W := word 0x501301e018 0x66400000038071dd
def vap : W := word 0x501341e09c 0x76400000038071dd
def vaq : W := word 0x529301e3dc 0x77400000038771dd
def var : W := word 0x8024020003 0x701c01c000e20
def vas : W := word 0x842402041f 0x8000000000007e00
def vat : W := word 0x862602065f 0x8500383800387e1e
def vau : W := word 0x862622265f 0x8700000000007e1c
def vav : W := word 0xa008021001 0x87c0001c400000
def vaw : W := word 0xa02c000002 0x7c1fc00000000
def vax : W := word 0xa02c021003 0x80003800000e02
def vay : W := word 0xa02e02301b 0x680003800007e1e
def vaz : W := word 0xa42e02341f 0x8680003800007e1e
def vaA : W := word 0xa62e02365f 0x8780383800387e1e
def vaB : W := word 0xc03403401b 0x600701c01c007fe0
def vaC : W := word 0xc03403601b 0x620701c01f807ffd
def vaD : W := word 0xc03403701b 0x628701c01c007ffe
def vaE : W := word 0xc03603601b 0x660701c01c007ffc
def vaF : W := word 0xc43443449f 0xf000000000007fc0
def vaG : W := word 0xc5740344bf 0xf80701c01c007fe0
def vaH : W := word 0xd03703e01b 0x664701c01f807ffd
def vaI : W := word 0xe03e03701b 0x668701f81c007ffe
def vaJ : W := word 0xf00803f009 0x2287c0001fc00000
def vaK : W := word 0xf03f008012 0x4447c1fc00000000
def vaL : W := word 0xf03f03f01b 0x66c0003803807fdf
def vaM : W := word 0xf03f03f01b 0x66c701f81f807fff
def vaN : W := word 0xf03f7c8ef6 0xdd47c1ffe03f8000
def vaO : W := word 0xf7c803f7ed 0xbb87fe001fff8000
def vaP : W := word 0xf7ff008112 0x4447fffc00000000
def vaQ : W := word 0x20000e00000 0x380000000
def vaR : W := word 0x20080800100 0x380603e0078000
def vaS : W := word 0x20080c00180 0x1000000380070000
def vaT : W := word 0x20280800100 0x0
def vaU : W := word 0x20280a00340 0x100000380070000
def vaV : W := word 0x20280e003c4 0x1100000380070000
def vaW : W := word 0x21000808000 0x38c003e3c00000
def vaX : W := word 0x21000a0a000 0x200000383800000
def vaY : W := word 0x21081808100 0x40000383870001
def vaZ : W := word 0x21283808100 0x440000000000000
def va0 : W := word 0x21283a0a340 0x74000038387001d
def va1 : W := word 0x217f7808112 0x44403ffc00000000
def va2 : W := word 0x24290e143dc 0x71000003800771c0
def va3 : W := word 0x25000808000 0x0
def va4 : W := word 0x25000e1e008 0x2200000383800000
def va5 : W := word 0x25091808100 0x4040000000000000
def va6 : W := word 0x25091c1c180 0x70400003838701c1
def va7 : W := word 0x25280e1e3cc 0x3300000383870000
def va8 : W := word 0x25293808110 0x4440000000000000
def va9 : W := word 0x2529381e118 0x66400000038071dd
def vba : W := word 0x2529381e3dc 0x77400000038771dd
def vbb : W := word 0x25293a0a35c 0x474000000000701c
def vbc : W := word 0x25293a1e358 0x67400003838771dd
def vbd : W := word 0x25293a1e35c 0x67400000038071dd
def vbe : W := word 0x25293a1e3dc 0x77400003838771dd
def vbf : W := word 0x25293c1c190 0x74400003838701c1
def vbg : W := word 0x25293c1c3d4 0x75400003838771dd
def vbh : W := word 0x25293c1c3dc 0x75400000000771dd
def vbi : W := word 0x25293c1c3dc 0x75400003838771dd
def vbj : W := word 0x25293c1e3dc 0x77400003838771dd
def vbk : W := word 0x25293e083d4 0x5540000380070000
def vbl : W := word 0x25293e1c3d4 0x75400003838701c1
def vbm : W := word 0x25293e1c3dc 0x75400003800771c0
def vbn : W := word 0x25293e1e3c0 0x77400003838701dd
def vbo : W := word 0x25293e1e3d0 0x77400003838701dd
def vbp : W := word 0x25293e1e3dc 0x7740000383870000
def vbq : W := word 0x25293e1e3dc 0x77400003838771dd
def vbr : W := word 0x25293e3e7dd 0xf740000383877fdd
def vbs : W := word 0x25293e3f3dd 0x77c0000383877fdf
def vbt : W := word 0x25293e9fbdc 0x77c00003e3c771dd
def vbu : W := word 0x25293ebfbdd 0x77c00003838771dd
def vbv : W := word 0x25293ebffdd 0xf7c0000383bf7fdf
def vbw : W := word 0x25293f5e3fc 0x7f400003e387f1dd
def vbx : W := word 0x25293f5e7fc 0xff400003838771dd
def vby : W := word 0x25293f7e7fd 0xff4000039f877ffd
def vbz : W := word 0x25293fdebdc 0x77400003e38771dd
def vbA : W := word 0x25293fdeffc 0xff400003e3bff1dd
def vbB : W := word 0x252b7808112 0x444001fc00000000
def vbC : W := word 0x257f7808112 0x44403ffc00000000
def vbD : W := word 0x257f7e1e3de 0x77403fff838771dd
def vbE : W := word 0x2d6b7e3e7df 0xf740000383877fdd
def vbF : W := word 0x2f2bf808112 0x4447c1fc00000000
def vbG : W := word 0x2f2bfe1e3de 0x7747c1ff838771dd
def vbH : W := word 0x2f7c8e3f7ed 0xbb87fe039fff8000
def vbI : W := word 0x2f7ff808112 0x4447fffc00000000
def vbJ : W := word 0x40800080800 0x383e0060388000
def vbK : W := word 0x40800280800 0x0
def vbL : W := word 0x40a00280a40 0x100380000380000
def vbM : W := word 0x40e00280e44 0x8100380000380000
def vbN : W := word 0x40e02282e5c 0x870038000038701c
def vbO : W := word 0x42808081800 0xb8c00060400000
def vbP : W := word 0x42808283800 0x280000000000000
def vbQ : W := word 0x42a0a283a40 0x78038380038001e
def vbR : W := word 0x48e242a0e5f 0x8100380000387e00
def vbS : W := word 0x4a8082a3809 0x280000000000000
def vbT : W := word 0x4a8086b7809 0x2280000383800000
def vbU : W := word 0x4a8087f7809 0x22800003ffc00000
def vbV : W := word 0x4aa0a2a3a5d 0x78000000000701c
def vbW : W := word 0x4aa2e2a3a43 0x780383800380e1e
def vbX : W := word 0x4aa2e2a3a5b 0x780383800387e1e
def vbY : W := word 0x4ac2c0a1c03 0x8080383800380e02
def vbZ : W := word 0x4ac2c0a1c1f 0x8080383800387e02
def vb0 : W := word 0x4ac2c2a3e4f 0x8380383800387e1e
def vb1 : W := word 0x4ac2c2a3e5f 0x8380383800387e1e
def vb2 : W := word 0x4ac2e0a3c1b 0x8680383800387e1e
def vb3 : W := word 0x4ac2e2a3e5f 0x8780383800387e1e
def vb4 : W := word 0x4ae082a3e4d 0x8380380000380000
def vb5 : W := word 0x4ae2c2a3e4f 0x8380383800380e02
def vb6 : W := word 0x4ae2c2a3e4f 0x8380383800387e1e
def vb7 : W := word 0x4ae2c2a3e5f 0x8380380000387e00
def vb8 : W := word 0x4ae2e000012 0x400383800000000
def vb9 : W := word 0x4ae2e02301b 0x680383800007e1e
def vca : W := word 0x4ae2e0a1c13 0x8480383800380e02
def vcb : W := word 0x4ae2e2a3a5b 0x780383800387e1e
def vcc : W := word 0x4ae2e2a3e43 0x8780383800380e1e
def vcd : W := word 0x4ae2e2a3e4f 0x8780383800387e1e
def vce : W := word 0x4ae2e2a3e53 0x8780383800380e1e
def vcf : W := word 0x4ae2e2a3e5b 0x8780383800387e1e
def vcg : W := word 0x4ae2e2a3e5f 0x8780383800380000
def vch : W := word 0x4ae2e2a3e5f 0x8780383800387e1e
def vci : W := word 0x4ae2e6a3edf 0x9780383800387e1e
def vcj : W := word 0x4ae2e6b7edf 0xb780383800387fde
def vck : W := word 0x4ae2e6b7edf 0xb780383b83bf7fdf
def vcl : W := word 0x4ae2e7e3eff 0x9f80383800387e1e
def vcm : W := word 0x4ae2e7e3eff 0x9f80383be03ffe1e
def vcn : W := word 0x4ae3f2a3e5f 0xc7c0383800387fdf
def vco : W := word 0x4aebf2a3f5f 0xc7c0383800387e1e
def vcp : W := word 0x4ee3e2a3e5f 0xc780383800387e1e
def vcq : W := word 0x4ee3e6b7edf 0xf780383800387fde
def vcr : W := word 0x4f8082bf809 0x2287c0001fc00000
def vcs : W := word 0x4fe3f008012 0x4447f9fc00000000
def vct : W := word 0x4fe3f2abe5f 0xc7c0383800387e1e
def vcu : W := word 0x4fe3f7c8ef6 0xdd47f9ffe03f8000
def vcv : W := word 0x60800a80800 0x380003e0000000
def vcw : W := word 0x60a80800100 0x383e0000000000
def vcx : W := word 0x60a80a80b40 0x1383e03e03f8000
def vcy : W := word 0x60e80e80fc4 0x91003803803f0000
def vcz : W := word 0x61a83a8ab40 0x7783e03e3bf801d
def vcA : W := word 0x63808808000 0x38c00000000000
def vcB : W := word 0x63808a8b800 0x2b8c003e3c00000
def vcC : W := word 0x63808fff809 0x22b8c003ffc00000
def vcD : W := word 0x63a88a8bb40 0x3b8fe03e3ff8000
def vcE : W := word 0x63a8aa8bb40 0x7b8fe3be3ff801e
def vcF : W := word 0x63a8b808100 0x478fe3c00000000
def vcG : W := word 0x63a8ba8ab40 0x778fe3fe3bf801d
def vcH : W := word 0x63a8ba8bb40 0x7c0383b83bf001f
def vcI : W := word 0x63a8ba8bb40 0x7f83e3be3bf801f
def vcJ : W := word 0x63a8ba8bb40 0x7f8fe3fe3ff8000
def vcK : W := word 0x63abf808112 0x4478fffc00000000
def vcL : W := word 0x63d7ca8bcb6 0xdab8c1c3e3c07fe0
def vcM : W := word 0x63fff808112 0x4478fffc00000000
def vcN : W := word 0x65a93e9ebdc 0x77400003838771dd
def vcO : W := word 0x65a93e9ebdc 0x77783e03e3bff1dd
def vcP : W := word 0x67a9be9fbdc 0x77c00003838771dd
def vcQ : W := word 0x67a9be9fbdc 0x77f8c003e3c771dd
def vcR : W := word 0x6aeaeaa3f5f 0x8780383800387e1e
def vcS : W := word 0x6aeaeaa3f5f 0x87b83e3be03ffe1e
def vcT : W := word 0x6aeaeea3fdf 0x9780383b803f7e1e
def vcU : W := word 0x6be2eaabe5f 0x87b8f83be3f87e1e
def vcV : W := word 0x6beafaabf5f 0x87c0383800387e1e
def vcW : W := word 0x6beafaabf5f 0x87c0383b83bf7e1f
def vcX : W := word 0x6cab4ab4b5b 0x613f3fc3fc3fffe0
def vcY : W := word 0x6f808abf809 0x22bfc003ffc00000
def vcZ : W := word 0x6f808ebf809 0x2280000383800000
def vc0 : W := word 0x6f808ebf809 0x2287c0039fc00000
def vc1 : W := word 0x6f808ebf809 0x22b8c003e3c00000
def vc2 : W := word 0x6f808fff809 0x22800003ffc00000
def vc3 : W := word 0x6fa9bebfbdd 0x77c00003838771dd
def vc4 : W := word 0x6fabf808112 0x447ffffc00000000
def vc5 : W := word 0x6fcbdcbdd83 0xf0c0383b83bf0fc3
def vc6 : W := word 0x6fcbdcbdd9f 0xf0c0383b83bf7fc3
def vc7 : W := word 0x6fe2eaabe5f 0x8780383800387e1e
def vc8 : W := word 0x6febf808112 0x4440383800000000
def vc9 : W := word 0x6febf808112 0x4447f9fc00000000
def vda : W := word 0x6febf808112 0x4478fe3c00000000
def vdb : W := word 0x6febfaabf5f 0xc7c0383800387e1e
def vdc : W := word 0x6febfe1e3de 0x7740383b838771dd
def vdd : W := word 0x6febfebffdf 0xf7c0383b83bf7fdf
def vde : W := word 0x6ffff808112 0x44403ffc00000000
def vdf : W := word 0x6ffff808112 0x447ffffc00000000
def vdg : W := word 0x90000140000 0x3fc0007c400000
def vdh : W := word 0x90000540000 0x0
def vdi : W := word 0x90140000000 0x3fc7c400000000
def vdj : W := word 0x90140140020 0x80701c01c000020
def vdk : W := word 0x90140140020 0x838060060008000
def vdl : W := word 0x901407c0ee4 0x99380603e03f8000
def vdm : W := word 0x905405404a4 0x9800000000000000
def vdn : W := word 0x905407406e4 0x9900000380070000
def vdo : W := word 0x905407c0ee4 0x9900000000380000
def vdp : W := word 0x905407c0ee4 0x99000003e03f8000
def vdq : W := word 0x905745404b6 0xd80001c000007fe0
def vdr : W := word 0x907407406e4 0x9900000000000000
def vds : W := word 0x907c01407e4 0x99383e00603f8000
def vdt : W := word 0x907c05407e4 0x99003e00003f8000
def vdu : W := word 0x907c07c0fe4 0x99003e03e03f8000
def vdv : W := word 0x941505540a0 0x780701c01c0001e0
def vdw : W := word 0x945505544bc 0xf8000000000071c0
def vdx : W := word 0x945745544be 0xf80001c000007fe0
def vdy : W := word 0x98564160423 0x880701c01c000e20
def vdz : W := word 0x9856416043f 0x880701c01c007e20
def vdA : W := word 0x985645604a7 0x980701c01c000e20
def vdB : W := word 0x985645744af 0xb80701c01c007fe0
def vdC : W := word 0x985645744bf 0xb80701c01c007fe0
def vdD : W := word 0x985745744bf 0xf80701c01c007fe0
def vdE : W := word 0x9c000574009 0x200700001c000000
def vdF : W := word 0x9c5405744ad 0xb80700001c000000
def vdG : W := word 0x9c5645744af 0xb80701c01c000e20
def vdH : W := word 0x9c5645744af 0xb80701c01c007fe0
def vdI : W := word 0x9c5645744bf 0xb80700001c007e00
def vdJ : W := word 0x9c574000012 0x400701c000000000
def vdK : W := word 0x9c5740004b6 0xd80701c000007fe0
def vdL : W := word 0x9c57403401b 0x600701c01c007fe0
def vdM : W := word 0x9c574160433 0xc80701c01c000e20
def vdN : W := word 0x9c57417443b 0xe80701c01c007fe0
def vdO : W := word 0x9c5745540b2 0x780701c01c0001e0
def vdP : W := word 0x9c5745544b6 0xf80701c01c0001e0
def vdQ : W := word 0x9c5745544b6 0xf80701c01c007fe0
def vdR : W := word 0x9c5745544be 0xf80701c0000071c0
def vdS : W := word 0x9c5745744a3 0xf80701c01c000fe0
def vdT : W := word 0x9c5745744a7 0xf80701c01c000fe0
def vdU : W := word 0x9c5745744ab 0xf80701c01c000fe0
def vdV : W := word 0x9c5745744af 0xf80701c01c007fe0
def vdW : W := word 0x9c5745744b3 0xf80701c01c000fe0
def vdX : W := word 0x9c5745744b7 0xf80701c01c007fe0
def vdY : W := word 0x9c5745744bb 0xf80701c01c007fe0
def vdZ : W := word 0x9c5745744bf 0xf800000000007fc0
def vd0 : W := word 0x9c5745744bf 0xf80701c01c000000
def vd1 : W := word 0x9c5745744bf 0xf80701c01c007fe0
def vd2 : W := word 0x9c5745774bf 0xfa8701c01c007ffe
def vd3 : W := word 0x9c5747764bf 0xfa0701c01c007fe0
def vd4 : W := word 0x9c5747766ff 0xfb0701c01c007ffc
def vd5 : W := word 0x9c5747766ff 0xfb0701c39f877ffd
def vd6 : W := word 0x9c5747f4eff 0xf90701c3fc3fffe0
def vd7 : W := word 0x9c5747f7cbf 0xfa8701c01c007fe0
def vd8 : W := word 0x9c5747f7eff 0xfb8701c01c387ffe
def vd9 : W := word 0x9c5765764bf 0xfe0701c01c007ffc
def vea : W := word 0x9c5775744bf 0xfc4701c01c007ffd
def veb : W := word 0x9c7747746ff 0xf90701c01c007fe0
def vec : W := word 0x9c7765744bf 0xfc0701c01c007fe0
def ved : W := word 0x9c7765746ff 0xfd0701c01c007ffc
def vee : W := word 0x9c7767766ff 0xff0701c01c007ffc
def vef : W := word 0x9c7f7000112 0x44473ffc00000000
def veg : W := word 0x9c7f75745bf 0xfc4701c01c007fe0
def veh : W := word 0x9c7f77f791b 0x66c73fffffc00000
def vei : W := word 0x9d57757c4bf 0xfc4701c01c007fe0
def vej : W := word 0x9e57c5754bf 0xf887c1c01c407fe0
def vek : W := word 0x9f00857f009 0x2287c0001fc00000
def vel : W := word 0x9f57f008012 0x4447c1fc00000000
def vem : W := word 0xb0000d40000 0x380003e0000000
def ven : W := word 0xb01c0d401a0 0x18380603e0078000
def veo : W := word 0xb01c0fc0fe4 0x99380603e03f8000
def vep : W := word 0xb07c0d407e4 0x99383e03e03f8000
def veq : W := word 0xb07c0f407e4 0x9900000380070000
def ver : W := word 0xb07c0f407e4 0x99003e03803f8000
def ves : W := word 0xb41d0d541a0 0x783f07c3fc0781e0
def vet : W := word 0xb5000d5c000 0x203fc003ffc00000
def veu : W := word 0xb51c0d5c1a0 0x383fc603ffc78000
def vev : W := word 0xb51d0d5c1a0 0x783fc7c3ffc781e0
def vew : W := word 0xb51d1808100 0x407fc7c400000000
def vex : W := word 0xb51d1aabf4d 0xc3ffc7c400387e1e
def vey : W := word 0xb51d1d5c1a0 0x78780603e38781c1
def vez : W := word 0xb51d1d5c1a0 0x787fc7c7ffc78000
def veA : W := word 0xb51f7808112 0x447fc7fc00000000
def veB : W := word 0xb5293f5e3dc 0x77400003838771dd
def veC : W := word 0xb53d3808110 0x447fc7c400000000
def veD : W := word 0xb57d3f5e7fc 0xff400003838771dd
def veE : W := word 0xb97e7b6a763 0x8f4701c39f870e3d
def veF : W := word 0xb97e7b6a77f 0x8f4701c39f877e3d
def veG : W := word 0xbc7f4d745bf 0xf80701c01c007fe0
def veH : W := word 0xbc7f4f747ff 0xf90701c39c077fe0
def veI : W := word 0xbd574d7c4bf 0xf80701c01c007fe0
def veJ : W := word 0xbd5f5d7c5bf 0xf84701c01c007fe0
def veK : W := word 0xbd7f7808112 0x444701c000000000
def veL : W := word 0xbd7f7808112 0x44473ffc00000000
def veM : W := word 0xbd7f7808112 0x447ffffc00000000
def veN : W := word 0xbd7f7d7c5bf 0xfc4701c01c007fe0
def veO : W := word 0xbd7f7e1e3de 0x774701c3838771dd
def veP : W := word 0xbd7f7f7e7ff 0xff4701c01c007ffc
def veQ : W := word 0xbd7f7f7e7ff 0xff4701c39f877ffd
def veR : W := word 0xbf5ff808112 0x447fc7fc00000000
def veS : W := word 0xbf7ff808112 0x4447c1fc00000000
def veT : W := word 0xbf7ff808112 0x447ffffc00000000
def veU : W := word 0xd08001c0800 0x38000060000000
def veV : W := word 0xd0d401c0c20 0x88383e0060388000
def veW : W := word 0xd0d405c0ca4 0x98383e0060388000
def veX : W := word 0xd0d407c0ee4 0x99383e03e03f8000
def veY : W := word 0xd0f407c0ee4 0x9900380000380000
def veZ : W := word 0xd0f407c0ee4 0x99383e0060388000
def ve0 : W := word 0xd0f407c0ee4 0x99383e03e03f8000
def ve1 : W := word 0xd0fc01c0fe4 0x99383e00603f8000
def ve2 : W := word 0xd0fc05c0fe4 0x99383e00603f8000
def ve3 : W := word 0xd0fc07c0fe4 0x99003e00003f8000
def ve4 : W := word 0xd0fc07c0fe4 0x99383e03e03f8000
def ve5 : W := word 0xd5d531dec38 0xee783e0063b8f1dd
def ve6 : W := word 0xd8d641e0c23 0x883f3fc07c388e20
def ve7 : W := word 0xda8081e1801 0xbfc0007c400000
def ve8 : W := word 0xda8087f7809 0x22bfc003ffc00000
def ve9 : W := word 0xdad481e1c21 0x88bffe007c788000
def vfa : W := word 0xdad6c000002 0x3ffffc00000000
def vfb : W := word 0xdad6c1c0c22 0x883ffffc60388000
def vfc : W := word 0xdad6c1e0c23 0x883ffffc7c388e20
def vfd : W := word 0xdad6c1e1803 0xbffffc7c400000
def vfe : W := word 0xdad6c1e1c23 0x88bffffc7c788000
def vff : W := word 0xdad6c6162ce 0x333fffff838771dd
def vfg : W := word 0xdae2e7e3e5f 0x8780383800387e1e
def vfh : W := word 0xdaf6e7e3eff 0x9f80383800387e1e
def vfi : W := word 0xdcd747f4cbf 0xf80701c01c007fe0
def vfj : W := word 0xde8085f5809 0x20bfc0007c400000
def vfk : W := word 0xde8087f7809 0x228700001c000000
def vfl : W := word 0xde8087f7809 0x22bfc0007c400000
def vfm : W := word 0xde8087f7809 0x22bfc003ffc00000
def vfn : W := word 0xded7c000012 0x403ffffc00000000
def vfo : W := word 0xded7c7f7cbf 0xfa8701c01c007fe0
def vfp : W := word 0xdef7e7f7eff 0xff80383800387fde
def vfq : W := word 0xdef7e7f7eff 0xff8701c01c007ffc
def vfr : W := word 0xdef7e7f7eff 0xff8739f81c387ffe
def vfs : W := word 0xdf8081ff809 0x22bfc0007fc00000
def vft : W := word 0xdf8083ff809 0x22bfc0007fc00000
def vfu : W := word 0xdf8085ff809 0x22bfc0007fc00000
def vfv : W := word 0xdf8087ff809 0x2287c0001fc00000
def vfw : W := word 0xdf8087ff809 0x22bfc003ffc00000
def vfx : W := word 0xdfd7f008012 0x447ffffc00000000
def vfy : W := word 0xf0800800000 0x38000000000000
def vfz : W := word 0xf0800fc0800 0x380003e0000000
def vfA : W := word 0xf09c0fc09a0 0x18380603e0078000
def vfB : W := word 0xf0a80fc0bc4 0x11380003e0070000
def vfC : W := word 0xf0d40fc0ca4 0x98380003e0000000
def vfD : W := word 0xf0d40fc0ee4 0x99383e03e03f8000
def vfE : W := word 0xf0dc0dc0da0 0x98383e03e03f8000
def vfF : W := word 0xf0dc0fc0fe4 0x99383e03e03f8000
def vfG : W := word 0xf0fc0800100 0x383e0000000000
def vfH : W := word 0xf0fc09c0d20 0x88383e0060388000
def vfI : W := word 0xf0fc09c0fe4 0x99383e00603f8000
def vfJ : W := word 0xf0fc0d401a0 0x18383e03e0078000
def vfK : W := word 0xf0fc0d407e4 0x99383e00003f8000
def vfL : W := word 0xf0fc0d407e4 0x99383e03e03f8000
def vfM : W := word 0xf0fc0dc0fe4 0x99383e03e03f8000
def vfN : W := word 0xf0fc0fc0fe4 0x99003803803f0000
def vfO : W := word 0xf0fc0fc0fe4 0x99383e03e03f8000
def vfP : W := word 0xf0fc0fc2fec 0x9b383e03e03f8000
def vfQ : W := word 0xf0fc0fc3fe4 0x9bb83e03e3ff8000
def vfR : W := word 0xf0fc0fd6fec 0xbb383e03e3bf8000
def vfS : W := word 0xf0fc0fd6fec 0xbb383e03e3bff1dd
def vfT : W := word 0xf0fc0fe3fed 0x9bb83e03e03f8000
def vfU : W := word 0xf0fc0fe3fed 0x9bb83e03e03ffe1e
def vfV : W := word 0xf0fc2fc0ff4 0x9d383e03e03f8000
def vfW : W := word 0xf0fc2fc2ffc 0x9f383e03e03ff01c
def vfX : W := word 0xf0fd3fc0ff4 0xdd783e03e03f8000
def vfY : W := word 0xf1fc0fc8fe4 0x9938fe03e3ff8000
def vfZ : W := word 0xf1fc0fcafe4 0x9b383e03e3bf8000
def vf0 : W := word 0xf1fc1fc8fe4 0x99783e03e3bf8001
def vf1 : W := word 0xf1fc3fc8fe4 0x9d783e03e03f8000
def vf2 : W := word 0xf1fc3fcafe4 0x9f783e03e3bf801d
def vf3 : W := word 0xf2fc8fc1fe4 0x99b8fe03e07f8000
def vf4 : W := word 0xf2fc8fc3fe4 0x9bb83e03e03f8000
def vf5 : W := word 0xf3808fcb800 0x2b8c003e3c00000
def vf6 : W := word 0xf3fc8fc8fe4 0x9938fe03e03f8000
def vf7 : W := word 0xf3fc8fcbfe4 0x9bb8fe03e3ff8000
def vf8 : W := word 0xf3fcbfc8fe4 0x9d78fe3fe03f8000
def vf9 : W := word 0xf4fd0fc0ff4 0xd9383e03e03f8000
def vga : W := word 0xf5800fde808 0x22380003e3800000
def vgb : W := word 0xf5a93fdebdc 0x77780003e38771dd
def vgc : W := word 0xf5fc0fc8fe4 0x99383e03e03f8000
def vgd : W := word 0xf5fc0fdefec 0xbb383e03e3bf8000
def vge : W := word 0xf5fd1fc8fe4 0xd9783e03e03f8000
def vgf : W := word 0xf5fd3808110 0x44783e0000000000
def vgg : W := word 0xf5fd3fc8ff4 0xdd783e03e03f8000
def vgh : W := word 0xf5fd3fdeffc 0xff783e03e3bff1dd
def vgi : W := word 0xf5ff7808112 0x44783ffc00000000
def vgj : W := word 0xfa808fe3809 0x2b80003e0000000
def vgk : W := word 0xfa808ff7809 0x22bfc003ffc00000
def vgl : W := word 0xfae2efe3e5f 0x87b8383be0387e1e
def vgm : W := word 0xfafc8fe3fed 0x9bb83e03e03f8000
def vgn : W := word 0xfafeefc0ff6 0x9d383e3be03f8000
def vgo : W := word 0xfafeefe3fff 0x9fb83e3be03ffe1e
def vgp : W := word 0xfb808fff809 0x22bfc003ffc00000
def vgq : W := word 0xfc800ff4809 0x203f0003fc000000
def vgr : W := word 0xfcd74ff4cbf 0xf83f01c3fc007fe0
def vgs : W := word 0xfcff4800112 0x403f3fc000000000
def vgt : W := word 0xfcff4ff4fff 0xf93f3fc3fc3fffe0
def vgu : W := word 0xfdff7808112 0x447f3fc000000000
def vgv : W := word 0xfdff7ffefff 0xff7f3fc3ffbffffd
def vgw : W := word 0xfe808ff7809 0x22bf0003fc000000
def vgx : W := word 0xfeffeff7fff 0xffbf3ffbfc3ffffe
def vgy : W := word 0xff808808000 0x3fc00000000000
def vgz : W := word 0xff80883f009 0x22bfc0001fc00000
def vgA : W := word 0xff8089e9801 0xbfc0007c400000
def vgB : W := word 0xff8089ff809 0x22bfc0007fc00000
def vgC : W := word 0xff808abf809 0x22bfc0001fc00000
def vgD : W := word 0xff808abf809 0x22bfc003ffc00000
def vgE : W := word 0xff808bff809 0x22bfc003ffc00000
def vgF : W := word 0xff808d5c000 0x203fc003ffc00000
def vgG : W := word 0xff808dfd801 0x20bfc003ffc00000
def vgH : W := word 0xff808dff809 0x22bfc003ffc00000
def vgI : W := word 0xff808ebf809 0x22bfc00383800000
def vgJ : W := word 0xff808fff809 0x228700039f800000
def vgK : W := word 0xff808fff809 0x22b80003e3800000
def vgL : W := word 0xff808fff809 0x22bfc003ffc00000
def vgM : W := word 0xff808fff88d 0x32bfc003ffc00000
def vgN : W := word 0xff808fff8a9 0x3abfc003ffc78000
def vgO : W := word 0xff808fffacd 0x33bfc003ffc70000
def vgP : W := word 0xff808fffacd 0x33bfc003ffc771dd
def vgQ : W := word 0xff808fffcad 0xbabfc003ffc00000
def vgR : W := word 0xff808fffe4d 0xa3bfc003fff87e1e
def vgS : W := word 0xff808fffeed 0xbbbfc003ffff8000
def vgT : W := word 0xff818fff819 0x62bfc003ffc00000
def vgU : W := word 0xff81bfff819 0x66ffc003ffc00000
def vgV : W := word 0xff888fff909 0x22bfc603ffc78000
def vgW : W := word 0xff888fff989 0x32bfc003ffc70000
def vgX : W := word 0xff889fff909 0x22ffc003ffc70001
def vgY : W := word 0xff899fff909 0x62ffc003ffc00000
def vgZ : W := word 0xff948fff809 0x22bfc7c7ffc00000
def vg0 : W := word 0xff948fff829 0x2abfc1c3ffc00020
def vg1 : W := word 0xff948fff829 0x2abfc603ffc08000
def vg2 : W := word 0xff9c8fff9a9 0x3abfc603ffc78000
def vg3 : W := word 0xff9d9fff909 0x62ffc7c7ffc00000
def vg4 : W := word 0xffa08fffa4d 0x23bfc003ffc00000
def vg5 : W := word 0xffa0afff819 0x26bfc003ffc00000
def vg6 : W := word 0xffa0afffa5d 0x27bfc003ffc0701c
def vg7 : W := word 0xffa88fff909 0x22bfc003ffc00000
def vg8 : W := word 0xffa88fffb49 0x23bfc003ffc70000
def vg9 : W := word 0xffa88fffb49 0x23bffe03ffff8000
def vha : W := word 0xffa88fffbcd 0x33bfc003ffc70000
def vhb : W := word 0xffa8bfff909 0x26ffc003ffc00000
def vhc : W := word 0xffa8bfffb49 0x27ffc003ffc7001d
def vhd : W := word 0xffa9bfff919 0x66ffc003ffc00000
def vhe : W := word 0xffa9bfffbdd 0x77ffc003ffc771dd
def vhf : W := word 0xffd48fffcad 0xbabfc003ffc00000
def vhg : W := word 0xffd7cfff81b 0x62bfc1c3ffc00000
def vhh : W := word 0xffd7cfffcbf 0xfabfc1c3ffc07fe0
def vhi : W := word 0xffdfd808102 0x407ffffc00000000
def vhj : W := word 0xffdff808112 0x447ffffc00000000
def vhk : W := word 0xffe2efffe5f 0xa7bff83bfff87e1e
def vhl : W := word 0xffebf808112 0x447ff83800000000
def vhm : W := word 0xffebfffffdf 0xf7fff83bffff7fdf
def vhn : W := word 0xfffc8808100 0x3ffe0000000000
def vho : W := word 0xfffc8ffffed 0xbbb83e03e3bf8000
def vhp : W := word 0xfffc8ffffed 0xbbbffe03ffff8000
def vhq : W := word 0xfffdbfffffd 0xfffffe03fffff1dd
def vhr : W := word 0xfffeeffffff 0xbfbffe3bfffffe1e
def vhs : W := word 0xffffcffffff 0xfbbfffc3ffffffe0
def vht : W := word 0xfffff808112 0x444739f800000000
def vhu : W := word 0xfffff808112 0x44783e3800000000
def vhv : W := word 0xfffff808112 0x447ffffc00000000
def vhw : W := word 0xfffff829113 0x44fffffc1c400000
def vhx : W := word 0xfffff888912 0x447ffffc60388000
def vhy : W := word 0xfffff889912 0x44fffffc60400000
def vhz : W := word 0xfffff948112 0x447ffffc7c400000
def vhA : W := word 0xfffff948132 0x4c7ffffc1c000020
def vhB : W := word 0xfffff948132 0x4c7ffffc60008000
def vhC : W := word 0xfffff9c8912 0x447ffffc60000000
def vhD : W := word 0xfffff9c8d32 0xcc7ffffc60388000
def vhE : W := word 0xfffff9e9913 0x44fffffc7c400000
def vhF : W := word 0xfffff9e9d33 0xccfffffc7c788000
def vhG : W := word 0xfffffa08356 0x457ffffc00000000
def vhH : W := word 0xfffffa0a11a 0x467ffffc00000000
def vhI : W := word 0xfffffa0a352 0x477fffff8387001d
def vhJ : W := word 0xfffffa0a35e 0x477ffffc0000701c
def vhK : W := word 0xfffffa88912 0x447ffffc00000000
def vhL : W := word 0xfffffa88b52 0x457ffffc00380000
def vhM : W := word 0xfffffa88b52 0x457fffffe03f8000
def vhN : W := word 0xfffffa88f56 0xc57ffffc00380000
def vhO : W := word 0xfffffa8b912 0x46fffffc00000000
def vhP : W := word 0xfffffa8b912 0x46ffffffe3c00000
def vhQ : W := word 0xfffffaab91b 0x46fffffc00000000
def vhR : W := word 0xfffffaabf5f 0xc7fffffc00380000
def vhS : W := word 0xfffffaabf5f 0xc7fffffc00387e1e
def vhT : W := word 0xfffffc08196 0x547ffffc00000000
def vhU : W := word 0xfffffd48112 0x447ffffc00000000
def vhV : W := word 0xfffffd485b6 0xdc7ffffc00000000
def vhW : W := word 0xfffffd7c11b 0x647ffffc1c000000
def vhX : W := word 0xfffffd7c5bf 0xfc7ffffc1c000000
def vhY : W := word 0xfffffd7c5bf 0xfc7ffffc1c007fe0
def vhZ : W := word 0xfffffdc8db6 0xdc7ffffc60388000
def vh0 : W := word 0xfffffdfd91b 0x64fffffc7c400000
def vh1 : W := word 0xfffffe083d6 0x557fffff80070000
def vh2 : W := word 0xfffffe1e3de 0x777fffff838771dd
def vh3 : W := word 0xfffffebffdf 0xf7ffffff83bf7fdf
def vh4 : W := word 0xffffffc8912 0x447fffffe0000000
def vh5 : W := word 0xffffffc8ff6 0xdd783e3be03f8000
def vh6 : W := word 0xffffffc8ff6 0xdd7fffffe03f8000
def vh7 : W := word 0xffffffdeffe 0xff7fffffe3bff1dd
def vh8 : W := word 0xfffffffcfff 0xfd7ffffffc3fffe0
def vh9 : W := word 0xffffffff91b 0x66ffc1c3ffc00000
def via : W := word 0xffffffff91b 0x66ffffffffc00000
def vib : W := word 0xfffffffffff 0xffc739fb9fbf7fff
def vic : W := word 0xfffffffffff 0xfff83e3be3bfffdf
def vid : W := word 0xfffffffffff 0xffffffffffff8000

def ins : List W := [vbq,vch,vd1,vfO,vgL,vhv]

theorem sampled : ∀ j : Fin 108,
    Nat.testBit 0xfeeefaeafcecf800 (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) =
      goal[j.val] := by decide +kernel
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level0 : BinaryTree (List W) := .nil
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level0_ok : everyKey (fun q => !doneTest q) level0 = true := by
  decide +kernel
theorem closed0 : Closed 0 level0 := closed_nil level0 level0_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level1 : BinaryTree (List W) := .nil
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level1_ok : everyKey (rowOK 0 level0) level1 = true := by
  decide +kernel
theorem closed1 : Closed 1 level1 := closed_next 0 (by decide) level1 level0 closed0 level1_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level2 : BinaryTree (List W) := .nil
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level2_ok : everyKey (rowOK 1 level1) level2 = true := by
  decide +kernel
theorem closed2 : Closed 2 level2 := closed_next 1 (by decide) level2 level1 closed1 level2_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level3 : BinaryTree (List W) := (blockTree #[[vcZ,vc8,vee,vfO]])
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level3_ok : everyKey (rowOK 2 level2) level3 = true := by
  decide +kernel
theorem closed3 : Closed 3 level3 := closed_next 2 (by decide) level3 level2 closed2 level3_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level4 : BinaryTree (List W) := (.node [vch,vcX,veD,vgL,vhv]
    (.node [vbq,vch,vcX,vcY,vhv]
    (.node [vbc,vch,vcX,vgL,vhv]
    (blockTree #[[vC,vc5,vd1,vfO,vgL],[vC,vdd,vee,vfO,vgL],[vX,vcZ,vc8,vd1,vfO],[v6,vc5,vd1,vfO,vhv],[v6,vdd,vee,vfO,vhv],[vaE,vdd,vee,vgL,vhv],
      [vaN,vbq,vch,vd1,vgL],[vaO,vbq,vch,vd1,vhv]])
    (blockTree #[[vbq,vbH,vch,vd1,vhv],[vbq,vbU,vd1,vex,vfO],[vbq,vbX,vcX,vgL,vhv],[vbq,vch,vcu,vd1,vgL],[vbq,vch,vcL,vdt,vhv],[vbq,vch,vcL,vfO,vhv],
      [vbq,vch,vcL,vf7,vhv]]))
    (.node [vbq,vcX,vfh,vgL,vhv]
    (blockTree #[[vbq,vch,vcX,vc4,vgL],[vbq,vch,vcX,vgL,vhv],[vbq,vch,vcX,vgL,vhV],[vbq,vch,vcX,vhf,vhv],[vbq,vch,vd1,veh,vfO],[vbq,vch,veN,vfO,vhg],
      [vbq,vch,veN,vfO,vh9]])
    (blockTree #[[vbq,vdb,vd1,vgn,vgL],[vbq,vdb,vd1,vgL,vh5],[vbq,vd1,vex,vfO,vgL],[vbq,vd1,vex,vfO,vg3],[vbq,vfh,vgt,vhf,vhv],[vbE,vfr,vfO,vgL,vhv],
      [vb0,vd1,vff,vfO,vgL]])))
    (.node [vcq,veQ,vfO,vgL,vhv]
    (.node [vch,vd1,vff,vfO,vgL]
    (blockTree #[[vch,vc3,vd1,vho,vhv],[vch,vdB,vff,vfO,vgL],[vch,vd1,veD,vha,vhv],[vch,vd1,veX,vff,vgL],[vch,vd1,ve5,vfs,vhv],[vch,vd1,ve5,vgL,vhv],
      [vch,vd1,ve5,vha,vhv],[vch,vd1,ve8,vff,vfO]])
    (blockTree #[[vch,vd1,vff,vfO,vhd],[vch,vd1,vff,vgg,vgL],[vch,veD,vgt,vgL,vhV],[vch,veE,vfO,vgL,vhv],[vch,veF,vfO,vgL,vhv],[vch,veN,vff,vfO,vgL],
      [vch,veN,vgg,vgL,vh2]]))
    (.node [vc8,vdd,vee,vfO,vgL]
    (blockTree #[[vcZ,vc5,vd1,vfO,vhv],[vcZ,vdd,vee,vfO,vhv],[vc5,vc8,vd1,vfO,vgL],[vc5,vdS,vfO,vgL,vhv],[vc5,vd1,vfO,vgL,vhv],[vc5,vee,vfO,vgL,vhv],
      [vc6,vd1,vfO,vgL,vhv]])
    (blockTree #[[vdb,vd1,vff,vfO,vgL],[vdb,vd1,vfO,vhd,vh2],[vdd,vdr,vee,vgL,vhv],[vdd,vee,vfO,vgL,vhv],[vdd,veP,vfO,vgL,vhv],[vdd,vfq,vfO,vgL,vhv],
      [veQ,vfp,vfO,vgL,vhv]]))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level4_ok : everyKey (rowOK 3 level3) level4 = true := by
  refine every_node ?_ ?_ ?_
  · decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        decide +kernel
      ·
        decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        decide +kernel
      ·
        decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        decide +kernel
      ·
        decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        decide +kernel
      ·
        decide +kernel
theorem closed4 : Closed 4 level4 := closed_next 3 (by decide) level4 level3 closed3 level4_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level5 : BinaryTree (List W) := (.node [vbq,vch,vdX,vfO,vgL,vhv]
    (.node [vbc,vch,vd1,vfO,vgL,vhv]
    (.node [vao,vch,vd1,veW,vgL,vhv]
    (.node [vJ,vbq,vch,vd1,vef,vfO]
    (.node [vB,vch,vd1,vfb,vfO,vgL]
    (.node [vs,vbq,vd1,veC,vfO,vgL]
    (blockTree #[[vs,vbq,vbU,vd1,vew,vfO],[vs,vbq,vck,vd1,vfO,vgL],[vs,vbq,vc8,vd1,vfO,vgL],[vs,vbq,vdb,vd1,vfO,vgL],[vs,vbq,vd1,vew,vfO,vgL],[vs,vbq,vd1,vew,vfO,vg3],
      [vs,vbq,vd1,vex,vfO,vgL]])
    (blockTree #[[vy,vbq,vch,vd5,vfO,vgL],[vy,vbq,vch,veN,vfO,vgL],[vB,vbq,vch,vd1,vfO,vhg],[vB,vbq,vch,vd1,vgn,vgL],[vB,vbv,vch,vd1,vfO,vgL],[vB,vby,vch,vd1,vfO,vgL],
      [vB,vch,vd1,vfa,vfO,vgL]]))
    (.node [vF,vaK,vbq,vch,vd1,vgL]
    (blockTree #[[vB,vch,vd1,vfd,vfO,vgL],[vB,vch,vd1,vff,vfO,vgL],[vC,vX,vdd,vd1,vfO,vgL],[vC,v6,vbq,vch,vd1,vfO],[vC,vbq,vch,vcZ,vd1,vfO],[vC,vbq,vch,vd1,vfO,vgL],
      [vD,vbq,vch,vd1,vfO,vgL]])
    (blockTree #[[vF,vaN,vbq,vch,vd1,vgL],[vF,vbq,vbF,vch,vd1,vgL],[vF,vbq,vch,vcs,vd1,vgL],[vF,vbq,vch,vc4,vd1,vgL],[vF,vbq,vd1,vfh,vgL,vhv],[vF,vch,vd1,veD,vgL,vhv],
      [vI,vbq,vch,vd1,vfO,vgL]])))
    (.node [v3,vbq,vch,vcL,vfO,vhv]
    (.node [vX,vc8,vdd,vd1,vfO,vgL]
    (blockTree #[[vK,vbq,vch,vd1,vfO,vgL],[vL,vbq,vch,vd1,vfO,vgL],[vM,vbq,vch,vd1,vfO,vgL],[vW,vdd,vd1,vfO,vgL,vhv],[vX,v6,vdd,vd1,vfO,vhv],[vX,vcZ,vdd,vd1,vfO,vhv],
      [vX,vc5,vd1,vfO,vgL,vhv]])
    (blockTree #[[vX,vdd,vdS,vfO,vgL,vhv],[vX,vdd,vd1,vfO,vgL,vhv],[vX,vdd,vee,vfO,vgL,vhv],[v2,vch,vcZ,vd1,vfO,vhv],[v3,vbq,vch,vcB,vdt,vhv],[v3,vbq,vch,vcB,vfO,vhv],
      [v3,vbq,vch,vcB,vf7,vhv]]))
    (.node [vab,vbq,vch,veN,vfO,vgL]
    (blockTree #[[v4,vbq,vd1,veu,vfO,vhv],[v5,vbq,vch,vd1,vfO,vhv],[v6,vbq,vch,vc8,vd1,vfO],[v6,vbq,vch,vd1,vfO,vhv],[v7,vaJ,vbq,vch,vd1,vhv],[vaa,vbq,vch,vd1,vfO,vhv],
      [vab,vbq,vch,vd1,ve8,vfO]])
    (blockTree #[[vab,vbq,vdb,vd1,vfO,vgL],[vac,vbq,vch,vd1,vfO,vhv],[vad,vbq,vch,vd1,vfO,vhv],[vae,vbq,vch,vd1,vfO,vhv],[vak,vch,veQ,vfO,vgL,vhv],[val,vdd,vd1,vfO,vgL,vhv],
      [vao,vch,vd1,veV,vgL,vhv]]))))
    (.node [vaV,vch,vd1,vgh,vha,vhv]
    (.node [vaK,vbq,vch,vd1,veX,vgL]
    (.node [vaE,vbq,vch,vd1,vgL,vhv]
    (blockTree #[[vau,vdd,vd1,vfO,vgL,vhv],[vaB,vbq,vch,vcx,vgL,vhv],[vaB,vbq,vch,vcD,vgL,vhv],[vaB,vbq,vch,vcX,vgL,vhv],[vaB,vbq,vch,vd1,vha,vhv],[vaC,vbq,vch,vd1,vgL,vhv],
      [vaD,vbq,vch,vd1,vgL,vhv]])
    (blockTree #[[vaE,vbq,vch,vee,vgL,vhv],[vaF,vbq,vfr,vfO,vgL,vhv],[vaF,vch,veQ,vfO,vgL,vhv],[vaH,vbq,vch,vd1,vgL,vhv],[vaI,vbq,vch,vd1,vgL,vhv],[vaJ,vbq,vch,vdt,vd1,vhv],
      [vaK,vaN,vbq,vch,vd1,vgL]]))
    (.node [vaO,vbq,vch,vd1,vfO,vhv]
    (blockTree #[[vaK,vbq,vch,veN,vfO,vgL],[vaK,vbq,vdb,vd1,vfO,vgL],[vaM,vbq,vch,vd1,vgL,vhv],[vaN,vbq,vch,vd1,vfO,vgL],[vaN,vbq,vch,vd1,vgL],[vaN,vbq,vch,vd1,vgL,vhv],
      [vaO,vbq,vch,vd1,vfz,vhv]])
    (blockTree #[[vaO,vbq,vch,vd1,vgL,vhv],[vaO,vbq,vch,vd1,vhp,vhv],[vaO,vbq,vch,vd1,vhv],[vaV,vch,vd1,veD,vgL,vhv],[vaV,vch,vd1,ve5,vgL,vhv],[vaV,vch,vd1,vfs,vgh,vhv],
      [vaV,vch,vd1,vgh,vgL,vhv]])))
    (.node [va8,vb0,vd1,vfO,vgL,vh2]
    (.node [va6,vbZ,vd1,vfO,vgL,vhv]
    (blockTree #[[va0,vch,vdy,vfO,vgL,vhv],[va0,vch,vdz,vfO,vgL,vhv],[va0,vch,vdA,vfO,vgL,vhv],[va0,vch,veE,vfO,vgL,vhv],[va0,vcq,vd1,vfO,vgL,vhv],[va1,vbq,vch,vd1,vfO,vgL],
      [va6,vbY,vd1,vfO,vgL,vhv]])
    (blockTree #[[va6,vch,vee,vfO,vgL,vhv],[va7,vch,vd1,vfO,vhe,vhv],[va7,vch,vd1,vgh,vgL,vhv],[va8,vbq,vch,vd1,vfO,vhg],[va8,vbq,vch,vd1,vgn,vgL],[va8,vbD,vch,vd1,vfO,vgL],
      [va8,vbG,vch,vd1,vfO,vgL]]))
    (.node [va8,vch,vd1,vfO,vhd,vh2]
    (blockTree #[[va8,vch,vdc,vd1,vfO,vgL],[va8,vch,vdB,vfO,vgL,vh2],[va8,vch,vd1,veO,vfO,vgL],[va8,vch,vd1,veX,vgL,vh2],[va8,vch,vd1,ve8,vfO,vh2],[va8,vch,vd1,vff,vfO,vgL],
      [va8,vch,vd1,vfO,vgL,vh2]])
    (blockTree #[[va8,vch,vd1,vgg,vgL,vh2],[va8,vch,veN,vfO,vgL,vh2],[va8,vdb,vd1,vfO,vgL,vh2],[va9,vch,vd1,veV,vgL,vhv],[vba,vch,vd1,vfO,vgL,vhv],[vbb,vdd,vd1,vfO,vgL,vhv],
      [vbc,vch,vdm,vgt,vgL,vhv]])))))
    (.node [vbq,vch,vcM,vd1,vfO,vgL]
    (.node [vbq,vb1,vd1,vfO,vgL,vhv]
    (.node [vbq,vbC,vch,vd1,vfO,vgL]
    (.node [vbk,vch,vd1,vgh,vgL,vhv]
    (blockTree #[[vbd,vch,vd1,vfO,vgL,vhv],[vbe,vch,vd1,vfO,vgL,vhv],[vbf,vbY,vd1,vfO,vgL,vhv],[vbg,vch,vd1,vfO,vgL,vhv],[vbh,vch,vd1,vfO,vgL,vhv],[vbi,vch,vd1,vfO,vgL,vhv],
      [vbj,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbl,vch,vd1,vfO,vgL,vhv],[vbm,vch,vd1,vfO,vgL,vhv],[vbn,vch,vd1,vfO,vgL,vhv],[vbo,vch,vd1,vfO,vgL,vhv],[vbp,vch,vd1,vfO,vgL,vhv],[vbq,vbB,vch,vd1,vfO,vgL],
      [vbq,vbC,vch,vd1,ve8,vfO]]))
    (.node [vbq,vbY,vee,vfO,vgL,vhv]
    (blockTree #[[vbq,vbF,vch,vd1,veX,vgL],[vbq,vbF,vch,vd1,vfO,vgL],[vbq,vbI,vch,vd1,vfO,vgL],[vbq,vbT,vch,vd1,vfO,vhv],[vbq,vbW,vd1,vfO,vgL,vhv],[vbq,vbX,vdm,vgt,vgL,vhv],
      [vbq,vbX,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbq,vb0,vdB,vfO,vgL,vhv],[vbq,vb0,vd1,veX,vgL,vhv],[vbq,vb0,vd1,ve8,vfO,vhv],[vbq,vb0,vd1,vfO,vgL,vhv],[vbq,vb0,vd1,vfO,vhd,vhv],[vbq,vb0,vd1,vgg,vgL,vhv],
      [vbq,vb0,veN,vfO,vgL,vhv]])))
    (.node [vbq,vch,vcr,vd1,vhp,vhv]
    (.node [vbq,vb9,vd1,ven,vgL,vhv]
    (blockTree #[[vbq,vb3,vd1,vfO,vgL,vhv],[vbq,vb4,vd1,vgo,vgL,vhv],[vbq,vb5,vd1,vfO,vgL,vhv],[vbq,vb6,vd1,vfO,vgL,vhv],[vbq,vb7,vd1,vfO,vgL,vhv],[vbq,vb8,vdb,vd1,vfO,vgL],
      [vbq,vb8,vd1,vfO,vgL,vhS]])
    (blockTree #[[vbq,vcb,vd1,vfO,vgL,vhv],[vbq,vcc,vd1,vfO,vgL,vhv],[vbq,vcd,vd1,vfO,vgL,vhv],[vbq,vce,vd1,vfO,vgL,vhv],[vbq,vcf,vd1,vfO,vgL,vhv],[vbq,vcg,vd1,vfO,vgL,vhv],
      [vbq,vch,vcr,vd1,vfO,vhv]]))
    (.node [vbq,vch,vcE,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vcx,vcX,vgL,vhv],[vbq,vch,vcA,vd1,vfO,via],[vbq,vch,vcB,vcL,vfO,vhv],[vbq,vch,vcB,vdq,vfO,vhv],[vbq,vch,vcB,vdK,vfO,vhv],[vbq,vch,vcB,vd1,vfO,vhW],
      [vbq,vch,vcC,vd1,vfO,vhv]])
    (blockTree #[[vbq,vch,vcG,vfO,vgL,vhv],[vbq,vch,vcI,vfO,vgL,vhv],[vbq,vch,vcJ,vfO,vgL,vhv],[vbq,vch,vcK,vd1,vfO,vgL],[vbq,vch,vcL,vd1,vfO,vhv],[vbq,vch,vcL,vfO,vgL,vhv],
      [vbq,vch,vcL,vfO,vhv]]))))
    (.node [vbq,vch,vdm,vgt,vhf,vhv]
    (.node [vbq,vch,vc2,vd1,vfO,vhv]
    (.node [vbq,vch,vcY,vd1,vfO,vhv]
    (blockTree #[[vbq,vch,vcX,vdm,vgL,vhv],[vbq,vch,vcX,vd1,vgL,vhv],[vbq,vch,vcX,vfO,vgL,vhv],[vbq,vch,vcX,vgt,vgL,vhv],[vbq,vch,vcX,vgL,vhv],[vbq,vch,vcY,vdm,vgt,vhv],
      [vbq,vch,vcY,vdt,vd1,vhv]])
    (blockTree #[[vbq,vch,vcY,vd1,vhp,vhv],[vbq,vch,vcZ,vc8,vd1,vfO],[vbq,vch,vcZ,vds,vd1,vhv],[vbq,vch,vcZ,vd1,vfO,vhv],[vbq,vch,vcZ,vd1,vho,vhv],[vbq,vch,vc0,vd1,vfO,vhv],
      [vbq,vch,vc1,vd1,vfO,vhv]]))
    (.node [vbq,vch,vde,vd1,vfO,vgL]
    (blockTree #[[vbq,vch,vc4,vdm,vgt,vgL],[vbq,vch,vc4,vd1,vfO,vgL],[vbq,vch,vc8,vdl,vd1,vgL],[vbq,vch,vc8,vd1,vfO,vgL],[vbq,vch,vc8,vd1,vgL,vh5],[vbq,vch,vc9,vd1,vfO,vgL],
      [vbq,vch,vda,vd1,vfO,vgL]])
    (blockTree #[[vbq,vch,vdf,vd1,vfO,vgL],[vbq,vch,vdl,vd1,vgL,vhv],[vbq,vch,vdm,vd1,vha,vhv],[vbq,vch,vdm,vd6,vgL,vhv],[vbq,vch,vdm,veH,vgL,vhv],[vbq,vch,vdm,vgt,vgL,vhv],
      [vbq,vch,vdm,vgt,vgL,vhV]])))
    (.node [vbq,vch,vdC,vfO,vgL,vhv]
    (.node [vbq,vch,vdt,vd1,vhp,vhv]
    (blockTree #[[vbq,vch,vdn,vd1,vgL,vhv],[vbq,vch,vdo,vd1,vgL,vhv],[vbq,vch,vdp,vd1,vgL,vhv],[vbq,vch,vdr,vd1,vgL,vhv],[vbq,vch,vdr,vee,vgL,vhv],[vbq,vch,vds,vd1,vgL,vhv],
      [vbq,vch,vdt,vd1,vgL,vhv]])
    (blockTree #[[vbq,vch,vdu,vd1,vgL,vhv],[vbq,vch,vdx,vfO,vgL,vhv],[vbq,vch,vdB,veX,vgL,vhv],[vbq,vch,vdB,ve8,vfO,vhv],[vbq,vch,vdB,vfO,vgL,vhv],[vbq,vch,vdB,vfO,vhd,vhv],
      [vbq,vch,vdB,vgg,vgL,vhv]]))
    (.node [vbq,vch,vdP,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vdD,vfO,vgL,vhv],[vbq,vch,vdE,vfO,vhh,vhv],[vbq,vch,vdF,vfO,vhh,vhv],[vbq,vch,vdG,vfO,vgL,vhv],[vbq,vch,vdH,vfO,vgL,vhv],[vbq,vch,vdI,vfO,vgL,vhv],
      [vbq,vch,vdJ,veN,vfO,vgL]])
    (blockTree #[[vbq,vch,vdQ,vfO,vgL,vhv],[vbq,vch,vdR,vfO,vgL,vhv],[vbq,vch,vdS,vfO,vgL,vhv],[vbq,vch,vdT,vfO,vgL,vhv],[vbq,vch,vdU,vfO,vgL,vhv],[vbq,vch,vdV,vfO,vgL,vhv],
      [vbq,vch,vdW,vfO,vgL,vhv]]))))))
    (.node [vbq,vch,vd1,vfY,vgL,vhv]
    (.node [vbq,vch,vd1,vfO,vgD,vhv]
    (.node [vbq,vch,vd1,ve8,vfO,via]
    (.node [vbq,vch,vd1,veT,vfO,vgL]
    (.node [vbq,vch,vd1,ver,vgL,vhv]
    (blockTree #[[vbq,vch,vdY,vfO,vgL,vhv],[vbq,vch,vdZ,vfO,vgL,vhv],[vbq,vch,vd0,vfO,vgL,vhv],[vbq,vch,vd1,veo,vgL,vhv],[vbq,vch,vd1,vep,vgL,vhv],[vbq,vch,vd1,vep,vhp,vhv],
      [vbq,vch,vd1,veq,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vex,vfO,vgL],[vbq,vch,vd1,veA,vfO,vgL],[vbq,vch,vd1,veK,vfO,vgL],[vbq,vch,vd1,veL,vfO,vgL],[vbq,vch,vd1,veM,vfO,vgL],[vbq,vch,vd1,veR,vfO,vgL],
      [vbq,vch,vd1,veS,vfO,vgL]]))
    (.node [vbq,vch,vd1,veZ,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,veU,vhp,vhv],[vbq,vch,vd1,veV,vha,vhv],[vbq,vch,vd1,veX,ve8,vhv],[vbq,vch,vd1,veX,vgL,vhv],[vbq,vch,vd1,veX,vgL,vh6],[vbq,vch,vd1,veX,vhd,vhv],
      [vbq,vch,vd1,veY,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,ve0,vgL,vhv],[vbq,vch,vd1,ve1,vgL,vhv],[vbq,vch,vd1,ve2,vgL,vhv],[vbq,vch,vd1,ve3,vgL,vhv],[vbq,vch,vd1,ve4,vgL,vhv],[vbq,vch,vd1,ve5,vgL,vhv],
      [vbq,vch,vd1,ve8,vfO,vhv]])))
    (.node [vbq,vch,vd1,vfF,vgL,vhv]
    (.node [vbq,vch,vd1,vfu,vfO,vhv]
    (blockTree #[[vbq,vch,vd1,ve8,vgg,vhv],[vbq,vch,vd1,vff,vfO,vgL],[vbq,vch,vd1,vfk,vfO,vhv],[vbq,vch,vd1,vfl,vfO,vhv],[vbq,vch,vd1,vfm,vfO,vhv],[vbq,vch,vd1,vfs,vfO,vhv],
      [vbq,vch,vd1,vft,vfO,vhv]])
    (blockTree #[[vbq,vch,vd1,vfv,vfO,vhv],[vbq,vch,vd1,vfw,vfO,vhv],[vbq,vch,vd1,vfz,vhp,vhv],[vbq,vch,vd1,vfA,vhp,vhv],[vbq,vch,vd1,vfB,vhp,vhv],[vbq,vch,vd1,vfC,vhp,vhv],
      [vbq,vch,vd1,vfD,vgL,vhv]]))
    (.node [vbq,vch,vd1,vfO,vgi,vgL]
    (blockTree #[[vbq,vch,vd1,vfG,vgL,vh6],[vbq,vch,vd1,vfH,vgL,vh6],[vbq,vch,vd1,vfI,vgL,vhv],[vbq,vch,vd1,vfK,vgL,vhv],[vbq,vch,vd1,vfL,vgL,vhv],[vbq,vch,vd1,vfM,vgL,vhv],
      [vbq,vch,vd1,vfN,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vfO,vgk,vhv],[vbq,vch,vd1,vfO,vgp,vhv],[vbq,vch,vd1,vfO,vgu,vgL],[vbq,vch,vd1,vfO,vgw,vhv],[vbq,vch,vd1,vfO,vgA,via],[vbq,vch,vd1,vfO,vgB,vhv],
      [vbq,vch,vd1,vfO,vgC,vhv]]))))
    (.node [vbq,vch,vd1,vfO,vgL,vhW]
    (.node [vbq,vch,vd1,vfO,vgL,vhB]
    (.node [vbq,vch,vd1,vfO,vgL,vht]
    (blockTree #[[vbq,vch,vd1,vfO,vgE,vhv],[vbq,vch,vd1,vfO,vgH,vhv],[vbq,vch,vd1,vfO,vgI,vhv],[vbq,vch,vd1,vfO,vgJ,vhv],[vbq,vch,vd1,vfO,vgK,vhv],[vbq,vch,vd1,vfO,vgL,vhj],
      [vbq,vch,vd1,vfO,vgL,vhl]])
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhu],[vbq,vch,vd1,vfO,vgL,vhv],[vbq,vch,vd1,vfO,vgL,vhw],[vbq,vch,vd1,vfO,vgL,vhx],[vbq,vch,vd1,vfO,vgL,vhy],[vbq,vch,vd1,vfO,vgL,vhz],
      [vbq,vch,vd1,vfO,vgL,vhA]]))
    (.node [vbq,vch,vd1,vfO,vgL,vhL]
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhC],[vbq,vch,vd1,vfO,vgL,vhD],[vbq,vch,vd1,vfO,vgL,vhE],[vbq,vch,vd1,vfO,vgL,vhF],[vbq,vch,vd1,vfO,vgL,vhG],[vbq,vch,vd1,vfO,vgL,vhH],
      [vbq,vch,vd1,vfO,vgL,vhK]])
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhN],[vbq,vch,vd1,vfO,vgL,vhO],[vbq,vch,vd1,vfO,vgL,vhQ],[vbq,vch,vd1,vfO,vgL,vhR],[vbq,vch,vd1,vfO,vgL,vhT],[vbq,vch,vd1,vfO,vgL,vhU],
      [vbq,vch,vd1,vfO,vgL,vhV]])))
    (.node [vbq,vch,vd1,vfO,vg1,vhv]
    (.node [vbq,vch,vd1,vfO,vgT,vhv]
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhX],[vbq,vch,vd1,vfO,vgL,vhZ],[vbq,vch,vd1,vfO,vgL,vh0],[vbq,vch,vd1,vfO,vgM,vhv],[vbq,vch,vd1,vfO,vgN,vhv],[vbq,vch,vd1,vfO,vgO,vhv],
      [vbq,vch,vd1,vfO,vgQ,vhv]])
    (blockTree #[[vbq,vch,vd1,vfO,vgU,vhv],[vbq,vch,vd1,vfO,vgV,vhv],[vbq,vch,vd1,vfO,vgW,vhv],[vbq,vch,vd1,vfO,vgX,vhv],[vbq,vch,vd1,vfO,vgY,vhv],[vbq,vch,vd1,vfO,vgZ,vhv],
      [vbq,vch,vd1,vfO,vg0,vhv]]))
    (.node [vbq,vch,vd1,vfO,vhd,vhv]
    (blockTree #[[vbq,vch,vd1,vfO,vg2,vhv],[vbq,vch,vd1,vfO,vg4,vhv],[vbq,vch,vd1,vfO,vg5,vhv],[vbq,vch,vd1,vfO,vg7,vhv],[vbq,vch,vd1,vfO,vg8,vhv],[vbq,vch,vd1,vfO,vha,vhv],
      [vbq,vch,vd1,vfO,vhb,vhv]])
    (blockTree #[[vbq,vch,vd1,vfO,vhf,vhv],[vbq,vch,vd1,vfP,vgL,vhv],[vbq,vch,vd1,vfQ,vgL,vhv],[vbq,vch,vd1,vfR,vgL,vhv],[vbq,vch,vd1,vfT,vgL,vhv],[vbq,vch,vd1,vfV,vgL,vhv],
      [vbq,vch,vd1,vfX,vgL,vhv]])))))
    (.node [vbq,vc7,vd1,vfO,vgL,vhv]
    (.node [vbq,vch,vec,vfO,vgL,vhv]
    (.node [vbq,vch,vd1,vgf,vgL,vh6]
    (.node [vbq,vch,vd1,vf7,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,vfZ,vgL,vhv],[vbq,vch,vd1,vf0,vgL,vhv],[vbq,vch,vd1,vf1,vgL,vhv],[vbq,vch,vd1,vf3,vgL,vhv],[vbq,vch,vd1,vf4,vgL,vhv],[vbq,vch,vd1,vf5,vhp,vhv],
      [vbq,vch,vd1,vf6,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vf8,vgL,vhv],[vbq,vch,vd1,vf9,vgL,vhv],[vbq,vch,vd1,vga,vhp,vhv],[vbq,vch,vd1,vgb,vhp,vhv],[vbq,vch,vd1,vgc,vgL,vhv],[vbq,vch,vd1,vgd,vgL,vhv],
      [vbq,vch,vd1,vge,vgL,vhv]]))
    (.node [vbq,vch,vd1,vgL,vhv,vh5]
    (blockTree #[[vbq,vch,vd1,vgg,vgL,vhv],[vbq,vch,vd1,vgg,vhd,vhv],[vbq,vch,vd1,vgh,vha,vhv],[vbq,vch,vd1,vgj,vhp,vhv],[vbq,vch,vd1,vgm,vgL,vhv],[vbq,vch,vd1,vgn,vgL,vhv],
      [vbq,vch,vd1,vgL,vho,vhv]])
    (blockTree #[[vbq,vch,vd2,vfO,vgL,vhv],[vbq,vch,vd3,vfO,vgL,vhv],[vbq,vch,vd4,vfO,vgL,vhv],[vbq,vch,vd7,vfO,vgL,vhv],[vbq,vch,vd9,vfO,vgL,vhv],[vbq,vch,vea,vfO,vgL,vhv],
      [vbq,vch,veb,vfO,vgL,vhv]])))
    (.node [vbq,vch,veN,vfO,vhd,vhv]
    (.node [vbq,vch,veI,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,ved,vfO,vgL,vhv],[vbq,vch,vee,vfO,vgL,vhv],[vbq,vch,veg,vfO,vgL,vhv],[vbq,vch,vei,vfO,vgL,vhv],[vbq,vch,vej,vfO,vgL,vhv],[vbq,vch,veE,vfO,vgL,vhv],
      [vbq,vch,veG,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,veJ,vfO,vgL,vhv],[vbq,vch,veK,veN,vfO,vgL],[vbq,vch,veN,veX,vgL,vhv],[vbq,vch,veN,ve8,vfO,vhv],[vbq,vch,veN,vfO,vgL,vhv],[vbq,vch,veN,vfO,vgL,vh6],
      [vbq,vch,veN,vfO,vgL,via]]))
    (.node [vbq,vcn,vd1,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,veN,vgg,vgL,vhv],[vbq,vch,vfi,vfO,vgL,vhv],[vbq,vch,vfo,vfO,vgL,vhv],[vbq,vch,vfo,vfO,vhp,vhv],[vbq,vci,vd1,vfO,vgL,vhv],[vbq,vcj,vd1,vfO,vgL,vhv],
      [vbq,vcl,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbq,vco,vd1,vfO,vgL,vhv],[vbq,vcp,vd1,vfO,vgL,vhv],[vbq,vcq,vd1,vfO,vgL,vhv],[vbq,vct,vd1,vfO,vgL,vhv],[vbq,vcR,vd1,vfO,vgL,vhv],[vbq,vcV,vd1,vfO,vgL,vhv],
      [vbq,vc5,vd1,vfO,vgL,vhv]]))))
    (.node [vch,vcN,vd1,vfO,vgL,vhv]
    (.node [vbq,vd1,vex,vfO,vgL]
    (.node [vbq,vdb,vd1,vfO,vgL,via]
    (blockTree #[[vbq,vc8,vdb,vd1,vfO,vgL],[vbq,vc8,vd1,vfO,vgL,vhS],[vbq,vdb,vdB,vfO,vgL,vhv],[vbq,vdb,vd1,veX,vgL,vhv],[vbq,vdb,vd1,ve8,vfO,vhv],[vbq,vdb,vd1,vfO,vgL,vhv],
      [vbq,vdb,vd1,vfO,vgL,vh6]])
    (blockTree #[[vbq,vdb,vd1,vfO,vhd,vhv],[vbq,vdb,vd1,vgg,vgL,vhv],[vbq,vdb,veN,vfO,vgL,vhv],[vbq,vdd,vee,vfO,vgL,vhv],[vbq,vdm,vfh,vgt,vgL,vhv],[vbq,vd1,vev,vfO,vgL,vhv],
      [vbq,vd1,vew,vex,vfO,vgL]]))
    (.node [vbs,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vbq,vd1,vex,vfO,vgL,vhv],[vbq,vd1,vez,vfO,vgL,vhv],[vbq,vd1,vfg,vfO,vgL,vhv],[vbq,vd1,vfh,vfO,vgL,vhv],[vbq,vd1,vfh,vgL,vhp,vhv],[vbq,vd1,vfp,vfO,vgL,vhv],
      [vbr,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbt,vch,vd1,vfO,vgL,vhv],[vbu,vch,vd1,vfO,vgL,vhv],[vbw,vch,vd1,vfO,vgL,vhv],[vbx,vch,vd1,vfO,vgL,vhv],[vbz,vch,vd1,vfO,vgL,vhv],[vbE,vch,vd1,vfO,vgL,vhv],
      [vbV,vdd,vd1,vfO,vgL,vhv]])))
    (.node [vch,vd1,ve5,vfO,vgL,vhv]
    (.node [vch,vdm,veD,vgt,vgL,vhv]
    (blockTree #[[vch,vcP,vd1,vfO,vgL,vhv],[vch,vcZ,vc3,vd1,vfO,vhv],[vch,vcZ,vd1,vfO,vhe,vhv],[vch,vc3,vd1,vfO,vgL,vhv],[vch,vc3,vd1,vfO,vhp,vhv],[vch,vc5,vd1,vfO,vgL,vhv],
      [vch,vdd,vee,vfO,vgL,vhv]])
    (blockTree #[[vch,vdw,veQ,vfO,vgL,vhv],[vch,vdy,veE,vfO,vgL,vhv],[vch,vd1,veq,vgh,vgL,vhv],[vch,vd1,veB,vfO,vgL,vhv],[vch,vd1,veD,vfO,vgL,vhv],[vch,vd1,veD,vgL,vhp,vhv],
      [vch,vd1,veE,vfO,vgL,vhv]]))
    (.node [vch,vd1,vff,vfO,vgL,vh2]
    (blockTree #[[vch,vd1,ve5,vgh,vgL,vhv],[vch,vd1,ve5,vgL,vhv],[vch,vd1,vfa,vff,vfO,vgL],[vch,vd1,vfc,vfO,vgL,vhv],[vch,vd1,vfe,vfO,vgL,vhv],[vch,vd1,vff,vfO,vgL],
      [vch,vd1,vff,vfO,vgL,vhv]])
    (blockTree #[[vch,veE,vfO,vgL,vhv],[vc5,vdd,vd1,vfO,vgL,vhv],[vc5,vd1,vfO,vgL,vhv],[vdd,vd1,vee,vfO,vgL,vhv],[vdd,vee,vfO,vgL,vhv],[vdd,veQ,vfr,vfO,vgL,vhv]])))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level5_ok : everyKey (rowOK 4 level4) level5 = true := by
  refine every_node ?_ ?_ ?_
  · decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine every_node ?_ ?_ ?_
            · decide +kernel
            ·
              decide +kernel
            ·
              decide +kernel
theorem closed5 : Closed 5 level5 := closed_next 4 (by decide) level5 level4 closed4 level5_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level6 : BinaryTree (List W) := (.node [vbq,vbv,vch,vd1,vfO,vgL,vhv]
    (.node [v6,vbq,vch,vd1,vfO,vhv]
    (.node [vB,vch,vd1,vfa,vfO,vgL,vhv]
    (.node [vs,vbq,vch,vd1,vfO,vgL,vhS]
    (.node [vm,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[va,vbq,vch,vd1,vfO,vgL,vhv],[vb,vbq,vch,vd1,vfO,vgL,vhv],[vc,vbq,vch,vd1,vfO,vgL,vhv],[vd,vbq,vch,vd1,vfO,vgL,vhv],[ve,vbq,vch,vd1,vfO,vgL,vhv],[vf,vbq,vch,vd1,vfO,vgL,vhv],
      [vg,vbq,vch,vd1,vfO,vgL,vhv],[vh,vbq,vch,vd1,vfO,vgL,vhv],[vi,vbq,vch,vd1,vfO,vgL,vhv],[vj,vbq,vch,vd1,vfO,vgL,vhv],[vk,vbq,vch,vd1,vfO,vgL,vhv],[vl,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vn,vbq,vch,vd1,vfO,vgL,vhv],[vo,vbq,vch,vd1,vfO,vgL,vhv],[vp,vbq,vch,vd1,vfO,vgL,vhv],[vq,vbq,vch,vd1,vfO,vgL,vhv],[vr,vbq,vch,vd1,vfO,vgL,vhv],[vs,vB,vbq,vch,vd1,vfO,vgL],
      [vs,va8,vbq,vch,vd1,vfO,vgL],[vs,vbq,vbY,vd1,vfO,vgL,vhv],[vs,vbq,vb8,vd1,vfO,vgL,vhv],[vs,vbq,vch,vd1,vew,vfO,vgL],[vs,vbq,vch,vd1,vfO,vgL,vhv]]))
    (.node [vA,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vs,vbq,vdd,vd1,vfO,vgL,vhv],[vs,vbq,vd1,vew,vfO,vgL],[vs,vbq,vd1,vew,vfO,vgL,vhv],[vt,vbq,vch,vd1,vfO,vgL,vhv],[vu,vbq,vch,vd1,vfO,vgL,vhv],[vv,vbq,vch,vd1,vfO,vgL,vhv],
      [vw,vbq,vch,vd1,vfO,vgL,vhv],[vx,vbq,vch,vd1,vfO,vgL,vhv],[vy,vB,vbq,vch,vd1,vfO,vgL],[vy,va8,vbq,vch,vd1,vfO,vgL],[vz,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vB,vab,vbq,vch,vd1,vfO,vgL],[vB,vaK,vbq,vch,vd1,vfO,vgL],[vB,va8,vch,vd1,vfO,vgL,vhv],[vB,vbq,vb8,vch,vd1,vfO,vgL],[vB,vbq,vch,vdJ,vd1,vfO,vgL],[vB,vbq,vch,vd1,vfa,vfO,vgL],
      [vB,vbq,vch,vd1,vfO,vgL,vhv],[vB,vbq,vch,vd1,vfO,vgL,vh2],[vB,vbq,vch,vd1,vfO,vgL,vh6],[vB,vbq,vch,vd1,vfO,vgL,via],[vB,vch,vd1,vfa,vfO,vgL]])))
    (.node [vS,vbq,vch,vd1,vfO,vgL,vhv]
    (.node [vF,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vC,vbq,vch,vdd,vd1,vfO,vgL],[vC,vbq,vch,vd1,vfO,vgL],[vC,vbq,vch,vd1,vfO,vgL,vhv],[vE,vbq,vch,vd1,vfO,vgL,vhv],[vF,vaB,vbq,vch,vd1,vgL,vhv],[vF,vaK,vbq,vch,vd1,vfO,vgL],
      [vF,vaK,vbq,vch,vd1,vgL],[vF,vaK,vbq,vch,vd1,vgL,vhv],[vF,vbq,vch,vdm,vd1,vgL,vhv],[vF,vbq,vch,vd1,ven,vgL,vhv],[vF,vbq,vch,vd1,veV,vgL,vhv],[vF,vbq,vch,vd1,vfG,vgL,vhv]])
    (blockTree #[[vF,vbq,vch,vd1,vfO,vgL,vh6],[vF,vbq,vch,vd1,vgh,vgL,vhv],[vF,vbq,vch,vd1,vgo,vgL,vhv],[vG,vbq,vch,vd1,vfO,vgL,vhv],[vH,vbq,vch,vd1,vfO,vgL,vhv],[vJ,vbq,vch,vcB,vd1,vfO,vhv],
      [vN,vbq,vch,vd1,vfO,vgL,vhv],[vO,vbq,vch,vd1,vfO,vgL,vhv],[vP,vbq,vch,vd1,vfO,vgL,vhv],[vQ,vbq,vch,vd1,vfO,vgL,vhv],[vR,vbq,vch,vd1,vfO,vgL,vhv]]))
    (.node [vX,vdd,vd1,vfO,vgL,vhv]
    (blockTree #[[vT,vbq,vch,vd1,vfO,vgL,vhv],[vU,vbq,vch,vd1,vfO,vgL,vhv],[vV,vbq,vch,vd1,vfO,vgL,vhv],[vW,vbq,vch,vd1,vfO,vgL,vhv],[vX,va6,vch,vd1,vfO,vgL,vhv],[vX,vbq,vbY,vd1,vfO,vgL,vhv],
      [vX,vbq,vch,vdS,vfO,vgL,vhv],[vX,vbq,vch,vd1,vfO,vgL,vhv],[vX,vbq,vch,vee,vfO,vgL,vhv],[vX,vbq,vdd,vd1,vfO,vgL,vhv],[vX,vch,vdd,vd1,vfO,vgL,vhv]])
    (blockTree #[[vY,vbq,vch,vd1,vfO,vgL,vhv],[vZ,vbq,vch,vd1,vfO,vgL,vhv],[v0,vbq,vch,vd1,vfO,vgL,vhv],[v1,vbq,vch,vd1,vfO,vgL,vhv],[v2,vch,vdd,vd1,vfO,vgL,vhv],[v3,vbq,vch,vcB,vd1,vfO,vhv],
      [v3,vbq,vch,vcB,vfO,vgL,vhv],[v3,vbq,vch,vcB,vfO,vhv],[v4,vbq,vch,vd1,vfO,vhp,vhv],[v6,vbq,vch,vdd,vd1,vfO,vhv],[v6,vbq,vch,vd1,vfO,vgL,vhv]]))))
    (.node [vaT,vbq,vch,vd1,vfO,vgL,vhv]
    (.node [vav,vbq,vch,vd1,vfO,vgL,vhv]
    (.node [vak,va0,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[v7,vbq,vch,vd1,vfz,vgL,vhv],[v7,vbq,vch,vd1,vfO,vgL,vhv],[v7,vbq,vch,vd1,vfO,vhp,vhv],[v7,vbq,vch,vd1,vgh,vgL,vhv],[v8,vbq,vch,vd1,vfO,vgL,vhv],[v9,vbq,vch,vd1,vfO,vgL,vhv],
      [vab,va8,vbq,vch,vd1,vfO,vgL],[vaf,vbq,vch,vd1,vfO,vgL,vhv],[vag,vbq,vch,vd1,vfO,vgL,vhv],[vah,vbq,vch,vd1,vfO,vgL,vhv],[vai,vbq,vch,vd1,vfO,vgL,vhv],[vaj,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vak,vbq,vch,vd1,vfO,vgL,vhv],[vam,vbq,vch,vd1,vfO,vgL,vhv],[van,vbq,vch,vd1,vfO,vgL,vhv],[vao,vaV,vch,vd1,vfO,vgL,vhv],[vao,va0,vch,vd1,vfO,vgL,vhv],[vao,vbq,vch,vd1,vfO,vgL,vhv],
      [vao,vbq,vch,vd1,vgh,vgL,vhv],[vap,vbq,vch,vd1,vfO,vgL,vhv],[vaq,vbq,vch,vd1,vfO,vgL,vhv],[var,vbq,vch,vd1,vfO,vgL,vhv],[vat,vbq,vch,vd1,vfO,vgL,vhv]]))
    (.node [vaF,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vaw,vbq,vch,vd1,vfO,vgL,vhv],[vax,vbq,vch,vd1,vfO,vgL,vhv],[vaz,vbq,vch,vd1,vfO,vgL,vhv],[vaA,vbq,vch,vd1,vfO,vgL,vhv],[vaB,vaV,vbq,vch,vd1,vgL,vhv],[vaB,vbq,vch,vcx,vd1,vgL,vhv],
      [vaB,vbq,vch,vcx,vfO,vgL,vhv],[vaB,vbq,vch,vcx,vgL,vhv],[vaB,vbq,vch,vd1,vfO,vgL,vhv],[vaB,vbq,vch,vd1,vgt,vgL,vhv],[vaB,vbq,vch,vd1,vgL,vhp,vhv]])
    (blockTree #[[vaG,vbq,vch,vd1,vfO,vgL,vhv],[vaJ,vbq,vch,vcB,vd1,vfO,vhv],[vaJ,vbq,vch,vd1,vfz,vfO,vhv],[vaJ,vbq,vch,vd1,vfO,vgL,vhv],[vaJ,vbq,vch,vd1,vgL,vhp,vhv],[vaK,va8,vbq,vch,vd1,vfO,vgL],
      [vaL,vbq,vch,vd1,vfO,vgL,vhv],[vaP,vbq,vch,vd1,vfO,vgL,vhv],[vaQ,vbq,vch,vd1,vfO,vgL,vhv],[vaR,vbq,vch,vd1,vfO,vgL,vhv],[vaS,vbq,vch,vd1,vfO,vgL,vhv]])))
    (.node [va5,vbq,vch,vd1,vfO,vgL,vhv]
    (.node [vaY,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vaU,vbq,vch,vd1,vfO,vgL,vhv],[vaV,vbq,vch,vdm,vd1,vgL,vhv],[vaV,vbq,vch,vd1,veV,vgL,vhv],[vaV,vbq,vch,vd1,vfs,vfO,vhv],[vaV,vbq,vch,vd1,vfO,vgL,vhv],[vaV,vbq,vch,vd1,vfO,vha,vhv],
      [vaV,vbq,vch,vd1,vgh,vgL,vhv],[vaV,vch,vd1,vfO,vgh,vgL,vhv],[vaV,vch,vd1,vgh,vgL,vhv],[vaW,vbq,vch,vd1,vfO,vgL,vhv],[vaX,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vaZ,vbq,vch,vd1,vfO,vgL,vhv],[va0,va6,vch,vd1,vfO,vgL,vhv],[va0,vbq,vch,vdy,vfO,vgL,vhv],[va0,vbq,vch,vd1,vfO,vgL,vhv],[va0,vbq,vch,veQ,vfO,vgL,vhv],[va0,vch,vdd,vd1,vfO,vgL,vhv],
      [va0,vch,vdy,vd1,vfO,vgL,vhv],[va0,vch,vdy,vfO,vgL,vhv],[va0,vch,vd1,vfO,vgh,vgL,vhv],[va2,vbq,vch,vd1,vfO,vgL,vhv],[va3,vbq,vch,vd1,vfO,vgL,vhv]]))
    (.node [va8,vbq,vch,vd1,vfO,vgL,vh2]
    (blockTree #[[va6,vbq,vch,vd1,vfO,vgL,vhv],[va6,vbq,vdd,vd1,vfO,vgL,vhv],[va7,vbq,vch,vd1,vfO,vgL,vhv],[va8,vbq,vb0,vd1,vfO,vgL,vhv],[va8,vbq,vb8,vch,vd1,vfO,vgL],[va8,vbq,vch,vdB,vfO,vgL,vhv],
      [va8,vbq,vch,vdJ,vd1,vfO,vgL],[va8,vbq,vch,vd1,veX,vgL,vhv],[va8,vbq,vch,vd1,ve8,vfO,vhv],[va8,vbq,vch,vd1,vfa,vfO,vgL],[va8,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[va8,vbq,vch,vd1,vfO,vgL,vh6],[va8,vbq,vch,vd1,vfO,vgL,via],[va8,vbq,vch,vd1,vfO,vhd,vhv],[va8,vbq,vch,vd1,vgg,vgL,vhv],[va8,vbq,vch,veN,vfO,vgL,vhv],[va8,vbq,vdb,vd1,vfO,vgL,vhv],
      [va8,vch,vd1,vfO,vgL,vhv,vh2],[va8,vch,vd1,vfO,vgL,vh2],[va9,vbq,vch,vd1,vfO,vgL,vhv],[vbf,vbq,vch,vd1,vfO,vgL,vhv],[vbq,vbq,vch,vd1,vfO,vgL,vhv]])))))
    (.node [vbq,vch,vd1,veX,vfO,vgL,vhv]
    (.node [vbq,vch,vc8,vdd,vd1,vfO,vgL]
    (.node [vbq,vch,vcx,vdm,vd1,vgL,vhv]
    (.node [vbq,vb0,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vbq,vbA,vch,vd1,vfO,vgL,vhv],[vbq,vbJ,vch,vd1,vfO,vgL,vhv],[vbq,vbK,vch,vd1,vfO,vgL,vhv],[vbq,vbL,vch,vd1,vfO,vgL,vhv],[vbq,vbN,vch,vd1,vfO,vgL,vhv],[vbq,vbO,vch,vd1,vfO,vgL,vhv],
      [vbq,vbP,vch,vd1,vfO,vgL,vhv],[vbq,vbQ,vdd,vd1,vfO,vgL,vhv],[vbq,vbR,vch,vd1,vfO,vgL,vhv],[vbq,vbS,vch,vd1,vfO,vhp,vhv],[vbq,vbY,vch,vd1,vfO,vgL,vhv],[vbq,vbZ,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbq,vb0,vd1,vfO,vgL,vhv],[vbq,vb2,vch,vd1,vfO,vgL,vhv],[vbq,vb4,vch,vd1,vfO,vgL,vhv],[vbq,vb8,vch,vd1,vfO,vgL,vhv],[vbq,vb9,vch,vd1,vfO,vgL,vhv],[vbq,vca,vch,vd1,vfO,vgL,vhv],
      [vbq,vch,vch,vd1,vfO,vgL,vhv],[vbq,vch,vck,vd1,vfO,vgL,vhv],[vbq,vch,vcm,vd1,vfO,vgL,vhv],[vbq,vch,vcv,vd1,vfO,vgL,vhv],[vbq,vch,vcw,vd1,vfO,vgL,vhv]]))
    (.node [vbq,vch,vcB,vfO,vgL,vhh,vhv]
    (blockTree #[[vbq,vch,vcx,vd1,vfO,vgL,vhv],[vbq,vch,vcx,vfO,vgt,vgL,vhv],[vbq,vch,vcy,vd1,vfO,vgL,vhv],[vbq,vch,vcz,vd1,vfO,vgL,vhv],[vbq,vch,vcA,vd1,vfO,vgL,vhv],[vbq,vch,vcB,vdt,vd1,vgL,vhv],
      [vbq,vch,vcB,vdE,vd1,vfO,vhv],[vbq,vch,vcB,vd1,vfO,vgL,vhv],[vbq,vch,vcB,vd1,vfO,vhp,vhv],[vbq,vch,vcB,vd1,vfO,vhv,via],[vbq,vch,vcB,vd1,vf7,vgL,vhv]])
    (blockTree #[[vbq,vch,vcD,vd1,vfO,vgL,vhv],[vbq,vch,vcH,vd1,vfO,vgL,vhv],[vbq,vch,vcO,vd1,vfO,vgL,vhv],[vbq,vch,vcQ,vd1,vfO,vgL,vhv],[vbq,vch,vcS,vd1,vfO,vgL,vhv],[vbq,vch,vcT,vd1,vfO,vgL,vhv],
      [vbq,vch,vcU,vd1,vfO,vgL,vhv],[vbq,vch,vcW,vd1,vfO,vgL,vhv],[vbq,vch,vcZ,vdd,vd1,vfO,vhv],[vbq,vch,vcZ,vd1,vfO,vgL,vhv],[vbq,vch,vcZ,vd1,vfO,vhv]])))
    (.node [vbq,vch,vdN,vd1,vfO,vgL,vhv]
    (.node [vbq,vch,vdm,vd1,vgL,vhp,vhv]
    (blockTree #[[vbq,vch,vc8,vd1,vfO,vgL],[vbq,vch,vc8,vd1,vfO,vgL,vhv],[vbq,vch,vdb,vd1,vfO,vgL,vhv],[vbq,vch,vdd,vd1,vfO,vgL,vhv],[vbq,vch,vdg,vd1,vfO,vgL,vhv],[vbq,vch,vdh,vd1,vfO,vgL,vhv],
      [vbq,vch,vdi,vd1,vfO,vgL,vhv],[vbq,vch,vdj,vd1,vfO,vgL,vhv],[vbq,vch,vdk,vd1,vfO,vgL,vhv],[vbq,vch,vdm,vd1,vfO,vgL,vhv],[vbq,vch,vdm,vd1,vgt,vgL,vhv]])
    (blockTree #[[vbq,vch,vdm,vfO,vgt,vgL,vhv],[vbq,vch,vdm,vgt,vgL,vhv],[vbq,vch,vdt,vd1,vfO,vgL,vhv],[vbq,vch,vdt,vd1,vgL,vhv],[vbq,vch,vdw,vd1,vfO,vgL,vhv],[vbq,vch,vdB,vd1,vfO,vgL,vhv],
      [vbq,vch,vdB,vfO,vgL,vhv],[vbq,vch,vdE,vd1,vfO,vgL,vhv],[vbq,vch,vdF,vd1,vfO,vgL,vhv],[vbq,vch,vdL,vd1,vfO,vgL,vhv],[vbq,vch,vdM,vd1,vfO,vgL,vhv]]))
    (.node [vbq,vch,vd1,vem,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vdO,vd1,vfO,vgL,vhv],[vbq,vch,vdS,vd1,vfO,vgL,vhv],[vbq,vch,vdS,vfO,vgL,vhv],[vbq,vch,vd1,vd1,vfO,vgL,vhv],[vbq,vch,vd1,vd5,vfO,vgL,vhv],[vbq,vch,vd1,vd6,vfO,vgL,vhv],
      [vbq,vch,vd1,vd8,vfO,vgL,vhv],[vbq,vch,vd1,vee,vfO,vgL,vhv],[vbq,vch,vd1,vef,vfO,vgL,vhv],[vbq,vch,vd1,vek,vfO,vgL,vhv],[vbq,vch,vd1,vel,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,ven,vgL,vhp,vhv],[vbq,vch,vd1,ves,vfO,vgL,vhv],[vbq,vch,vd1,veu,vfO,vgL,vhv],[vbq,vch,vd1,vey,vfO,vgL,vhv],[vbq,vch,vd1,veH,vfO,vgL,vhv],[vbq,vch,vd1,veN,vfO,vgL,vhv],
      [vbq,vch,vd1,veQ,vfO,vgL,vhv],[vbq,vch,vd1,veU,vfO,vgL,vhv],[vbq,vch,vd1,veV,vfO,vgL,vhv],[vbq,vch,vd1,veV,vgL,vhp,vhv],[vbq,vch,vd1,veW,vfO,vgL,vhv]]))))
    (.node [vbq,vch,vd1,vfO,vgL,vg9,vhv]
    (.node [vbq,vch,vd1,vfO,vfW,vgL,vhv]
    (.node [vbq,vch,vd1,vfy,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,veX,vgL,vhv],[vbq,vch,vd1,ve6,vfO,vgL,vhv],[vbq,vch,vd1,ve7,vfO,vhp,vhv],[vbq,vch,vd1,ve8,vfO,vgL,vhv],[vbq,vch,vd1,ve8,vfO,vhv],[vbq,vch,vd1,ve9,vfO,vgL,vhv],
      [vbq,vch,vd1,vfa,vfO,vgL,vhv],[vbq,vch,vd1,vfj,vfO,vgL,vhv],[vbq,vch,vd1,vfn,vfO,vgL,vhv],[vbq,vch,vd1,vfs,vfO,vgL,vhv],[vbq,vch,vd1,vfs,vfO,vhv],[vbq,vch,vd1,vfx,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vfz,vfO,vgL,vhv],[vbq,vch,vd1,vfz,vfO,vhp,vhv],[vbq,vch,vd1,vfz,vgL,vhp,vhv],[vbq,vch,vd1,vfz,vhp,vhv],[vbq,vch,vd1,vfE,vfO,vgL,vhv],[vbq,vch,vd1,vfG,vfO,vgL,vhv],
      [vbq,vch,vd1,vfH,vfO,vgL,vhv],[vbq,vch,vd1,vfJ,vfO,vgL,vhv],[vbq,vch,vd1,vfO,vfO,vgL,vhv],[vbq,vch,vd1,vfO,vfS,vgL,vhv],[vbq,vch,vd1,vfO,vfU,vgL,vhv]]))
    (.node [vbq,vch,vd1,vfO,vgt,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,vfO,vf2,vgL,vhv],[vbq,vch,vd1,vfO,vf7,vgL,vhv],[vbq,vch,vd1,vfO,vga,vgL,vhv],[vbq,vch,vd1,vfO,vgb,vgL,vhv],[vbq,vch,vd1,vfO,vgf,vgL,vhv],[vbq,vch,vd1,vfO,vgg,vgL,vhv],
      [vbq,vch,vd1,vfO,vgh,vgL,vhv],[vbq,vch,vd1,vfO,vgl,vgL,vhv],[vbq,vch,vd1,vfO,vgq,vgL,vhv],[vbq,vch,vd1,vfO,vgr,vgL,vhv],[vbq,vch,vd1,vfO,vgs,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vfO,vgv,vgL,vhv],[vbq,vch,vd1,vfO,vgx,vgL,vhv],[vbq,vch,vd1,vfO,vgz,vgL,vhv],[vbq,vch,vd1,vfO,vgA,vgL,vhv],[vbq,vch,vd1,vfO,vgF,vgL,vhv],[vbq,vch,vd1,vfO,vgG,vgL,vhv],
      [vbq,vch,vd1,vfO,vgL,vgL,vhv],[vbq,vch,vd1,vfO,vgL,vgP,vhv],[vbq,vch,vd1,vfO,vgL,vgR,vhv],[vbq,vch,vd1,vfO,vgL,vgS,vhv],[vbq,vch,vd1,vfO,vgL,vg6,vhv]])))
    (.node [vbq,vch,vd1,vfO,vgL,vhv,vh7]
    (.node [vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vha,vhv],[vbq,vch,vd1,vfO,vgL,vhc,vhv],[vbq,vch,vd1,vfO,vgL,vhd,vhv],[vbq,vch,vd1,vfO,vgL,vhh,vhv],[vbq,vch,vd1,vfO,vgL,vhi,vhv],[vbq,vch,vd1,vfO,vgL,vhm,vhv],
      [vbq,vch,vd1,vfO,vgL,vhn,vhv],[vbq,vch,vd1,vfO,vgL,vhp,vhv],[vbq,vch,vd1,vfO,vgL,vhq,vhv],[vbq,vch,vd1,vfO,vgL,vhr,vhv],[vbq,vch,vd1,vfO,vgL,vhs,vhv]])
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhv,vhv],[vbq,vch,vd1,vfO,vgL,vhv,vhI],[vbq,vch,vd1,vfO,vgL,vhv,vhJ],[vbq,vch,vd1,vfO,vgL,vhv,vhM],[vbq,vch,vd1,vfO,vgL,vhv,vhP],[vbq,vch,vd1,vfO,vgL,vhv,vhS],
      [vbq,vch,vd1,vfO,vgL,vhv,vh1],[vbq,vch,vd1,vfO,vgL,vhv,vh2],[vbq,vch,vd1,vfO,vgL,vhv,vh3],[vbq,vch,vd1,vfO,vgL,vhv,vh4],[vbq,vch,vd1,vfO,vgL,vhv,vh6]]))
    (.node [vbq,vch,vd1,vgh,vgL,vhv,vh6]
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhv,vh8],[vbq,vch,vd1,vfO,vgL,vhv,vib],[vbq,vch,vd1,vfO,vgL,vhv,vic],[vbq,vch,vd1,vfO,vgL,vhv,vid],[vbq,vch,vd1,vfO,vha,vhv],[vbq,vch,vd1,vfO,vhd,vhv],
      [vbq,vch,vd1,vfO,vhe,vhp,vhv],[vbq,vch,vd1,vfO,vhh,vhp,vhv],[vbq,vch,vd1,vf7,vgL,vhv],[vbq,vch,vd1,vgg,vgL,vhv],[vbq,vch,vd1,vgh,vgL,vhp,vhv]])
    (blockTree #[[vbq,vch,vd1,vgo,vgL,vhp,vhv],[vbq,vch,vee,vfO,vgL,vhv],[vbq,vch,veN,vfO,vgL,vhv],[vbq,vdb,vd1,vfO,vgL,vhv],[vbq,vdd,vd1,vfr,vfO,vgL,vhv],[vbq,vdd,vd1,vfO,vgL,vhv,vhS],
      [vbY,vch,vdd,vd1,vfO,vgL,vhv],[vch,vdd,vd1,veQ,vfO,vgL,vhv],[vch,vdd,vd1,vfO,vgL,vhe,vhv],[vch,vd1,veQ,vfO,vgh,vgL,vhv],[vch,vd1,veV,vfO,vgh,vgL,vhv]]))))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level6_ok : everyKey (rowOK 5 level5) level6 = true := by
  refine every_node ?_ ?_ ?_
  · decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine every_node ?_ ?_ ?_
          · decide +kernel
          ·
            decide +kernel
          ·
            decide +kernel
theorem closed6 : Closed 6 level6 := closed_next 5 (by decide) level6 level5 closed5 level6_ok
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level7 : BinaryTree (List W) := (.node [vbq,vch,vcx,vd1,vfO,vgL,vhv]
    (blockTree #[[vs,vbq,vch,vd1,vfO,vgL,vhv],[vB,vbq,vch,vd1,vfO,vgL,vhv],[vF,vbq,vch,vd1,vfO,vgL,vhv],[vX,vbq,vch,vd1,vfO,vgL,vhv],[vaV,vbq,vch,vd1,vfO,vgL,vhv],[va0,vbq,vch,vd1,vfO,vgL,vhv],
      [va8,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,vcB,vd1,vfO,vgL,vhv],[vbq,vch,vdd,vd1,vfO,vgL,vhv],[vbq,vch,vd1,vfz,vfO,vgL,vhv],[vbq,vch,vd1,vfO,vgh,vgL,vhv],[vbq,vch,vd1,vfO,vgt,vgL,vhv],[vbq,vch,vd1,vfO,vgL,vhp,vhv]]))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level7_ok : everyKey (rowOK 6 level6) level7 = true := by
  refine every_node ?_ ?_ ?_
  · decide +kernel
  ·
    decide +kernel
  ·
    decide +kernel
theorem closed7 : Closed 7 level7 := closed_next 6 (by decide) level7 level6 closed6 level7_ok
def p0 (i : Fin 108) : Fin 108 := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107] : Array (Fin 108))[i.val]!
def p1 (i : Fin 108) : Fin 108 := (#[0,5,7,6,8,1,3,2,4,10,9,11,13,12,14,22,24,23,25,26,27,28,15,17,16,18,19,20,21,30,29,32,31,33,34,38,39,40,35,36,37,46,47,48,49,50,41,42,43,44,45,51,53,52,54,59,61,60,62,55,57,56,58,64,63,65,67,66,68,76,78,77,79,80,81,82,69,71,70,72,73,74,75,84,83,86,85,87,88,92,93,94,89,90,91,100,101,102,103,104,95,96,97,98,99,105,107,106] : Array (Fin 108))[i.val]!
def p2 (i : Fin 108) : Fin 108 := (#[1,0,2,4,3,5,9,11,10,6,8,7,12,14,13,15,19,20,21,16,17,18,34,35,36,37,39,38,40,41,42,43,44,45,22,23,24,25,27,26,28,29,30,31,32,33,47,46,49,48,50,52,51,53,55,54,56,58,57,59,63,65,64,60,62,61,66,68,67,69,73,74,75,70,71,72,88,89,90,91,93,92,94,95,96,97,98,99,76,77,78,79,81,80,82,83,84,85,86,87,101,100,103,102,104,106,105,107] : Array (Fin 108))[i.val]!
def p3 (i : Fin 108) : Fin 108 := (#[5,0,7,8,6,1,10,11,9,3,4,2,13,14,12,22,26,27,28,24,23,25,34,38,39,40,36,35,37,46,47,48,49,50,15,17,16,18,20,19,21,30,29,32,31,33,42,41,44,43,45,53,51,52,59,54,61,62,60,55,64,65,63,57,58,56,67,68,66,76,80,81,82,78,77,79,88,92,93,94,90,89,91,100,101,102,103,104,69,71,70,72,74,73,75,84,83,86,85,87,96,95,98,97,99,107,105,106] : Array (Fin 108))[i.val]!
def p4 (i : Fin 108) : Fin 108 := (#[1,5,11,9,10,0,4,2,3,8,6,7,14,12,13,34,36,35,37,39,38,40,15,20,19,21,16,17,18,42,41,44,43,45,22,27,26,28,23,24,25,47,46,49,48,50,29,30,31,32,33,52,53,51,55,59,65,63,64,54,58,56,57,62,60,61,68,66,67,88,90,89,91,93,92,94,69,74,73,75,70,71,72,96,95,98,97,99,76,81,80,82,77,78,79,101,100,103,102,104,83,84,85,86,87,106,107,105] : Array (Fin 108))[i.val]!
def p5 (i : Fin 108) : Fin 108 := (#[5,1,11,10,9,0,8,7,6,4,3,2,14,13,12,34,39,38,40,36,35,37,22,27,26,28,24,23,25,47,46,49,48,50,15,20,19,21,17,16,18,42,41,44,43,45,30,29,32,31,33,53,52,51,59,55,65,64,63,54,62,61,60,58,57,56,68,67,66,88,93,92,94,90,89,91,76,81,80,82,78,77,79,101,100,103,102,104,69,74,73,75,71,70,72,96,95,98,97,99,84,83,86,85,87,107,106,105] : Array (Fin 108))[i.val]!
def maps : List (Fin 108 → Fin 108) := [p0, p1, p2, p3, p4, p5]
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in

theorem map0_valid : Function.Surjective p0 ∧ wordMap p0 goal = goal := by
  have inv : ∀ x, p0 (p0 x) = x := by decide +kernel
  exact ⟨fun x => ⟨p0 x, inv x⟩, by decide +kernel⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in

theorem map1_valid : Function.Surjective p1 ∧ wordMap p1 goal = goal := by
  have inv : ∀ x, p1 (p1 x) = x := by decide +kernel
  exact ⟨fun x => ⟨p1 x, inv x⟩, by decide +kernel⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in

theorem map2_valid : Function.Surjective p2 ∧ wordMap p2 goal = goal := by
  have inv : ∀ x, p2 (p2 x) = x := by decide +kernel
  exact ⟨fun x => ⟨p2 x, inv x⟩, by decide +kernel⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in

theorem map3_valid : Function.Surjective p3 ∧ wordMap p3 goal = goal := by
  have inv : ∀ x, p3 (p4 x) = x := by decide +kernel
  exact ⟨fun x => ⟨p4 x, inv x⟩, by decide +kernel⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in

theorem map4_valid : Function.Surjective p4 ∧ wordMap p4 goal = goal := by
  have inv : ∀ x, p4 (p3 x) = x := by decide +kernel
  exact ⟨fun x => ⟨p3 x, inv x⟩, by decide +kernel⟩
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in

theorem map5_valid : Function.Surjective p5 ∧ wordMap p5 goal = goal := by
  have inv : ∀ x, p5 (p5 x) = x := by decide +kernel
  exact ⟨fun x => ⟨p5 x, inv x⟩, by decide +kernel⟩

theorem all_maps_valid : ∀ p ∈ maps, Function.Surjective p ∧ wordMap p goal = goal := by
  intro p hp
  simp only [maps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact map0_valid
  · exact map1_valid
  · exact map2_valid
  · exact map3_valid
  · exact map4_valid
  · exact map5_valid

set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def fullSeven : BinaryTree (List W) := (.node [vbq,vch,vcF,vd1,vfO,vgL,vhv]
    (.node [vaB,vbq,vch,vd1,vfO,vgL,vhv]
    (.node [v3,vbq,vch,vd1,vfO,vgL,vhv]
    (.node [vF,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vs,vbq,vch,vd1,vfO,vgL,vhv],[vy,vbq,vch,vd1,vfO,vgL,vhv],[vB,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vJ,vbq,vch,vd1,vfO,vgL,vhv],[vX,vbq,vch,vd1,vfO,vgL,vhv],[v2,vbq,vch,vd1,vfO,vgL,vhv]]))
    (.node [vak,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[v4,vbq,vch,vd1,vfO,vgL,vhv],[v7,vbq,vch,vd1,vfO,vgL,vhv],[vab,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vao,vbq,vch,vd1,vfO,vgL,vhv],[vas,vbq,vch,vd1,vfO,vgL,vhv],[vay,vbq,vch,vd1,vfO,vgL,vhv]])))
    (.node [vbq,vbM,vch,vd1,vfO,vgL,vhv]
    (.node [va0,vbq,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vaJ,vbq,vch,vd1,vfO,vgL,vhv],[vaK,vbq,vch,vd1,vfO,vgL,vhv],[vaV,vbq,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[va4,vbq,vch,vd1,vfO,vgL,vhv],[va6,vbq,vch,vd1,vfO,vgL,vhv],[va8,vbq,vch,vd1,vfO,vgL,vhv]]))
    (.node [vbq,vb8,vch,vd1,vfO,vgL,vhv]
    (blockTree #[[vbq,vbQ,vch,vd1,vfO,vgL,vhv],[vbq,vbS,vch,vd1,vfO,vgL,vhv],[vbq,vbY,vch,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,vcx,vd1,vfO,vgL,vhv],[vbq,vch,vcB,vd1,vfO,vgL,vhv]]))))
    (.node [vbq,vch,vd1,vfz,vfO,vgL,vhv]
    (.node [vbq,vch,vd1,vet,vfO,vgL,vhv]
    (.node [vbq,vch,vdy,vd1,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vdd,vd1,vfO,vgL,vhv],[vbq,vch,vdm,vd1,vfO,vgL,vhv],[vbq,vch,vdv,vd1,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,vdE,vd1,vfO,vgL,vhv],[vbq,vch,vdJ,vd1,vfO,vgL,vhv],[vbq,vch,vd1,ven,vfO,vgL,vhv]]))
    (.node [vbq,vch,vd1,ve7,vfO,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,vew,vfO,vgL,vhv],[vbq,vch,vd1,veQ,vfO,vgL,vhv],[vbq,vch,vd1,veV,vfO,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vfa,vfO,vgL,vhv],[vbq,vch,vd1,vfr,vfO,vgL,vhv]])))
    (.node [vbq,vch,vd1,vfO,vgL,vhk,vhv]
    (.node [vbq,vch,vd1,vfO,vgt,vgL,vhv]
    (blockTree #[[vbq,vch,vd1,vfG,vfO,vgL,vhv],[vbq,vch,vd1,vfO,vgh,vgL,vhv],[vbq,vch,vd1,vfO,vgo,vgL,vhv]])
    (blockTree #[[vbq,vch,vd1,vfO,vgy,vgL,vhv],[vbq,vch,vd1,vfO,vgL,vhe,vhv],[vbq,vch,vd1,vfO,vgL,vhh,vhv]]))
    (.node [vbq,vch,vd1,vfO,vgL,vhv,vh2]
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhp,vhv],[vbq,vch,vd1,vfO,vgL,vhv,vhS],[vbq,vch,vd1,vfO,vgL,vhv,vhY]])
    (blockTree #[[vbq,vch,vd1,vfO,vgL,vhv,vh6],[vbq,vch,vd1,vfO,vgL,vhv,via]])))))
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem fullSeven_ok : everyKey (orbitCovered maps level7) fullSeven = true := by
  refine every_node ?_ ?_ ?_
  · decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
  ·
    refine every_node ?_ ?_ ?_
    · decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
    ·
      refine every_node ?_ ?_ ?_
      · decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel
      ·
        refine every_node ?_ ?_ ?_
        · decide +kernel
        ·
          decide +kernel
        ·
          decide +kernel

theorem closedFullSeven : Closed 7 fullSeven :=
  closed_cover 7 fullSeven level7 maps all_maps_valid fullSeven_ok closed7
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
def level8 : BinaryTree (List W) := (blockTree #[[vbq,vch,vd1,vfO,vgL,vhv]])
set_option maxRecDepth 24000 in
set_option maxHeartbeats 32000000 in
theorem level8_ok : everyKey (rowOK 7 fullSeven) level8 = true := by
  decide +kernel

theorem closed8 : Closed 8 level8 :=
  closed_next 7 (by decide) level8 fullSeven closedFullSeven level8_ok

theorem lower : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins.toFinset :=
  @no_build 8 level8 ins (by decide +kernel) (by decide) closed8 (by decide +kernel)

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit 0xfeeefaeafcecf800 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem binary_lower (C : Circuit) (ok : PEqualNP.MetaComplexity.FanInTwo C)
    (h : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) : 9 ≤ binaryCost C.gates :=
  Nat.succ_le_of_lt (bound_from_search 0xfeeefaeafcecf800 8 ins (by decide +kernel)
    sampled rfl lower C.gates C.output ok h)

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 7]⟩,
    ⟨.or, [0, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [3, 4]⟩,
    ⟨.and, [6, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [9, 10]⟩,
    ⟨.and, [13, 14]⟩], 15⟩

theorem witness_mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

theorem witness_size : witness.size = 10 := rfl

set_option maxRecDepth 100000 in
theorem witness_correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_13733_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_13733_aux in
theorem PEqualNP.Outside.L_meta_13733 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4243388416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, ok, size, eval⟩ := h
  change ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x at eval
  by_cases hasNot : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hg, hn⟩ := hasNot
    have less : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, hg, by simp [isBinary, hn]⟩
    have lower := binary_lower C ok eval
    change C.gates.length ≤ s at size
    exact ⟨witness, witness_mono, by rw [witness_size]; omega, witness_correct⟩
  · refine ⟨C, ?_, size, eval⟩
    intro g hg
    obtain ⟨hop, cap⟩ := ok g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun e => (hasNot ⟨g, hg, e⟩).elim)), cap⟩
