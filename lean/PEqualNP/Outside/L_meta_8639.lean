import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8639

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

-- The upper and lower halves represent opposite target labels on 30 pairs of assignments.
abbrev W := BitVec 60
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 30 := ((x >>> 30) ^^^ x).setWidth 30
def cuts (ws : List W) : BitVec 30 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 30) ++ (0 : BitVec 30)
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

def differs (i : Fin 30) (w : W) : Prop :=
  w.getLsbD (30+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 30) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 30+i.val < 60 := by omega
  have hi' : i.val < 60 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 30) :
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
  change (cuts ws)[j] = (BitVec.allOnes 30)[j]
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
  · change reachable av (BitVec.allOnes 60 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 60)
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

private def bit (k : Fin 60) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 60) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 60) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#60)[k.val] = false; simp
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
    (row : ∀ j : Fin 60, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 60) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
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

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 60, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩

def v0 : W := 0x5ad468300a01804
def v1 : W := 0xb72f25fe089816e
def v2 : W := 0xedfbdfdcb566611
def v3 : W := 0xff34f32e00918ca
def v4 : W := 0x5a14f32200118c0
def v5 : W := 0x7fde68380a0980e
def v6 : W := 0x12cf2cf3c1b5eda
def v7 : W := 0x5ad5ff320a15fc4
def v8 : W := 0x7fde6839cf6980e
def v9 : W := 0x120525320810144
def v10 : W := 0xedfbdfdc0004600
def v11 : W := 0xff34f32f74d38cb
def v12 : W := 0x7fd468394e4180e
def v13 : W := 0x5ad468314a0980e
def v14 : W := 0x7f14f32b44518ca
def v15 : W := 0x5a14f32340918ca
def v16 : W := 0x5ad4fb320a118c4
def v17 : W := 0x7f146029444180a
def v18 : W := 0x5ad4fb2202118c0
def v19 : W := 0x5ad4fa300a01884
def v20 : W := 0x5ad4fa22bdfe77f
def v21 : W := 0x5ad4fb3200118c0
def v22 : W := 0x5ad4fb300a01804
def v23 : W := 0x9225b7e57a0fe1f
def v24 : W := 0x80ea9b16bbba0c5
def v25 : W := 0x5ad5ff320814744
def v26 : W := 0xa52b05dc0000000
def v27 : W := 0xa5e10c1d7ec670f
def v28 : W := 0xcb0cd08b24714
def v29 : W := 0xc10c100a04704
def v30 : W := 0x1970200147c0
def v31 : W := 0xcb0cd00a0c724
def v32 : W := 0xca08108b28004
def v33 : W := 0x8020930630920c1
def v34 : W := 0xa520000d74c200b
def v35 : W := 0xcb0c108b2c704
def v36 : W := 0xcb0cd0892c734
def v37 : W := 0xcb0cd08124610
def v38 : W := 0x1204202340918ca
def v39 : W := 0x250a0009c56800a
def v40 : W := 0x120420220a999ee
def v41 : W := 0x120420214a0980e
def v42 : W := 0x802197c43006611
def v43 : W := 0xcb0cd08b2c614
def v44 : W := 0x12042022089816e
def v45 : W := 0x48d0da00b566611
def v46 : W := 0x12ce2831cb2980e
def v47 : W := 0xfffffffe0a9dfee
def v48 : W := 0x48d0da000205e80
def v49 : W := 0x37ce28388b2800e
def v50 : W := 0x370e2038080800e
def v51 : W := 0xffff6dffcff996e
def v52 : W := 0x48d0da01f567e91
def v53 : W := 0x48d0da00b767e91
def v54 : W := 0x5ad46821cf6980e
def v55 : W := 0x48d1df100004600
def v56 : W := 0x5a14f22374d38cb
def v57 : W := 0xa52a00ccb562011
def v58 : W := 0xfff5ff3f7ed7fcf
def v59 : W := 0x5a14f32374538c1
def v60 : W := 0x5ad46831cf61804
def v61 : W := 0x7fdfff3bcf7dfce
def v62 : W := 0x5ad4fb220215ec0
def v63 : W := 0x5ad4fa300a05e84
def v64 : W := 0x5ad4fa220a15fc4
def v65 : W := 0x5ad5ff300a05e04
def v66 : W := 0x48d0da01f767e11
def v67 : W := 0xfffffffebdfe77f
def v68 : W := 0x7fd46829c76180a
def v69 : W := 0xfffefb3ffffb8cf
def v70 : W := 0x5ade68308b29804
def v71 : W := 0x6dda48188560000
def v72 : W := 0xfffffffdff6fe1f
def v73 : W := 0x7f14f229744388b
def v74 : W := 0x7fde68388f61804
def v75 : W := 0x7fde68388d6800e
def v76 : W := 0x9224b32770938cb
def v77 : W := 0x7fde6839c56180a
def v78 : W := 0xed30d30c3442001
def v79 : W := 0xfffffffff5f7edb
def v80 : W := 0xb72f25fe009004a
def v81 : W := 0xb724b32e30920cb
def v82 : W := 0xb724212e009004a
def v83 : W := 0xff3ff7ff7cdb9ef
def v84 : W := 0xb72f25fc080800e
def v85 : W := 0xda34f32630938c1
def v86 : W := 0xb72f25fe0810144
def v87 : W := 0xff34f32d744380b
def v88 : W := 0xff34f32e34d204b
def v89 : W := 0xff34f32e34538c1
def v90 : W := 0x802197c63096771
def v91 : W := 0xfffefb3ff5f38cb
def v92 : W := 0xff3ef3eff5f38db
def v93 : W := 0xff3ef32ff5fb8cb
def v94 : W := 0xff35f7ef74d39eb
def v95 : W := 0xff3ef3ef74db8eb
def v96 : W := 0xfff4fb2ff7f38cb
def v97 : W := 0xff3ff7ff74d38cb
def v98 : W := 0x802197c600947e0
def v99 : W := 0x7fdf6cf9cf6992e
def v100 : W := 0x7fdefa39ff6b88f
def v101 : W := 0x8021970630967c1
def v102 : W := 0x802197c630966d1
def v103 : W := 0x802197c630167d1
def v104 : W := 0xa52a000df5ea00b
def v105 : W := 0xfffefb3dff6b80f
def v106 : W := 0xfffe68fdcfe982e
def v107 : W := 0xfffe683dffeb80f
def v108 : W := 0xfffe68fdff6b81f
def v109 : W := 0x5adffff20a1dfe4
def v110 : W := 0xffff6dfdcf6980e
def v111 : W := 0xa52a00cdf5e201b
def v112 : W := 0xa52a00cdf56a01b
def v113 : W := 0xa52a00ccb5ea03b
def v114 : W := 0xfffffffe0a15fc4
def v115 : W := 0xdaf5fff60a95fe4
def v116 : W := 0x5ad5ff320015ec0
def v117 : W := 0xb04d00808124
def v118 : W := 0x120420220a119c4
def v119 : W := 0x4810d2017443881
def v120 : W := 0x48d04801c761800
def v121 : W := 0x802105c60090160
def v122 : W := 0xa52a00cc008802a
def v123 : W := 0xfffffffebf77fd5

def ins_e8a8a888 : List W := [0xedfbdfdcb566611, 0xb72f25fe089816e, 0x5ad5ff320a15fc4, 0x7fde6839cf6980e, 0xff34f32f74d38cb]
theorem nd_e8a8a888 : ins_e8a8a888.Nodup := by decide +kernel
theorem rows_e8a8a888 : ∀ j : Fin 60, Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if (ins_e8a8a888.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_e8a8a888_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_0 : everyKey (fun q => !doneTest q) tree_e8a8a888_0 = true := by decide +kernel
theorem closed_e8a8a888_0 : Closed 0 tree_e8a8a888_0 := closed_nil tree_e8a8a888_0 ok_tree_e8a8a888_0
def tree_e8a8a888_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_1 : everyKey (rowOK 0 tree_e8a8a888_0) tree_e8a8a888_1 = true := by decide +kernel
theorem closed_e8a8a888_1 : Closed 1 tree_e8a8a888_1 := closed_next 0 (by decide) tree_e8a8a888_1 tree_e8a8a888_0 closed_e8a8a888_0 ok_tree_e8a8a888_1
def tree_e8a8a888_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_2 : everyKey (rowOK 1 tree_e8a8a888_1) tree_e8a8a888_2 = true := by decide +kernel
theorem closed_e8a8a888_2 : Closed 2 tree_e8a8a888_2 := closed_next 1 (by decide) tree_e8a8a888_2 tree_e8a8a888_1 closed_e8a8a888_1 ok_tree_e8a8a888_2
def tree_e8a8a888_3 : BinaryTree (List W) := (.node [v0,v1,v2,v3] (.node [v4,v5,v1,v2] (.node [v4,v0,v1,v2] (.node [v6,v7,v8,v1] (.node [v9,v8,v10,v11] .nil .nil) .nil) (.node [v4,v12,v1,v2] (.node [v4,v13,v1,v2] .nil .nil) .nil)) (.node [v0,v14,v1,v2] (.node [v15,v0,v1,v2] (.node [v4,v8,v1,v10] .nil .nil) .nil) (.node [v0,v1,v10,v11] .nil .nil))) (.node [v16,v17,v1,v2] (.node [v18,v8,v1,v2] (.node [v19,v1,v2,v11] (.node [v20,v7,v8,v11] .nil .nil) .nil) (.node [v21,v8,v1,v2] (.node [v22,v1,v2,v11] .nil .nil) .nil)) (.node [v7,v23,v1,v11] (.node [v7,v24,v1,v2] (.node [v25,v8,v26,v11] .nil .nil) .nil) (.node [v8,v27,v1,v2] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_3 : everyKey (rowOK 2 tree_e8a8a888_2) tree_e8a8a888_3 = true := by decide +kernel
theorem closed_e8a8a888_3 : Closed 3 tree_e8a8a888_3 := closed_next 2 (by decide) tree_e8a8a888_3 tree_e8a8a888_2 closed_e8a8a888_2 ok_tree_e8a8a888_3
def tree_e8a8a888_4ll : BinaryTree (List W) := (.node [v28,v7,v8,v1,v2] (.node [v29,v7,v8,v1,v2] (.node [v30,v7,v1,v2,v11] (.node [v30,v4,v7,v1,v2] (.node [v30,v29,v7,v1,v2] .nil .nil) (.node [v30,v0,v1,v2,v11] .nil .nil)) (.node [v29,v0,v7,v1,v2] (.node [v29,v4,v8,v1,v2] .nil .nil) .nil)) (.node [v31,v7,v8,v1,v2] (.node [v32,v7,v33,v1,v2] (.node [v29,v8,v34,v1,v2] .nil .nil) (.node [v35,v7,v8,v1,v2] .nil .nil)) (.node [v36,v7,v8,v1,v2] (.node [v37,v38,v7,v8,v1] .nil .nil) .nil))) (.node [v39,v4,v8,v1,v2] (.node [v40,v7,v8,v1,v11] (.node [v41,v7,v42,v1,v11] (.node [v43,v7,v8,v1,v2] .nil .nil) (.node [v44,v45,v7,v8,v11] .nil .nil)) (.node [v46,v7,v1,v2,v11] (.node [v9,v8,v2,v11,v47] .nil .nil) .nil)) (.node [v48,v0,v1,v2,v11] (.node [v49,v7,v1,v2,v11] (.node [v50,v7,v2,v11,v51] .nil .nil) (.node [v48,v4,v8,v1,v2] .nil .nil)) (.node [v52,v7,v8,v2,v11] (.node [v53,v7,v8,v2,v11] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4ll : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4ll = true := by decide +kernel
def tree_e8a8a888_4lr : BinaryTree (List W) := (.node [v54,v7,v1,v2,v11] (.node [v4,v0,v1,v2,v11] (.node [v4,v0,v7,v1,v2] (.node [v55,v0,v1,v2,v11] (.node [v55,v4,v8,v1,v2] .nil .nil) (.node [v56,v7,v8,v1,v2] .nil .nil)) (.node [v4,v0,v1,v2] (.node [v4,v0,v8,v1,v2] .nil .nil) .nil)) (.node [v4,v8,v1,v2,v47] (.node [v4,v8,v57,v1,v2] (.node [v4,v7,v8,v1,v2] .nil .nil) (.node [v4,v8,v1,v2,v58] .nil .nil)) (.node [v59,v7,v8,v1,v2] (.node [v15,v7,v8,v1,v2] .nil .nil) .nil))) (.node [v60,v7,v1,v2,v11] (.node [v0,v57,v1,v2,v11] (.node [v0,v61,v1,v2,v11] (.node [v0,v7,v1,v2,v11] .nil .nil) (.node [v0,v34,v1,v2,v11] .nil .nil)) (.node [v13,v7,v1,v2,v11] (.node [v0,v1,v2,v11,v47] .nil .nil) .nil)) (.node [v62,v8,v1,v2,v11] (.node [v63,v8,v1,v2,v11] (.node [v64,v8,v1,v2,v11] .nil .nil) .nil) (.node [v65,v8,v1,v2,v11] (.node [v16,v8,v1,v2,v11] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4lr : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4lr = true := by decide +kernel
def tree_e8a8a888_4l : BinaryTree (List W) := .node [v66,v7,v8,v2,v11] tree_e8a8a888_4ll tree_e8a8a888_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4l : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4l = true := by
  change (_ && everyKey _ tree_e8a8a888_4ll && everyKey _ tree_e8a8a888_4lr) = true
  rw [ok_tree_e8a8a888_4ll, ok_tree_e8a8a888_4lr]
  decide +kernel
def tree_e8a8a888_4rl : BinaryTree (List W) := (.node [v7,v8,v26,v11,v67] (.node [v7,v68,v1,v2,v11] (.node [v7,v17,v1,v2,v69] (.node [v7,v70,v1,v2,v11] (.node [v25,v8,v1,v2,v11] .nil .nil) (.node [v7,v71,v1,v11,v72] .nil .nil)) (.node [v7,v14,v8,v1,v2] (.node [v7,v73,v8,v1,v2] .nil .nil) .nil)) (.node [v7,v74,v1,v2,v11] (.node [v7,v5,v1,v2,v11] (.node [v7,v12,v1,v2,v11] .nil .nil) (.node [v7,v75,v1,v2,v11] .nil .nil)) (.node [v7,v8,v76,v1,v2] (.node [v7,v77,v1,v2,v11] .nil .nil) .nil))) (.node [v7,v8,v1,v78,v79] (.node [v7,v8,v80,v2,v11] (.node [v7,v8,v81,v1,v2] (.node [v7,v8,v82,v2,v83] .nil .nil) (.node [v7,v8,v84,v2,v11] .nil .nil)) (.node [v7,v8,v1,v85,v2] (.node [v7,v8,v86,v2,v11] .nil .nil) .nil)) (.node [v7,v8,v1,v2,v3] (.node [v7,v8,v1,v2,v87] (.node [v7,v8,v1,v10,v11] .nil .nil) .nil) (.node [v7,v8,v1,v2,v88] (.node [v7,v8,v1,v2,v89] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4rl : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4rl = true := by decide +kernel
def tree_e8a8a888_4rr : BinaryTree (List W) := (.node [v7,v90,v1,v2,v11] (.node [v7,v8,v1,v2,v91] (.node [v7,v8,v1,v2,v92] (.node [v7,v8,v1,v2,v93] (.node [v7,v8,v1,v2,v94] .nil .nil) (.node [v7,v8,v1,v2,v95] .nil .nil)) (.node [v7,v8,v1,v2,v96] (.node [v7,v8,v1,v2,v97] .nil .nil) .nil)) (.node [v7,v98,v1,v2,v11] (.node [v7,v99,v1,v2,v11] (.node [v7,v100,v1,v2,v11] .nil .nil) (.node [v7,v101,v1,v2,v11] .nil .nil)) (.node [v7,v102,v1,v2,v11] (.node [v7,v103,v1,v2,v11] .nil .nil) .nil))) (.node [v8,v104,v1,v2,v11] (.node [v7,v1,v2,v11,v105] (.node [v7,v1,v2,v11,v106] (.node [v7,v1,v2,v11,v107] .nil .nil) (.node [v7,v1,v2,v11,v108] .nil .nil)) (.node [v109,v8,v1,v2,v11] (.node [v7,v1,v2,v11,v110] .nil .nil) .nil)) (.node [v8,v111,v1,v2,v11] (.node [v8,v112,v1,v2,v11] (.node [v8,v113,v1,v2,v11] .nil .nil) .nil) (.node [v8,v1,v2,v11,v114] (.node [v8,v1,v115,v2,v11] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4rr : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4rr = true := by decide +kernel
def tree_e8a8a888_4r : BinaryTree (List W) := .node [v7,v8,v1,v2,v11] tree_e8a8a888_4rl tree_e8a8a888_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4r : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4r = true := by
  change (_ && everyKey _ tree_e8a8a888_4rl && everyKey _ tree_e8a8a888_4rr) = true
  rw [ok_tree_e8a8a888_4rl, ok_tree_e8a8a888_4rr]
  decide +kernel
def tree_e8a8a888_4 : BinaryTree (List W) := .node [v116,v8,v1,v2,v11] tree_e8a8a888_4l tree_e8a8a888_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4 : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4 = true := by
  change (_ && everyKey _ tree_e8a8a888_4l && everyKey _ tree_e8a8a888_4r) = true
  rw [ok_tree_e8a8a888_4l, ok_tree_e8a8a888_4r]
  decide +kernel
theorem closed_e8a8a888_4 : Closed 4 tree_e8a8a888_4 := closed_next 3 (by decide) tree_e8a8a888_4 tree_e8a8a888_3 closed_e8a8a888_3 ok_tree_e8a8a888_4
def tree_e8a8a888_5l : BinaryTree (List W) := (.node [v9,v7,v8,v1,v2,v11] (.node [v32,v7,v8,v1,v2,v11] (.node [v117,v7,v8,v1,v2,v11] (.node [v30,v7,v1,v2,v11] (.node [v30,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v29,v7,v8,v1,v2,v11] (.node [v29,v7,v8,v1,v2] .nil .nil) .nil)) (.node [v44,v7,v8,v1,v2,v11] (.node [v41,v7,v8,v1,v2,v11] (.node [v37,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v38,v7,v8,v1,v2,v11] (.node [v118,v7,v8,v1,v2,v11] .nil .nil) .nil))) (.node [v45,v7,v8,v1,v2,v11] (.node [v119,v7,v8,v1,v2,v11] (.node [v50,v7,v8,v1,v2,v11] (.node [v39,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v48,v7,v8,v1,v2,v11] (.node [v120,v7,v8,v1,v2,v11] .nil .nil) .nil)) (.node [v4,v7,v8,v1,v2,v11] (.node [v4,v7,v8,v1,v2] (.node [v55,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v0,v7,v8,v1,v2,v11] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_5l : everyKey (rowOK 4 tree_e8a8a888_4) tree_e8a8a888_5l = true := by decide +kernel
def tree_e8a8a888_5r : BinaryTree (List W) := (.node [v7,v8,v82,v1,v2,v11] (.node [v7,v8,v42,v1,v2,v11] (.node [v7,v8,v61,v1,v2,v11] (.node [v7,v17,v8,v1,v2,v11] (.node [v7,v71,v8,v1,v2,v11] .nil .nil) .nil) (.node [v7,v8,v121,v1,v2,v11] (.node [v7,v8,v33,v1,v2,v11] .nil .nil) .nil)) (.node [v7,v8,v57,v1,v2,v11] (.node [v7,v8,v122,v1,v2,v11] (.node [v7,v8,v34,v1,v2,v11] .nil .nil) .nil) (.node [v7,v8,v26,v1,v2,v11] .nil .nil))) (.node [v7,v8,v1,v2,v11,v72] (.node [v7,v8,v1,v2,v11,v58] (.node [v7,v8,v1,v2,v11,v83] (.node [v7,v8,v1,v78,v2,v11] .nil .nil) .nil) (.node [v7,v8,v1,v2,v11,v51] (.node [v7,v8,v1,v2,v11,v69] .nil .nil) .nil)) (.node [v7,v8,v1,v2,v11,v123] (.node [v7,v8,v1,v2,v11,v67] (.node [v7,v8,v1,v2,v11,v47] .nil .nil) .nil) (.node [v7,v8,v1,v2,v11,v79] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_5r : everyKey (rowOK 4 tree_e8a8a888_4) tree_e8a8a888_5r = true := by decide +kernel
def tree_e8a8a888_5 : BinaryTree (List W) := .node [v0,v7,v1,v2,v11] tree_e8a8a888_5l tree_e8a8a888_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_5 : everyKey (rowOK 4 tree_e8a8a888_4) tree_e8a8a888_5 = true := by
  change (_ && everyKey _ tree_e8a8a888_5l && everyKey _ tree_e8a8a888_5r) = true
  rw [ok_tree_e8a8a888_5l, ok_tree_e8a8a888_5r]
  decide +kernel
theorem closed_e8a8a888_5 : Closed 5 tree_e8a8a888_5 := closed_next 4 (by decide) tree_e8a8a888_5 tree_e8a8a888_4 closed_e8a8a888_4 ok_tree_e8a8a888_5
def tree_e8a8a888_6 : BinaryTree (List W) := (.node [v7,v8,v1,v2,v11] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_6 : everyKey (rowOK 5 tree_e8a8a888_5) tree_e8a8a888_6 = true := by decide +kernel
theorem closed_e8a8a888_6 : Closed 6 tree_e8a8a888_6 := closed_next 5 (by decide) tree_e8a8a888_6 tree_e8a8a888_5 closed_e8a8a888_5 ok_tree_e8a8a888_6
theorem lower_e8a8a888 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 6 ins_e8a8a888.toFinset := @no_build 6 tree_e8a8a888_6 ins_e8a8a888 nd_e8a8a888 (by decide) closed_e8a8a888_6 (by decide +kernel)
def gates_e8a8a888 : List Gate := [⟨.and, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [5, 11]⟩]
theorem upper_e8a8a888 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_e8a8a888, 12, by simp [gates_e8a8a888], rfl, by decide +kernel⟩

end PEqualNP.Outside.L_meta_8639

open PEqualNP.Outside.L_meta_8639 in
theorem PEqualNP.Outside.L_meta_8639 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, fan, size, computes⟩ := h
  obtain ⟨gates, out, mono, bound, eval⟩ :=
    replace 0xe8a8a888 8 ins_e8a8a888 nd_e8a8a888 rows_e8a8a888 rfl
      lower_e8a8a888 upper_e8a8a888 C.gates C.output fan computes
  exact ⟨⟨gates, out⟩, mono, bound.trans size, eval⟩
