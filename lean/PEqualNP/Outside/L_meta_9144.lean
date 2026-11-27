import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9144

-- The signed circuit search uses the live-wire compression from L-meta-1423.
-- A NOT gate costs one gate in the given circuit and zero in the signed search.
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

-- The upper and lower halves represent opposite target labels on 44 pairs of assignments.
abbrev W := BitVec 88
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 44 := ((x >>> 44) ^^^ x).setWidth 44
def cuts (ws : List W) : BitVec 44 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 44) ++ (0 : BitVec 44)
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

def differs (i : Fin 44) (w : W) : Prop :=
  w.getLsbD (44+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 44) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 44+i.val < 88 := by omega
  have hi' : i.val < 88 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 44) :
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
  change (cuts ws)[j] = (BitVec.allOnes 44)[j]
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
  · change reachable av (BitVec.allOnes 88 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 88)
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

private def bit (k : Fin 88) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 88) :
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

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 88) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#88)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
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
    (row : ∀ j : Fin 88, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 88) :
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

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 88, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
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

def signal0 : W := (0x181409 : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal1 : W := (0xb05802 : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal2 : W := (0xb85c0b : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal3 : W := (0x10a84f9 : BitVec 44) ++ (0x78 : BitVec 44)
def signal4 : W := (0x1badcfb : BitVec 44) ++ (0x783c7f : BitVec 44)
def signal5 : W := (0x2151f90 : BitVec 44) ++ (0x3f80 : BitVec 44)
def signal6 : W := (0x2bd5f9b : BitVec 44) ++ (0x783f87 : BitVec 44)
def signal7 : W := (0x3a1c922 : BitVec 44) ++ (0x381c000 : BitVec 44)
def signal8 : W := (0x3b9dd2b : BitVec 44) ++ (0x3f9fc07 : BitVec 44)
def signal9 : W := (0x3be1240 : BitVec 44) ++ (0x3fe0000 : BitVec 44)
def signal10 : W := (0x3be5e4b : BitVec 44) ++ (0x3fe3c07 : BitVec 44)
def signal11 : W := (0x8080409 : BitVec 44) ++ (0x0 : BitVec 44)
def signal12 : W := (0x8b85c0b : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal13 : W := (0x80103c00 : BitVec 44) ++ (0x3c00 : BitVec 44)
def signal14 : W := (0x110000490 : BitVec 44) ++ (0x0 : BitVec 44)
def signal15 : W := (0x88c006c0f : BitVec 44) ++ (0x3c07 : BitVec 44)
def signal16 : W := (0x11380084b9 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal17 : W := (0x2390012d90 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal18 : W := (0x33b801adb9 : BitVec 44) ++ (0x7f8003ff8 : BitVec 44)
def signal19 : W := (0x3a2001c922 : BitVec 44) ++ (0x380001c000 : BitVec 44)
def signal20 : W := (0x3a23a1c922 : BitVec 44) ++ (0x380381c000 : BitVec 44)
def signal21 : W := (0x3bbc002004 : BitVec 44) ++ (0x3ffc000000 : BitVec 44)
def signal22 : W := (0x3bbfbe3244 : BitVec 44) ++ (0x3ffffe0000 : BitVec 44)
def signal23 : W := (0x408c402004 : BitVec 44) ++ (0x0 : BitVec 44)
def signal24 : W := (0x408c58340d : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal25 : W := (0x81580a04d9 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal26 : W := (0x10590143690 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal27 : W := (0x14484402004 : BitVec 44) ++ (0x1c784000000 : BitVec 44)
def signal28 : W := (0x184401e1240 : BitVec 44) ++ (0x1c0007e0000 : BitVec 44)
def signal29 : W := (0x1c4405e1240 : BitVec 44) ++ (0x1c0007e0000 : BitVec 44)
def signal30 : W := (0x1c443fe1240 : BitVec 44) ++ (0x1c003fe0000 : BitVec 44)
def signal31 : W := (0x1c5dc402004 : BitVec 44) ++ (0x1c7fc000000 : BitVec 44)
def signal32 : W := (0x1c5dc4a24dd : BitVec 44) ++ (0x1c7fc000078 : BitVec 44)
def signal33 : W := (0x1c5dfe1e926 : BitVec 44) ++ (0x1c7ff81c000 : BitVec 44)
def signal34 : W := (0x1fe605fdb62 : BitVec 44) ++ (0x1f8007fc000 : BitVec 44)
def signal35 : W := (0x1fffc402004 : BitVec 44) ++ (0x1fffc000000 : BitVec 44)
def signal36 : W := (0x20800a04802 : BitVec 44) ++ (0x0 : BitVec 44)
def signal37 : W := (0x20800b85c0b : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal38 : W := (0x23a20a1c922 : BitVec 44) ++ (0x380001c000 : BitVec 44)
def signal39 : W := (0x24000f81000 : BitVec 44) ++ (0x780000 : BitVec 44)
def signal40 : W := (0x2480ce8400f : BitVec 44) ++ (0x780007 : BitVec 44)
def signal41 : W := (0x24884402004 : BitVec 44) ++ (0x0 : BitVec 44)
def signal42 : W := (0x24884f07806 : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal43 : W := (0x2488c402004 : BitVec 44) ++ (0x0 : BitVec 44)
def signal44 : W := (0x2488c48240d : BitVec 44) ++ (0x0 : BitVec 44)
def signal45 : W := (0x2488ce06806 : BitVec 44) ++ (0x0 : BitVec 44)
def signal46 : W := (0x2488ce8600f : BitVec 44) ++ (0x780007 : BitVec 44)
def signal47 : W := (0x2488ce86c0f : BitVec 44) ++ (0x0 : BitVec 44)
def signal48 : W := (0x2488ce86c0f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal49 : W := (0x2488cf07c0f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal50 : W := (0x2488cf8740f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal51 : W := (0x2488cf8780f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal52 : W := (0x2488cf87c0f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal53 : W := (0x2488efd7f9f : BitVec 44) ++ (0x783f87 : BitVec 44)
def signal54 : W := (0x2499cf87c9f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal55 : W := (0x27bbc402004 : BitVec 44) ++ (0x3ffc000000 : BitVec 44)
def signal56 : W := (0x3c440fe1240 : BitVec 44) ++ (0x1c0007e0000 : BitVec 44)
def signal57 : W := (0x3cddc402004 : BitVec 44) ++ (0x1c7fc000000 : BitVec 44)
def signal58 : W := (0x41021008020 : BitVec 44) ++ (0x0 : BitVec 44)
def signal59 : W := (0x480410a0040 : BitVec 44) ++ (0x0 : BitVec 44)
def signal60 : W := (0x490690a8069 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal61 : W := (0x491710280f0 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal62 : W := (0x491710a84f9 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal63 : W := (0x49178000000 : BitVec 44) ++ (0x78000000 : BitVec 44)
def signal64 : W := (0x491790a84f9 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal65 : W := (0x49179badcfb : BitVec 44) ++ (0x78783c7f : BitVec 44)
def signal66 : W := (0x4d1fd4aa4fd : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal67 : W := (0x5c4415e1240 : BitVec 44) ++ (0x1c0007e0000 : BitVec 44)
def signal68 : W := (0x5d5fc402004 : BitVec 44) ++ (0x1c7fc000000 : BitVec 44)
def signal69 : W := (0x5d5fd4aa4fd : BitVec 44) ++ (0x1c7fc000078 : BitVec 44)
def signal70 : W := (0x61821a0c022 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal71 : W := (0x63a21a1c922 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal72 : W := (0x658adf8fc2f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal73 : W := (0x69979aaccfb : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal74 : W := (0x6c041ea0040 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal75 : W := (0x6c8cdfa7c4f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal76 : W := (0x6d86c400004 : BitVec 44) ++ (0xff87c000000 : BitVec 44)
def signal77 : W := (0x6d86e551f94 : BitVec 44) ++ (0xff87c003f80 : BitVec 44)
def signal78 : W := (0x6d8ec402004 : BitVec 44) ++ (0xff87c000000 : BitVec 44)
def signal79 : W := (0x6d9f5f2f8f6 : BitVec 44) ++ (0x78783c7f : BitVec 44)
def signal80 : W := (0x6d9fc402004 : BitVec 44) ++ (0x78000000 : BitVec 44)
def signal81 : W := (0x6d9fd4aa4fd : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal82 : W := (0x6d9fdeaecff : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal83 : W := (0x6d9fdfafcff : BitVec 44) ++ (0x78783c7f : BitVec 44)
def signal84 : W := (0x6e3d1eb2dd0 : BitVec 44) ++ (0xfc783fe3f80 : BitVec 44)
def signal85 : W := (0x6fbfc402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal86 : W := (0x71db1b4f6b2 : BitVec 44) ++ (0xe3f8381ff80 : BitVec 44)
def signal87 : W := (0x7c441fe1240 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal88 : W := (0x7ddfc402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal89 : W := (0x82202010900 : BitVec 44) ++ (0x0 : BitVec 44)
def signal90 : W := (0x90402141200 : BitVec 44) ++ (0x0 : BitVec 44)
def signal91 : W := (0x92682153b00 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal92 : W := (0x92712050390 : BitVec 44) ++ (0x780000380 : BitVec 44)
def signal93 : W := (0x92712151390 : BitVec 44) ++ (0x780000380 : BitVec 44)
def signal94 : W := (0x92712151f90 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal95 : W := (0x92790002000 : BitVec 44) ++ (0x780000000 : BitVec 44)
def signal96 : W := (0x92792153790 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal97 : W := (0x92792153b90 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal98 : W := (0x92792153f90 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal99 : W := (0x9279a1d3f99 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal100 : W := (0x92f9e157f9f : BitVec 44) ++ (0x780003f87 : BitVec 44)
def signal101 : W := (0x9c4425e1240 : BitVec 44) ++ (0x1c0007e0000 : BitVec 44)
def signal102 : W := (0x9e7dc402004 : BitVec 44) ++ (0x1c7fc000000 : BitVec 44)
def signal103 : W := (0xa2a02a14902 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal104 : W := (0xa3a22a1c922 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal105 : W := (0xa6a8ef97d0f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal106 : W := (0xaab5aab4ddb : BitVec 44) ++ (0xe387b81c078 : BitVec 44)
def signal107 : W := (0xb2f92b57f92 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal108 : W := (0xb4402f41200 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal109 : W := (0xb4c8efc7e0f : BitVec 44) ++ (0x783c07 : BitVec 44)
def signal110 : W := (0xb553af496b9 : BitVec 44) ++ (0xfc07bfe0078 : BitVec 44)
def signal111 : W := (0xb6e84402004 : BitVec 44) ++ (0xfff84000000 : BitVec 44)
def signal112 : W := (0xb6e854aa4fd : BitVec 44) ++ (0xfff84000078 : BitVec 44)
def signal113 : W := (0xb6e86e16906 : BitVec 44) ++ (0xfff8781c000 : BitVec 44)
def signal114 : W := (0xb6e8c402004 : BitVec 44) ++ (0xfff84000000 : BitVec 44)
def signal115 : W := (0xb6f1eed439f : BitVec 44) ++ (0x780780387 : BitVec 44)
def signal116 : W := (0xb6f94402004 : BitVec 44) ++ (0xfff84000000 : BitVec 44)
def signal117 : W := (0xb6f9c402004 : BitVec 44) ++ (0x780000000 : BitVec 44)
def signal118 : W := (0xb6f9e553f94 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal119 : W := (0xb6f9efd7f9f : BitVec 44) ++ (0x780783f87 : BitVec 44)
def signal120 : W := (0xb7fbc402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal121 : W := (0xbc442fe1240 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal122 : W := (0xbefdc402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal123 : W := (0xc3223018120 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal124 : W := (0xc3223a1c922 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal125 : W := (0xc72af59b52d : BitVec 44) ++ (0xe3803f9fc07 : BitVec 44)
def signal126 : W := (0xcb37b0b8df9 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal127 : W := (0xd37b315bfb0 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal128 : W := (0xd8443060240 : BitVec 44) ++ (0xfc003860000 : BitVec 44)
def signal129 : W := (0xd8443161240 : BitVec 44) ++ (0xfc003860000 : BitVec 44)
def signal130 : W := (0xd84431e1240 : BitVec 44) ++ (0x0 : BitVec 44)
def signal131 : W := (0xd8443be1240 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal132 : W := (0xd8ccf066e4f : BitVec 44) ++ (0xfc003863c07 : BitVec 44)
def signal133 : W := (0xd957b1e96f9 : BitVec 44) ++ (0x78000078 : BitVec 44)
def signal134 : W := (0xda7d31f3fd0 : BitVec 44) ++ (0x780003f80 : BitVec 44)
def signal135 : W := (0xdb6eb1fbb69 : BitVec 44) ++ (0x7f8003ff8 : BitVec 44)
def signal136 : W := (0xdb770000000 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal137 : W := (0xdb770b85c0b : BitVec 44) ++ (0xffffc783c07 : BitVec 44)
def signal138 : W := (0xdb7fb1fbff9 : BitVec 44) ++ (0x7f8003ff8 : BitVec 44)
def signal139 : W := (0xdc4435e1240 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal140 : W := (0xdf7fc402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal141 : W := (0xe0003a00000 : BitVec 44) ++ (0xe0003800000 : BitVec 44)
def signal142 : W := (0xe3a20000000 : BitVec 44) ++ (0xe3800000000 : BitVec 44)
def signal143 : W := (0xe3a23a1c922 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal144 : W := (0xe3a23b9dd2b : BitVec 44) ++ (0xe3803f9fc07 : BitVec 44)
def signal145 : W := (0xe3a2ba9cd2b : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal146 : W := (0xe3b33a1cdb2 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal147 : W := (0xe7aa7e1e926 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal148 : W := (0xe7aac402004 : BitVec 44) ++ (0xe3800000000 : BitVec 44)
def signal149 : W := (0xe7aafe1e926 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal150 : W := (0xe7aafe9ed2f : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal151 : W := (0xe7aaff9fd2f : BitVec 44) ++ (0xe3803f9fc07 : BitVec 44)
def signal152 : W := (0xeba63abc962 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal153 : W := (0xebb7babcdfb : BitVec 44) ++ (0xe387b81c078 : BitVec 44)
def signal154 : W := (0xf3e23b5db22 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal155 : W := (0xf3fb3b5ffb2 : BitVec 44) ++ (0xe3f8381ff80 : BitVec 44)
def signal156 : W := (0xf7ea4402004 : BitVec 44) ++ (0xfff84000000 : BitVec 44)
def signal157 : W := (0xf7ea7e1e926 : BitVec 44) ++ (0xfff8781c000 : BitVec 44)
def signal158 : W := (0xfbe63a7cb62 : BitVec 44) ++ (0xff80387c000 : BitVec 44)
def signal159 : W := (0xfbe63b7db62 : BitVec 44) ++ (0xff80387c000 : BitVec 44)
def signal160 : W := (0xfbe63bfdb62 : BitVec 44) ++ (0xe380381c000 : BitVec 44)
def signal161 : W := (0xfc440400000 : BitVec 44) ++ (0xfc000000000 : BitVec 44)
def signal162 : W := (0xfc4405e1240 : BitVec 44) ++ (0xfc0007e0000 : BitVec 44)
def signal163 : W := (0xfc443f61240 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal164 : W := (0xfc443fe1240 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal165 : W := (0xfc443ffdb62 : BitVec 44) ++ (0xfc003ffc000 : BitVec 44)
def signal166 : W := (0xfc44bfe1649 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal167 : W := (0xfc553fe16d0 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal168 : W := (0xfc5dc402004 : BitVec 44) ++ (0xfc7fc000000 : BitVec 44)
def signal169 : W := (0xfcc43fe5a42 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal170 : W := (0xfcc4ffe524f : BitVec 44) ++ (0xfc003fe0007 : BitVec 44)
def signal171 : W := (0xfcccc402004 : BitVec 44) ++ (0xfc000000000 : BitVec 44)
def signal172 : W := (0xfcccffe3244 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal173 : W := (0xfcccffe7e4f : BitVec 44) ++ (0xfc003fe3c07 : BitVec 44)
def signal174 : W := (0xfd463fe9260 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal175 : W := (0xfd57bfe96f9 : BitVec 44) ++ (0xfc07bfe0078 : BitVec 44)
def signal176 : W := (0xfdc63fed262 : BitVec 44) ++ (0xff803ffc000 : BitVec 44)
def signal177 : W := (0xfe643ff1b40 : BitVec 44) ++ (0xfc003fe0000 : BitVec 44)
def signal178 : W := (0xfe7d3ff3fd0 : BitVec 44) ++ (0xfc783fe3f80 : BitVec 44)
def signal179 : W := (0xfee43ff5b42 : BitVec 44) ++ (0xff803ffc000 : BitVec 44)
def signal180 : W := (0xfeec4402004 : BitVec 44) ++ (0xfff84000000 : BitVec 44)
def signal181 : W := (0xff663ff9360 : BitVec 44) ++ (0xff803ffc000 : BitVec 44)
def signal182 : W := (0xffe63e1c922 : BitVec 44) ++ (0xff80381c000 : BitVec 44)
def signal183 : W := (0xffe63fe1240 : BitVec 44) ++ (0xff803fe0000 : BitVec 44)
def signal184 : W := (0xffe63ffdb62 : BitVec 44) ++ (0xff803ffc000 : BitVec 44)
def signal185 : W := (0xffeec402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal186 : W := (0xffeefe1e926 : BitVec 44) ++ (0xff80381c000 : BitVec 44)
def signal187 : W := (0xffeeffffb66 : BitVec 44) ++ (0xff803ffc000 : BitVec 44)
def signal188 : W := (0xffff4402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal189 : W := (0xffffc402004 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal190 : W := (0xffffc402494 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal191 : W := (0xffffc40a4bd : BitVec 44) ++ (0xffffc000078 : BitVec 44)
def signal192 : W := (0xffffc41e926 : BitVec 44) ++ (0xffffc01c000 : BitVec 44)
def signal193 : W := (0xffffc48240d : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal194 : W := (0xffffc4a24dd : BitVec 44) ++ (0xffffc000078 : BitVec 44)
def signal195 : W := (0xffffce06806 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal196 : W := (0xffffcf87c0f : BitVec 44) ++ (0xffffc783c07 : BitVec 44)
def signal197 : W := (0xffffd40a024 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal198 : W := (0xffffd42a0f4 : BitVec 44) ++ (0xffffc000078 : BitVec 44)
def signal199 : W := (0xffffd4a2044 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal200 : W := (0xffffd4aa06d : BitVec 44) ++ (0xffffc000078 : BitVec 44)
def signal201 : W := (0xffffd4aa4fd : BitVec 44) ++ (0xffffc000078 : BitVec 44)
def signal202 : W := (0xffffde0e026 : BitVec 44) ++ (0xfffff81c000 : BitVec 44)
def signal203 : W := (0xffffe412904 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal204 : W := (0xffffe452394 : BitVec 44) ++ (0xffffc000380 : BitVec 44)
def signal205 : W := (0xffffe543204 : BitVec 44) ++ (0xffffc000000 : BitVec 44)
def signal206 : W := (0xffffe553f94 : BitVec 44) ++ (0xffffc003f80 : BitVec 44)
def signal207 : W := (0xffffee16906 : BitVec 44) ++ (0xfffff81c000 : BitVec 44)
def signal208 : W := (0xfffff41a124 : BitVec 44) ++ (0xfffff81c000 : BitVec 44)
def signal209 : W := (0xfffff462244 : BitVec 44) ++ (0xfffff860000 : BitVec 44)
def signal210 : W := (0xfffffe02004 : BitVec 44) ++ (0xfffff800000 : BitVec 44)
def signal211 : W := (0xfffffe1e926 : BitVec 44) ++ (0xfffff81c000 : BitVec 44)
def signal212 : W := (0xfffffebedff : BitVec 44) ++ (0xfffff81c078 : BitVec 44)
def signal213 : W := (0xffffffe3244 : BitVec 44) ++ (0xffffffe0000 : BitVec 44)
def ins : List W := [signal52,signal64,signal98,signal143,signal164,signal189]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok0 : everyKey (fun q => !doneTest q) layer0=true := by decide +kernel
theorem closed0 : Closed 0 layer0 := closed_nil _ ok0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok1 : everyKey (rowOK 0 layer0) layer1=true := by decide +kernel
theorem closed1 : Closed 1 layer1 := closed_next 0 (by decide) _ _ closed0 ok1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok2 : everyKey (rowOK 1 layer1) layer2=true := by decide +kernel
theorem closed2 : Closed 2 layer2 := closed_next 1 (by decide) _ _ closed1 ok2
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer3 : BinaryTree (List W) := (.node [signal82,signal98,signal151,signal164] (.node [signal52,signal82,signal98,signal184] (.node [signal47,signal64,signal98,signal184] .nil .nil) .nil) (.node [signal83,signal98,signal150,signal164] .nil .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok3 : everyKey (rowOK 2 layer2) layer3=true := by decide +kernel
theorem closed3 : Closed 3 layer3 := closed_next 2 (by decide) _ _ closed2 ok3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer4 : BinaryTree (List W) := (.node [signal52,signal64,signal98,signal184,signal210] (.node [signal52,signal64,signal98,signal113,signal184] (.node [signal44,signal83,signal98,signal143,signal164] (.node [signal29,signal52,signal81,signal98,signal143] (.node [signal28,signal52,signal64,signal98,signal149] (.node [signal22,signal52,signal64,signal98,signal143] (.node [signal0,signal52,signal64,signal98,signal184] .nil .nil) .nil) (.node [signal29,signal52,signal64,signal98,signal149] .nil .nil)) (.node [signal40,signal64,signal98,signal149,signal164] (.node [signal34,signal52,signal64,signal98,signal189] (.node [signal33,signal52,signal64,signal98,signal164] .nil .nil) .nil) (.node [signal40,signal81,signal98,signal143,signal164] .nil .nil))) (.node [signal52,signal64,signal77,signal143,signal164] (.node [signal47,signal64,signal98,signal143,signal164] (.node [signal45,signal64,signal98,signal151,signal164] (.node [signal45,signal52,signal64,signal98,signal184] .nil .nil) .nil) (.node [signal52,signal62,signal98,signal149,signal164] .nil .nil)) (.node [signal52,signal64,signal86,signal164,signal189] (.node [signal52,signal64,signal84,signal143,signal189] .nil .nil) (.node [signal52,signal64,signal94,signal149,signal164] .nil .nil)))) (.node [signal52,signal64,signal98,signal159,signal189] (.node [signal52,signal64,signal98,signal149,signal184] (.node [signal52,signal64,signal98,signal149,signal164] (.node [signal52,signal64,signal98,signal147,signal164] (.node [signal52,signal64,signal98,signal131,signal149] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal149,signal172] .nil .nil)) (.node [signal52,signal64,signal98,signal150,signal164] (.node [signal52,signal64,signal98,signal149,signal187] .nil .nil) (.node [signal52,signal64,signal98,signal157,signal184] .nil .nil))) (.node [signal52,signal64,signal98,signal183,signal211] (.node [signal52,signal64,signal98,signal181,signal211] (.node [signal52,signal64,signal98,signal164,signal186] (.node [signal52,signal64,signal98,signal160,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal182,signal213] .nil .nil)) (.node [signal52,signal64,signal98,signal184,signal202] (.node [signal52,signal64,signal98,signal184,signal195] .nil .nil) (.node [signal52,signal64,signal98,signal184,signal207] .nil .nil))))) (.node [signal52,signal98,signal112,signal143,signal164] (.node [signal52,signal81,signal98,signal131,signal143] (.node [signal52,signal64,signal118,signal149,signal164] (.node [signal52,signal64,signal107,signal184,signal189] (.node [signal52,signal64,signal98,signal184,signal212] (.node [signal52,signal64,signal98,signal184,signal211] .nil .nil) .nil) (.node [signal52,signal64,signal118,signal143,signal172] .nil .nil)) (.node [signal52,signal81,signal94,signal143,signal164] (.node [signal52,signal73,signal98,signal184,signal189] (.node [signal52,signal66,signal98,signal143,signal164] .nil .nil) .nil) (.node [signal52,signal81,signal98,signal124,signal164] .nil .nil))) (.node [signal52,signal81,signal118,signal143,signal164] (.node [signal52,signal81,signal98,signal143,signal184] (.node [signal52,signal81,signal98,signal143,signal172] (.node [signal52,signal81,signal98,signal143,signal164] .nil .nil) .nil) (.node [signal52,signal81,signal98,signal149,signal164] .nil .nil)) (.node [signal52,signal98,signal106,signal164,signal189] (.node [signal52,signal82,signal98,signal143,signal164] .nil .nil) (.node [signal52,signal98,signal110,signal143,signal189] .nil .nil)))) (.node [signal64,signal98,signal125,signal164,signal189] (.node [signal52,signal135,signal143,signal164,signal189] (.node [signal52,signal133,signal143,signal178,signal189] (.node [signal52,signal127,signal153,signal164,signal189] (.node [signal52,signal126,signal155,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal134,signal143,signal175,signal189] .nil .nil)) (.node [signal52,signal138,signal146,signal164,signal189] (.node [signal52,signal138,signal143,signal167,signal189] .nil .nil) (.node [signal64,signal98,signal119,signal149,signal164] .nil .nil))) (.node [signal73,signal98,signal151,signal164,signal189] (.node [signal64,signal115,signal143,signal164,signal189] (.node [signal64,signal98,signal137,signal143,signal164] (.node [signal64,signal98,signal132,signal143,signal189] .nil .nil) .nil) (.node [signal72,signal98,signal153,signal164,signal189] .nil .nil)) (.node [signal81,signal98,signal119,signal143,signal164] (.node [signal79,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal83,signal98,signal145,signal164,signal189] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal52,signal64,signal98,signal102,signal143,signal164] (.node [signal40,signal43,signal64,signal98,signal143,signal164] (.node [signal19,signal52,signal64,signal98,signal164,signal211] (.node [signal7,signal52,signal64,signal98,signal184,signal189] (.node [signal2,signal64,signal98,signal136,signal143,signal164] (.node [signal2,signal43,signal64,signal98,signal143,signal164] (.node [signal1,signal52,signal64,signal98,signal143,signal164] (.node [signal0,signal52,signal64,signal98,signal143,signal164] .nil .nil) (.node [signal2,signal29,signal52,signal64,signal98,signal143] .nil .nil)) (.node [signal2,signal52,signal64,signal98,signal143,signal184] (.node [signal2,signal52,signal64,signal98,signal143,signal164] .nil .nil) .nil)) (.node [signal5,signal52,signal64,signal76,signal143,signal164] (.node [signal4,signal52,signal64,signal98,signal143,signal164] (.node [signal3,signal52,signal98,signal111,signal143,signal164] .nil .nil) .nil) (.node [signal7,signal31,signal52,signal64,signal98,signal164] (.node [signal6,signal52,signal64,signal98,signal143,signal164] .nil .nil) .nil))) (.node [signal14,signal52,signal138,signal143,signal164,signal189] (.node [signal11,signal83,signal98,signal143,signal164,signal189] (.node [signal9,signal21,signal52,signal64,signal98,signal143] (.node [signal8,signal52,signal64,signal98,signal143,signal164] .nil .nil) (.node [signal10,signal52,signal64,signal98,signal143,signal164] .nil .nil)) (.node [signal13,signal64,signal119,signal143,signal164,signal189] (.node [signal12,signal52,signal64,signal98,signal143,signal164] .nil .nil) .nil)) (.node [signal17,signal52,signal64,signal74,signal143,signal189] (.node [signal16,signal52,signal98,signal108,signal143,signal189] (.node [signal15,signal64,signal98,signal128,signal143,signal189] .nil .nil) .nil) (.node [signal19,signal29,signal52,signal64,signal98,signal189] (.node [signal18,signal52,signal64,signal98,signal143,signal189] .nil .nil) .nil)))) (.node [signal29,signal52,signal64,signal98,signal143,signal211] (.node [signal27,signal52,signal64,signal98,signal143,signal164] (.node [signal24,signal64,signal98,signal123,signal164,signal189] (.node [signal23,signal52,signal64,signal98,signal143,signal164] (.node [signal20,signal52,signal64,signal98,signal164,signal189] .nil .nil) (.node [signal24,signal52,signal64,signal98,signal184,signal189] .nil .nil)) (.node [signal26,signal52,signal64,signal70,signal164,signal189] (.node [signal25,signal52,signal98,signal103,signal164,signal189] .nil .nil) .nil)) (.node [signal29,signal52,signal64,signal98,signal111,signal143] (.node [signal29,signal43,signal52,signal64,signal98,signal143] (.node [signal29,signal31,signal52,signal64,signal98,signal143] .nil .nil) .nil) (.node [signal29,signal52,signal64,signal98,signal143,signal201] (.node [signal29,signal52,signal64,signal98,signal143,signal189] .nil .nil) .nil))) (.node [signal35,signal52,signal64,signal98,signal143,signal164] (.node [signal31,signal52,signal64,signal98,signal143,signal184] (.node [signal30,signal52,signal64,signal98,signal143,signal189] (.node [signal29,signal52,signal64,signal98,signal184,signal189] .nil .nil) (.node [signal31,signal52,signal64,signal98,signal143,signal164] .nil .nil)) (.node [signal32,signal52,signal64,signal98,signal143,signal164] (.node [signal31,signal52,signal64,signal98,signal164,signal211] .nil .nil) .nil)) (.node [signal37,signal52,signal64,signal98,signal143,signal164] (.node [signal36,signal64,signal98,signal151,signal164,signal189] (.node [signal36,signal52,signal64,signal98,signal184,signal189] .nil .nil) .nil) (.node [signal39,signal64,signal98,signal143,signal173,signal189] (.node [signal38,signal52,signal64,signal98,signal164,signal189] .nil .nil) .nil))))) (.node [signal52,signal58,signal98,signal153,signal164,signal189] (.node [signal43,signal52,signal81,signal98,signal143,signal164] (.node [signal43,signal52,signal64,signal98,signal131,signal143] (.node [signal43,signal52,signal62,signal98,signal143,signal164] (.node [signal41,signal52,signal64,signal98,signal143,signal164] (.node [signal40,signal64,signal92,signal143,signal164,signal189] .nil .nil) (.node [signal42,signal61,signal98,signal143,signal164,signal189] .nil .nil)) (.node [signal43,signal52,signal64,signal98,signal124,signal164] (.node [signal43,signal52,signal64,signal94,signal143,signal164] .nil .nil) .nil)) (.node [signal43,signal52,signal64,signal98,signal143,signal184] (.node [signal43,signal52,signal64,signal98,signal143,signal172] (.node [signal43,signal52,signal64,signal98,signal143,signal164] .nil .nil) .nil) (.node [signal43,signal52,signal64,signal118,signal143,signal164] (.node [signal43,signal52,signal64,signal98,signal149,signal164] .nil .nil) .nil))) (.node [signal49,signal64,signal98,signal143,signal164,signal189] (.node [signal45,signal52,signal64,signal98,signal143,signal164] (.node [signal43,signal64,signal98,signal143,signal164,signal196] (.node [signal43,signal64,signal98,signal119,signal143,signal164] .nil .nil) (.node [signal44,signal52,signal64,signal98,signal143,signal164] .nil .nil)) (.node [signal48,signal64,signal98,signal143,signal164,signal189] (.node [signal46,signal64,signal98,signal143,signal164,signal189] .nil .nil) .nil)) (.node [signal52,signal55,signal64,signal98,signal143,signal164] (.node [signal51,signal64,signal98,signal143,signal164,signal189] (.node [signal50,signal64,signal98,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal57,signal64,signal98,signal143,signal164] (.node [signal52,signal56,signal64,signal98,signal143,signal189] .nil .nil) .nil)))) (.node [signal52,signal64,signal80,signal98,signal143,signal164] (.node [signal52,signal64,signal67,signal98,signal143,signal189] (.node [signal52,signal62,signal98,signal143,signal164,signal189] (.node [signal52,signal60,signal91,signal143,signal164,signal189] (.node [signal52,signal59,signal98,signal143,signal175,signal189] .nil .nil) (.node [signal52,signal61,signal98,signal143,signal164,signal201] .nil .nil)) (.node [signal52,signal64,signal65,signal98,signal143,signal164] (.node [signal52,signal63,signal98,signal143,signal164,signal201] .nil .nil) .nil)) (.node [signal52,signal64,signal70,signal98,signal184,signal189] (.node [signal52,signal64,signal69,signal98,signal143,signal164] (.node [signal52,signal64,signal68,signal98,signal143,signal164] .nil .nil) .nil) (.node [signal52,signal64,signal78,signal98,signal143,signal164] (.node [signal52,signal64,signal71,signal98,signal164,signal189] .nil .nil) .nil))) (.node [signal52,signal64,signal93,signal143,signal164,signal189] (.node [signal52,signal64,signal88,signal98,signal143,signal164] (.node [signal52,signal64,signal85,signal98,signal143,signal164] (.node [signal52,signal64,signal81,signal98,signal143,signal164] .nil .nil) (.node [signal52,signal64,signal87,signal98,signal143,signal189] .nil .nil)) (.node [signal52,signal64,signal90,signal143,signal178,signal189] (.node [signal52,signal64,signal89,signal155,signal164,signal189] .nil .nil) .nil)) (.node [signal52,signal64,signal96,signal143,signal164,signal189] (.node [signal52,signal64,signal95,signal143,signal164,signal206] (.node [signal52,signal64,signal94,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal101,signal143,signal189] (.node [signal52,signal64,signal97,signal143,signal164,signal189] .nil .nil) .nil)))))) (.node [signal52,signal64,signal98,signal143,signal164,signal209] (.node [signal52,signal64,signal98,signal143,signal161,signal213] (.node [signal52,signal64,signal98,signal124,signal164,signal189] (.node [signal52,signal64,signal98,signal116,signal143,signal164] (.node [signal52,signal64,signal98,signal111,signal143,signal184] (.node [signal52,signal64,signal98,signal104,signal164,signal189] (.node [signal52,signal64,signal98,signal103,signal184,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal111,signal143,signal164] .nil .nil)) (.node [signal52,signal64,signal98,signal114,signal143,signal164] (.node [signal52,signal64,signal98,signal113,signal143,signal164] .nil .nil) .nil)) (.node [signal52,signal64,signal98,signal121,signal143,signal189] (.node [signal52,signal64,signal98,signal120,signal143,signal164] (.node [signal52,signal64,signal98,signal117,signal143,signal164] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal123,signal164,signal211] (.node [signal52,signal64,signal98,signal122,signal143,signal164] .nil .nil) .nil))) (.node [signal52,signal64,signal98,signal142,signal164,signal211] (.node [signal52,signal64,signal98,signal139,signal143,signal189] (.node [signal52,signal64,signal98,signal130,signal143,signal189] (.node [signal52,signal64,signal98,signal129,signal143,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal131,signal143,signal189] .nil .nil)) (.node [signal52,signal64,signal98,signal141,signal184,signal189] (.node [signal52,signal64,signal98,signal140,signal143,signal164] .nil .nil) .nil)) (.node [signal52,signal64,signal98,signal143,signal149,signal164] (.node [signal52,signal64,signal98,signal143,signal148,signal164] (.node [signal52,signal64,signal98,signal143,signal144,signal164] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal143,signal157,signal164] (.node [signal52,signal64,signal98,signal143,signal156,signal164] .nil .nil) .nil)))) (.node [signal52,signal64,signal98,signal143,signal164,signal194] (.node [signal52,signal64,signal98,signal143,signal164,signal188] (.node [signal52,signal64,signal98,signal143,signal164,signal171] (.node [signal52,signal64,signal98,signal143,signal163,signal189] (.node [signal52,signal64,signal98,signal143,signal162,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal168] .nil .nil)) (.node [signal52,signal64,signal98,signal143,signal164,signal185] (.node [signal52,signal64,signal98,signal143,signal164,signal180] .nil .nil) .nil)) (.node [signal52,signal64,signal98,signal143,signal164,signal191] (.node [signal52,signal64,signal98,signal143,signal164,signal190] (.node [signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal193] (.node [signal52,signal64,signal98,signal143,signal164,signal192] .nil .nil) .nil))) (.node [signal52,signal64,signal98,signal143,signal164,signal202] (.node [signal52,signal64,signal98,signal143,signal164,signal199] (.node [signal52,signal64,signal98,signal143,signal164,signal197] (.node [signal52,signal64,signal98,signal143,signal164,signal195] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal198] .nil .nil)) (.node [signal52,signal64,signal98,signal143,signal164,signal201] (.node [signal52,signal64,signal98,signal143,signal164,signal200] .nil .nil) .nil)) (.node [signal52,signal64,signal98,signal143,signal164,signal205] (.node [signal52,signal64,signal98,signal143,signal164,signal204] (.node [signal52,signal64,signal98,signal143,signal164,signal203] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal208] (.node [signal52,signal64,signal98,signal143,signal164,signal207] .nil .nil) .nil))))) (.node [signal52,signal64,signal98,signal154,signal164,signal189] (.node [signal52,signal64,signal98,signal143,signal179,signal189] (.node [signal52,signal64,signal98,signal143,signal169,signal189] (.node [signal52,signal64,signal98,signal143,signal165,signal189] (.node [signal52,signal64,signal98,signal143,signal164,signal211] (.node [signal52,signal64,signal98,signal143,signal164,signal210] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal212] .nil .nil)) (.node [signal52,signal64,signal98,signal143,signal167,signal189] (.node [signal52,signal64,signal98,signal143,signal166,signal189] .nil .nil) .nil)) (.node [signal52,signal64,signal98,signal143,signal174,signal189] (.node [signal52,signal64,signal98,signal143,signal172,signal189] (.node [signal52,signal64,signal98,signal143,signal170,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal143,signal177,signal189] (.node [signal52,signal64,signal98,signal143,signal176,signal189] .nil .nil) .nil))) (.node [signal52,signal64,signal98,signal146,signal164,signal189] (.node [signal52,signal64,signal98,signal143,signal184,signal201] (.node [signal52,signal64,signal98,signal143,signal183,signal189] (.node [signal52,signal64,signal98,signal143,signal181,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal184,signal189] .nil .nil)) (.node [signal52,signal64,signal98,signal145,signal164,signal189] (.node [signal52,signal64,signal98,signal143,signal184,signal211] .nil .nil) .nil)) (.node [signal52,signal64,signal98,signal151,signal164,signal211] (.node [signal52,signal64,signal98,signal149,signal164,signal189] (.node [signal52,signal64,signal98,signal149,signal164] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal153,signal184,signal189] (.node [signal52,signal64,signal98,signal152,signal164,signal189] .nil .nil) .nil)))) (.node [signal52,signal73,signal98,signal143,signal164,signal189] (.node [signal52,signal64,signal99,signal143,signal164,signal189] (.node [signal52,signal64,signal98,signal164,signal184,signal211] (.node [signal52,signal64,signal98,signal158,signal164,signal189] (.node [signal52,signal64,signal98,signal155,signal184,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal164,signal182,signal189] .nil .nil)) (.node [signal52,signal64,signal98,signal184,signal211] (.node [signal52,signal64,signal98,signal184,signal189,signal211] .nil .nil) .nil)) (.node [signal52,signal64,signal118,signal143,signal164,signal189] (.node [signal52,signal64,signal107,signal143,signal164,signal189] (.node [signal52,signal64,signal100,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal134,signal143,signal164,signal189] (.node [signal52,signal64,signal127,signal143,signal164,signal189] .nil .nil) .nil))) (.node [signal53,signal64,signal98,signal143,signal164,signal189] (.node [signal52,signal98,signal111,signal143,signal164,signal201] (.node [signal52,signal81,signal98,signal143,signal164,signal189] (.node [signal52,signal81,signal98,signal143,signal164] .nil .nil) (.node [signal52,signal83,signal98,signal143,signal164,signal201] .nil .nil)) (.node [signal52,signal98,signal133,signal143,signal164,signal189] (.node [signal52,signal98,signal126,signal143,signal164,signal189] .nil .nil) .nil)) (.node [signal64,signal75,signal98,signal143,signal164,signal189] (.node [signal64,signal72,signal98,signal143,signal164,signal189] (.node [signal54,signal64,signal98,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal64,signal98,signal109,signal143,signal164,signal189] (.node [signal64,signal98,signal105,signal143,signal164,signal189] .nil .nil) .nil)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal52,signal64,signal76,signal98,signal143,signal164,signal189] (.node [signal29,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal14,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal7,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal3,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal2,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal2,signal52,signal64,signal98,signal143,signal164] .nil .nil) .nil) (.node [signal5,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil)) (.node [signal11,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal9,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal13,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil))) (.node [signal21,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal17,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal16,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal15,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal19,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil)) (.node [signal25,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal24,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal26,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil)))) (.node [signal43,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal39,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal31,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal31,signal52,signal64,signal98,signal143,signal164] (.node [signal29,signal52,signal64,signal98,signal143,signal189] .nil .nil) .nil) (.node [signal36,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil)) (.node [signal42,signal52,signal64,signal98,signal143,signal164,signal189] (.node [signal40,signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal43,signal52,signal64,signal98,signal143,signal164] .nil .nil))) (.node [signal52,signal61,signal64,signal98,signal143,signal164,signal189] (.node [signal52,signal59,signal64,signal98,signal143,signal164,signal189] (.node [signal52,signal58,signal64,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal52,signal60,signal64,signal98,signal143,signal164,signal189] .nil .nil)) (.node [signal52,signal64,signal70,signal98,signal143,signal164,signal189] (.node [signal52,signal63,signal64,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal52,signal64,signal74,signal98,signal143,signal164,signal189] .nil .nil))))) (.node [signal52,signal64,signal98,signal142,signal143,signal164,signal189] (.node [signal52,signal64,signal98,signal111,signal143,signal164] (.node [signal52,signal64,signal92,signal98,signal143,signal164,signal189] (.node [signal52,signal64,signal90,signal98,signal143,signal164,signal189] (.node [signal52,signal64,signal89,signal98,signal143,signal164,signal189] (.node [signal52,signal64,signal83,signal98,signal143,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal91,signal98,signal143,signal164,signal189] .nil .nil)) (.node [signal52,signal64,signal98,signal103,signal143,signal164,signal189] (.node [signal52,signal64,signal95,signal98,signal143,signal164,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal108,signal143,signal164,signal189] .nil .nil))) (.node [signal52,signal64,signal98,signal128,signal143,signal164,signal189] (.node [signal52,signal64,signal98,signal119,signal143,signal164,signal189] (.node [signal52,signal64,signal98,signal111,signal143,signal164,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal123,signal143,signal164,signal189] .nil .nil)) (.node [signal52,signal64,signal98,signal138,signal143,signal164,signal189] (.node [signal52,signal64,signal98,signal136,signal143,signal164,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal141,signal143,signal164,signal189] .nil .nil)))) (.node [signal52,signal64,signal98,signal143,signal164,signal189,signal196] (.node [signal52,signal64,signal98,signal143,signal164,signal173,signal189] (.node [signal52,signal64,signal98,signal143,signal155,signal164,signal189] (.node [signal52,signal64,signal98,signal143,signal153,signal164,signal189] (.node [signal52,signal64,signal98,signal143,signal151,signal164,signal189] .nil .nil) .nil) (.node [signal52,signal64,signal98,signal143,signal161,signal164,signal189] .nil .nil)) (.node [signal52,signal64,signal98,signal143,signal164,signal178,signal189] (.node [signal52,signal64,signal98,signal143,signal164,signal175,signal189] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal184,signal189] .nil .nil))) (.node [signal52,signal64,signal98,signal143,signal164,signal189,signal213] (.node [signal52,signal64,signal98,signal143,signal164,signal189,signal206] (.node [signal52,signal64,signal98,signal143,signal164,signal189,signal201] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal164,signal189,signal211] .nil .nil)) (.node [signal52,signal64,signal98,signal143,signal164,signal211] (.node [signal52,signal64,signal98,signal143,signal164,signal201] .nil .nil) (.node [signal52,signal64,signal98,signal143,signal184,signal189] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal52,signal64,signal98,signal143,signal164,signal189] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 0xfefefeeafefcfec8
theorem row : ∀j : Fin 88, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[1,2]⟩,⟨.or,[3,4]⟩,⟨.and,[6,7]⟩,⟨.and,[1,2]⟩,⟨.or,[1,3]⟩,⟨.or,[10,5]⟩,⟨.and,[0,11]⟩,⟨.or,[8,9]⟩,⟨.or,[13,12]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
theorem tableSpec : ∀x : Fin 6 → Bool, decide (∃ i < ([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).getD (2 * i + 1) 0) false = true) = Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := by decide +kernel
end PEqualNP.Outside.L_meta_9144
open PEqualNP.Outside.L_meta_9144 in
theorem PEqualNP.Outside.L_meta_9144 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).length / 2, (List.ofFn x).getD (([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 1, 0, 3, 0, 5, 1, 2, 1, 3, 1, 4, 2, 3, 2, 4] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legalGates _ correct
  obtain ⟨ds,p,mono,size,ev⟩ := replace table 9 ins (by decide) row rfl reject upper gs o legalGates
    (fun x => (correct x).trans (tableSpec x))
  exact ⟨ds,p,mono,size,fun x => (ev x).trans (tableSpec x).symm⟩
