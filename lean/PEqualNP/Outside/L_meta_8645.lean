import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8645

-- The signed lower bound and the nine-gate witness are specialized from L-meta-1423.
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

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

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

def v242 : W := 0x3a3cecdc00f1b36
def v243 : W := 0x596599e821de7d0
def v244 : W := 0x775d3d37dc54f09
def v245 : W := 0xfdeffbec652a0eb
def v246 : W := 0x31cb5d7dee72ef
def v247 : W := 0xa796d7d39a135d4
def v248 : W := 0xc5c31323ff0e0c9
def v249 : W := 0xa796d7d39a030c4
def v250 : W := 0x5869282c65ec22b
def v251 : W := 0x3a3cecdc00e1226
def v252 : W := 0x775d3d37dc44209
def v253 : W := 0x88a2c2c823ab0e6
def v254 : W := 0x382ce8cc0020022
def v255 : W := 0xa796d7d000131d4
def v256 : W := 0xfef34e3821c9204
def v257 : W := 0x775d3d344450b09
def v258 : W := 0xfef34e3bbbcd204
def v259 : W := 0x2f34151bb938522
def v260 : W := 0xfce34a282108000
def v261 : W := 0x6255c4f0651911d
def v262 : W := 0x89ae730c6799d0d
def v263 : W := 0x76518cf398662e2
def v264 : W := 0xa69a6617de2102f
def v265 : W := 0x4d61d1ebdca543f
def v266 : W := 0xd0cbeae44647add
def v267 : W := 0xc7d3173065dbbdd
def v268 : W := 0x9daa3b0f9ae2ee2
def v269 : W := 0xb29e2e14215abc0
def v270 : W := 0x10cb1c444220eb
def v271 : W := 0x10491c000125d0
def v272 : W := 0xa79ef7d7de335ff
def v273 : W := 0x100110044020c9
def v274 : W := 0x3a304c1800c1204
def v275 : W := 0x82004442002b
def v276 : W := 0xa69246139a01004
def v277 : W := 0x80c000220e2
def v278 : W := 0x76510c339844200
def v279 : W := 0x5861082821cc200
def v280 : W := 0x10c31044410d09
def v281 : W := 0x88a242082389004
def v282 : W := 0x775dbdf7dc76feb
def v283 : W := 0x21004139ac5204
def v284 : W := 0x10cb1c444321fb
def v285 : W := 0xfdeffbec653a5fb
def v286 : W := 0xfdeffbec653adeb
def v287 : W := 0xfdeffbec653a9fb
def v288 : W := 0x10cb1c444325fb
def v289 : W := 0x775d3d37dc10509
def v290 : W := 0x3a3cecdc0031136
def v291 : W := 0x10cb1c444325eb
def v292 : W := 0x10cb1c44432deb
def v293 : W := 0x10cb1c444329fb
def v294 : W := 0xfffffffc65fbbff
def v295 : W := 0x10cb1c444329eb
def v296 : W := 0xc5c31323ff0a4c9
def v297 : W := 0x5869282c65e8a2b
def v298 : W := 0x3a3cecdc0070b22
def v299 : W := 0x88a2c2c821ab0f6
def v300 : W := 0xa796d7d398125c0
def v301 : W := 0x5869282c656ca2b
def v302 : W := 0x21004139a11514
def v303 : W := 0x5a792c3fff3953f
def v304 : W := 0x21004139854f00
def v305 : W := 0x88a2c2c8212a0e2
def v306 : W := 0x10cb1c44432dfb
def v307 : W := 0xc5c31323fd0e4c9
def v308 : W := 0x5869282c652802b
def v309 : W := 0x8ab2c6dbb97efe2
def v310 : W := 0x21004139ad5f14
def v311 : W := 0x88a2c2c8232b0f6
def v312 : W := 0x1a3cacdc00f1b36
def v313 : W := 0x820c0c800a1036
def v314 : W := 0xbabeeedc21fbbf6
def v315 : W := 0x82000082128022
def v316 : W := 0x271415139810500
def v317 : W := 0xffffffffffef2ef
def v318 : W := 0x45411123dc04409
def v319 : W := 0x1828280c00e0a22
def v320 : W := 0x858213039a024c0
def v321 : W := 0x7a7decfc65f9b3f
def v322 : W := 0xa3ce4dc00f1b36
def v323 : W := 0x1a38ecdc00f1b36
def v324 : W := 0x2214c4d00011114
def v325 : W := 0xbfbeffdf9af3ff6
def v326 : W := 0xbdaefbcc00220e2
def v327 : W := 0x404100206508009
def v328 : W := 0xbfbeffdf9a335f6
def v329 : W := 0xbfbeffdc00f3bf6
def v330 : W := 0xf7dffff7dc56fc9
def v331 : W := 0xf5cffbe444020c9
def v332 : W := 0xf7dffff7de135dd
def v333 : W := 0x321c2c140050b00
def v334 : W := 0x7f7dfdffdcf5f3f
def v335 : W := 0x7d6df9ec442002b
def v336 : W := 0x2a3ce4dc00b1936
def v337 : W := 0x7f7dfdffdc74f2b
def v338 : W := 0x7f7dfdfc44f1b3f
def v339 : W := 0x80820200210a0c0
def v340 : W := 0xfffffffc65eb2ef
def v341 : W := 0xfffffffc657abeb
def v342 : W := 0xfffffffc653b1ff
def v343 : W := 0xc4cfa2e7bb3c932
def v344 : W := 0xfcefeaec2128022
def v345 : W := 0xf7dffff7de57fdd
def v346 : W := 0x3a3cecdc0030122
def v347 : W := 0x3a38ecdc00e1a36
def v348 : W := 0xfeffeeffbbfdb36
def v349 : W := 0xfeffeeffbbed226
def v350 : W := 0x3a3cecdc0021026
def v351 : W := 0x3a3cacdc00f0b32
def v352 : W := 0xa586d3c000020c0
def v353 : W := 0xfef34e3bbb09004
def v354 : W := 0xfef34e3bb94c200
def v355 : W := 0x3a3cecdc0060222
def v356 : W := 0x3a3cecdc0031936
def v357 : W := 0x754d39244400009
def v358 : W := 0x3a3cecdc0070b32
def v359 : W := 0x3a3cecdc0071b36
def v360 : W := 0x3a3cecdc00f1336
def v361 : W := 0x3a3cecdc00d1b14
def v362 : W := 0x3a3cecdc00e1236
def v363 : W := 0x3a3cecdc00f0b22
def v364 : W := 0x3a3cecdc00e1a26
def v365 : W := 0x504928244444a09
def v366 : W := 0x475d3537dc54f09
def v367 : W := 0x3a3cecdc00f1b26
def v368 : W := 0x8082c2c002030d4
def v369 : W := 0x7f7d3d3ffd7cf2b
def v370 : W := 0x57593d37dc54f09
def v371 : W := 0x535d3d37dc54f09
def v372 : W := 0xfefb6e3fffed22f
def v373 : W := 0x3a3cecdc00b1136
def v374 : W := 0x5869282c6568a2b
def v375 : W := 0xfdeffbec656eaeb
def v376 : W := 0xfdeffbec65ee2eb
def v377 : W := 0xfdeffbec65eaaeb
def v378 : W := 0x5869282c656c22b
def v379 : W := 0x5869282c65e822b
def v380 : W := 0x5869282c65eca2b
def v381 : W := 0xffff7f3fffcd20d
def v382 : W := 0xfff7dffbbbdf7d4
def v383 : W := 0x735d3d344454f09
def v384 : W := 0x675d3537dc14d09
def v385 : W := 0xffff7f3ffd5cf09
def v386 : W := 0xfdef7b2c6508009
def v387 : W := 0x775d3d344410109
def v388 : W := 0x77593d37dc44e09
def v389 : W := 0xffff7f3fffddf0d
def v390 : W := 0x775d3d344440209
def v391 : W := 0x775d3d344454b09
def v392 : W := 0x775d3d344450f09
def v393 : W := 0x775d3d379854f00
def v394 : W := 0xfeffeefc21f9b36
def v395 : W := 0x775d3d37dc50f09
def v396 : W := 0x775d3d37dc14509
def v397 : W := 0x775d3d37dc10d09
def v398 : W := 0x775d3d37dc44a09
def v399 : W := 0x775d3d37dc44609
def v400 : W := 0x8396d7d39a135d4
def v401 : W := 0x775d3d37dc54b09
def v402 : W := 0x775d3d37dc54709
def v403 : W := 0x879697d39a135d4
def v404 : W := 0x8792d7d39a135d4
def v405 : W := 0xa396d7d002135d4
def v406 : W := 0xa796d7d002131d4
def v407 : W := 0xa79697d39a125d0
def v408 : W := 0xfff7dffbbbcf2c4
def v409 : W := 0xfff7dffbbb1b5d4
def v410 : W := 0xfde7dbe8210a0c0
def v411 : W := 0xa792d7d39a034d4
def v412 : W := 0xa796d7d000121c0
def v413 : W := 0xa796d7d000030c4
def v414 : W := 0xa796d7d000135d4
def v415 : W := 0xa796d7d398020c0
def v416 : W := 0xa796d7d398135d4
def v417 : W := 0xa796d7d398125d0
def v418 : W := 0xa796d7d39a030d4
def v419 : W := 0xa796d7d39a034c4
def v420 : W := 0xfffffffffd6e2eb
def v421 : W := 0xcef3463bbbcd204
def v422 : W := 0xa796d7d39a135c4
def v423 : W := 0xa796d7d39a131d4
def v424 : W := 0xa796d7d39a125c0
def v425 : W := 0xeef3463bbb8d004
def v426 : W := 0xdef30e3bbbcd204
def v427 : W := 0xdaf34e3bbbcd204
def v428 : W := 0xfaf34e3823cd204
def v429 : W := 0xfdeffbec652802b
def v430 : W := 0xfdeffbec212a0e2
def v431 : W := 0xffffffffff2b0ef
def v432 : W := 0xfdeffbec650a0c9
def v433 : W := 0xfdeffbec44220eb
def v434 : W := 0xfef34e382148200
def v435 : W := 0xfef34e382109004
def v436 : W := 0xfef30e3bbbcc200
def v437 : W := 0xfef34e3bbbc9204
def v438 : W := 0xfef34e3bb9cd204
def v439 : W := 0xfef34e3bb908000
def v440 : W := 0xfef34e3b9ac5204
def v441 : W := 0xfef34e3823c9204
def v442 : W := 0xfef34e3bb9cc200
def v443 : W := 0xfef34e3bbb4c200
def v444 : W := 0xfef34e3bbb0d004
def v445 : W := 0xfef34e3bbb89004
def v446 : W := 0xfef34e3bbb4d204
def v447 : W := 0xfef7cefbbbcd204
def v448 : W := 0xfef34e3bbbcd604
def v449 : W := 0xfef34e3bbbcd214
def v450 : W := 0xfef3cefbbbcd214
def v451 : W := 0xfef34e3bbbcda04
def v452 : W := 0xfff35f3bbbcd604
def v453 : W := 0xfeff6e3fbbcd204
def v454 : W := 0xfefb6e3fbbcda04
def v455 : W := 0xfff75f3bbbcd204
def v456 : W := 0xfef34e3821cd204
def v457 : W := 0xa796d7d39a11514
def v458 : W := 0x775d3d37de54f09
def v459 : W := 0xbfb6dfdb9a135d4
def v460 : W := 0xa79ef7d79a13dd4
def v461 : W := 0xa796d7d39a935d4
def v462 : W := 0xa796d7d39a175d4
def v463 : W := 0xb79effd79a135d4
def v464 : W := 0xafb6d7db9a935d4
def v465 : W := 0xf7d7dff39a135d4
def v466 : W := 0xe7d7d7f39a175d4
def v467 : W := 0x775d3d37dcd4f09
def v468 : W := 0x775d3d37dc54f19
def v469 : W := 0x7f7d3d3fdcd4f09
def v470 : W := 0x775dfdf7dc54f09
def v471 : W := 0x775dbdf7dc54f19
def v472 : W := 0xafb6d7dbbb3b5f6
def v473 : W := 0x7f7d7d3fdc54f09
def v474 : W := 0xfef3cefbbbef2e6
def v475 : W := 0xfdeffbec67ab0ef
def v476 : W := 0xfdeffbec672b0ff
def v477 : W := 0xfdeffbec65ab0ff
def v478 : W := 0x88a2c2c821ab0e6
def v479 : W := 0x88a2c2c8212b0f6
def v480 : W := 0x88a2c2c8232b0e6
def v481 : W := 0x88a2c2c823ab0f6
def v482 : W := 0xf7df3f37de54f09
def v483 : W := 0xf7df7f37dc54f09
def v484 : W := 0x3f3cfddc00f1b36
def v485 : W := 0x3a3cecdc00f5b36
def v486 : W := 0x3a3cecdc00f1f36
def v487 : W := 0x3b3cfddc00f1f36
def v488 : W := 0x3a3cecdc02f1b36
def v489 : W := 0xf7df3f37fd5efc9
def v490 : W := 0x7e7decfc00f1b36
def v491 : W := 0xc5c31320650a0c9
def v492 : W := 0x7a7decfc00f5b36
def v493 : W := 0xe7d7d7f3ff1b5dd
def v494 : W := 0xbebeeedc00f1b36
def v495 : W := 0xbabeeedc02f1b36
def v496 : W := 0xc5c31323fd0a4c9
def v497 : W := 0xc5c31323fd0e0c9
def v498 : W := 0xc5c31323ff0e4c9
def v499 : W := 0xc5c31323ff0a0c9
def v500 : W := 0xa796d7d39a13dd4
def v501 : W := 0x775d3d37dc00009
def v502 : W := 0x201014
def v503 : W := 0x44a00
def v504 : W := 0x10910
def v505 : W := 0x10510
def v506 : W := 0x0
def v507 : W := 0x10d00
def v508 : W := 0xc0a00
def v509 : W := 0x81014
def v510 : W := 0xc4200
def v511 : W := 0x80c000020d0
def v512 : W := 0x39a00400
def v513 : W := 0x39804400
def v514 : W := 0x281004
def v515 : W := 0x39a04000
def v516 : W := 0x80c00020032
def v517 : W := 0xc0c00001014
def v518 : W := 0xca0c40030932
def v519 : W := 0xca0c40020022
def v520 : W := 0x820044400809
def v521 : W := 0x820040020822
def v522 : W := 0xc20040010900
def v523 : W := 0xc4c30223bb0c000
def v524 : W := 0x100110000024c0
def v525 : W := 0x10011004400409
def v526 : W := 0x10411000010500
def v527 : W := 0x480c00010110
def v528 : W := 0x10c31044400009
def v529 : W := 0x10cb1c44412dd9
def v530 : W := 0x10cb1c44430d3b
def v531 : W := 0xffffffffff3b5ff
def v532 : W := 0x10cb1c40032df2
def v533 : W := 0x10491c000020c0
def v534 : W := 0x210041000d1b14
def v535 : W := 0x21004100050b00
def v536 : W := 0xfffffffffd7efeb
def v537 : W := 0x21004100011114
def v538 : W := 0x210041000c1204
def v539 : W := 0x21004139810500
def v540 : W := 0x21004139844200
def v541 : W := 0x21004139a01004
def v542 : W := 0x210041398d5f14
def v543 : W := 0x21004139a55f14
def v544 : W := 0x21004139ad5714
def v545 : W := 0x21004139ad1f14
def v546 : W := 0x21004139ad5b14
def v547 : W := 0x820c0c80020022
def v548 : W := 0x820000800a0022
def v549 : W := 0x31c3517dc54f09
def v550 : W := 0x31495d39a135d4
def v551 : W := 0x21ca4d400f1b36
def v552 : W := 0x50011039800400
def v553 : W := 0x82000082188000
def v554 : W := 0x82040080081004
def v555 : W := 0x1820080800c0200
def v556 : W := 0x100828040040a00
def v557 : W := 0xa30c4d800f1b36
def v558 : W := 0x1828280c0020022
def v559 : W := 0x1828e8cc00e1a36
def v560 : W := 0x1a382c1c00f1b36
def v561 : W := 0x182ca8cc00f0b32
def v562 : W := 0x2004c0c00000000
def v563 : W := 0x82ce0cc00b1936
def v564 : W := 0x21004139ad5f04
def v565 : W := 0x221404100010100
def v566 : W := 0x2314d5d000135d4
def v567 : W := 0x2214c4d39a11514
def v568 : W := 0x2214c4d000d1b14
def v569 : W := 0x221ce4d40031936
def v570 : W := 0x261004139800000
def v571 : W := 0x250411000000000
def v572 : W := 0x271415139854f00
def v573 : W := 0x271c3517dc10d09
def v574 : W := 0x271495d398125d0
def v575 : W := 0x271415139a11514
def v576 : W := 0x2714d5d39811514
def v577 : W := 0x300c28040000000
def v578 : W := 0x2a34c4d800b1136
def v579 : W := 0x32100c100040200
def v580 : W := 0x321c2c1400d1b14
def v581 : W := 0x371c3d179850f00
def v582 : W := 0x321cecd40051b14
def v583 : W := 0x321cacd40070b32
def v584 : W := 0x321c2c179854f00
def v585 : W := 0x331c3d144450f09
def v586 : W := 0x382048080000000
def v587 : W := 0x382ce8cc00e0a22
def v588 : W := 0x382ce8cc0030932
def v589 : W := 0x382ce8cc00a1036
def v590 : W := 0x392cf9cc44220eb
def v591 : W := 0x3a386c1c00e1a26
def v592 : W := 0x3a30ccd800e1236
def v593 : W := 0x3a304c1b9ac5204
def v594 : W := 0x3a304c1800d1b14
def v595 : W := 0x3a34ccd800d1314
def v596 : W := 0x3a3c6c1c00d1b04
def v597 : W := 0x3a3c2c1c00f0b22
def v598 : W := 0x3b3cfddc44f3bff
def v599 : W := 0x3b3cfddc00f3ff6
def v600 : W := 0x3a3cecdf9af5b36
def v601 : W := 0x3a3cecdf9af1f36
def v602 : W := 0x3b3cfddc44f1f3f
def v603 : W := 0x40410020210c000
def v604 : W := 0x3f3cfddf98f1f36
def v605 : W := 0x404100204404009
def v606 : W := 0x454d3127dc14d09
def v607 : W := 0x454111204400009
def v608 : W := 0x444100239804000
def v609 : W := 0x504108200044200
def v610 : W := 0x47511533dc54f09
def v611 : W := 0x504928244400009
def v612 : W := 0x3a3cecdf98f5f36
def v613 : W := 0x55493927dc44e09
def v614 : W := 0x514d39244454f09
def v615 : W := 0x52592c37dc54f09
def v616 : W := 0x586108282108000
def v617 : W := 0x5869282c21eca22
def v618 : W := 0x5869282c44e4a2b
def v619 : W := 0x5869282c65cca09
def v620 : W := 0x5a710c3bbbcd204
def v621 : W := 0x596db9ec652a0eb
def v622 : W := 0x67551533dc14509
def v623 : W := 0x221044100001004
def v624 : W := 0x754d39244410d09
def v625 : W := 0x744108200000000
def v626 : W := 0x754db9e444220eb
def v627 : W := 0x754d3927dc04409
def v628 : W := 0x754d39244444a09
def v629 : W := 0x765d2c379854b00
def v630 : W := 0x76510c339ac5204
def v631 : W := 0x76510c339854f00
def v632 : W := 0x76592c37dc44a09
def v633 : W := 0x77551d339854700
def v634 : W := 0x77511d33dc44609
def v635 : W := 0x7a714c3821cd204
def v636 : W := 0x775dbdf7dc74f3b
def v637 : W := 0x775d3d37ded5f0d
def v638 : W := 0x775d3d37de55f1d
def v639 : W := 0x775d3d37dcd5f1d
def v640 : W := 0x775dbdf7dc56fd9
def v641 : W := 0x775dfdf7dc55f1d
def v642 : W := 0x786de8ec652802b
def v643 : W := 0x7a7decfc44f5b3f
def v644 : W := 0x7a7decfc21fdb36
def v645 : W := 0x7d6d392c652802b
def v646 : W := 0x7e714c3b98c5204
def v647 : W := 0x7e710c3bb9cc200
def v648 : W := 0x7e7decff98f5b36
def v649 : W := 0x808202002308000
def v650 : W := 0x7f7d7d3fdcd5f0d
def v651 : W := 0x7f7d3d3ffddcf09
def v652 : W := 0x8082020002020c0
def v653 : W := 0x8186d3c002135d4
def v654 : W := 0x8082c2c000020c0
def v655 : W := 0x808242000201004
def v656 : W := 0x848202039a00000
def v657 : W := 0x8292c6d39a135d4
def v658 : W := 0x8582130000020c0
def v659 : W := 0x7f7d3d3fdcf4f2b
def v660 : W := 0x879217139a135d4
def v661 : W := 0x858693c39a125d0
def v662 : W := 0x8582d3c39a034d4
def v663 : W := 0x88a242082108000
def v664 : W := 0x88a2c2c802a30f6
def v665 : W := 0x8ab2461bbbcd204
def v666 : W := 0x88a2c2c823a9036
def v667 : W := 0x88a2c2c8238b0d4
def v668 : W := 0x89aef3cc652a0eb
def v669 : W := 0xa48242000000000
def v670 : W := 0xa296c6d002131d4
def v671 : W := 0xa586d3c39a024c0
def v672 : W := 0xa586d3c000125d0
def v673 : W := 0xa586d3c002030d4
def v674 : W := 0xa58ef3c444220eb
def v675 : W := 0xa69246139ac5204
def v676 : W := 0xa69246139a11514
def v677 : W := 0xa696c6d39a11114
def v678 : W := 0xa692c6d39a030d4
def v679 : W := 0xa79257139a034c4
def v680 : W := 0xa79657139a11504
def v681 : W := 0xa796d7d39ad77d4
def v682 : W := 0xa796d7d39a57fd4
def v683 : W := 0xa796d7d39ad3fd4
def v684 : W := 0xa79ef7d7de13ddd
def v685 : W := 0xa79ef7d79a33df6
def v686 : W := 0xb79effd79a53fd4
def v687 : W := 0xafb6d7db9ab35f6
def v688 : W := 0xaeb2461bbb89004
def v689 : W := 0xafb6d7dbbb9b5d4
def v690 : W := 0xbab24e1823c9204
def v691 : W := 0xb8aeeacc212a0e2
def v692 : W := 0xbabeeedc02f3bf6
def v693 : W := 0xbebeeedf9af1b36
def v694 : W := 0xbabeeedc23f9b36
def v695 : W := 0xbeb24e1b9ac1204
def v696 : W := 0xbfb6dfdb9ad37d4
def v697 : W := 0xada6d3c8212a0e2
def v698 : W := 0xa79617139a125c0
def v699 : W := 0xc5c31323de064c9
def v700 : W := 0xc4c302202108000
def v701 : W := 0xc5c31323bb0e4c0
def v702 : W := 0xc5c31323ff0c409
def v703 : W := 0xd8e34a2823cd204
def v704 : W := 0xcce3422bbb8d004
def v705 : W := 0xc6d30633bbcd204
def v706 : W := 0xc5cfb3e4652a0eb
def v707 : W := 0xcde3d3e8652a0eb
def v708 : W := 0xdce30a2bbbcc200
def v709 : W := 0xd8ebeaec652a0eb
def v710 : W := 0xddeb3b2c652a0eb
def v711 : W := 0xf7d7dff39a577d4
def v712 : W := 0xf5cf3b24650a0c9
def v713 : W := 0xe7d7d7f3de175dd
def v714 : W := 0xe7d7d7f3bb1f5d4
def v715 : W := 0xe6d34633bb0d004
def v716 : W := 0xf6d30e33bb4c200
def v717 : W := 0xf6d34e339a45204
def v718 : W := 0xf7df7f37de55f0d
def v719 : W := 0xf7df3f37de56fc9
def v720 : W := 0xf7df3f37ff5cf09
def v721 : W := 0xe5c7d3e0650a0c9
def v722 : W := 0xfce34a282389004
def v723 : W := 0xfce34a2821cc200
def v724 : W := 0xfce3cae8212a0e2
def v725 : W := 0xfce34a2bbb0c000
def v726 : W := 0xfceb6a2c652802b
def v727 : W := 0xfde35b28650a0c9
def v728 : W := 0xfdeffbeffd2e4eb
def v729 : W := 0xfdeffbefff2e0eb
def v730 : W := 0xfdeffbefff2a4eb
def v731 : W := 0xfefb6e3fbbeda26
def v732 : W := 0xfef3cefbbbcf2d4
def v733 : W := 0xfef34e3bbbddb14
def v734 : W := 0xfef34e3bbbdd714
def v735 : W := 0xfef34e3bbbddf04
def v736 : W := 0xfef3cefbbbed236
def v737 : W := 0xfef7cefbbbdd314
def v738 : W := 0xfeff6e3fbbddb04
def v739 : W := 0xfefb6e3fffcda0d
def v740 : W := 0xfff35f3bbbcf6c4
def v741 : W := 0xfff35f3bffcd60d
def v742 : W := 0xfff75f3bbbdd704
def v743 : W := 0xffffffffdef7fff
def v744 : W := 0xffffffffbbffff6
def v745 : W := 0xfffffffffd3a5eb
def v746 : W := 0xfff35f3bffcf2cd
def v747 : W := 0xffffffffffffbff
def v748 : W := 0xffffffffff7ffff
def v749 : W := 0xffffffffffdffdd
def v750 : W := 0xfffffffffffdf3f
def v751 : W := 0xfffffffffffbfff
def v752 : W := 0xffffffffffff7ff
def v753 : W := 0xfffffffffffffef
def v754 : W := 0xfffffffffdfffff
def v755 : W := 0x725d2c344454b09

def ins_eaa8a880 : List W := [0xfdeffbec652a0eb, 0x3a3cecdc00f1b36, 0x775d3d37dc54f09, 0xa796d7d39a135d4, 0xfef34e3bbbcd204]
theorem nd_eaa8a880 : ins_eaa8a880.Nodup := by decide +kernel
theorem rows_eaa8a880 : ∀ j : Fin 60, Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if (ins_eaa8a880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_eaa8a880_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_0 : everyKey (fun q => !doneTest q) tree_eaa8a880_0 = true := by decide +kernel
theorem closed_eaa8a880_0 : Closed 0 tree_eaa8a880_0 := closed_nil tree_eaa8a880_0 ok_tree_eaa8a880_0
def tree_eaa8a880_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_1 : everyKey (rowOK 0 tree_eaa8a880_0) tree_eaa8a880_1 = true := by decide +kernel
theorem closed_eaa8a880_1 : Closed 1 tree_eaa8a880_1 := closed_next 0 (by decide) tree_eaa8a880_1 tree_eaa8a880_0 closed_eaa8a880_0 ok_tree_eaa8a880_1
def tree_eaa8a880_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_2 : everyKey (rowOK 1 tree_eaa8a880_1) tree_eaa8a880_2 = true := by decide +kernel
theorem closed_eaa8a880_2 : Closed 2 tree_eaa8a880_2 := closed_next 1 (by decide) tree_eaa8a880_2 tree_eaa8a880_1 closed_eaa8a880_1 ok_tree_eaa8a880_2
def tree_eaa8a880_3 : BinaryTree (List W) := (.node [v242,v243,v244,v245] (.node [v246,v244,v247,v248] (.node [v246,v242,v244,v249] (.node [v246,v242,v250,v244] (.node [v246,v251,v244,v247] .nil .nil) (.node [v246,v242,v252,v247] .nil .nil)) (.node [v246,v242,v253,v247] (.node [v246,v242,v244,v247] .nil .nil) .nil)) (.node [v254,v244,v255,v256] (.node [v254,v257,v255,v258] (.node [v259,v242,v245,v258] .nil .nil) (.node [v254,v257,v247,v256] .nil .nil)) (.node [v251,v244,v249,v260] (.node [v251,v252,v247,v260] .nil .nil) .nil))) (.node [v261,v244,v245,v258] (.node [v242,v262,v247,v245] (.node [v242,v252,v249,v260] (.node [v242,v263,v247,v245] .nil .nil) (.node [v242,v244,v264,v245] .nil .nil)) (.node [v265,v247,v245,v258] (.node [v242,v266,v245,v258] .nil .nil) .nil)) (.node [v244,v255,v267,v258] (.node [v244,v268,v245,v258] (.node [v257,v247,v267,v258] .nil .nil) .nil) (.node [v247,v269,v245,v258] (.node [v244,v247,v267,v256] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_3 : everyKey (rowOK 2 tree_eaa8a880_2) tree_eaa8a880_3 = true := by decide +kernel
theorem closed_eaa8a880_3 : Closed 3 tree_eaa8a880_3 := closed_next 2 (by decide) tree_eaa8a880_3 tree_eaa8a880_2 closed_eaa8a880_2 ok_tree_eaa8a880_3
def tree_eaa8a880_4llll : BinaryTree (List W) := (.node [v270,v251,v244,v247,v245] (.node [v271,v242,v244,v272,v245] (.node [v273,v274,v244,v247,v245] (.node [v275,v242,v244,v276,v245] (.node [v277,v242,v278,v247,v245] .nil .nil) .nil) (.node [v271,v242,v243,v244,v245] (.node [v271,v242,v279,v244,v245] .nil .nil) .nil)) (.node [v280,v242,v262,v247,v245] (.node [v280,v242,v281,v247,v245] (.node [v280,v242,v282,v247,v245] .nil .nil) .nil) (.node [v270,v246,v242,v244,v247] (.node [v270,v283,v242,v244,v247] .nil .nil) .nil))) (.node [v284,v242,v244,v247,v245] (.node [v270,v242,v244,v247,v285] (.node [v270,v242,v244,v249,v245] (.node [v270,v242,v252,v247,v245] .nil .nil) .nil) (.node [v270,v242,v244,v247,v286] (.node [v270,v242,v244,v247,v287] .nil .nil) .nil)) (.node [v288,v242,v289,v247,v245] (.node [v288,v290,v244,v247,v245] (.node [v291,v242,v244,v247,v245] .nil .nil) .nil) (.node [v288,v242,v244,v247,v245] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llll = true := by decide +kernel
def tree_eaa8a880_4lllr : BinaryTree (List W) := (.node [v292,v242,v244,v247,v245] (.node [v293,v242,v244,v255,v245] (.node [v293,v254,v244,v247,v294] (.node [v295,v242,v244,v247,v245] (.node [v288,v244,v247,v296,v245] .nil .nil) .nil) (.node [v293,v242,v257,v247,v245] (.node [v293,v242,v297,v244,v245] .nil .nil) .nil)) (.node [v292,v298,v244,v247,v245] (.node [v293,v242,v299,v247,v245] (.node [v293,v242,v244,v247,v245] .nil .nil) .nil) (.node [v292,v242,v244,v300,v245] (.node [v292,v242,v301,v244,v245] .nil .nil) .nil))) (.node [v302,v242,v303,v244,v258] (.node [v304,v242,v305,v247,v258] (.node [v306,v242,v244,v247,v245] (.node [v292,v244,v247,v307,v245] .nil .nil) .nil) (.node [v302,v242,v308,v244,v258] (.node [v304,v242,v309,v247,v258] .nil .nil) .nil)) (.node [v246,v242,v244,v247] (.node [v310,v242,v244,v247,v258] (.node [v283,v246,v242,v244,v247] .nil .nil) .nil) (.node [v246,v242,v244,v247,v260] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lllr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lllr = true := by decide +kernel
def tree_eaa8a880_4lll : BinaryTree (List W) := .node [v288,v242,v311,v247,v245] tree_eaa8a880_4llll tree_eaa8a880_4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lll = true := by
  change (_ && everyKey _ tree_eaa8a880_4llll && everyKey _ tree_eaa8a880_4lllr) = true
  rw [ok_tree_eaa8a880_4llll, ok_tree_eaa8a880_4lllr]
  decide +kernel
def tree_eaa8a880_4llrl : BinaryTree (List W) := (.node [v312,v244,v247,v245,v258] (.node [v313,v247,v314,v245,v258] (.node [v315,v316,v242,v245,v258] (.node [v246,v242,v244,v247,v317] (.node [v246,v242,v244,v247,v258] .nil .nil) .nil) (.node [v313,v265,v247,v245,v258] (.node [v313,v318,v247,v245,v258] .nil .nil) .nil)) (.node [v319,v244,v320,v245,v258] (.node [v319,v244,v321,v245,v258] (.node [v322,v244,v247,v245,v258] .nil .nil) .nil) (.node [v323,v244,v247,v245,v258] (.node [v319,v244,v268,v245,v258] .nil .nil) .nil))) (.node [v324,v244,v325,v245,v258] (.node [v324,v244,v326,v245,v258] (.node [v324,v244,v268,v245,v258] (.node [v324,v327,v244,v245,v258] .nil .nil) .nil) (.node [v324,v244,v328,v245,v258] (.node [v324,v244,v329,v245,v258] .nil .nil) .nil)) (.node [v316,v242,v330,v245,v258] (.node [v316,v242,v331,v245,v258] (.node [v316,v242,v266,v245,v258] .nil .nil) .nil) (.node [v316,v242,v332,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llrl = true := by decide +kernel
def tree_eaa8a880_4llrr : BinaryTree (List W) := (.node [v254,v244,v255,v258,v294] (.node [v333,v334,v247,v245,v258] (.node [v333,v335,v247,v245,v258] (.node [v333,v265,v247,v245,v258] (.node [v336,v244,v247,v245,v258] .nil .nil) .nil) (.node [v333,v337,v247,v245,v258] (.node [v333,v338,v247,v245,v258] .nil .nil) .nil)) (.node [v254,v257,v247,v245,v258] (.node [v254,v297,v244,v258,v294] (.node [v333,v339,v247,v245,v258] .nil .nil) .nil) (.node [v254,v244,v255,v245,v258] (.node [v254,v257,v247,v258,v294] .nil .nil) .nil))) (.node [v254,v244,v247,v258,v340] (.node [v254,v244,v247,v256,v294] (.node [v254,v244,v247,v245,v256] (.node [v254,v244,v247,v267,v258] .nil .nil) .nil) (.node [v254,v244,v247,v258,v341] (.node [v254,v244,v247,v258,v342] .nil .nil) .nil)) (.node [v274,v244,v247,v343,v245] (.node [v254,v299,v247,v258,v294] (.node [v254,v244,v247,v258,v294] .nil .nil) .nil) (.node [v274,v244,v247,v344,v245] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llrr = true := by decide +kernel
def tree_eaa8a880_4llr : BinaryTree (List W) := .node [v316,v242,v345,v245,v258] tree_eaa8a880_4llrl tree_eaa8a880_4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llr = true := by
  change (_ && everyKey _ tree_eaa8a880_4llrl && everyKey _ tree_eaa8a880_4llrr) = true
  rw [ok_tree_eaa8a880_4llrl, ok_tree_eaa8a880_4llrr]
  decide +kernel
def tree_eaa8a880_4ll : BinaryTree (List W) := .node [v246,v242,v244,v247,v245] tree_eaa8a880_4lll tree_eaa8a880_4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4ll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4ll = true := by
  change (_ && everyKey _ tree_eaa8a880_4lll && everyKey _ tree_eaa8a880_4llr) = true
  rw [ok_tree_eaa8a880_4lll, ok_tree_eaa8a880_4llr]
  decide +kernel
def tree_eaa8a880_4lrll : BinaryTree (List W) := (.node [v290,v311,v247,v245,v258] (.node [v346,v244,v247,v245,v258] (.node [v347,v244,v247,v245,v258] (.node [v274,v244,v247,v245,v348] (.node [v274,v244,v247,v245,v349] .nil .nil) .nil) (.node [v350,v244,v247,v245,v258] (.node [v351,v244,v247,v245,v258] .nil .nil) .nil)) (.node [v290,v244,v352,v245,v258] (.node [v290,v289,v247,v245,v258] (.node [v290,v308,v244,v245,v258] .nil .nil) .nil) (.node [v290,v244,v247,v245,v258] (.node [v290,v244,v247,v245,v353] .nil .nil) .nil))) (.node [v298,v244,v247,v245,v354] (.node [v298,v301,v244,v245,v258] (.node [v355,v244,v247,v245,v258] (.node [v356,v244,v247,v245,v258] .nil .nil) .nil) (.node [v298,v244,v300,v245,v258] (.node [v298,v357,v247,v245,v258] .nil .nil) .nil)) (.node [v358,v244,v247,v245,v258] (.node [v298,v305,v247,v245,v258] (.node [v298,v244,v247,v245,v258] .nil .nil) .nil) (.node [v359,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrll = true := by decide +kernel
def tree_eaa8a880_4lrlr : BinaryTree (List W) := (.node [v360,v244,v247,v245,v258] (.node [v251,v244,v247,v260,v317] (.node [v251,v252,v247,v245,v258] (.node [v251,v250,v244,v245,v258] (.node [v361,v244,v247,v245,v258] .nil .nil) .nil) (.node [v251,v244,v247,v260,v245] (.node [v251,v244,v249,v245,v258] .nil .nil) .nil)) (.node [v362,v244,v247,v245,v258] (.node [v251,v253,v247,v245,v258] (.node [v251,v244,v247,v245,v258] .nil .nil) .nil) (.node [v363,v244,v247,v245,v258] (.node [v364,v244,v247,v245,v258] .nil .nil) .nil))) (.node [v242,v365,v266,v245,v258] (.node [v242,v265,v247,v245,v258] (.node [v242,v366,v247,v245,v258] (.node [v367,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v365,v368,v245,v258] (.node [v242,v365,v369,v245,v258] .nil .nil) .nil)) (.node [v242,v279,v243,v244,v245] (.node [v242,v370,v247,v245,v258] (.node [v242,v371,v247,v245,v258] .nil .nil) .nil) (.node [v242,v279,v244,v245,v372] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrlr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrlr = true := by decide +kernel
def tree_eaa8a880_4lrl : BinaryTree (List W) := .node [v373,v244,v247,v245,v258] tree_eaa8a880_4lrll tree_eaa8a880_4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrl = true := by
  change (_ && everyKey _ tree_eaa8a880_4lrll && everyKey _ tree_eaa8a880_4lrlr) = true
  rw [ok_tree_eaa8a880_4lrll, ok_tree_eaa8a880_4lrlr]
  decide +kernel
def tree_eaa8a880_4lrrl : BinaryTree (List W) := (.node [v242,v297,v244,v245,v256] (.node [v242,v374,v244,v245,v258] (.node [v242,v308,v244,v375,v258] (.node [v242,v308,v244,v245,v353] (.node [v242,v308,v289,v245,v258] .nil .nil) .nil) (.node [v242,v308,v244,v376,v258] (.node [v242,v308,v244,v377,v258] .nil .nil) .nil)) (.node [v242,v301,v244,v245,v258] (.node [v242,v301,v244,v245,v354] (.node [v242,v378,v244,v245,v258] .nil .nil) .nil) (.node [v242,v297,v257,v245,v258] (.node [v242,v379,v244,v245,v258] .nil .nil) .nil))) (.node [v242,v250,v253,v245,v258] (.node [v242,v250,v252,v245,v258] (.node [v242,v297,v299,v245,v258] (.node [v242,v297,v244,v245,v258] .nil .nil) .nil) (.node [v242,v250,v244,v245,v258] (.node [v242,v250,v244,v260,v317] .nil .nil) .nil)) (.node [v242,v243,v244,v247,v245] (.node [v242,v243,v244,v276,v245] (.node [v242,v380,v244,v245,v258] .nil .nil) .nil) (.node [v242,v243,v244,v245] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrrl = true := by decide +kernel
def tree_eaa8a880_4lrrr : BinaryTree (List W) := (.node [v242,v278,v247,v245,v381] (.node [v242,v357,v300,v245,v258] (.node [v242,v303,v244,v245,v258] (.node [v242,v303,v244,v247,v258] (.node [v242,v243,v244,v245,v382] .nil .nil) .nil) (.node [v242,v383,v247,v245,v258] (.node [v242,v384,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v278,v262,v247,v245] (.node [v242,v357,v247,v258,v341] (.node [v242,v357,v247,v245,v354] .nil .nil) .nil) (.node [v242,v278,v247,v245,v385] (.node [v242,v278,v247,v386,v245] .nil .nil) .nil))) (.node [v242,v257,v247,v245,v256] (.node [v242,v387,v247,v245,v258] (.node [v242,v388,v247,v245,v258] (.node [v242,v278,v247,v245,v389] .nil .nil) .nil) (.node [v242,v257,v255,v245,v258] (.node [v242,v390,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v391,v247,v245,v258] (.node [v242,v392,v247,v245,v258] (.node [v242,v257,v247,v245,v258] .nil .nil) .nil) (.node [v242,v393,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrrr = true := by decide +kernel
def tree_eaa8a880_4lrr : BinaryTree (List W) := .node [v242,v243,v244,v245,v258] tree_eaa8a880_4lrrl tree_eaa8a880_4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrr = true := by
  change (_ && everyKey _ tree_eaa8a880_4lrrl && everyKey _ tree_eaa8a880_4lrrr) = true
  rw [ok_tree_eaa8a880_4lrrl, ok_tree_eaa8a880_4lrrr]
  decide +kernel
def tree_eaa8a880_4lr : BinaryTree (List W) := .node [v242,v308,v303,v244,v258] tree_eaa8a880_4lrl tree_eaa8a880_4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lr = true := by
  change (_ && everyKey _ tree_eaa8a880_4lrl && everyKey _ tree_eaa8a880_4lrr) = true
  rw [ok_tree_eaa8a880_4lrl, ok_tree_eaa8a880_4lrr]
  decide +kernel
def tree_eaa8a880_4l : BinaryTree (List W) := .node [v274,v244,v247,v245,v394] tree_eaa8a880_4ll tree_eaa8a880_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4l : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4l = true := by
  change (_ && everyKey _ tree_eaa8a880_4ll && everyKey _ tree_eaa8a880_4lr) = true
  rw [ok_tree_eaa8a880_4ll, ok_tree_eaa8a880_4lr]
  decide +kernel
def tree_eaa8a880_4rlll : BinaryTree (List W) := (.node [v242,v395,v247,v245,v258] (.node [v242,v252,v249,v245,v258] (.node [v242,v289,v247,v245,v258] (.node [v242,v289,v247,v245,v353] (.node [v242,v289,v352,v245,v258] .nil .nil) .nil) (.node [v242,v396,v247,v245,v258] (.node [v242,v397,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v252,v247,v245,v258] (.node [v242,v252,v247,v260,v317] (.node [v242,v252,v247,v260,v245] .nil .nil) .nil) (.node [v242,v398,v247,v245,v258] (.node [v242,v399,v247,v245,v258] .nil .nil) .nil))) (.node [v242,v244,v262,v247,v245] (.node [v242,v244,v400,v245,v258] (.node [v242,v401,v247,v245,v258] (.node [v242,v402,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v403,v245,v258] (.node [v242,v244,v404,v245,v258] .nil .nil) .nil)) (.node [v242,v244,v405,v245,v258] (.node [v242,v244,v268,v245,v258] (.node [v242,v244,v309,v247,v258] .nil .nil) .nil) (.node [v242,v244,v352,v245,v353] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlll = true := by decide +kernel
def tree_eaa8a880_4rllr : BinaryTree (List W) := (.node [v242,v244,v406,v245,v258] (.node [v242,v244,v407,v245,v258] (.node [v242,v244,v276,v245,v408] (.node [v242,v244,v276,v245,v409] (.node [v242,v244,v276,v410,v245] .nil .nil) .nil) (.node [v242,v244,v411,v245,v258] (.node [v242,v244,v276,v245,v382] .nil .nil) .nil)) (.node [v242,v244,v255,v245,v256] (.node [v242,v244,v412,v245,v258] (.node [v242,v244,v413,v245,v258] .nil .nil) .nil) (.node [v242,v244,v414,v245,v258] (.node [v242,v244,v255,v245,v258] .nil .nil) .nil))) (.node [v242,v244,v249,v260,v245] (.node [v242,v244,v300,v245,v258] (.node [v242,v244,v300,v245,v354] (.node [v242,v244,v415,v245,v258] .nil .nil) .nil) (.node [v242,v244,v416,v245,v258] (.node [v242,v244,v417,v245,v258] .nil .nil) .nil)) (.node [v242,v244,v418,v245,v258] (.node [v242,v244,v249,v245,v258] (.node [v242,v244,v249,v260,v317] .nil .nil) .nil) (.node [v242,v244,v419,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rllr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rllr = true := by decide +kernel
def tree_eaa8a880_4rll : BinaryTree (List W) := .node [v242,v244,v352,v258,v342] tree_eaa8a880_4rlll tree_eaa8a880_4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rll = true := by
  change (_ && everyKey _ tree_eaa8a880_4rlll && everyKey _ tree_eaa8a880_4rllr) = true
  rw [ok_tree_eaa8a880_4rlll, ok_tree_eaa8a880_4rllr]
  decide +kernel
def tree_eaa8a880_4rlrl : BinaryTree (List W) := (.node [v242,v244,v247,v260,v420] (.node [v242,v244,v247,v421,v245] (.node [v242,v244,v422,v245,v258] (.node [v242,v244,v423,v245,v258] (.node [v242,v244,v424,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v267,v258] (.node [v242,v244,v247,v343,v245] .nil .nil) .nil)) (.node [v242,v244,v247,v425,v245] (.node [v242,v244,v247,v426,v245] (.node [v242,v244,v247,v427,v245] .nil .nil) .nil) (.node [v242,v244,v247,v260,v340] (.node [v242,v244,v247,v428,v245] .nil .nil) .nil))) (.node [v242,v244,v247,v429,v258] (.node [v242,v244,v247,v430,v258] (.node [v242,v244,v247,v260,v317] (.node [v242,v244,v247,v260,v431] .nil .nil) .nil) (.node [v242,v244,v247,v432,v258] (.node [v242,v244,v247,v433,v258] .nil .nil) .nil)) (.node [v242,v244,v247,v245,v434] (.node [v242,v244,v247,v245,v435] (.node [v242,v244,v247,v245,v436] .nil .nil) .nil) (.node [v242,v244,v247,v245,v256] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlrl = true := by decide +kernel
def tree_eaa8a880_4rlrr : BinaryTree (List W) := (.node [v242,v244,v247,v245,v437] (.node [v242,v244,v247,v245,v438] (.node [v242,v244,v247,v245,v439] (.node [v242,v244,v247,v245,v440] (.node [v242,v244,v247,v245,v441] .nil .nil) .nil) (.node [v242,v244,v247,v245,v442] (.node [v242,v244,v247,v245,v354] .nil .nil) .nil)) (.node [v242,v244,v247,v245,v443] (.node [v242,v244,v247,v245,v444] (.node [v242,v244,v247,v245,v353] .nil .nil) .nil) (.node [v242,v244,v247,v245,v445] (.node [v242,v244,v247,v245,v446] .nil .nil) .nil))) (.node [v242,v244,v247,v245,v447] (.node [v242,v244,v247,v245,v448] (.node [v242,v244,v247,v245,v449] (.node [v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v450] (.node [v242,v244,v247,v245,v451] .nil .nil) .nil)) (.node [v242,v244,v247,v245,v452] (.node [v242,v244,v247,v245,v453] (.node [v242,v244,v247,v245,v454] .nil .nil) .nil) (.node [v242,v244,v247,v245,v455] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlrr = true := by decide +kernel
def tree_eaa8a880_4rlr : BinaryTree (List W) := .node [v242,v244,v247,v245,v456] tree_eaa8a880_4rlrl tree_eaa8a880_4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlr = true := by
  change (_ && everyKey _ tree_eaa8a880_4rlrl && everyKey _ tree_eaa8a880_4rlrr) = true
  rw [ok_tree_eaa8a880_4rlrl, ok_tree_eaa8a880_4rlrr]
  decide +kernel
def tree_eaa8a880_4rl : BinaryTree (List W) := .node [v242,v244,v457,v245,v258] tree_eaa8a880_4rll tree_eaa8a880_4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rl = true := by
  change (_ && everyKey _ tree_eaa8a880_4rll && everyKey _ tree_eaa8a880_4rlr) = true
  rw [ok_tree_eaa8a880_4rll, ok_tree_eaa8a880_4rlr]
  decide +kernel
def tree_eaa8a880_4rrll : BinaryTree (List W) := (.node [v242,v458,v247,v245,v258] (.node [v242,v244,v459,v245,v258] (.node [v242,v244,v460,v245,v258] (.node [v242,v244,v461,v245,v258] (.node [v242,v244,v462,v245,v258] .nil .nil) .nil) (.node [v242,v244,v463,v245,v258] (.node [v242,v244,v464,v245,v258] .nil .nil) .nil)) (.node [v242,v244,v465,v245,v258] (.node [v242,v244,v466,v245,v258] (.node [v242,v244,v266,v245,v258] .nil .nil) .nil) (.node [v242,v467,v247,v245,v258] (.node [v242,v468,v247,v245,v258] .nil .nil) .nil))) (.node [v242,v368,v266,v245,v258] (.node [v242,v469,v247,v245,v258] (.node [v242,v470,v247,v245,v258] (.node [v242,v471,v247,v245,v258] .nil .nil) .nil) (.node [v242,v368,v472,v245,v258] (.node [v242,v473,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v305,v309,v247,v258] (.node [v242,v281,v247,v245,v474] (.node [v242,v281,v262,v247,v245] .nil .nil) .nil) (.node [v242,v305,v300,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrll = true := by decide +kernel
def tree_eaa8a880_4rrlr : BinaryTree (List W) := (.node [v242,v253,v249,v245,v258] (.node [v242,v299,v255,v245,v258] (.node [v242,v305,v247,v475,v258] (.node [v242,v305,v247,v476,v258] (.node [v242,v305,v247,v477,v258] .nil .nil) .nil) (.node [v242,v478,v247,v245,v258] (.node [v242,v479,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v480,v247,v245,v258] (.node [v242,v299,v247,v245,v258] (.node [v242,v299,v247,v245,v256] .nil .nil) .nil) (.node [v242,v311,v247,v245,v258] (.node [v242,v311,v247,v245,v353] .nil .nil) .nil))) (.node [v242,v262,v247,v245,v389] (.node [v242,v481,v247,v245,v258] (.node [v242,v253,v247,v245,v258] (.node [v242,v253,v247,v260,v317] .nil .nil) .nil) (.node [v242,v262,v247,v245,v258] (.node [v242,v262,v247,v245] .nil .nil) .nil)) (.node [v242,v247,v482,v245,v258] (.node [v242,v247,v266,v245,v258] (.node [v242,v309,v247,v245,v258] .nil .nil) .nil) (.node [v242,v247,v483,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrlr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrlr = true := by decide +kernel
def tree_eaa8a880_4rrl : BinaryTree (List W) := .node [v242,v305,v247,v245,v354] tree_eaa8a880_4rrll tree_eaa8a880_4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrl = true := by
  change (_ && everyKey _ tree_eaa8a880_4rrll && everyKey _ tree_eaa8a880_4rrlr) = true
  rw [ok_tree_eaa8a880_4rrll, ok_tree_eaa8a880_4rrlr]
  decide +kernel
def tree_eaa8a880_4rrrl : BinaryTree (List W) := (.node [v301,v244,v307,v245,v258] (.node [v484,v244,v247,v245,v258] (.node [v485,v244,v247,v245,v258] (.node [v486,v244,v247,v245,v258] (.node [v242,v266,v245,v258] .nil .nil) .nil) (.node [v487,v244,v247,v245,v258] (.node [v488,v244,v247,v245,v258] .nil .nil) .nil)) (.node [v265,v244,v247,v245,v258] (.node [v318,v247,v489,v245,v258] (.node [v318,v265,v247,v245,v258] .nil .nil) .nil) (.node [v265,v247,v245,v258] (.node [v265,v334,v247,v245,v258] .nil .nil) .nil))) (.node [v244,v490,v247,v245,v258] (.node [v289,v247,v296,v245,v258] (.node [v257,v247,v491,v245,v258] (.node [v250,v244,v248,v245,v258] .nil .nil) .nil) (.node [v244,v492,v247,v245,v258] (.node [v252,v247,v248,v245,v258] .nil .nil) .nil)) (.node [v244,v268,v247,v245,v258] (.node [v244,v320,v493,v245,v258] (.node [v244,v320,v268,v245,v258] .nil .nil) .nil) (.node [v244,v268,v325,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrrl = true := by decide +kernel
def tree_eaa8a880_4rrrr : BinaryTree (List W) := (.node [v244,v247,v307,v245,v258] (.node [v244,v247,v343,v245,v258] (.node [v244,v249,v248,v245,v258] (.node [v244,v300,v307,v245,v258] (.node [v244,v255,v491,v245,v258] .nil .nil) .nil) (.node [v244,v247,v494,v245,v258] (.node [v244,v247,v495,v245,v258] .nil .nil) .nil)) (.node [v244,v247,v496,v245,v258] (.node [v244,v247,v491,v245,v256] (.node [v244,v247,v343,v245,v348] .nil .nil) .nil) (.node [v244,v247,v307,v245,v354] (.node [v244,v247,v497,v245,v258] .nil .nil) .nil))) (.node [v244,v247,v498,v245,v258] (.node [v244,v247,v296,v245,v258] (.node [v244,v247,v296,v245,v353] (.node [v244,v247,v499,v245,v258] .nil .nil) .nil) (.node [v244,v247,v248,v245,v258] (.node [v244,v247,v248,v260,v317] .nil .nil) .nil)) (.node [v311,v247,v296,v245,v258] (.node [v244,v247,v267,v258,v294] (.node [v244,v247,v267,v245,v258] .nil .nil) .nil) (.node [v253,v247,v248,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrrr = true := by decide +kernel
def tree_eaa8a880_4rrr : BinaryTree (List W) := .node [v244,v268,v245,v258] tree_eaa8a880_4rrrl tree_eaa8a880_4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrr = true := by
  change (_ && everyKey _ tree_eaa8a880_4rrrl && everyKey _ tree_eaa8a880_4rrrr) = true
  rw [ok_tree_eaa8a880_4rrrl, ok_tree_eaa8a880_4rrrr]
  decide +kernel
def tree_eaa8a880_4rr : BinaryTree (List W) := .node [v242,v266,v345,v245,v258] tree_eaa8a880_4rrl tree_eaa8a880_4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rr = true := by
  change (_ && everyKey _ tree_eaa8a880_4rrl && everyKey _ tree_eaa8a880_4rrr) = true
  rw [ok_tree_eaa8a880_4rrl, ok_tree_eaa8a880_4rrr]
  decide +kernel
def tree_eaa8a880_4r : BinaryTree (List W) := .node [v242,v244,v500,v245,v258] tree_eaa8a880_4rl tree_eaa8a880_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4r : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4r = true := by
  change (_ && everyKey _ tree_eaa8a880_4rl && everyKey _ tree_eaa8a880_4rr) = true
  rw [ok_tree_eaa8a880_4rl, ok_tree_eaa8a880_4rr]
  decide +kernel
def tree_eaa8a880_4 : BinaryTree (List W) := .node [v242,v501,v247,v245,v258] tree_eaa8a880_4l tree_eaa8a880_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4 : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4 = true := by
  change (_ && everyKey _ tree_eaa8a880_4l && everyKey _ tree_eaa8a880_4r) = true
  rw [ok_tree_eaa8a880_4l, ok_tree_eaa8a880_4r]
  decide +kernel
theorem closed_eaa8a880_4 : Closed 4 tree_eaa8a880_4 := closed_next 3 (by decide) tree_eaa8a880_4 tree_eaa8a880_3 closed_eaa8a880_3 ok_tree_eaa8a880_4
def tree_eaa8a880_5lllll : BinaryTree (List W) := (.node [v502,v242,v244,v247,v245,v258] (.node [v503,v242,v244,v247,v245,v258] (.node [v504,v242,v244,v247,v245,v258] (.node [v505,v242,v244,v247,v245,v258] (.node [v506,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v507,v242,v244,v247,v245,v258] .nil .nil)) (.node [v508,v242,v244,v247,v245,v258] (.node [v509,v242,v244,v247,v245,v258] .nil .nil) (.node [v510,v242,v244,v247,v245,v258] .nil .nil))) (.node [v511,v242,v244,v247,v245,v258] (.node [v512,v242,v244,v247,v245,v258] (.node [v513,v242,v244,v247,v245,v258] (.node [v514,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v515,v242,v244,v247,v245,v258] .nil .nil)) (.node [v277,v242,v244,v247,v245,v258] (.node [v516,v242,v244,v247,v245,v258] .nil .nil) (.node [v517,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllll = true := by decide +kernel
def tree_eaa8a880_5llllr : BinaryTree (List W) := (.node [v518,v242,v244,v247,v260,v245] (.node [v519,v242,v244,v247,v245,v258] (.node [v275,v242,v244,v247,v245,v258] (.node [v520,v242,v244,v247,v245,v258] (.node [v521,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v522,v242,v244,v247,v245,v258] .nil .nil)) (.node [v518,v274,v244,v247,v245,v258] (.node [v518,v270,v242,v244,v247,v245] .nil .nil) (.node [v518,v242,v244,v247,v523,v245] .nil .nil))) (.node [v524,v242,v244,v247,v245,v258] (.node [v518,v242,v244,v247,v245,v348] (.node [v518,v242,v244,v247,v245,v258] .nil .nil) (.node [v518,v244,v247,v523,v245,v258] .nil .nil)) (.node [v273,v242,v244,v247,v245,v258] (.node [v525,v242,v244,v247,v245,v258] .nil .nil) (.node [v526,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llllr = true := by decide +kernel
def tree_eaa8a880_5llll : BinaryTree (List W) := .node [v527,v242,v244,v247,v245,v258] tree_eaa8a880_5lllll tree_eaa8a880_5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llll = true := by
  change (_ && everyKey _ tree_eaa8a880_5lllll && everyKey _ tree_eaa8a880_5llllr) = true
  rw [ok_tree_eaa8a880_5lllll, ok_tree_eaa8a880_5llllr]
  decide +kernel
def tree_eaa8a880_5lllrl : BinaryTree (List W) := (.node [v528,v242,v244,v247,v245,v258] (.node [v271,v242,v244,v276,v245,v258] (.node [v271,v242,v279,v244,v245] (.node [v271,v242,v279,v244,v247,v245] (.node [v271,v270,v242,v244,v247,v245] .nil .nil) .nil) (.node [v271,v242,v279,v244,v245,v258] .nil .nil)) (.node [v271,v242,v244,v247,v245,v258] (.node [v271,v242,v244,v247,v260,v245] .nil .nil) (.node [v271,v242,v244,v247,v245,v382] .nil .nil))) (.node [v280,v242,v244,v247,v245,v258] (.node [v280,v242,v244,v281,v247,v245] (.node [v280,v242,v278,v247,v245,v258] (.node [v280,v270,v242,v244,v247,v245] .nil .nil) .nil) (.node [v280,v242,v244,v247,v260,v245] .nil .nil)) (.node [v280,v242,v281,v247,v245] (.node [v280,v242,v244,v247,v245,v389] .nil .nil) (.node [v280,v242,v281,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllrl = true := by decide +kernel
def tree_eaa8a880_5lllrr : BinaryTree (List W) := (.node [v270,v242,v244,v247,v245,v258] (.node [v270,v274,v242,v244,v247,v245] (.node [v270,v283,v242,v244,v247,v245] (.node [v270,v283,v242,v244,v247] (.node [v529,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v270,v283,v242,v244,v247,v258] .nil .nil)) (.node [v270,v242,v244,v276,v247,v245] (.node [v270,v242,v278,v244,v247,v245] .nil .nil) (.node [v270,v242,v244,v247,v260,v258] .nil .nil))) (.node [v288,v242,v244,v247,v245,v258] (.node [v530,v242,v244,v247,v245,v258] (.node [v270,v242,v244,v247,v245,v317] .nil .nil) (.node [v288,v242,v244,v247,v245] .nil .nil)) (.node [v293,v242,v244,v247,v245] (.node [v288,v242,v244,v247,v245,v531] .nil .nil) (.node [v293,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllrr = true := by decide +kernel
def tree_eaa8a880_5lllr : BinaryTree (List W) := .node [v532,v242,v244,v247,v245,v258] tree_eaa8a880_5lllrl tree_eaa8a880_5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lllrl && everyKey _ tree_eaa8a880_5lllrr) = true
  rw [ok_tree_eaa8a880_5lllrl, ok_tree_eaa8a880_5lllrr]
  decide +kernel
def tree_eaa8a880_5lll : BinaryTree (List W) := .node [v533,v242,v244,v247,v245,v258] tree_eaa8a880_5llll tree_eaa8a880_5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lll = true := by
  change (_ && everyKey _ tree_eaa8a880_5llll && everyKey _ tree_eaa8a880_5lllr) = true
  rw [ok_tree_eaa8a880_5llll, ok_tree_eaa8a880_5lllr]
  decide +kernel
def tree_eaa8a880_5llrll : BinaryTree (List W) := (.node [v534,v242,v244,v247,v245,v258] (.node [v535,v242,v244,v247,v245,v258] (.node [v292,v242,v244,v247,v245,v536] (.node [v292,v242,v244,v247,v245,v258] (.node [v292,v242,v244,v247,v245] .nil .nil) .nil) (.node [v537,v242,v244,v247,v245,v258] .nil .nil)) (.node [v534,v254,v244,v247,v245,v258] (.node [v538,v242,v244,v247,v245,v258] .nil .nil) (.node [v534,v242,v244,v247,v491,v258] .nil .nil))) (.node [v304,v242,v357,v247,v245,v258] (.node [v539,v242,v244,v247,v245,v258] (.node [v534,v244,v247,v491,v245,v258] (.node [v534,v242,v244,v247,v258,v294] .nil .nil) .nil) (.node [v540,v242,v244,v247,v245,v258] .nil .nil)) (.node [v304,v242,v244,v247,v245,v258] (.node [v304,v242,v244,v305,v247,v258] .nil .nil) (.node [v304,v242,v244,v247,v258,v536] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrll = true := by decide +kernel
def tree_eaa8a880_5llrlr : BinaryTree (List W) := (.node [v302,v242,v244,v247,v258,v531] (.node [v302,v242,v308,v244,v245,v258] (.node [v541,v242,v244,v247,v245,v258] (.node [v542,v242,v244,v247,v245,v258] (.node [v304,v242,v305,v247,v258] .nil .nil) .nil) (.node [v302,v242,v308,v244,v247,v258] .nil .nil)) (.node [v302,v242,v244,v352,v245,v258] (.node [v302,v242,v308,v244,v258] .nil .nil) (.node [v302,v242,v244,v247,v245,v258] .nil .nil))) (.node [v283,v242,v244,v247,v258,v317] (.node [v283,v242,v244,v247,v260,v245] (.node [v543,v242,v244,v247,v245,v258] .nil .nil) (.node [v283,v242,v244,v247,v245,v258] .nil .nil)) (.node [v544,v242,v244,v247,v245,v258] (.node [v545,v242,v244,v247,v245,v258] .nil .nil) (.node [v546,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrlr = true := by decide +kernel
def tree_eaa8a880_5llrl : BinaryTree (List W) := .node [v304,v242,v305,v247,v245,v258] tree_eaa8a880_5llrll tree_eaa8a880_5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5llrll && everyKey _ tree_eaa8a880_5llrlr) = true
  rw [ok_tree_eaa8a880_5llrll, ok_tree_eaa8a880_5llrlr]
  decide +kernel
def tree_eaa8a880_5llrrl : BinaryTree (List W) := (.node [v547,v242,v244,v247,v245,v258] (.node [v548,v242,v244,v247,v245,v258] (.node [v549,v242,v244,v247,v245,v258] (.node [v550,v242,v244,v247,v245,v258] (.node [v551,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v552,v242,v244,v247,v245,v258] .nil .nil)) (.node [v553,v242,v244,v247,v245,v258] (.node [v315,v242,v244,v247,v245,v258] .nil .nil) (.node [v554,v242,v244,v247,v245,v258] .nil .nil))) (.node [v313,v242,v334,v247,v245,v258] (.node [v313,v242,v357,v247,v245,v258] (.node [v313,v242,v318,v247,v245,v258] (.node [v313,v333,v244,v247,v245,v258] .nil .nil) .nil) (.node [v313,v242,v244,v247,v245,v258] .nil .nil)) (.node [v313,v318,v244,v247,v245,v258] (.node [v313,v242,v305,v247,v245,v258] .nil .nil) (.node [v313,v318,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrrl = true := by decide +kernel
def tree_eaa8a880_5llrrr : BinaryTree (List W) := (.node [v319,v242,v244,v247,v245,v258] (.node [v319,v324,v244,v247,v245,v258] (.node [v555,v242,v244,v247,v245,v258] (.node [v556,v242,v244,v247,v245,v258] (.node [v557,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v558,v242,v244,v247,v245,v258] .nil .nil)) (.node [v319,v242,v244,v320,v245,v258] (.node [v319,v242,v308,v244,v245,v258] .nil .nil) (.node [v319,v242,v244,v352,v245,v258] .nil .nil))) (.node [v559,v242,v244,v247,v245,v258] (.node [v319,v244,v320,v247,v245,v258] (.node [v319,v242,v244,v325,v245,v258] .nil .nil) (.node [v319,v244,v320,v245,v258] .nil .nil)) (.node [v560,v242,v244,v247,v245,v258] (.node [v561,v242,v244,v247,v245,v258] .nil .nil) (.node [v562,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrrr = true := by decide +kernel
def tree_eaa8a880_5llrr : BinaryTree (List W) := .node [v563,v242,v244,v247,v245,v258] tree_eaa8a880_5llrrl tree_eaa8a880_5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5llrrl && everyKey _ tree_eaa8a880_5llrrr) = true
  rw [ok_tree_eaa8a880_5llrrl, ok_tree_eaa8a880_5llrrr]
  decide +kernel
def tree_eaa8a880_5llr : BinaryTree (List W) := .node [v564,v242,v244,v247,v245,v258] tree_eaa8a880_5llrl tree_eaa8a880_5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llr = true := by
  change (_ && everyKey _ tree_eaa8a880_5llrl && everyKey _ tree_eaa8a880_5llrr) = true
  rw [ok_tree_eaa8a880_5llrl, ok_tree_eaa8a880_5llrr]
  decide +kernel
def tree_eaa8a880_5ll : BinaryTree (List W) := .node [v293,v242,v244,v247,v245,v294] tree_eaa8a880_5lll tree_eaa8a880_5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5ll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5ll = true := by
  change (_ && everyKey _ tree_eaa8a880_5lll && everyKey _ tree_eaa8a880_5llr) = true
  rw [ok_tree_eaa8a880_5lll, ok_tree_eaa8a880_5llr]
  decide +kernel
def tree_eaa8a880_5lrlll : BinaryTree (List W) := (.node [v324,v244,v247,v491,v245,v258] (.node [v324,v242,v244,v352,v245,v258] (.node [v324,v242,v308,v244,v245,v258] (.node [v324,v254,v244,v247,v245,v258] (.node [v565,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v324,v242,v244,v320,v245,v258] .nil .nil)) (.node [v324,v242,v244,v325,v245,v258] (.node [v324,v242,v244,v247,v245,v258] .nil .nil) (.node [v324,v244,v247,v325,v245,v258] .nil .nil))) (.node [v566,v242,v244,v247,v245,v258] (.node [v567,v242,v244,v247,v245,v258] (.node [v568,v242,v244,v247,v245,v258] (.node [v324,v244,v325,v245,v258] .nil .nil) .nil) (.node [v569,v242,v244,v247,v245,v258] .nil .nil)) (.node [v570,v242,v244,v247,v245,v258] (.node [v571,v242,v244,v247,v245,v258] .nil .nil) (.node [v316,v242,v365,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlll = true := by decide +kernel
def tree_eaa8a880_5lrllr : BinaryTree (List W) := (.node [v572,v242,v244,v247,v245,v258] (.node [v316,v242,v244,v345,v245,v258] (.node [v316,v242,v244,v352,v245,v258] (.node [v316,v242,v244,v368,v245,v258] (.node [v316,v242,v357,v247,v245,v258] .nil .nil) .nil) (.node [v316,v242,v244,v247,v245,v258] .nil .nil)) (.node [v316,v242,v247,v345,v245,v258] (.node [v316,v242,v305,v247,v245,v258] .nil .nil) (.node [v316,v242,v345,v245,v258] .nil .nil))) (.node [v573,v242,v244,v247,v245,v258] (.node [v574,v242,v244,v247,v245,v258] (.node [v575,v242,v244,v247,v245,v258] .nil .nil) (.node [v576,v242,v244,v247,v245,v258] .nil .nil)) (.node [v577,v242,v244,v247,v245,v258] (.node [v578,v242,v244,v247,v245,v258] .nil .nil) (.node [v579,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrllr = true := by decide +kernel
def tree_eaa8a880_5lrll : BinaryTree (List W) := .node [v316,v242,v308,v244,v245,v258] tree_eaa8a880_5lrlll tree_eaa8a880_5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrll = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrlll && everyKey _ tree_eaa8a880_5lrllr) = true
  rw [ok_tree_eaa8a880_5lrlll, ok_tree_eaa8a880_5lrllr]
  decide +kernel
def tree_eaa8a880_5lrlrl : BinaryTree (List W) := (.node [v580,v242,v244,v247,v245,v258] (.node [v333,v242,v305,v247,v245,v258] (.node [v333,v242,v244,v247,v245,v258] (.node [v333,v242,v357,v247,v245,v258] (.node [v333,v242,v318,v247,v245,v258] .nil .nil) .nil) (.node [v333,v242,v334,v247,v245,v258] .nil .nil)) (.node [v333,v244,v247,v491,v245,v258] (.node [v333,v244,v334,v247,v245,v258] .nil .nil) (.node [v333,v334,v247,v245,v258] .nil .nil))) (.node [v581,v242,v244,v247,v245,v258] (.node [v582,v242,v244,v247,v245,v258] (.node [v583,v242,v244,v247,v245,v258] (.node [v584,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v585,v242,v244,v247,v245,v258] .nil .nil)) (.node [v254,v274,v244,v247,v245,v258] (.node [v586,v242,v244,v247,v245,v258] .nil .nil) (.node [v254,v242,v244,v247,v491,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlrl = true := by decide +kernel
def tree_eaa8a880_5lrlrr : BinaryTree (List W) := (.node [v587,v242,v244,v247,v245,v258] (.node [v254,v244,v247,v245,v258,v294] (.node [v254,v244,v320,v247,v245,v258] (.node [v254,v318,v244,v247,v245,v258] (.node [v254,v242,v244,v247,v258,v294] .nil .nil) .nil) (.node [v254,v244,v247,v523,v245,v258] .nil .nil)) (.node [v588,v242,v244,v247,v245,v258] (.node [v254,v244,v247,v258,v294] .nil .nil) (.node [v589,v242,v244,v247,v245,v258] .nil .nil))) (.node [v274,v242,v244,v247,v245,v258] (.node [v274,v242,v244,v247,v523,v245] (.node [v590,v242,v244,v247,v245,v258] .nil .nil) (.node [v274,v242,v244,v247,v260,v245] .nil .nil)) (.node [v274,v244,v247,v491,v245,v258] (.node [v274,v242,v244,v247,v245,v348] .nil .nil) (.node [v274,v244,v247,v245,v258,v348] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlrr = true := by decide +kernel
def tree_eaa8a880_5lrlr : BinaryTree (List W) := .node [v254,v242,v244,v247,v245,v258] tree_eaa8a880_5lrlrl tree_eaa8a880_5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrlrl && everyKey _ tree_eaa8a880_5lrlrr) = true
  rw [ok_tree_eaa8a880_5lrlrl, ok_tree_eaa8a880_5lrlrr]
  decide +kernel
def tree_eaa8a880_5lrl : BinaryTree (List W) := .node [v333,v254,v244,v247,v245,v258] tree_eaa8a880_5lrll tree_eaa8a880_5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrll && everyKey _ tree_eaa8a880_5lrlr) = true
  rw [ok_tree_eaa8a880_5lrll, ok_tree_eaa8a880_5lrlr]
  decide +kernel
def tree_eaa8a880_5lrrll : BinaryTree (List W) := (.node [v290,v244,v247,v245,v258] (.node [v591,v242,v244,v247,v245,v258] (.node [v592,v242,v244,v247,v245,v258] (.node [v593,v242,v244,v247,v245,v258] (.node [v594,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v595,v242,v244,v247,v245,v258] .nil .nil)) (.node [v596,v242,v244,v247,v245,v258] (.node [v597,v242,v244,v247,v245,v258] .nil .nil) (.node [v290,v242,v244,v247,v245,v258] .nil .nil))) (.node [v251,v242,v244,v247,v245,v258] (.node [v298,v244,v247,v245,v258] (.node [v298,v242,v244,v247,v245,v258] (.node [v290,v244,v247,v245,v258,v531] .nil .nil) .nil) (.node [v298,v244,v247,v245,v258,v536] .nil .nil)) (.node [v251,v244,v247,v245,v258,v317] (.node [v251,v244,v247,v245,v258] .nil .nil) (.node [v242,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrll = true := by decide +kernel
def tree_eaa8a880_5lrrlr : BinaryTree (List W) := (.node [v242,v327,v244,v247,v245,v258] (.node [v242,v598,v244,v247,v245,v258] (.node [v242,v599,v244,v247,v245,v258] (.node [v242,v600,v244,v247,v245,v258] (.node [v242,v601,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v602,v244,v247,v245,v258] .nil .nil)) (.node [v242,v603,v244,v247,v245,v258] (.node [v242,v604,v244,v247,v245,v258] .nil .nil) (.node [v242,v605,v244,v247,v245,v258] .nil .nil))) (.node [v242,v606,v244,v247,v245,v258] (.node [v242,v607,v244,v247,v245,v258] (.node [v242,v608,v244,v247,v245,v258] .nil .nil) (.node [v242,v318,v244,v247,v245,v258] .nil .nil)) (.node [v242,v609,v244,v247,v245,v258] (.node [v242,v610,v244,v247,v245,v258] .nil .nil) (.node [v242,v611,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrlr = true := by decide +kernel
def tree_eaa8a880_5lrrl : BinaryTree (List W) := .node [v242,v612,v244,v247,v245,v258] tree_eaa8a880_5lrrll tree_eaa8a880_5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrrll && everyKey _ tree_eaa8a880_5lrrlr) = true
  rw [ok_tree_eaa8a880_5lrrll, ok_tree_eaa8a880_5lrrlr]
  decide +kernel
def tree_eaa8a880_5lrrrl : BinaryTree (List W) := (.node [v242,v613,v244,v247,v245,v258] (.node [v242,v365,v368,v247,v245,v258] (.node [v242,v365,v244,v247,v245,v258] (.node [v242,v365,v244,v352,v245,v258] (.node [v242,v365,v244,v368,v245,v258] .nil .nil) .nil) (.node [v242,v365,v244,v345,v245,v258] .nil .nil)) (.node [v242,v614,v244,v247,v245,v258] (.node [v242,v365,v368,v245,v258] .nil .nil) (.node [v242,v615,v244,v247,v245,v258] .nil .nil))) (.node [v242,v279,v244,v247,v245,v258] (.node [v242,v279,v244,v352,v245,v258] (.node [v242,v279,v308,v244,v245,v258] (.node [v242,v616,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v279,v244,v276,v247,v245] .nil .nil)) (.node [v242,v617,v244,v247,v245,v258] (.node [v242,v279,v244,v245,v258,v382] .nil .nil) (.node [v242,v618,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrrl = true := by decide +kernel
def tree_eaa8a880_5lrrrr : BinaryTree (List W) := (.node [v242,v297,v244,v245,v258] (.node [v242,v301,v244,v245,v258] (.node [v242,v308,v244,v245,v258,v531] (.node [v242,v308,v244,v247,v245,v258] (.node [v242,v308,v244,v276,v245,v258] .nil .nil) .nil) (.node [v242,v301,v244,v247,v245,v258] .nil .nil)) (.node [v242,v619,v244,v247,v245,v258] (.node [v242,v301,v244,v245,v258,v536] .nil .nil) (.node [v242,v297,v244,v247,v245,v258] .nil .nil))) (.node [v242,v250,v244,v245,v258,v317] (.node [v242,v250,v244,v247,v245,v258] (.node [v242,v297,v244,v245,v258,v294] .nil .nil) (.node [v242,v250,v244,v245,v258] .nil .nil)) (.node [v242,v620,v244,v247,v245,v258] (.node [v242,v621,v244,v247,v245,v258] .nil .nil) (.node [v242,v622,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrrr = true := by decide +kernel
def tree_eaa8a880_5lrrr : BinaryTree (List W) := .node [v242,v308,v244,v352,v247,v258] tree_eaa8a880_5lrrrl tree_eaa8a880_5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrrrl && everyKey _ tree_eaa8a880_5lrrrr) = true
  rw [ok_tree_eaa8a880_5lrrrl, ok_tree_eaa8a880_5lrrrr]
  decide +kernel
def tree_eaa8a880_5lrr : BinaryTree (List W) := .node [v242,v365,v308,v244,v245,v258] tree_eaa8a880_5lrrl tree_eaa8a880_5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrrl && everyKey _ tree_eaa8a880_5lrrr) = true
  rw [ok_tree_eaa8a880_5lrrl, ok_tree_eaa8a880_5lrrr]
  decide +kernel
def tree_eaa8a880_5lr : BinaryTree (List W) := .node [v274,v244,v247,v245,v348] tree_eaa8a880_5lrl tree_eaa8a880_5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrl && everyKey _ tree_eaa8a880_5lrr) = true
  rw [ok_tree_eaa8a880_5lrl, ok_tree_eaa8a880_5lrr]
  decide +kernel
def tree_eaa8a880_5l : BinaryTree (List W) := .node [v623,v242,v244,v247,v245,v258] tree_eaa8a880_5ll tree_eaa8a880_5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5l : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5l = true := by
  change (_ && everyKey _ tree_eaa8a880_5ll && everyKey _ tree_eaa8a880_5lr) = true
  rw [ok_tree_eaa8a880_5ll, ok_tree_eaa8a880_5lr]
  decide +kernel
def tree_eaa8a880_5rllll : BinaryTree (List W) := (.node [v242,v624,v244,v247,v245,v258] (.node [v242,v357,v244,v247,v258,v536] (.node [v242,v357,v244,v305,v247,v258] (.node [v242,v357,v278,v247,v245,v258] (.node [v242,v625,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v357,v244,v247,v245,v258] .nil .nil)) (.node [v242,v357,v281,v247,v245,v258] (.node [v242,v357,v368,v247,v245,v258] .nil .nil) (.node [v242,v357,v247,v245,v258,v536] .nil .nil))) (.node [v242,v278,v244,v247,v260,v245] (.node [v242,v626,v244,v247,v245,v258] (.node [v242,v627,v244,v247,v245,v258] (.node [v242,v628,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v278,v244,v281,v247,v245] .nil .nil)) (.node [v242,v278,v244,v247,v245,v389] (.node [v242,v278,v244,v247,v245,v258] .nil .nil) (.node [v242,v278,v305,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllll = true := by decide +kernel
def tree_eaa8a880_5rlllr : BinaryTree (List W) := (.node [v242,v257,v247,v245,v258] (.node [v242,v629,v244,v247,v245,v258] (.node [v242,v630,v244,v247,v245,v258] (.node [v242,v631,v244,v247,v245,v258] (.node [v242,v278,v247,v245,v389] .nil .nil) .nil) (.node [v242,v632,v244,v247,v245,v258] .nil .nil)) (.node [v242,v633,v244,v247,v245,v258] (.node [v242,v634,v244,v247,v245,v258] .nil .nil) (.node [v242,v257,v244,v247,v245,v258] .nil .nil))) (.node [v242,v289,v247,v245,v258,v531] (.node [v242,v289,v244,v247,v245,v258] (.node [v242,v257,v247,v245,v258,v294] .nil .nil) (.node [v242,v289,v247,v245,v258] .nil .nil)) (.node [v242,v252,v247,v245,v258] (.node [v242,v252,v244,v247,v245,v258] .nil .nil) (.node [v242,v252,v247,v245,v258,v317] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlllr = true := by decide +kernel
def tree_eaa8a880_5rlll : BinaryTree (List W) := .node [v242,v278,v247,v245,v258,v389] tree_eaa8a880_5rllll tree_eaa8a880_5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlll = true := by
  change (_ && everyKey _ tree_eaa8a880_5rllll && everyKey _ tree_eaa8a880_5rlllr) = true
  rw [ok_tree_eaa8a880_5rllll, ok_tree_eaa8a880_5rlllr]
  decide +kernel
def tree_eaa8a880_5rllrl : BinaryTree (List W) := (.node [v242,v244,v635,v247,v245,v258] (.node [v242,v244,v636,v247,v245,v258] (.node [v242,v244,v637,v247,v245,v258] (.node [v242,v244,v638,v247,v245,v258] (.node [v242,v244,v639,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v640,v247,v245,v258] .nil .nil)) (.node [v242,v244,v641,v247,v245,v258] (.node [v242,v244,v282,v247,v245,v258] .nil .nil) (.node [v242,v244,v642,v247,v245,v258] .nil .nil))) (.node [v242,v244,v335,v247,v245,v258] (.node [v242,v244,v321,v247,v245,v258] (.node [v242,v244,v643,v247,v245,v258] (.node [v242,v244,v644,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v645,v247,v245,v258] .nil .nil)) (.node [v242,v244,v646,v247,v245,v258] (.node [v242,v244,v647,v247,v245,v258] .nil .nil) (.node [v242,v244,v648,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllrl = true := by decide +kernel
def tree_eaa8a880_5rllrr : BinaryTree (List W) := (.node [v242,v244,v649,v247,v245,v258] (.node [v242,v244,v337,v247,v245,v258] (.node [v242,v244,v650,v247,v245,v258] (.node [v242,v244,v651,v247,v245,v258] (.node [v242,v244,v369,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v338,v247,v245,v258] .nil .nil)) (.node [v242,v244,v652,v247,v245,v258] (.node [v242,v244,v334,v247,v245,v258] .nil .nil) (.node [v242,v244,v339,v247,v245,v258] .nil .nil))) (.node [v242,v244,v653,v247,v245,v258] (.node [v242,v244,v654,v247,v245,v258] (.node [v242,v244,v655,v247,v245,v258] .nil .nil) (.node [v242,v244,v368,v247,v245,v258] .nil .nil)) (.node [v242,v244,v656,v247,v245,v258] (.node [v242,v244,v657,v247,v245,v258] .nil .nil) (.node [v242,v244,v658,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllrr = true := by decide +kernel
def tree_eaa8a880_5rllr : BinaryTree (List W) := .node [v242,v244,v659,v247,v245,v258] tree_eaa8a880_5rllrl tree_eaa8a880_5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rllrl && everyKey _ tree_eaa8a880_5rllrr) = true
  rw [ok_tree_eaa8a880_5rllrl, ok_tree_eaa8a880_5rllrr]
  decide +kernel
def tree_eaa8a880_5rll : BinaryTree (List W) := .node [v242,v244,v244,v247,v245,v258] tree_eaa8a880_5rlll tree_eaa8a880_5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rll = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlll && everyKey _ tree_eaa8a880_5rllr) = true
  rw [ok_tree_eaa8a880_5rlll, ok_tree_eaa8a880_5rllr]
  decide +kernel
def tree_eaa8a880_5rlrll : BinaryTree (List W) := (.node [v242,v244,v311,v247,v245,v258] (.node [v242,v244,v281,v247,v245,v258] (.node [v242,v244,v660,v247,v245,v258] (.node [v242,v244,v661,v247,v245,v258] (.node [v242,v244,v662,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v663,v247,v245,v258] .nil .nil)) (.node [v242,v244,v305,v247,v245,v258] (.node [v242,v244,v664,v247,v245,v258] .nil .nil) (.node [v242,v244,v299,v247,v245,v258] .nil .nil))) (.node [v242,v244,v665,v247,v245,v258] (.node [v242,v244,v253,v247,v245,v258] (.node [v242,v244,v666,v247,v245,v258] (.node [v242,v244,v667,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v668,v247,v245,v258] .nil .nil)) (.node [v242,v244,v669,v247,v245,v258] (.node [v242,v244,v670,v247,v245,v258] .nil .nil) (.node [v242,v244,v352,v276,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrll = true := by decide +kernel
def tree_eaa8a880_5rlrlr : BinaryTree (List W) := (.node [v242,v244,v276,v247,v245,v382] (.node [v242,v244,v671,v247,v245,v258] (.node [v242,v244,v672,v247,v245,v258] (.node [v242,v244,v352,v245,v258,v531] (.node [v242,v244,v352,v247,v258,v531] .nil .nil) .nil) (.node [v242,v244,v673,v247,v245,v258] .nil .nil)) (.node [v242,v244,v276,v247,v260,v245] (.node [v242,v244,v674,v247,v245,v258] .nil .nil) (.node [v242,v244,v276,v247,v245,v258] .nil .nil))) (.node [v242,v244,v675,v247,v245,v258] (.node [v242,v244,v276,v245,v382] (.node [v242,v244,v276,v245,v258,v382] .nil .nil) (.node [v242,v244,v676,v247,v245,v258] .nil .nil)) (.node [v242,v244,v677,v247,v245,v258] (.node [v242,v244,v678,v247,v245,v258] .nil .nil) (.node [v242,v244,v679,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrlr = true := by decide +kernel
def tree_eaa8a880_5rlrl : BinaryTree (List W) := .node [v242,v244,v352,v247,v245,v258] tree_eaa8a880_5rlrll tree_eaa8a880_5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlrll && everyKey _ tree_eaa8a880_5rlrlr) = true
  rw [ok_tree_eaa8a880_5rlrll, ok_tree_eaa8a880_5rlrlr]
  decide +kernel
def tree_eaa8a880_5rlrrl : BinaryTree (List W) := (.node [v242,v244,v249,v245,v258] (.node [v242,v244,v300,v247,v245,v258] (.node [v242,v244,v255,v245,v258] (.node [v242,v244,v255,v247,v245,v258] (.node [v242,v244,v680,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v255,v245,v258,v294] .nil .nil)) (.node [v242,v244,v300,v245,v258,v536] (.node [v242,v244,v300,v245,v258] .nil .nil) (.node [v242,v244,v249,v247,v245,v258] .nil .nil))) (.node [v242,v244,v247,v681,v245,v258] (.node [v242,v244,v247,v682,v245,v258] (.node [v242,v244,v247,v247,v245,v258] (.node [v242,v244,v249,v245,v258,v317] .nil .nil) .nil) (.node [v242,v244,v247,v683,v245,v258] .nil .nil)) (.node [v242,v244,v247,v684,v245,v258] (.node [v242,v244,v247,v685,v245,v258] .nil .nil) (.node [v242,v244,v247,v272,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrrl = true := by decide +kernel
def tree_eaa8a880_5rlrrr : BinaryTree (List W) := (.node [v242,v244,v247,v314,v245,v258] (.node [v242,v244,v247,v686,v245,v258] (.node [v242,v244,v247,v472,v245,v258] (.node [v242,v244,v247,v687,v245,v258] (.node [v242,v244,v247,v688,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v689,v245,v258] .nil .nil)) (.node [v242,v244,v247,v690,v245,v258] (.node [v242,v244,v247,v691,v245,v258] .nil .nil) (.node [v242,v244,v247,v692,v245,v258] .nil .nil))) (.node [v242,v244,v247,v693,v245,v258] (.node [v242,v244,v247,v326,v245,v258] (.node [v242,v244,v247,v694,v245,v258] .nil .nil) (.node [v242,v244,v247,v695,v245,v258] .nil .nil)) (.node [v242,v244,v247,v329,v245,v258] (.node [v242,v244,v247,v696,v245,v258] .nil .nil) (.node [v242,v244,v247,v328,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrrr = true := by decide +kernel
def tree_eaa8a880_5rlrr : BinaryTree (List W) := .node [v242,v244,v247,v697,v245,v258] tree_eaa8a880_5rlrrl tree_eaa8a880_5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlrrl && everyKey _ tree_eaa8a880_5rlrrr) = true
  rw [ok_tree_eaa8a880_5rlrrl, ok_tree_eaa8a880_5rlrrr]
  decide +kernel
def tree_eaa8a880_5rlr : BinaryTree (List W) := .node [v242,v244,v698,v247,v245,v258] tree_eaa8a880_5rlrl tree_eaa8a880_5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlrl && everyKey _ tree_eaa8a880_5rlrr) = true
  rw [ok_tree_eaa8a880_5rlrl, ok_tree_eaa8a880_5rlrr]
  decide +kernel
def tree_eaa8a880_5rl : BinaryTree (List W) := .node [v242,v244,v320,v247,v245,v258] tree_eaa8a880_5rll tree_eaa8a880_5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rll && everyKey _ tree_eaa8a880_5rlr) = true
  rw [ok_tree_eaa8a880_5rll, ok_tree_eaa8a880_5rlr]
  decide +kernel
def tree_eaa8a880_5rrlll : BinaryTree (List W) := (.node [v242,v244,v247,v248,v245,v258] (.node [v242,v244,v247,v699,v245,v258] (.node [v242,v244,v247,v491,v245,v258] (.node [v242,v244,v247,v523,v245,v258] (.node [v242,v244,v247,v700,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v701,v245,v258] .nil .nil)) (.node [v242,v244,v247,v296,v245,v258] (.node [v242,v244,v247,v307,v245,v258] .nil .nil) (.node [v242,v244,v247,v702,v245,v258] .nil .nil))) (.node [v242,v244,v247,v703,v245,v258] (.node [v242,v244,v247,v704,v245,v258] (.node [v242,v244,v247,v705,v245,v258] (.node [v242,v244,v247,v706,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v707,v245,v258] .nil .nil)) (.node [v242,v244,v247,v708,v245,v258] (.node [v242,v244,v247,v709,v245,v258] .nil .nil) (.node [v242,v244,v247,v710,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlll = true := by decide +kernel
def tree_eaa8a880_5rrllr : BinaryTree (List W) := (.node [v242,v244,v247,v711,v245,v258] (.node [v242,v244,v247,v712,v245,v258] (.node [v242,v244,v247,v713,v245,v258] (.node [v242,v244,v247,v714,v245,v258] (.node [v242,v244,v247,v715,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v493,v245,v258] .nil .nil)) (.node [v242,v244,v247,v716,v245,v258] (.node [v242,v244,v247,v331,v245,v258] .nil .nil) (.node [v242,v244,v247,v717,v245,v258] .nil .nil))) (.node [v242,v244,v247,v718,v245,v258] (.node [v242,v244,v247,v489,v245,v258] (.node [v242,v244,v247,v719,v245,v258] .nil .nil) (.node [v242,v244,v247,v720,v245,v258] .nil .nil)) (.node [v242,v244,v247,v332,v245,v258] (.node [v242,v244,v247,v330,v245,v258] .nil .nil) (.node [v242,v244,v247,v345,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrllr = true := by decide +kernel
def tree_eaa8a880_5rrll : BinaryTree (List W) := .node [v242,v244,v247,v721,v245,v258] tree_eaa8a880_5rrlll tree_eaa8a880_5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrll = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrlll && everyKey _ tree_eaa8a880_5rrllr) = true
  rw [ok_tree_eaa8a880_5rrlll, ok_tree_eaa8a880_5rrllr]
  decide +kernel
def tree_eaa8a880_5rrlrl : BinaryTree (List W) := (.node [v242,v244,v247,v344,v245,v258] (.node [v242,v244,v247,v722,v245,v258] (.node [v242,v244,v247,v260,v317] (.node [v242,v244,v247,v260,v258,v317] (.node [v242,v244,v247,v260,v245,v317] .nil .nil) .nil) (.node [v242,v244,v247,v723,v245,v258] .nil .nil)) (.node [v242,v244,v247,v724,v245,v258] (.node [v242,v244,v247,v725,v245,v258] .nil .nil) (.node [v242,v244,v247,v726,v245,v258] .nil .nil))) (.node [v242,v244,v247,v245,v285,v258] (.node [v242,v244,v247,v386,v245,v258] (.node [v242,v244,v247,v410,v245,v258] (.node [v242,v244,v247,v727,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v245,v258] .nil .nil)) (.node [v242,v244,v247,v245,v286,v258] (.node [v242,v244,v247,v245,v287,v258] .nil .nil) (.node [v242,v244,v247,v245,v375,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlrl = true := by decide +kernel
def tree_eaa8a880_5rrlrr : BinaryTree (List W) := (.node [v242,v244,v247,v245,v256,v258] (.node [v242,v244,v247,v245,v728,v258] (.node [v242,v244,v247,v245,v476,v258] (.node [v242,v244,v247,v245,v376,v258] (.node [v242,v244,v247,v245,v377,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v475,v258] .nil .nil)) (.node [v242,v244,v247,v245,v729,v258] (.node [v242,v244,v247,v245,v730,v258] .nil .nil) (.node [v242,v244,v247,v245,v256] .nil .nil))) (.node [v242,v244,v247,v245,v354,v536] (.node [v242,v244,v247,v245,v354] (.node [v242,v244,v247,v245,v256,v294] .nil .nil) (.node [v242,v244,v247,v245,v354,v258] .nil .nil)) (.node [v242,v244,v247,v245,v353,v258] (.node [v242,v244,v247,v245,v353] .nil .nil) (.node [v242,v244,v247,v245,v353,v531] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlrr = true := by decide +kernel
def tree_eaa8a880_5rrlr : BinaryTree (List W) := .node [v242,v244,v247,v245,v477,v258] tree_eaa8a880_5rrlrl tree_eaa8a880_5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrlrl && everyKey _ tree_eaa8a880_5rrlrr) = true
  rw [ok_tree_eaa8a880_5rrlrl, ok_tree_eaa8a880_5rrlrr]
  decide +kernel
def tree_eaa8a880_5rrl : BinaryTree (List W) := .node [v242,v244,v247,v260,v245,v258] tree_eaa8a880_5rrll tree_eaa8a880_5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrll && everyKey _ tree_eaa8a880_5rrlr) = true
  rw [ok_tree_eaa8a880_5rrll, ok_tree_eaa8a880_5rrlr]
  decide +kernel
def tree_eaa8a880_5rrrll : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258,v731] (.node [v242,v244,v247,v245,v258,v732] (.node [v242,v244,v247,v245,v258,v733] (.node [v242,v244,v247,v245,v258,v734] (.node [v242,v244,v247,v245,v258,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v735] .nil .nil)) (.node [v242,v244,v247,v245,v258,v474] (.node [v242,v244,v247,v245,v258,v736] .nil .nil) (.node [v242,v244,v247,v245,v258,v737] .nil .nil))) (.node [v242,v244,v247,v245,v258,v349] (.node [v242,v244,v247,v245,v258,v738] (.node [v242,v244,v247,v245,v258,v372] (.node [v242,v244,v247,v245,v258,v739] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v394] .nil .nil)) (.node [v242,v244,v247,v245,v258,v740] (.node [v242,v244,v247,v245,v258,v348] .nil .nil) (.node [v242,v244,v247,v245,v258,v741] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrll = true := by decide +kernel
def tree_eaa8a880_5rrrlr : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258,v341] (.node [v242,v244,v247,v245,v258,v385] (.node [v242,v244,v247,v245,v258,v408] (.node [v242,v244,v247,v245,v258,v409] (.node [v242,v244,v247,v245,v258,v742] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v382] .nil .nil)) (.node [v242,v244,v247,v245,v258,v389] (.node [v242,v244,v247,v245,v258,v381] .nil .nil) (.node [v242,v244,v247,v245,v258,v342] .nil .nil))) (.node [v242,v244,v247,v245,v258,v743] (.node [v242,v244,v247,v245,v258,v294] (.node [v242,v244,v247,v245,v258,v340] .nil .nil) (.node [v242,v244,v247,v245,v258,v744] .nil .nil)) (.node [v242,v244,v247,v245,v258,v420] (.node [v242,v244,v247,v245,v258,v745] .nil .nil) (.node [v242,v244,v247,v245,v258,v536] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrlr = true := by decide +kernel
def tree_eaa8a880_5rrrl : BinaryTree (List W) := .node [v242,v244,v247,v245,v258,v746] tree_eaa8a880_5rrrll tree_eaa8a880_5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrrll && everyKey _ tree_eaa8a880_5rrrlr) = true
  rw [ok_tree_eaa8a880_5rrrll, ok_tree_eaa8a880_5rrrlr]
  decide +kernel
def tree_eaa8a880_5rrrrl : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258,v747] (.node [v242,v244,v247,v245,v258,v317] (.node [v242,v244,v247,v245,v258,v748] (.node [v242,v244,v247,v245,v258,v531] (.node [v242,v244,v247,v245,v258,v431] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v749] .nil .nil)) (.node [v242,v244,v247,v245,v258,v750] (.node [v242,v244,v247,v245,v258,v751] .nil .nil) (.node [v242,v244,v247,v245,v258,v752] .nil .nil))) (.node [v242,v281,v247,v245,v258,v389] (.node [v242,v368,v247,v345,v245,v258] (.node [v242,v368,v305,v247,v245,v258] (.node [v242,v244,v247,v245,v258,v753] .nil .nil) .nil) (.node [v242,v281,v305,v247,v245,v258] .nil .nil)) (.node [v242,v299,v247,v245,v258] (.node [v242,v305,v247,v245,v258,v536] .nil .nil) (.node [v242,v299,v247,v245,v258,v294] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrrl = true := by decide +kernel
def tree_eaa8a880_5rrrrr : BinaryTree (List W) := (.node [v244,v247,v523,v245,v258,v348] (.node [v318,v244,v247,v491,v245,v258] (.node [v242,v253,v247,v245,v258,v317] (.node [v242,v253,v247,v245,v258] (.node [v242,v311,v247,v245,v258,v531] .nil .nil) .nil) (.node [v318,v244,v334,v247,v245,v258] .nil .nil)) (.node [v244,v320,v247,v491,v245,v258] (.node [v244,v320,v247,v325,v245,v258] .nil .nil) (.node [v244,v247,v523,v491,v245,v258] .nil .nil))) (.node [v244,v247,v296,v245,v258] (.node [v244,v247,v307,v245,v258] (.node [v244,v247,v491,v245,v258,v294] .nil .nil) (.node [v244,v247,v307,v245,v258,v536] .nil .nil)) (.node [v244,v247,v248,v245,v258] (.node [v244,v247,v296,v245,v258,v531] .nil .nil) (.node [v244,v247,v248,v245,v258,v317] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrrr = true := by decide +kernel
def tree_eaa8a880_5rrrr : BinaryTree (List W) := .node [v242,v311,v247,v245,v258] tree_eaa8a880_5rrrrl tree_eaa8a880_5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrrrl && everyKey _ tree_eaa8a880_5rrrrr) = true
  rw [ok_tree_eaa8a880_5rrrrl, ok_tree_eaa8a880_5rrrrr]
  decide +kernel
def tree_eaa8a880_5rrr : BinaryTree (List W) := .node [v242,v244,v247,v245,v258,v754] tree_eaa8a880_5rrrl tree_eaa8a880_5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrrl && everyKey _ tree_eaa8a880_5rrrr) = true
  rw [ok_tree_eaa8a880_5rrrl, ok_tree_eaa8a880_5rrrr]
  decide +kernel
def tree_eaa8a880_5rr : BinaryTree (List W) := .node [v242,v244,v247,v245,v258] tree_eaa8a880_5rrl tree_eaa8a880_5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrl && everyKey _ tree_eaa8a880_5rrr) = true
  rw [ok_tree_eaa8a880_5rrl, ok_tree_eaa8a880_5rrr]
  decide +kernel
def tree_eaa8a880_5r : BinaryTree (List W) := .node [v242,v244,v247,v325,v245,v258] tree_eaa8a880_5rl tree_eaa8a880_5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5r : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5r = true := by
  change (_ && everyKey _ tree_eaa8a880_5rl && everyKey _ tree_eaa8a880_5rr) = true
  rw [ok_tree_eaa8a880_5rl, ok_tree_eaa8a880_5rr]
  decide +kernel
def tree_eaa8a880_5 : BinaryTree (List W) := .node [v242,v755,v244,v247,v245,v258] tree_eaa8a880_5l tree_eaa8a880_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5 : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5 = true := by
  change (_ && everyKey _ tree_eaa8a880_5l && everyKey _ tree_eaa8a880_5r) = true
  rw [ok_tree_eaa8a880_5l, ok_tree_eaa8a880_5r]
  decide +kernel
theorem closed_eaa8a880_5 : Closed 5 tree_eaa8a880_5 := closed_next 4 (by decide) tree_eaa8a880_5 tree_eaa8a880_4 closed_eaa8a880_4 ok_tree_eaa8a880_5
def tree_eaa8a880_6l : BinaryTree (List W) := (.node [v324,v242,v244,v247,v245,v258] (.node [v304,v242,v244,v247,v245,v258] (.node [v280,v242,v244,v247,v245,v258] (.node [v271,v242,v244,v247,v245,v258] (.node [v518,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v534,v242,v244,v247,v245,v258] (.node [v270,v242,v244,v247,v245,v258] .nil .nil) .nil)) (.node [v313,v242,v244,v247,v245,v258] (.node [v283,v242,v244,v247,v245,v258] (.node [v302,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v319,v242,v244,v247,v245,v258] .nil .nil))) (.node [v242,v318,v244,v247,v245,v258] (.node [v254,v242,v244,v247,v245,v258] (.node [v333,v242,v244,v247,v245,v258] (.node [v316,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v274,v242,v244,v247,v245,v258] .nil .nil)) (.node [v242,v308,v244,v247,v245,v258] (.node [v242,v279,v244,v247,v245,v258] (.node [v242,v365,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v357,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_6l : everyKey (rowOK 5 tree_eaa8a880_5) tree_eaa8a880_6l = true := by decide +kernel
def tree_eaa8a880_6r : BinaryTree (List W) := (.node [v242,v244,v247,v491,v245,v258] (.node [v242,v244,v305,v247,v245,v258] (.node [v242,v244,v320,v247,v245,v258] (.node [v242,v244,v368,v247,v245,v258] (.node [v242,v244,v334,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v281,v247,v245,v258] .nil .nil)) (.node [v242,v244,v247,v325,v245,v258] (.node [v242,v244,v276,v247,v245,v258] (.node [v242,v244,v352,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v523,v245,v258] .nil .nil))) (.node [v242,v244,v247,v245,v258,v389] (.node [v242,v244,v247,v245,v258,v348] (.node [v242,v244,v247,v260,v245,v258] (.node [v242,v244,v247,v345,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v382] .nil .nil)) (.node [v242,v244,v247,v245,v258,v531] (.node [v242,v244,v247,v245,v258,v536] (.node [v242,v244,v247,v245,v258,v294] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v317] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_6r : everyKey (rowOK 5 tree_eaa8a880_5) tree_eaa8a880_6r = true := by decide +kernel
def tree_eaa8a880_6 : BinaryTree (List W) := .node [v242,v278,v244,v247,v245,v258] tree_eaa8a880_6l tree_eaa8a880_6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_6 : everyKey (rowOK 5 tree_eaa8a880_5) tree_eaa8a880_6 = true := by
  change (_ && everyKey _ tree_eaa8a880_6l && everyKey _ tree_eaa8a880_6r) = true
  rw [ok_tree_eaa8a880_6l, ok_tree_eaa8a880_6r]
  decide +kernel
theorem closed_eaa8a880_6 : Closed 6 tree_eaa8a880_6 := closed_next 5 (by decide) tree_eaa8a880_6 tree_eaa8a880_5 closed_eaa8a880_5 ok_tree_eaa8a880_6
def tree_eaa8a880_7 : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_7 : everyKey (rowOK 6 tree_eaa8a880_6) tree_eaa8a880_7 = true := by decide +kernel
theorem closed_eaa8a880_7 : Closed 7 tree_eaa8a880_7 := closed_next 6 (by decide) tree_eaa8a880_7 tree_eaa8a880_6 closed_eaa8a880_6 ok_tree_eaa8a880_7
theorem lower_eaa8a880 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins_eaa8a880.toFinset := @no_build 7 tree_eaa8a880_7 ins_eaa8a880 nd_eaa8a880 (by decide) closed_eaa8a880_7 (by decide +kernel)
def gates_eaa8a880 : List Gate := [⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [8, 12]⟩]
theorem upper_eaa8a880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_eaa8a880, 13, by simp [gates_eaa8a880], rfl, by decide +kernel⟩

end PEqualNP.Outside.L_meta_8645

open PEqualNP.Outside.L_meta_8645 in
theorem PEqualNP.Outside.L_meta_8645 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, basis, size, computes⟩ := h
  obtain ⟨gates, output, mono, bound, correct⟩ :=
    replace 0xeaa8a880 9 ins_eaa8a880 nd_eaa8a880 rows_eaa8a880 rfl
      lower_eaa8a880 upper_eaa8a880 C.gates C.output basis computes
  exact ⟨⟨gates, output⟩, mono, bound.trans size, correct⟩
