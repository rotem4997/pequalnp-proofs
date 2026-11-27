import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12785
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Signed

-- Lower bound adapted from L-meta-8639.
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

abbrev W := BitVec 60

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
  all_goals have bit0 : (0 : W)[k.val] = false := by change ((0 : BitVec 60))[k.val] = false; simp
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

lemma checkedLower (gs : List Gate) (o : ℕ) (fits : ∀ g ∈ gs, legal g)
    (eval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      Nat.testBit 3903367304 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    6 < binaryCost gs :=
  bound_from_search 3903367304 6 ins_e8a8a888 nd_e8a8a888
    rows_e8a8a888 rfl lower_e8a8a888 gs o fits eval

end Signed

-- Binary gate elimination adapted from L-meta-9543 and L-meta-927.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity



abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

theorem getD_snoc_eq {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD_eq_getElem?_getD]

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
namespace Restrict

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
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

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

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
    obtain ⟨t, ht, _⟩ := wiresFrom_initial r.1.toList w'
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

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


open Signed (binaryCost isBinary)

theorem binaryCost_append (gs hs : List Gate) :
    binaryCost (gs ++ hs) = binaryCost gs + binaryCost hs := by
  simp [binaryCost]

theorem binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = binaryCost [g] + binaryCost gs := by
  exact binaryCost_append [g] gs

theorem binaryCost_singleton (g : Gate) :
    binaryCost [g] = (if isBinary g then 1 else 0) := by
  cases h : isBinary g <;> simp [binaryCost, h]

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

theorem step_cost (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + binaryCost [g] := by
  let res := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  change binaryCost (acc.2 ++ res.1.toList) ≤ _
  rw [binaryCost_append]
  cases h : res.1 with
  | none => simp [binaryCost]
  | some old =>
    have hop := simplify_op g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) old (by change old ∈ res.1; simp [h])
    have hb : isBinary old = isBinary g := by unfold isBinary; rw [hop]
    change binaryCost acc.2 + binaryCost [old] ≤ _
    rw [binaryCost_singleton, binaryCost_singleton, hb]

theorem elim_cost (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs generalizing acc with
  | nil => simp [elim, binaryCost]
  | cons g gs ih =>
    rw [elim_cons, binaryCost_cons]
    have h₁ := ih (elimStep n acc g)
    have h₂ := step_cost n acc g
    omega

def Stable (acc : List Stat × List Gate) (w v : List Bool) : Prop :=
  acc.1.length = w.length ∧ acc.1.length = v.length ∧
    ∀ i j, acc.1.getD i (Sum.inl false) = Sum.inr j → w.getD i false = v.getD i false

theorem stable_step (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (w v : List Bool) (h : Stable acc w v)
    (cost : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + binaryCost [g]) :
    Stable (elimStep n acc g)
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) := by
  let get := fun i => acc.1.getD i (Sum.inl false)
  let ins := g.inputs.map get
  let res := simplify g.op (n + acc.2.length) ins
  let wval := g.op.eval (g.inputs.map fun i => w.getD i false)
  let vval := g.op.eval (g.inputs.map fun i => v.getD i false)
  have live (j : ℕ) (hj : res.2 = Sum.inr j) : wval = vval := by
    have noConst : ∀ c, Sum.inl c ∉ ins := by
      intro c hc
      rcases hg.1.1 with ha | ho | hn
      · have gone := simplify_count g.op (n + acc.2.length) ins (Or.inl ha)
          (by simpa [ins] using hg.1.2) (fun he => by simpa [ins] using hg.2 he) ⟨c, hc⟩
        change res.1 = none at gone
        change binaryCost (acc.2 ++ res.1.toList) = _ at cost
        simp [gone, binaryCost, isBinary, ha] at cost
      · have gone := simplify_count g.op (n + acc.2.length) ins (Or.inr (Or.inl ho))
          (by simpa [ins] using hg.1.2) (fun he => by simpa [ins] using hg.2 he) ⟨c, hc⟩
        change res.1 = none at gone
        change binaryCost (acc.2 ++ res.1.toList) = _ at cost
        simp [gone, binaryCost, isBinary, ho] at cost
      · have hn' : g.op = GateOp.not := by simpa using hn
        have len : ins.length ≤ 1 := by simpa [ins] using hg.2 hn'
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp at hc
        · simp at hc
          subst a
          simp [res, hn', simplify, simpNot] at hj
        · simp at len
    have same : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      cases e : get i with
      | inl c => exact (noConst c (List.mem_map.2 ⟨i, hi, e⟩)).elim
      | inr r => exact h.2.2 i r e
    exact congrArg (g.op.eval) same
  refine ⟨by simp [elimStep, h.1], by simp [elimStep, h.2.1], ?_⟩
  intro i j hj
  change (acc.1 ++ [res.2]).getD i (Sum.inl false) = Sum.inr j at hj
  change (w ++ [wval]).getD i false = (v ++ [vval]).getD i false
  by_cases e : i = acc.1.length
  · subst i
    rw [getD_snoc_eq] at hj
    rw [getD_snoc_len _ _ _ _ h.1.symm, getD_snoc_len _ _ _ _ h.2.1.symm]
    exact live j hj
  · rw [getD_snoc_ne _ _ _ _ e] at hj
    have ew : i ≠ w.length := fun hw => e (hw.trans h.1.symm)
    have ev : i ≠ v.length := fun hv => e (hv.trans h.2.1.symm)
    rw [getD_snoc_ne _ _ _ _ ew, getD_snoc_ne _ _ _ _ ev]
    exact h.2.2 i j hj

theorem stable_elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (w v : List Bool)
    (hok : ∀ g ∈ gs, NOk g) (h : Stable acc w v)
    (cost : binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs) :
    Stable (elim n gs acc) (wiresFrom gs w) (wiresFrom gs v) := by
  induction gs generalizing acc w v with
  | nil => exact h
  | cons g gs ih =>
    rw [elim_cons, binaryCost_cons] at cost
    have h₁ := elim_cost n gs (elimStep n acc g)
    have h₂ := step_cost n acc g
    have hstep : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + binaryCost [g] := by omega
    rw [elim_cons, wiresFrom_cons, wiresFrom_cons]
    apply ih (elimStep n acc g) _ _ (fun g' hg' => hok g' (by simp [hg']))
    · exact stable_step n acc g (hok g (by simp)) w v h hstep
    · omega

theorem stable_init (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    Stable (initStats n b, []) (List.ofFn y ++ [b]) (List.ofFn y ++ [!b]) := by
  refine ⟨by simp [initStats], by simp [initStats], ?_⟩
  intro i j h
  by_cases eq : i = n
  · subst i
    change (initStats n b).getD n (Sum.inl false) = Sum.inr j at h
    rw [initStats_last] at h
    cases h
  · rw [getD_snoc_ne _ _ _ _ (by simpa using eq), getD_snoc_ne _ _ _ _ (by simpa using eq)]

theorem normalize_cost (gs : List Gate) :
    binaryCost (gs.map normGate) = binaryCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, binaryCost_cons (normGate g), binaryCost_cons g, ih]
    have equal : (normGate g).op = g.op := by cases h : g.op <;> simp [normGate, h]
    have hb : isBinary (normGate g) = isBinary g := by unfold isBinary; rw [equal]
    rw [binaryCost_singleton, binaryCost_singleton, hb]

theorem restrict_binary (n : ℕ) (gs : List Gate) (out : ℕ) (f : BFn (n + 1)) (b : Bool)
    (hok : ∀ g ∈ gs, Ok g)
    (hev : ∀ x : Fin (n + 1) → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = f x)
    (hdep : ∃ y : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y (!b)))
    (hnc : ∃ y z : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc z b)) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', Ok g) ∧ binaryCost gs' < binaryCost gs ∧
      ∀ y : Fin n → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn y) = f (Fin.snoc y b) := by
  let norm := gs.map normGate
  have normOK : ∀ g ∈ norm, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hok g' hg')
  have normEval (x : Fin (n + 1) → Bool) :
      (wiresFrom norm (List.ofFn x)).getD out false = f x := by
    rw [show norm = gs.map normGate from rfl, wiresFrom_norm]
    exact hev x
  let start : List Stat × List Gate := (initStats n b, [])
  let acc := elim n norm start
  have atOut (y : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD out (Sum.inl false)) =
        f (Fin.snoc y b) := by
    have h := inv_elim n (List.ofFn y) (by simp) norm _ _
      (fun g hg => (normOK g hg).1) (inv_init n b y)
    have e := (h.2 out).2
    change statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD out (Sum.inl false)) = _ at e
    rw [← ofFn_snoc] at e
    exact e.trans (normEval _)
  cases he : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨y, z, hne⟩ := hnc
    exact (hne (by rw [← atOut y, ← atOut z, he]; rfl)).elim
  | inr j =>
    have hle : binaryCost acc.2 ≤ binaryCost gs := by
      have h := elim_cost n norm start
      change binaryCost acc.2 ≤ binaryCost start.2 + binaryCost norm at h
      rw [show binaryCost start.2 = 0 from rfl, zero_add,
        show norm = gs.map normGate from rfl, normalize_cost] at h
      exact h
    have hlt : binaryCost acc.2 < binaryCost gs := by
      by_contra! hge
      have e : binaryCost (elim n norm start).2 = binaryCost start.2 + binaryCost norm := by
        change binaryCost acc.2 = _
        rw [show norm = gs.map normGate from rfl, normalize_cost]
        have z : binaryCost start.2 = 0 := rfl
        omega
      obtain ⟨y, hy⟩ := hdep
      apply hy
      have hstable := stable_elim n norm start (List.ofFn y ++ [b]) (List.ofFn y ++ [!b])
        normOK (stable_init n y b) e
      have e' := hstable.2.2 out j he
      rw [← ofFn_snoc, ← ofFn_snoc, normEval, normEval] at e'
      exact e'
    refine ⟨acc.2, j, elim_ok n norm start (by simp [start]), hlt, ?_⟩
    intro y
    have e := atOut y
    rw [he] at e
    exact e

end Restrict

open Signed (binaryCost isBinary)
open Restrict (binaryCost_cons)

theorem relabel_cost {n m : ℕ} (π : Fin n → Fin m) (gs : List Gate) :
    binaryCost (gs.map (relGate n m π)) = binaryCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, binaryCost_cons (relGate n m π g), binaryCost_cons g, ih]
    rw [Restrict.binaryCost_singleton, Restrict.binaryCost_singleton]
    rfl

namespace Signed

def mapping : Fin 5 → Fin 10 := ![5, 6, 7, 8, 9]

def inputWithSigns (y : Fin 5 → Bool) (i : Fin 10) : Bool :=
  if h : i.val < 5 then y ⟨i.val, h⟩ else !y ⟨i.val - 5, by omega⟩

def extraInputs : List Gate := [⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.not, [2]⟩, ⟨.not, [3]⟩, ⟨.not, [4]⟩]

def wired (gs : List Gate) : List Gate :=
  extraInputs ++ gs.map (relGate 5 10 mapping)

lemma newInputs (y : Fin 5 → Bool) : extraInputs.foldl step (List.ofFn y) =
    List.ofFn (inputWithSigns y) := by
  revert y
  decide +kernel

set_option maxRecDepth 16000 in
lemma lower (gs : List Gate) (o : ℕ) (ok : ∀ g ∈ gs, Restrict.Ok g)
    (correct : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      Nat.testBit 4008372968 (tableIndex x)) :
    6 < binaryCost gs := by
  have ev (y : Fin 5 → Bool) :
      (Restrict.wiresFrom (wired gs) (List.ofFn y)).getD (wmap 5 10 mapping o) false =
        Nat.testBit 4008372968 (tableIndex (inputWithSigns y ∘ mapping)) := by
    change ((extraInputs ++ gs.map (relGate 5 10 mapping)).foldl step
      (List.ofFn y)).getD (wmap 5 10 mapping o) false = _
    rw [List.foldl_append, newInputs, ← correct]
    exact (rel_fold 5 10 mapping gs _ _ (rel_init 5 10 mapping (inputWithSigns y))).2.2 o
  have align : ∀ y : Fin 5 → Bool,
      (!(Nat.testBit 4008372968 (tableIndex (inputWithSigns y ∘ mapping)))) = Nat.testBit 3903367304 (tableIndex y) := by decide +kernel
  have fits : ∀ g ∈ wired gs, legal g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · simp [extraInputs] at h
      rcases h with eq | eq | eq | eq | eq <;> subst g <;> simp [legal]
    · obtain ⟨base, mem, rfl⟩ := List.mem_map.mp h
      exact ⟨(ok base mem).1, by simpa [relGate] using (ok base mem).2⟩
  have budget : binaryCost (wired gs) = binaryCost gs := by
    change binaryCost (extraInputs ++ gs.map (relGate 5 10 mapping)) = _
    rw [Restrict.binaryCost_append, relabel_cost]
    simp [extraInputs, binaryCost, isBinary]
  have hg : ∀ g ∈ ((wired gs) ++ [⟨.not, [wmap 5 10 mapping o]⟩]), legal g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact fits g h
    · have eq := List.mem_singleton.mp h
      subst g
      simp [legal]
  have he : ∀ y : Fin 5 → Bool, Circuit.eval ⟨((wired gs) ++ [⟨.not, [wmap 5 10 mapping o]⟩]), (5 + (wired gs).length)⟩ (List.ofFn y) =
      Nat.testBit 3903367304 (tableIndex y) := by
    intro y
    have hw : (Restrict.wiresFrom (wired gs) (List.ofFn y)).length =
        5 + (wired gs).length := by rw [Restrict.length_wiresFrom]; simp
    change (Restrict.wiresFrom (wired gs ++ [_]) (List.ofFn y)).getD _ false = _
    rw [Restrict.wiresFrom_append, ← hw, Restrict.wiresFrom_cons]
    change (_ ++ [!(Restrict.wiresFrom (wired gs) (List.ofFn y)).getD (wmap 5 10 mapping o) false]).getD _ false = _
    rw [getD_snoc_eq, ev y]
    exact align y
  have bound := checkedLower ((wired gs) ++ [⟨.not, [wmap 5 10 mapping o]⟩]) (5 + (wired gs).length) hg he
  have same : binaryCost (wired gs ++ [⟨.not, [wmap 5 10 mapping o]⟩]) =
      binaryCost gs := by
    rw [Restrict.binaryCost_append, budget]
    simp [binaryCost, isBinary]
  rw [same] at bound
  omega

end Signed

def target6 (x : Fin 6 → Bool) : Bool := Nat.testBit 18374403832150949600 (tableIndex x)

def order : Fin 6 → Fin 6 := ![5, 0, 1, 2, 3, 4]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma binaryLower (gs : List Gate) (o : ℕ) (fits : ∀ g ∈ gs, Restrict.Ok g)
    (computes : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target6 x) :
    8 ≤ Signed.binaryCost gs := by
  let f : BFn 6 := fun x => target6 (x ∘ order)
  let C := relabel 6 6 order ⟨gs, o⟩
  have ok : ∀ g ∈ C.gates, Restrict.Ok g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    have h := fits g' hg'
    exact ⟨h.1, by simpa [relGate] using h.2⟩
  have hv : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
    intro x
    change C.eval (List.ofFn x) = target6 (x ∘ order)
    rw [← computes (x ∘ order)]
    exact (rel_fold 6 6 order gs _ _ (rel_init 6 6 order x)).2.2 o
  have dep : ∃ y : Fin 5 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y (!false)) :=
    ⟨fun i => (2 : ℕ).testBit i.val, by decide +kernel⟩
  have varies : ∃ y z : Fin 5 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false) :=
    ⟨fun i => (3 : ℕ).testBit i.val, fun i => (0 : ℕ).testBit i.val, by decide +kernel⟩
  obtain ⟨new, out, legal, cost, eval⟩ := Restrict.restrict_binary 5 C.gates C.output f false ok hv dep varies
  have eq : ∀ x : Fin 5 → Bool, f (Fin.snoc x false) =
      Nat.testBit 4008372968 (tableIndex x) := by decide +kernel
  have cut := Signed.lower new out legal (fun x => (eval x).trans (eq x))
  have same : Signed.binaryCost C.gates = Signed.binaryCost gs := relabel_cost order gs
  omega

def witness : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [2, 4]⟩,
   ⟨GateOp.and, [6, 7]⟩,
   ⟨GateOp.or, [8, 5]⟩,
   ⟨GateOp.or, [6, 4]⟩,
   ⟨GateOp.and, [9, 10]⟩,
   ⟨GateOp.or, [11, 3]⟩,
   ⟨GateOp.or, [6, 2]⟩,
   ⟨GateOp.and, [12, 13]⟩], 14⟩

lemma witnessCorrect : ∀ x : Fin 6 → Bool,
    witness.eval (List.ofFn x) = target6 x := by decide +kernel

end PEqualNP.Outside.L_meta_12785

open PEqualNP.Outside.L_meta_12785 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_12785 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277075680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, legal, size, computes⟩
  by_cases present : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, mem, op⟩ := present
    have cheaper : Signed.binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, mem, by simp [Signed.isBinary, op]⟩
    have lower := binaryLower C.gates C.output legal computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witnessCorrect⟩
    change 9 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := legal g mem
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g, mem, eq⟩).elim)), cap⟩
