import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17077

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

abbrev W := BitVec 100
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 50 := ((x >>> 50) ^^^ x).setWidth 50
def cuts (ws : List W) : BitVec 50 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 50) ++ (0 : BitVec 50)
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

def differs (i : Fin 50) (w : W) : Prop :=
  w.getLsbD (50+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 50) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 50+i.val < 100 := by omega
  have hi' : i.val < 100 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 50) :
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
  change (cuts ws)[j] = (BitVec.allOnes 50)[j]
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
  · change reachable av (BitVec.allOnes 100 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 100)
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

private def bit (k : Fin 100) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 100) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 100) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#100)[k.val] = false; simp
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
    (row : ∀ j : Fin 100, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 100) :
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
    (row : ∀ j : Fin 100, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0x20871f8e73b30001454294acc
def v1 : W := 0x4319e6139cc3c0847180c630a
def v2 : W := 0x9c61f863e0fc06106e10f83a0
def v3 : W := 0xe07e007c00fff80b800f00055
def v4 : W := 0xff80007fff003d60001d29400
def v5 : W := 0xffffff8000003bfe9aa000000
def v6 : W := 0x639fff9ffff3c08575c2d6bce
def v7 : W := 0xbce7ff80000002100a0000000
def v8 : W := 0xc078007000ffc000000000000
def v9 : W := 0x20871f8e73000000000000000
def v10 : W := 0x9c61f86000fc02100a0000000
def v11 : W := 0xfffe007ffffffd6b801f29455
def v12 : W := 0x20871f8e73030001454294acc
def v13 : W := 0x7c1ff81fe003fe1bee1ff83f5
def v14 : W := 0x1f81fffc00ffc3f51aaf00055
def v15 : W := 0x7fffffff00069e9abd29400
def v16 : W := 0xfffe007c00fff96b800f00055
def v17 : W := 0x7e007c00ffc00b800f00055
def v18 : W := 0x6ff3ff04016552fcbec
def v19 : W := 0x4319fe13fcf3c0847580d638a
def v20 : W := 0xbce7ffeff3ff06116f52fcbec
def v21 : W := 0xbce6e7ed934f06112b526c96c
def v22 : W := 0x1f01fe03fc0006947f90fe3aa
def v23 : W := 0x2087ff8ff3f300016542d4bcc
def v24 : W := 0xdf79fe73fcffc6947f90fe3aa
def v25 : W := 0xdf781e707c3fc6941f903e0aa
def v26 : W := 0xdf78e0718c003ffe9abd29400
def v27 : W := 0x639e079c0003f9ef90af00055
def v28 : W := 0x1f80007fff000560001d29400
def v29 : W := 0x20861f8c733300010542148cc
def v30 : W := 0x1ffe0003ffffc56b801229455
def v31 : W := 0x1fffff80000003fe9aa000000
def v32 : W := 0xfffe007fff003d6a801d29400
def v33 : W := 0xfffffffc00003bfe9aad00000
def v34 : W := 0x20871f8c63b30001454294acc
def v35 : W := 0xbc99e66c63c3fde4719def70a
def v36 : W := 0x20871f8c633000010442108c4
def v37 : W := 0xbce619939cc3fb7aeb20c630a
def v38 : W := 0xfffffffc00fffbff9aaf00055
def v39 : W := 0xffffffffff003ffe9abd29400
def v40 : W := 0x7f80001fff003d60001d29400
def v41 : W := 0x639e07e3e0fc3deef4b0f83a0
def v42 : W := 0x4319e6139c03c0847180c630a
def v43 : W := 0x20ffffffff00069e9abd29400
def v44 : W := 0x20871f8e73300001454294acc
def v45 : W := 0xa367e66f9c3c388ff18fc635f
def v46 : W := 0x5ffe0013ffffc56b801229455
def v47 : W := 0x63e1f81c1ffc3b706e0dd17a0
def v48 : W := 0x9c7fff800000029e9aa000000
def v49 : W := 0x807e006000ffc00b800200055
def v50 : W := 0xe3fe007c1ffff96b800f01455
def v51 : W := 0xffffff9c1f003bfe9aad01400
def v52 : W := 0xffffffe000fc3bfe9aa000000
def v53 : W := 0x7f9fff8000003bfe9aa000000
def v54 : W := 0xff871fffff003d60001d29400
def v55 : W := 0xffe0007ffffc3d60001d29400
def v56 : W := 0xff7e007c00fff96b800f00055
def v57 : W := 0xe07fffffff003e9e9abd29400
def v58 : W := 0xfff8007ffffffd60001d29400
def v59 : W := 0xfffffff000fffbfe9aa000000
def v60 : W := 0xff81fffc00fffbf51aaf00055
def v61 : W := 0x9c61f863e03c06106e10f83a0
def v62 : W := 0xfffffffc00c3fbfe9aad00000
def v63 : W := 0xfffe007fff4cfd6a801d29411
def v64 : W := 0xfffe007e73fff96b800f00055
def v65 : W := 0xfffe007c1ffff96b800f01455
def v66 : W := 0xfffe007f9cfff96b800f00055
def v67 : W := 0xffffffec00003bfe9aad00000
def v68 : W := 0xfffe007ffffc3d6a801d29400
def v69 : W := 0xfffe007fffc3fd6a801d29400
def v70 : W := 0xfffffffc004cfbfe9aad00011
def v71 : W := 0xffff1fffff003d6a801d29400
def v72 : W := 0xfffffffe73003bfe9aad00000
def v73 : W := 0xfffffffc1f003bfe9aad01400
def v74 : W := 0xfffffffc00fc3bfe9aad00000
def v75 : W := 0xffff1ffc00fff96b800f00055
def v76 : W := 0xffffffff9c003bfe9aad00000
def v77 : W := 0xc379e6739cffc0847180c630a
def v78 : W := 0xbce7ffe000fc02100a0000000
def v79 : W := 0x9c61f86060fc06106e10f83a0
def v80 : W := 0x9c61f860603c06100e10380a0
def v81 : W := 0xff98007fffc3fd60001d29400
def v82 : W := 0xbfe7ff8000003bfe9aa000000
def v83 : W := 0xbf80006fff003d60001d29400
def v84 : W := 0xa07e006c00fff80b800f00055
def v85 : W := 0xffffff9000c3fbfe9aa000000
def v86 : W := 0xffffff939c003bfe9aa000000
def v87 : W := 0xbcffff8000003bfe9aa000000
def v88 : W := 0xe37e007f9cfff80b800f00055
def v89 : W := 0xdc79f873e0ffc6106e10f83a0
def v90 : W := 0x9c61f873fcffc6106f10fe3aa
def v91 : W := 0xdf61f873fcfc06106e10f83a0
def v92 : W := 0xfc7ff87fe0fffe1bee1ff83f5
def v93 : W := 0xfc7ff87c00fffa1b8a0f00055
def v94 : W := 0xe37fe67f9cfff88ff18fc635f
def v95 : W := 0xfffe0003fffffd6b801229455
def v96 : W := 0xc07e007000fff80b800f00055
def v97 : W := 0xdf071ff18cb33d61455fbdecc
def v98 : W := 0x3f80000fff000560001029400
def v99 : W := 0xc0f91ff2734cf80ac54d94a99
def v100 : W := 0x20871f9ffff3c0016542d6bce
def v101 : W := 0xff99e67fffc3fde4719def70a
def v102 : W := 0xdf791e727cbfc6945f90be2aa
def v103 : W := 0xdf781e707cffc6941f903e0aa
def v104 : W := 0x2087ff8ff3b300016542d4bcc
def v105 : W := 0x2087ff9ffff3c0016542d6bce
def v106 : W := 0xa0e71fee73ff0001454294acc
def v107 : W := 0x4318e0139cc3c0847180c630a
def v108 : W := 0xdf78e00e73b33bffdfe294acc
def v109 : W := 0x4318e0118cc3c084308042102
def v110 : W := 0x3f87ff80000003f41aa000000
def v111 : W := 0x4319e6118cc3c0847180c630a
def v112 : W := 0x4318e6119c43c08431804610a
def v113 : W := 0x9c61f86180fc06106e10f83a0
def v114 : W := 0x9c60e063e0fc06106e10f83a0
def v115 : W := 0x9c60e06180fc06102a1068120
def v116 : W := 0xc078007c00fff80b800f00055
def v117 : W := 0xbce7ff8e73b302114f4294acc
def v118 : W := 0xfff8007fff4cfd6a801d29411
def v119 : W := 0xfffffff0004cfbfe9aad00011
def v120 : W := 0xdf7fff8000003bfe9aa000000
def v121 : W := 0xdf00007fff003d60001d29400
def v122 : W := 0xe0fe007e73fff80b800f00055
def v123 : W := 0xffffff8e73003bfe9aa000000
def v124 : W := 0xe0ff1ffc00fff80b800f00055
def v125 : W := 0xbce1f86ff3fc06106e10f83a0
def v126 : W := 0x9ce1ffe3f3fc06106f50fcba8
def v127 : W := 0xe0ff1ffe73ffc001454294acc
def v128 : W := 0xff871fffffb33d61455fbdecc
def v129 : W := 0x639ef99def70c08534c2529c6
def v130 : W := 0x609f1f9e73f3c001454294acc
def v131 : W := 0xbce7ffe3e0fc06106e10f83a0
def v132 : W := 0xffffff8e73b33bffdfe294acc
def v133 : W := 0xbce7ffeff3fc06106e10f83a0
def v134 : W := 0xe0ff1ffe73fff80b800f00055
def v135 : W := 0x4399ff93fff3c08475c0d6b8a
def v136 : W := 0x4399ff93ffc3c08475c0d6b8a
def v137 : W := 0x6399e61fffc3c0847180c630a
def v138 : W := 0x63871f9fffb30001454294acc
def v139 : W := 0x609fff9ff3f3c0016542d4bcc
def v140 : W := 0x6387ff9ffff300016542d4bcc
def v141 : W := 0x9c60f861e07c06102e10781a0
def v142 : W := 0x6399fe1ffff3c0847580d638a
def v143 : W := 0x9c61fe63f0ff06106f10fc3a8
def v144 : W := 0x639fff939cc3c0847180c630a
def v145 : W := 0x639ff99feff0c08574c2d2bc6
def v146 : W := 0x639ef99fff70c08534c2529c6
def v147 : W := 0x639fff9fffc3c0847180c630a
def v148 : W := 0x639fff93fcf3c0847580d638a
def v149 : W := 0x9c61fe63e0ff06106f10fc3a8
def v150 : W := 0xbce1fe6ff3ff06106f10fc3a8
def v151 : W := 0x9ce1ffe3f3ff06106f50fcba8
def v152 : W := 0x9c61fe73fcffc6106f10fe3aa
def v153 : W := 0xbce7ffe3f0ff06106f10fc3a8
def v154 : W := 0xa0e7ffeff3ff00016542d4bcc
def v155 : W := 0xdf61fe73fcff06106f10fc3a8
def v156 : W := 0xdc79fe73f0ffc6106f10fc3a8
def v157 : W := 0xc379fe73fcffc0847580d638a
def v158 : W := 0xbce7e7ef93cf06116b52ecb6c
def v159 : W := 0x63e0fc04006410f83a0
def v160 : W := 0x639f1f80000039ee90a000000
def v161 : W := 0x139cc3c0006100c630a
def v162 : W := 0xe73b30001454294acc
def v163 : W := 0xdf78e070004cfbfe9aad00011
def v164 : W := 0xdf78e00000003bfe9aa000000
def v165 : W := 0x20871feff3ff04016552fcbec
def v166 : W := 0xbce6198000003b7a8a2000000
def v167 : W := 0xff3b304016552fcbec
def v168 : W := 0xbce71f8000003b7a8a2000000
def v169 : W := 0x1ffff3c0016542d6bce
def v170 : W := 0x639e079c1f0039ee90ad01400
def v171 : W := 0x639e0780000039ee90a000000
def v172 : W := 0x7c00000000000d00000
def v173 : W := 0x63e0ff04016552fcbec
def v174 : W := 0x9c61f86ff3ff06116f52fcbec
def v175 : W := 0x1180260b00000440090280
def v176 : W := 0x73fcffc4006510fe3aa
def v177 : W := 0x7c00ffc001000f00055
def v178 : W := 0x1f81ff80000003f41aa000000
def v179 : W := 0xff81ff8000003bf41aa000000
def v180 : W := 0x7ff3ffc401655ffcbfd
def v181 : W := 0x7fff000400001d29400
def v182 : W := 0x7fff800000029e9aa000000
def v183 : W := 0x1060000830000410084208
def v184 : W := 0x7fffff0401655ffdfec
def v185 : W := 0xe07fff8000003a9e9aa000000
def v186 : W := 0x20ffff800000029e9aa000000
def v187 : W := 0x7ffff3c401655ffffce
def v188 : W := 0x180060300000040010080
def v189 : W := 0x60010030000010004008
def v190 : W := 0x7fffffc4016552febee
def v191 : W := 0xe00180400000200040100
def v192 : W := 0x106139cc3c0006100c630a
def v193 : W := 0x1060210830000410084208
def v194 : W := 0x1e00380c000006000c0300
def v195 : W := 0x11e0270b30000450094288
def v196 : W := 0x1e003800000006000c0300
def v197 : W := 0x1f803e0f000006400d0380
def v198 : W := 0x1e60390c300006100c4308
def v199 : W := 0x1e0139cc3c0006100c630a
def v200 : W := 0x71f8000b30001454294acc
def v201 : W := 0xdf0000718c003d60001d29400
def v202 : W := 0xdf0000739c003d60001d29400
def v203 : W := 0x7e000000ffc00b800200055
def v204 : W := 0x61f80000fc02106e00d03a0
def v205 : W := 0x6380001c1f003960000d01400
def v206 : W := 0x19e60000c3c0847180c630a
def v207 : W := 0xbc80006c63003d60001d29400
def v208 : W := 0xdf7800718c4cfd6a801d29411
def v209 : W := 0xbc80006e73003d60001d29400
def v210 : W := 0x78007c00ffc00b800f00055
def v211 : W := 0x6380001f9f003960000d01400
def v212 : W := 0x6380001e7f003960000d01400
def v213 : W := 0x1f800003ff000560001029400
def v214 : W := 0x7e00000000000a800000000
def v215 : W := 0x5f800013ff000560001029400
def v216 : W := 0xff800003ff003d60001029400
def v217 : W := 0x7e007000ffc00b800f00055
def v218 : W := 0x7e006c00ffc00b800f00055
def v219 : W := 0x7e006000ffc00b800200055
def v220 : W := 0xff80000000003960000000000
def v221 : W := 0x2080007fff000400001d29400
def v222 : W := 0x4300007fff000400001d29400
def v223 : W := 0x811f8273000000454094a88
def v224 : W := 0xc078007000cff80a800d00011
def v225 : W := 0x7fff8000ffc2957fc2d6bee
def v226 : W := 0xe000007fff003c00001d29400
def v227 : W := 0x7fff8000f3c29fffe2d6bce
def v228 : W := 0xc0780070004cf80a800d00011
def v229 : W := 0x301e6039c0000847180c630a
def v230 : W := 0xa066006c003c380b800f00055
def v231 : W := 0x811f8273830000454094a88
def v232 : W := 0xc078007000fcf80a800d00011
def v233 : W := 0x1c01f803e00006106e10f83a0
def v234 : W := 0x811f8273b00000454094a88
def v235 : W := 0x5f19fe13fcc3c6947f90fe3aa
def v236 : W := 0xa066006c00fc380b800f00055
def v237 : W := 0x601e001c0003f80b800f00055
def v238 : W := 0x381ff83ff00008475c0d6b8a
def v239 : W := 0x601e001c00c3f80b800f00055
def v240 : W := 0x6380007fff003d60001d29400
def v241 : W := 0x1cffff80000003fe9aa000000
def v242 : W := 0x9f61fe63fcfc06947f90fe3aa
def v243 : W := 0x1c7fff800000029e9aa000000
def v244 : W := 0x1c01fe03e00006947f90fe3aa
def v245 : W := 0x1c81ff83f30006106f50fcba8
def v246 : W := 0x1f7fff80000003fe9aa000000
def v247 : W := 0x1f00007fff000560001d29400
def v248 : W := 0x1f80000000000160000000000
def v249 : W := 0x407e001000ffc00b800200055
def v250 : W := 0x1f80006fff000560001d29400
def v251 : W := 0xe07e000000fff80b800200055
def v252 : W := 0x1f80000fff000560001029400
def v253 : W := 0x1f80001fff000560001d29400
def v254 : W := 0x1f81fe03ff0007f47f90ff7aa
def v255 : W := 0xe07e00000000380a800000000
def v256 : W := 0x8060007c00ffc001000f00055
def v257 : W := 0x4018007c00ffc001000f00055
def v258 : W := 0x1f81ff83fc0007f47fb0fe3aa
def v259 : W := 0x1f81ff83ff0006947fd0febaa
def v260 : W := 0x1fe7ff80000003fe9aa000000
def v261 : W := 0x1f87ff80000003f41aa000000
def v262 : W := 0x1f9fff80000003fe9aa000000
def v263 : W := 0xe000007c00003800000d00000
def v264 : W := 0x2080000e73000000000000000
def v265 : W := 0x2006000c00b30001000200044
def v266 : W := 0xe0ff1ffe73fff80bc54f94add
def v267 : W := 0x3f871f8fffb305614552bdecc
def v268 : W := 0x207e007c00ffc00b800f00055
def v269 : W := 0xe000007c00fff801000f00055
def v270 : W := 0x2086198c633000010442108c4
def v271 : W := 0x2086078c1303000101420484c
def v272 : W := 0x2086000e73b30001000200044
def v273 : W := 0x2081180e73b00000440090280
def v274 : W := 0x2081060e73830000410084208
def v275 : W := 0x2080000e73b30001454294acc
def v276 : W := 0x20811f8e73000000454094a88
def v277 : W := 0x9c61e06380cc06106a10e8320
def v278 : W := 0x9c60e061804c06102a1068120
def v279 : W := 0x4318e0139c40c084308042102
def v280 : W := 0x4318e0118c40c084308042102
def v281 : W := 0x2086078e7303000101420484c
def v282 : W := 0x4319e0138cc0c0847080c2302
def v283 : W := 0x20861f8c730300010542148cc
def v284 : W := 0x20861f8c633000010442108c4
def v285 : W := 0x2086198e733000010442108c4
def v286 : W := 0x20861f8c633300010542148cc
def v287 : W := 0x20861f8e73b30001454294acc
def v288 : W := 0x20861f8c73b300010542148cc
def v289 : W := 0x20861f8c733000010542148cc
def v290 : W := 0x20861f8e733300010542148cc
def v291 : W := 0x2087198e63b00001444290ac4
def v292 : W := 0x2087078e13830001414284a4c
def v293 : W := 0x20871f8000000000000000000
def v294 : W := 0x20871f8273000000454094a88
def v295 : W := 0xffffff8c63303bff9ee2108c4
def v296 : W := 0x20871f8210830000410084208
def v297 : W := 0x20871f8000b30001454294acc
def v298 : W := 0x20871f8260b00000440090280
def v299 : W := 0x20871f8c63000000000000000
def v300 : W := 0x20871f8c1303000101420484c
def v301 : W := 0x20871f8c00b30001000200044
def v302 : W := 0x430000139c000000000000000
def v303 : W := 0x20871f8c63b300010442108c4
def v304 : W := 0x20871f8c63300001454294acc
def v305 : W := 0x3f87ff8e73b303f55fe294acc
def v306 : W := 0x639e001c1f03f96b800f01455
def v307 : W := 0x20871f8e63b30001454294acc
def v308 : W := 0x20871f8c73b30001454294acc
def v309 : W := 0x20871f8c733300010542148cc
def v310 : W := 0x20871f8e63b00001444290ac4
def v311 : W := 0x9c61f800000002100a0000000
def v312 : W := 0x9c60e06180fc06106e10f83a0
def v313 : W := 0x4318e0118cc3c0847180c630a
def v314 : W := 0xc078007000fff80b800f00055
def v315 : W := 0x20871f8e73000001454294acc
def v316 : W := 0x20871f8e73000000454094a88
def v317 : W := 0x20871f8e7303000101420484c
def v318 : W := 0x8060006000fc0000000000000
def v319 : W := 0x4018001000c3c000000000000
def v320 : W := 0x20871f8e733000010442108c4
def v321 : W := 0x20871f8e73830001454294acc
def v322 : W := 0x20871f8e73330001454294acc
def v323 : W := 0x20871f8e73830000410084208
def v324 : W := 0x20871f8e73b00001454294acc
def v325 : W := 0x20871f8e73b00000440090280
def v326 : W := 0x20871f8e73b30001000200044
def v327 : W := 0x3f80007fff000560001d29400
def v328 : W := 0x3c87ff80000002100a0000000
def v329 : W := 0x3f80000fff003d60001d29400
def v330 : W := 0x3f87ff8000003bfe9aa000000
def v331 : W := 0x3fffff80000003fe9aa000000
def v332 : W := 0x4019e01380c3c0006000c0300
def v333 : W := 0xe37ee07d8cfff88fb08f42157
def v334 : W := 0x401800139cc3c0006100c630a
def v335 : W := 0x407e007c00ffc00b800f00055
def v336 : W := 0x4019e61000c3c0847180c630a
def v337 : W := 0x431806101c03c08411800600a
def v338 : W := 0x9c61186260bc06104e10b82a0
def v339 : W := 0x431800139cc3c000000000000
def v340 : W := 0x4301e0139cc000006000c0300
def v341 : W := 0x430000139cc3c0006100c630a
def v342 : W := 0x4301e6139c0000847180c630a
def v343 : W := 0x9c601860603c06100e10380a0
def v344 : W := 0x9c60186060fc06100e10380a0
def v345 : W := 0x431806139c03c08411800600a
def v346 : W := 0x431806101cc3c08411800600a
def v347 : W := 0x431806139cc3c0847180c630a
def v348 : W := 0x4318e0118c43c084308042102
def v349 : W := 0x4318e0119c43c08431804610a
def v350 : W := 0x4318e0139cc3c084308042102
def v351 : W := 0x4318e6118c43c08431804610a
def v352 : W := 0x4318e6119c03c08431804610a
def v353 : W := 0x4319e60000000084108000000
def v354 : W := 0xffffff939cc3fbfefba0c630a
def v355 : W := 0x4319e0138cc3c0847080c2302
def v356 : W := 0x4318e6139cc3c0847180c630a
def v357 : W := 0x4318e6139c43c08431804610a
def v358 : W := 0x4318e6119cc3c08431804610a
def v359 : W := 0x431906121c83c08451808620a
def v360 : W := 0x4319e0139cc3c0847180c630a
def v361 : W := 0x4319e0139cc3c0006000c0300
def v362 : W := 0x4319e6118cc3c084308042102
def v363 : W := 0x4319e61000c3c084108000000
def v364 : W := 0xe3fe07fc00fff9ef90af00055
def v365 : W := 0x4319e6139c03c08411800600a
def v366 : W := 0x4319e6138cc3c0847180c630a
def v367 : W := 0x4319e6119cc3c0847180c630a
def v368 : W := 0x4319e6119c43c08431804610a
def v369 : W := 0x4319e6139c000084108000000
def v370 : W := 0x5f80007fff000560001d29400
def v371 : W := 0x4319e6139c83c0847180c630a
def v372 : W := 0x4319e6139c43c0847180c630a
def v373 : W := 0x4319e6139cc3c084108000000
def v374 : W := 0x5fffff80000003fe9aa000000
def v375 : W := 0x639e061c1f03f9ef918f0745f
def v376 : W := 0x631e001c0003f9ef90af00055
def v377 : W := 0x607e007c00fff80b800f00055
def v378 : W := 0x8061f86000fc02106e00d03a0
def v379 : W := 0x80600063e0fc04006410f83a0
def v380 : W := 0x639e078c000039ef90af00055
def v381 : W := 0xffffff9c0003fbff9aaf00055
def v382 : W := 0x639e079c1c03f9ef91af0605f
def v383 : W := 0x639e079c1303f9ef91ef0485d
def v384 : W := 0x639e079c1f03f9ef90af01455
def v385 : W := 0x9c000063e0000400001028000
def v386 : W := 0xffffffe3e0fc3ffefeb0f83a0
def v387 : W := 0xffe1f87ffffc3f706e1df97a0
def v388 : W := 0x7f80001fff000560001029400
def v389 : W := 0x7fffff8000003bfe9aa000000
def v390 : W := 0x7f9fff80000003f41aa000000
def v391 : W := 0x7f80007fff003d60001d29400
def v392 : W := 0xfc7ee07d80fffe1baa1f68175
def v393 : W := 0x9c7ff863e0ffc61bee12f83f5
def v394 : W := 0x9c60e063e0fc06102a1068120
def v395 : W := 0x8078006000ffc000000000000
def v396 : W := 0x807e007c00ffc00b800f00055
def v397 : W := 0x807e006000fff80b800f00055
def v398 : W := 0x9c600063e0fc0400001028000
def v399 : W := 0x9c60e061807c06102a1068120
def v400 : W := 0x9c60e06000fc02100a0000000
def v401 : W := 0x9c60e061e07c06102e10781a0
def v402 : W := 0x9c60f861e03c06102e10781a0
def v403 : W := 0x9c60f860607c06102e10781a0
def v404 : W := 0x9c60f860603c06100e10380a0
def v405 : W := 0x9c60f861807c06102e10781a0
def v406 : W := 0x9c61e06380fc06106a10e8320
def v407 : W := 0x9c60f863e07c06102e10781a0
def v408 : W := 0x9c60f861e0fc06102e10781a0
def v409 : W := 0x9c60f863e0fc06106e10f83a0
def v410 : W := 0x9c61e063e0fc06106e10f83a0
def v411 : W := 0x9c61e063e0fc04006010e8300
def v412 : W := 0xffffffe0603c3ffe9eb0380a0
def v413 : W := 0x9c61f860003c02100a0000000
def v414 : W := 0x9c61f86000fc06106e10f83a0
def v415 : W := 0x9c61f86000fc02106e00d03a0
def v416 : W := 0x9c61f860603c06106e10f83a0
def v417 : W := 0x9c61f86060fc06100e10380a0
def v418 : W := 0x9c61f86180fc06102a1068120
def v419 : W := 0x9c61f86260fc02104e0090280
def v420 : W := 0x9c61f861e0fc06106e10f83a0
def v421 : W := 0x9c61f861e07c06102e10781a0
def v422 : W := 0x9c61f86260bc06104e10b82a0
def v423 : W := 0x9c61f86380fc02106a00c0300
def v424 : W := 0x9c61f86260fc06106e10f83a0
def v425 : W := 0x9c61f86380fc06106e10f83a0
def v426 : W := 0x9c7fffe3e0fc069efeb0f83a0
def v427 : W := 0x9c61f863e0fc06100a1028000
def v428 : W := 0x9c61f863e0bc06106e10f83a0
def v429 : W := 0x9c61f863e07c06106e10f83a0
def v430 : W := 0x9c67ff80000002100a0000000
def v431 : W := 0xa000006c00003800000d00000
def v432 : W := 0x9f80007fff000560001d29400
def v433 : W := 0x9c7fff8000003bfe9aa000000
def v434 : W := 0x9fffff80000003fe9aa000000
def v435 : W := 0xa07e006c00ffc00b800200055
def v436 : W := 0xbce7ff8000003bfe9aa000000
def v437 : W := 0xa07e007c00fff80b800f00055
def v438 : W := 0xbce7ff8000003b7a8a2000000
def v439 : W := 0xbcffff800000029e9aa000000
def v440 : W := 0xbf80006fff000560001029400
def v441 : W := 0xbf80007fff003d60001d29400
def v442 : W := 0xc07e007c00fff80b800f00055
def v443 : W := 0xbfffff8000003bfe9aa000000
def v444 : W := 0xc078007000fff80a800d00011
def v445 : W := 0xc078007c00ffc001000f00055
def v446 : W := 0xc07e007000ffc00b800200055
def v447 : W := 0xdf00000000003960000000000
def v448 : W := 0xdf00007fff000400001d29400
def v449 : W := 0xdfffff8000003bfe9aa000000
def v450 : W := 0xdf7fff800000029e9aa000000
def v451 : W := 0xdf80007fff003d60001d29400
def v452 : W := 0xe018007c00c3f800000d00000
def v453 : W := 0xbfe7ff80000003f41aa000000
def v454 : W := 0xff00007fff003d60001d29400
def v455 : W := 0xe07e0070004cf80a800d00011
def v456 : W := 0xe078007c00fff80b800f00055
def v457 : W := 0xe078007c00fff800000d00000
def v458 : W := 0xe078007c004cf80a800d00011
def v459 : W := 0xe07e006000fff80b800200055
def v460 : W := 0xe07e006000fc380a800000000
def v461 : W := 0xe07e001000c3f80a800000000
def v462 : W := 0xe07e006c00fff80b800f00055
def v463 : W := 0xe07e007c00ffc001000200044
def v464 : W := 0xe07e007c0000380a800d00000
def v465 : W := 0xe07e007000fff80b800f00055
def v466 : W := 0xe07e007000fff80a800000000
def v467 : W := 0xfcffff8000003a1a8a0000000
def v468 : W := 0xfc7fff8000003a9e9aa000000
def v469 : W := 0xfcffff8000003bfe9aa000000
def v470 : W := 0xff80006fff003d60001d29400
def v471 : W := 0xff8000139c003960000000000
def v472 : W := 0xff80000e73003960000000000
def v473 : W := 0xff7fff8000003bfe9aa000000
def v474 : W := 0xff80000fff003d60001029400
def v475 : W := 0xff80001fff003960000000000
def v476 : W := 0xff80001c1f003960000d01400
def v477 : W := 0xff80001fff003d60001d29400
def v478 : W := 0xff9fff8000003bfe9aa000000
def v479 : W := 0xff87ff8000003bf41aa000000
def v480 : W := 0xff80007fff000400001028000
def v481 : W := 0xff80007c00003960000d00000
def v482 : W := 0xff9fff80000039e4108000000
def v483 : W := 0xffe7ff8000003bfe9aa000000
def v484 : W := 0xffe7ff8000003b700a0000000
def v485 : W := 0xffffff80000002941a8000000
def v486 : W := 0xffffff9000003bfe9aa000000
def v487 : W := 0xffffff8260003bfe9aa000000
def v488 : W := 0xffffff8000c3fbfe9aa000000
def v489 : W := 0xffffff8000b03bfe9aa000000
def v490 : W := 0xffffff8000833bfe9aa000000
def v491 : W := 0xffffff80004cfbfe9aa000011
def v492 : W := 0xffffff8000c03bfe9aa000000
def v493 : W := 0xffffff801f003bfe9aa001400
def v494 : W := 0xffffff8000fc3bfe9aa000000
def v495 : W := 0xffffff8210003bfe9aa000000
def v496 : W := 0xffffff8c03003bfe9aad01400
def v497 : W := 0xffffff839c003bfe9aa000000
def v498 : W := 0xffffff8380003bfe9aa000000
def v499 : W := 0xffffff8273003bfe9aa000000
def v500 : W := 0xffffff8c00003bfe9aa000000
def v501 : W := 0xffffff8c63003bfe9aa000000
def v502 : W := 0xffffff8c13003bfe9aa000000
def v503 : W := 0xffffff900c003bfe9aad01400
def v504 : W := 0xffffff900040fbfe9aa000000
def v505 : W := 0xffffff900003fbfe9aa000000
def v506 : W := 0xffffff900000fbfe9aad00011
def v507 : W := 0xffffff901c003bfe9aa000000
def v508 : W := 0xffffff900c00fbfe9aa002002
def v509 : W := 0xffffff918c003bfe9aa000000
def v510 : W := 0xffffff9f9f003bfe9aad01400
def v511 : W := 0xffffff9c00003bfe9aad00000
def v512 : W := 0xffffff939cc3fbfe9aa000000
def v513 : W := 0xffffff9e7f003bfe9aad01400
def v514 : W := 0xffffffe000003bfe9aa000000
def v515 : W := 0xffffff9fff003bfe9aa000000
def v516 : W := 0xffffffe0000c3bfe9aad00011
def v517 : W := 0xe060007c00fc3800000d00000
def v518 : W := 0xff80007fffc03d60001d29400
def v519 : W := 0xffffffe0004c3bfe9aa000000
def v520 : W := 0xfffffff000003bfe9aad00000
def v521 : W := 0xfffffff000fcfbfe9aad00011
def v522 : W := 0xfffffff000cffbfe9aad00011
def v523 : W := 0xff80007fff833d60001d29400
def v524 : W := 0xff80007fff4cfd60001d29411
def v525 : W := 0xff80007fffb03d60001d29400
def v526 : W := 0xff8607ffff003d60001d29400
def v527 : W := 0xff811fffff003d60001d29400
def v528 : W := 0xff81067fff003d60001d29400
def v529 : W := 0xff80007ffffc3d60001d29400
def v530 : W := 0xff80007fffc3fd60001d29400
def v531 : W := 0xff81187fff003d60001d29400
def v532 : W := 0xff86007fff003d60001d29400
def v533 : W := 0xff81e07fff003d60001d29400
def v534 : W := 0xff8601ffff003d6a803d29400
def v535 : W := 0xff871f8e73b33961454294acc
def v536 : W := 0xff871f8000003960000000000
def v537 : W := 0xff8619ffff003d60001d29400
def v538 : W := 0xff98007fff003d60001d29400
def v539 : W := 0xffe0007fff4c3d60001d29400
def v540 : W := 0xff9e007fff003d6a801d29400
def v541 : W := 0xff98007fff40fd60001d29400
def v542 : W := 0xff98007fff03fd60001d29400
def v543 : W := 0xffe0007fff0c3d6a801d29411
def v544 : W := 0xffe0007fff003d60001d29400
def v545 : W := 0xffe0007fff3c3d60001d29400
def v546 : W := 0xffe6007fff003d6a801d29400
def v547 : W := 0xfff8007fff003d6a801d29400
def v548 : W := 0xfff8007fffcffd6a801d29411
def v549 : W := 0xfff8007ffffcfd6a801d29411
def v550 : W := 0xfffe00000000396a800000000
def v551 : W := 0xe07e007e60fff80b800f00055
def v552 : W := 0xe07e007c1ffff80b800f01455
def v553 : W := 0xe07e007e10fff80b800f00055
def v554 : W := 0xe07e007f80fff80b800f00055
def v555 : W := 0xe07e007e73fff80b800f00055
def v556 : W := 0xe07e007f9cfff80b800f00055
def v557 : W := 0xff98007fff00fd6a801d29411
def v558 : W := 0xe300007f9c003800000d00000
def v559 : W := 0xe0fe007c00fff80b800f00055
def v560 : W := 0xe07fe07c00fff80b800f00055
def v561 : W := 0xe07f1ffc00fff80b800f00055
def v562 : W := 0xe07f187c00fff80b800f00055
def v563 : W := 0xe080007e73003800000d00000
def v564 : W := 0xe0fe007c63fff80b800f00055
def v565 : W := 0xe0fe007c13fff80b800f00055
def v566 : W := 0xe0fe007c03fff96b800f01455
def v567 : W := 0xe0ff1f800000380a800000000
def v568 : W := 0xe0fe07fc00fff80b800f00055
def v569 : W := 0xe0fe01fc03fff80b804f00855
def v570 : W := 0xe0fe01fc00fff96b802f00055
def v571 : W := 0xe0fe19fc00fff80b800f00055
def v572 : W := 0xe37e007d8cfff80b800f00055
def v573 : W := 0xe37e007c0cfff96b800f01455
def v574 : W := 0xe37e007c00fff80b800f00055
def v575 : W := 0xe319e67f9cc3f884718dc630a
def v576 : W := 0xe37e007c1cfff80b800f00055
def v577 : W := 0xe3fe007e7ffff96b800f01455
def v578 : W := 0xe3fe007c00fff96b800f00055
def v579 : W := 0xe380007c1f003960000d01400
def v580 : W := 0xe3fe007ffffff80b800f00055
def v581 : W := 0xe3fe007f9ffff96b800f01455
def v582 : W := 0xfc7e007c00fff80b800f00055
def v583 : W := 0x9c61f863f3fc06106f50fcba8
def v584 : W := 0x9c61f863e0ff06106e10f83a0
def v585 : W := 0x9c61f863f0fc06106e10f83a0
def v586 : W := 0x9c61f863e0ffc6106f10fe3aa
def v587 : W := 0x9c61f863f0ff06106f10fc3a8
def v588 : W := 0x9c61f873ecfcc6106e10fa3a2
def v589 : W := 0x9c61f86ff3fc06106e10f83a0
def v590 : W := 0x9c61f863fffc06106e10f97a0
def v591 : W := 0x9c61f863fcfc06106f10fe3aa
def v592 : W := 0x9c61f873e0ffc6106e10f83a0
def v593 : W := 0x9c61f873fcfc06106e10f83a0
def v594 : W := 0x9c61fe63e0fc06106e10f83a0
def v595 : W := 0xfcfe007c00fff96b800f00055
def v596 : W := 0xe07f067c00fff80b800f00055
def v597 : W := 0xffffffe0003c3bfe9aa000000
def v598 : W := 0x9c67ffe3e0fc06106e10f83a0
def v599 : W := 0x9c61fe63f0fc06106f10fc3a8
def v600 : W := 0x9c61ffe3e0fc06106f50fcba8
def v601 : W := 0x9ce1f9e3e3fc06106e50f8ba0
def v602 : W := 0x9ce1f863f3fc06106e10f83a0
def v603 : W := 0x9c79f863e0ffc6106e10f83a0
def v604 : W := 0x9ce1ffe3e0fc06106e10f83a0
def v605 : W := 0xbc67f863e0fc06106e10f83a0
def v606 : W := 0x9f61f863fcfc06106e10f83a0
def v607 : W := 0xbc61f86fe0fc06106e10f83a0
def v608 : W := 0xbce1f863e0fc06106e10f83a0
def v609 : W := 0xbc80006ff3000400001028000
def v610 : W := 0xbce1f86fe3fc06106e10f83a0
def v611 : W := 0xbce7f9e3e0fc06106e10f83a0
def v612 : W := 0xbce1ffeff3fc06106f50fcba8
def v613 : W := 0xdc79f873fcffc6106f10fe3aa
def v614 : W := 0xbce7ffe3f3fc06106f50fcba8
def v615 : W := 0xdc79f873e0fcc6106e10f83a0
def v616 : W := 0xdc61f873e0fc06106e10f83a0
def v617 : W := 0xdc79f863e0fc06106e10f83a0
def v618 : W := 0xdf61f863e0fc06106e10f83a0
def v619 : W := 0xdf000073fc000400001028000
def v620 : W := 0xdf61f873ecfc06106e10f83a0
def v621 : W := 0xdf61f873fcffc6106f10fe3aa
def v622 : W := 0x4319e6139cffc0847580d63aa
def v623 : W := 0xffe1f87ffffc06106e10f83a0
def v624 : W := 0xdf79f873fcffc6106e10f83a0
def v625 : W := 0x4319e6139cf3c0847180c630a
def v626 : W := 0x4319e613fcf3c0847580d638a
def v627 : W := 0x4319e613fcc3c0847180c630a
def v628 : W := 0x4319e613ffc3c08475c0d6b8a
def v629 : W := 0x631fe6139cc3c0847180c630a
def v630 : W := 0x4379e6139cffc0847180c630a
def v631 : W := 0x4319fe139cf3c0847580d638a
def v632 : W := 0x4319fe139cc3c0847180c630a
def v633 : W := 0x4319e6739cffc0847180c630a
def v634 : W := 0x4319fe13fcc3c0847580d638a
def v635 : W := 0x4319ff939cc3c08475c0d6b8a
def v636 : W := 0x431fff939cc3c0847180c630a
def v637 : W := 0x4399ff939cc3c0847180c630a
def v638 : W := 0x4399e7939fc3c08471c0c6b0a
def v639 : W := 0x4399e613ffc3c0847180c630a
def v640 : W := 0x6319e61f9cc3c0847180c630a
def v641 : W := 0x6399e61f9fc3c0847180c630a
def v642 : W := 0x6399e6139cc3c0847180c630a
def v643 : W := 0x6380001fff000000000000000
def v644 : W := 0x6399ff9fffc3c08475c0d6b8a
def v645 : W := 0x639fe7939cc3c0847180c630a
def v646 : W := 0x639fff8000000084108000000
def v647 : W := 0x639fff93ffc3c08475c0d6b8a
def v648 : W := 0x8061e06380fc00006000c0300
def v649 : W := 0xbce6186c633c3f7b8e1f394f5
def v650 : W := 0x4319e61fffc3c0847180c630a
def v651 : W := 0xe07fe07f80fff80be00fc0355
def v652 : W := 0xc379e6139cc3c0847180c630a
def v653 : W := 0xbce619ec633c3f7b8a3f29455
def v654 : W := 0xc319e6739cc3c0847180c630a
def v655 : W := 0xc379e6739ccfc0847180c630a
def v656 : W := 0xdf19e6139cc3c0847180c630a
def v657 : W := 0x20871f9e7fb3c001454296ace
def v658 : W := 0x20871f8ff3b30001454294acc
def v659 : W := 0x20871f8e73ff00016542d4bec
def v660 : W := 0x20871f8e73f3c0016542d6bce
def v661 : W := 0x20871f8e73f30001454294acc
def v662 : W := 0x20871f8e73ffc001454294add
def v663 : W := 0x20871f8fffb300016542d6bce
def v664 : W := 0x20871f8ff3f300016542d4bcc
def v665 : W := 0x20871f9e73f3c001454294acc
def v666 : W := 0x20871fee73ff0001454294acc
def v667 : W := 0x20871f9fffb30001454294acc
def v668 : W := 0x2087ff8e73f300016542d4bcc
def v669 : W := 0x2087ff8e73b30001454294acc
def v670 : W := 0x23871f8fffb30001454294acc
def v671 : W := 0x209f1f8e73f3c001454294acc
def v672 : W := 0x20e71f8e73ff0001454294acc
def v673 : W := 0x4019061210c3c000410084208
def v674 : W := 0x430106139c830000410084208
def v675 : W := 0x609f1f8e73b30001454294acc
def v676 : W := 0x60871f9e73b30001454294acc
def v677 : W := 0x601e001c00f3c001000200044
def v678 : W := 0x609f1f9e73b3c001454294acc
def v679 : W := 0x609f1f9ffff3c0016542d6bce
def v680 : W := 0x63871f9e7fb30001454294acc
def v681 : W := 0x63871f8e73b30001454294acc
def v682 : W := 0x8061186260fc0000440090280
def v683 : W := 0x63871f9ffff3c0016542d6bce
def v684 : W := 0x639f1f9ffff3c001454294acc
def v685 : W := 0xa0e71f8e73b30001454294acc
def v686 : W := 0xa066006c00ff0001000200044
def v687 : W := 0xa0871fee73b30001454294acc
def v688 : W := 0xa0e71fee73bf0001454294acc
def v689 : W := 0xbc871f8e73b30001454294acc
def v690 : W := 0xdf78e0718c4c3ffebabd69520
def v691 : W := 0xfff8e07fff003ffe9abd29400
def v692 : W := 0xdf78e06000003ffe9abd29400
def v693 : W := 0xfffffff18c003ffe9abd29400
def v694 : W := 0xdf78e0718c40fffebabd6b502
def v695 : W := 0xdf78e0718c4cfffe9abd29411
def v696 : W := 0xff81067fff833d60411dad608
def v697 : W := 0x9c61f863e03c06100e10380a0
def v698 : W := 0xc00b30001000200044
def v699 : W := 0x210830000410084208
def v700 : W := 0xc00000000000000
def v701 : W := 0xb00000000000000
def v702 : W := 0x830000000000000
def v703 : W := 0x0
def v704 : W := 0xb30001454294acc
def v705 : W := 0xffc001000200055
def v706 : W := 0xfc00006400d03a0
def v707 : W := 0xc3c0006100c630a
def v708 : W := 0x210000000000000000
def v709 : W := 0x380c000006000c0300
def v710 : W := 0x273000000454094a88
def v711 : W := 0x260b00000440090280
def v712 : W := 0x260000000000000000
def v713 : W := 0x380000000000000000
def v714 : W := 0x3e00004006410f83a0
def v715 : W := 0x39c0000006100c630a
def v716 : W := 0x3ff000400001029400
def v717 : W := 0xe73000000000000000
def v718 : W := 0xc633000010442108c4
def v719 : W := 0xc1303000101420484c
def v720 : W := 0x1000c3c000000000000
def v721 : W := 0x118c40c000200042102
def v722 : W := 0x101c03c00001000600a
def v723 : W := 0x139c000000000000000
def v724 : W := 0x63e0000400001028000
def v725 : W := 0x1c0003c001000f00055
def v726 : W := 0x1c1f000000000d01400
def v727 : W := 0x60603c04000410380a0
def v728 : W := 0x6000fc0000000000000
def v729 : W := 0x61804c0400201068120
def v730 : W := 0x6c003c0001000f00055
def v731 : W := 0x6c63000400001d29400
def v732 : W := 0x70004cc000000d00011
def v733 : W := 0x7fe0ffc401641ff83f5
def v734 : W := 0x7e73ffc001454f94add
def v735 : W := 0x7f9cffc001610fc635f
def v736 : W := 0x7ffffc0400641df97a0
def v737 : W := 0x7fffb30401455fbdecc
def v738 : W := 0x7fffc3c400611def70a
def v739 : W := 0x1000200800000400080200
def v740 : W := 0x7fffffc401001f29455
def v741 : W := 0x1060000000000000000000
def v742 : W := 0x1060210000000410084208
def v743 : W := 0x1060e73b30001454294acc
def v744 : W := 0x1180260000000440090280
def v745 : W := 0x1180000b00000440090280
def v746 : W := 0x1180000000000000000000
def v747 : W := 0x1180e73b30001454294acc
def v748 : W := 0x11863e0fc04006410f83a0
def v749 : W := 0x1e00000000000000000000
def v750 : W := 0x11f8000000000454094a88
def v751 : W := 0x1e00000c000006000c0300
def v752 : W := 0x718c000400001d29400
def v753 : W := 0x71f8000000000000000000
def v754 : W := 0x1e600000000847180c630a
def v755 : W := 0x1e063e0fc04006410f83a0
def v756 : W := 0x1f800000002106e00d03a0
def v757 : W := 0x607800003000101420484c
def v758 : W := 0x6000000b30001000200044
def v759 : W := 0x1ff80000002941aa000000
def v760 : W := 0x61980003000010442108c4
def v761 : W := 0x18000000c3c000000000000
def v762 : W := 0x71f8260b30001454294acc
def v763 : W := 0x71f8210b30001454294acc
def v764 : W := 0x71f8e73b30001454294acc
def v765 : W := 0x18e0000040c084308042102
def v766 : W := 0x1806000003c08411800600a
def v767 : W := 0x19e60000000084108000000
def v768 : W := 0x19e60210c3c0847180c630a
def v769 : W := 0x60000000fc0000000000000
def v770 : W := 0x1e07800000008e90a000000
def v771 : W := 0x1e00000003c00b800200055
def v772 : W := 0x19e6139cc3c0847180c630a
def v773 : W := 0x1fff8000f3c08575c2d6bce
def v774 : W := 0x60e000004c02102a0040120
def v775 : W := 0x601800003c02100e00100a0
def v776 : W := 0x61f800000002100a0000000
def v777 : W := 0x79fe0000ffc2947f80d63aa
def v778 : W := 0x6619800000021a8a2000000
def v779 : W := 0x61f863e0fc06106e10f83a0
def v780 : W := 0x61f80380fc02106e00d03a0
def v781 : W := 0x61f80260fc02106e00d03a0
def v782 : W := 0x660000003c000b800200055
def v783 : W := 0x780000004cc00a800000011
def v784 : W := 0x67ff8000ff02116f42d4bec
def v785 : W := 0x78e0000000029e9aa000000
def v786 : W := 0x19e60380c3c0847180c630a
def v787 : W := 0x7f1f8000ffc00bc54294add
def v788 : W := 0x7ff80000ffc21bee02d03f5
def v789 : W := 0x7fe60000ffc08ff182c635f
def v790 : W := 0x80078013000000014004808
def v791 : W := 0x7fff8000c3c29efba0c630a
def v792 : W := 0x7fff8000b3029fdfe294acc
def v793 : W := 0x7fff8000ffc29f9aa200055
def v794 : W := 0x7fff8000fc029efea0d03a0
def v795 : W := 0x80000273000000000000000
def v796 : W := 0x811f8000000000000000000
def v797 : W := 0x80198063000000044010880
def v798 : W := 0x300e0018c000084308042102
def v799 : W := 0x30000039c000000000000000
def v800 : W := 0x871f8273b30001454294acc
def v801 : W := 0x811f8e73b30001454294acc
def v802 : W := 0x30006001c00008411800600a
def v803 : W := 0x301e60000000084108000000
def v804 : W := 0x301e6039cc000847180c630a
def v805 : W := 0x301e6039c8300847180c630a
def v806 : W := 0x38000001f000160000001400
def v807 : W := 0x319e6039cc3c0847180c630a
def v808 : W := 0x301e6139cc3c0847180c630a
def v809 : W := 0x3800780000001e410a000000
def v810 : W := 0x1c001800600006100e10380a0
def v811 : W := 0x1c000003e0000400001028000
def v812 : W := 0x1c00e001800006102a1068120
def v813 : W := 0x1f00e000000003f41aa000000
def v814 : W := 0x1c80000063000560001029400
def v815 : W := 0x1c01f863e0fc06106e10f83a0
def v816 : W := 0x1c01f803e0c006106e10f83a0
def v817 : W := 0x1c01f803e0b006106e10f83a0
def v818 : W := 0x1c61f803e0fc06106e10f83a0
def v819 : W := 0x1c801980000003700a2000000
def v820 : W := 0x1f0000018c000560001029400
def v821 : W := 0x1f811f83ff0005604550bde88
def v822 : W := 0x2000000c00000000000000000
def v823 : W := 0x1f81f803ff0007706e10f97a0
def v824 : W := 0x1f81ff83ff0007f41ab029400
def v825 : W := 0x1f81ff839c0003f47ba0c630a
def v826 : W := 0x1f81ff82730003f45fe094a88
def v827 : W := 0x1f81ff83e00007f47eb0f83a0
def v828 : W := 0x2006000c00030001000200044
def v829 : W := 0x2006000c0000380b800f00055
def v830 : W := 0x2006000000000000000000000
def v831 : W := 0x2006000c00300001000200044
def v832 : W := 0x20071f8c00b30001454294acc
def v833 : W := 0x2007060e10b3000141028424c
def v834 : W := 0x2006007c00ffc001000f00055
def v835 : W := 0x2006000e73b30001454294acc
def v836 : W := 0x2007180e60b300014402902c4
def v837 : W := 0x2080000000000000000000000
def v838 : W := 0x207e000c00ffc00b800200055
def v839 : W := 0x2080000c03003960000d01400
def v840 : W := 0x1f81e603ff0005e47190ef70a
def v841 : W := 0x2080000c63000000000000000
def v842 : W := 0x208601800000396a802000000
def v843 : W := 0x2086078000000000000000000
def v844 : W := 0x2086018c03000001004200844
def v845 : W := 0x2086078c13b3000101420484c
def v846 : W := 0x2086198000000000000000000
def v847 : W := 0x2086198e73b30001454294acc
def v848 : W := 0x2086198c63b300010442108c4
def v849 : W := 0x2086078e73b30001454294acc
def v850 : W := 0x2080000c13000000000000000
def v851 : W := 0x20871f8c13b30001454294acc
def v852 : W := 0x20e7ff8e73ff02116f42d4bec
def v853 : W := 0x20871ffe73ffc001454f94add
def v854 : W := 0x20871fffffb30401455fbdecc
def v855 : W := 0x209fff8e73f3c08575c2d6bce
def v856 : W := 0x3c87ff8ff3b306116f52fcbec
def v857 : W := 0x20ffff8e73b3029fdfe294acc
def v858 : W := 0x20ff1f8e73ffc00bc54294add
def v859 : W := 0x2387ff8fffb3008575c2d6bce
def v860 : W := 0x401800100040c000000000000
def v861 : W := 0x4000001000000000000000000
def v862 : W := 0x401800100000f80a800d00011
def v863 : W := 0x4018000000000000000000000
def v864 : W := 0x401800100003c000000000000
def v865 : W := 0x430000101c000000000000000
def v866 : W := 0x4300000000000000000000000
def v867 : W := 0x430000100c003960000d01400
def v868 : W := 0x430000118c000000000000000
def v869 : W := 0x43180000000039ee90a000000
def v870 : W := 0x431800100c00c084108002002
def v871 : W := 0x4318060000000084108000000
def v872 : W := 0x4318e00000000084108000000
def v873 : W := 0x4319e6101c03c08411800600a
def v874 : W := 0x4319e60210830084518084208
def v875 : W := 0x4319e60000c3c0847180c630a
def v876 : W := 0x4319e6039c0000847180c630a
def v877 : W := 0x4319e60380c000847080c0300
def v878 : W := 0x4319e6139c40c0847180c630a
def v879 : W := 0x4319e6118c40c084308042102
def v880 : W := 0x4319e6101cc3c0847180c630a
def v881 : W := 0x4319e67fffc3c484719def70a
def v882 : W := 0x4319e673fcffc4847590fe3aa
def v883 : W := 0x4319e61ffff3c08575c2d6bce
def v884 : W := 0x4319e67f9cffc085718fc635f
def v885 : W := 0x431fff939cf3c08575c2d6bce
def v886 : W := 0x4379fe139cffc2947f80d63aa
def v887 : W := 0x1c01f800000002100a0000000
def v888 : W := 0x601e00000000380a800000000
def v889 : W := 0x437fff939cc3c29efba0c630a
def v890 : W := 0x437fff800000029e9aa000000
def v891 : W := 0x5f99ff939cc3c3f47ba0c630a
def v892 : W := 0x5f99ff80000003f41aa000000
def v893 : W := 0x5f99e613ffc3c5e47190ef70a
def v894 : W := 0x6000001c00003800000d00000
def v895 : W := 0x601e001c00b3f80b800f00055
def v896 : W := 0x631fe61f9cf3c0857182c634e
def v897 : W := 0x609f1f9e73b3f80bc54f94add
def v898 : W := 0x607e001c00fff80b800f00055
def v899 : W := 0x601e007c00fff80b800f00055
def v900 : W := 0x609e079c1303f80b814f0485d
def v901 : W := 0x631e061c1c03f88f918f0605f
def v902 : W := 0x631fe61f9cc3f88ff18fc635f
def v903 : W := 0x6380000000003960000000000
def v904 : W := 0x6399e61f9fc3f9e4718dc770a
def v905 : W := 0x6386079c1f033961014f05c4c
def v906 : W := 0x63871f9e7fb33961454f95ecc
def v907 : W := 0x6398061c1f03f9e4118d0740a
def v908 : W := 0x639f1f8e73b339efd5e294acc
def v909 : W := 0x639e07901c03f9ee91a00600a
def v910 : W := 0x639e078c130339ef91e20484c
def v911 : W := 0x639e079c1f03c08511c20684e
def v912 : W := 0x639fe7939cc3f9eef1a0c630a
def v913 : W := 0x639fe780000039ee90a000000
def v914 : W := 0x639f1f9e7fb3c08555c296ace
def v915 : W := 0x639fe79f9fc3c08571c2c6b4e
def v916 : W := 0x639fff8e73b3008555c294acc
def v917 : W := 0x80600060003c0000000000000
def v918 : W := 0x8060000000000000000000000
def v919 : W := 0x8000006000000000000000000
def v920 : W := 0x80600060000c380a800d00011
def v921 : W := 0x80600060004c0000000000000
def v922 : W := 0x9c00006060000400001028000
def v923 : W := 0x9c00006000003d60001d29400
def v924 : W := 0x9c00000000000000000000000
def v925 : W := 0x9c00006180000400001028000
def v926 : W := 0x9c60e000000002100a0000000
def v927 : W := 0x9c60000000003b7a8a2000000
def v928 : W := 0x9c01e063e0c004006010e8300
def v929 : W := 0x9c011863e0b004004410b8280
def v930 : W := 0x9c00007fff000400001d29400
def v931 : W := 0x9c01f863e00006106e10f83a0
def v932 : W := 0x9c600060000c06100a1028020
def v933 : W := 0x9c601800000002100a0000000
def v934 : W := 0x9c601863e03c06100e10380a0
def v935 : W := 0x9c601863e0fc06106e10f83a0
def v936 : W := 0x9c60e063e04c06102a1068120
def v937 : W := 0x9c000063e0fc04006410f83a0
def v938 : W := 0x63ffff8000003bfe9aa000000
def v939 : W := 0x9c61f863e04c06106e10f83a0
def v940 : W := 0x9c61f803e00006106e10f83a0
def v941 : W := 0x9c61f80260b002104e0090280
def v942 : W := 0x9c61f80000fc02106e00d03a0
def v943 : W := 0x9c61f80380c002106a00c0300
def v944 : W := 0x9c61f861804c06102a1068120
def v945 : W := 0x9c61f863e00006100a1028000
def v946 : W := 0x9c61f87ffffc06106e1df97a0
def v947 : W := 0x9c61f87fe0ffc6116e1ff83f5
def v948 : W := 0x9c67ffe3e0ff06116f52fcbec
def v949 : W := 0x9c79fe63e0ffc6947f90fe3aa
def v950 : W := 0x9fe1f863fffc07706e10f97a0
def v951 : W := 0x9f800063ff000560001029400
def v952 : W := 0x9fe1ff80000003f41aa000000
def v953 : W := 0xa066006c00bf380b800f00055
def v954 : W := 0xa06600000000380a800000000
def v955 : W := 0xa066007c00fff80b800f00055
def v956 : W := 0xbc66186c603c3e1b8e1f380f5
def v957 : W := 0xa0e71fee73bf380bc54f94add
def v958 : W := 0xa0e619ec633c380b844f108d5
def v959 : W := 0xbc67f86fe0ff06116e12f83e4
def v960 : W := 0xbc67f86fe0fc3e1bee1ff83f5
def v961 : W := 0xbc80000000003960000000000
def v962 : W := 0xbce0186c633c3f700e1d394a0
def v963 : W := 0xbc80007fff003d60001d29400
def v964 : W := 0xbc80006fe3003d60001d29400
def v965 : W := 0xbc871fee73b33d61455fbdecc
def v966 : W := 0xbc8619ec63303d61045f39cc4
def v967 : W := 0xbc871feff3b304014552bcacc
def v968 : W := 0xbce6006c633c3d6b801f29455
def v969 : W := 0xbce1f86fe3fc3f706e1df97a0
def v970 : W := 0xbce6198c63303b7b8e62108c4
def v971 : W := 0xbce619e0603c3f7a8e30380a0
def v972 : W := 0x9fe1ffe3e0fc07f47eb0f83a0
def v973 : W := 0xbce71fee73bf06114f52bcaec
def v974 : W := 0xbce619ec633c06110e52388e4
def v975 : W := 0xbce619ec63003f7a8a3d29400
def v976 : W := 0xbce71f8e73b33b7bcf6294acc
def v977 : W := 0xbce7f9e3e0fc3f7aee30f83a0
def v978 : W := 0xbce7f98000003b7a8a2000000
def v979 : W := 0xbce7f9efe3fc06116e52f8be4
def v980 : W := 0xc000007000003800000d00000
def v981 : W := 0xc07800000000380a800000000
def v982 : W := 0xdf60e0718c4c3f702a1d69520
def v983 : W := 0xdc79f873e0fcfe1aee1df83b1
def v984 : W := 0xc379e6739ccff88ef18dc631b
def v985 : W := 0xc378e0718c4cf88eb08d42113
def v986 : W := 0xdc78e071804cfe1aaa1d68131
def v987 : W := 0xdf000073ec003d60001d29400
def v988 : W := 0xdf19e6739cc3fde4719def70a
def v989 : W := 0xdf18e0718c40fde4309d6b502
def v990 : W := 0xdf19e673fcc3c4847190ee30a
def v991 : W := 0xdf61f873ecfc3f706e1df97a0
def v992 : W := 0xdf78e061804c3ffebab068120
def v993 : W := 0xdf78e0118c40fbfebaa042102
def v994 : W := 0xdf79f80000003bfe9aa000000
def v995 : W := 0xdf79e6139cc3fbfefba0c630a
def v996 : W := 0xdf79e60000003bfe9aa000000
def v997 : W := 0xdf78e0718c4cc6943a906a122
def v998 : W := 0xdf79e6739ccfc6947b90ee32a
def v999 : W := 0xdf79f873ecfcc6947e90fa3a2
def v1000 : W := 0xdf79f863e0fc3ffefeb0f83a0
def v1001 : W := 0xdf79fe00000002941a8000000
def v1002 : W := 0xbce619ec003c3b7b8a2f00055
def v1003 : W := 0xe066007c003c380b800f00055
def v1004 : W := 0xdf800073ff003d60001d29400
def v1005 : W := 0xdf79fe63e0fc06947e90f83a0
def v1006 : W := 0xe000000000003800000000000
def v1007 : W := 0xdff9ff8000003bfe9aa000000
def v1008 : W := 0xe006007c00b33801000f00044
def v1009 : W := 0xe01e007c0003f80b800f00055
def v1010 : W := 0xe07e000c00b3380b800200044
def v1011 : W := 0xe07e006c003c380b800f00055
def v1012 : W := 0xe07e001c0003f80b800f00055
def v1013 : W := 0xe07e007c004ff80b800f00055
def v1014 : W := 0xe07e007c003ff80b800f00055
def v1015 : W := 0xe07e007c007cf80b800f00055
def v1016 : W := 0xe07fe67c00fff88ff18fc635f
def v1017 : W := 0xe07f067e10fff80bc10f8425d
def v1018 : W := 0xe07e007fe0fffc0be41ff83f5
def v1019 : W := 0xe07e007f9cfff80be10fc635f
def v1020 : W := 0xe07e007e73fff80bc54f94add
def v1021 : W := 0xe07e007ffffffc0b801f29455
def v1022 : W := 0xe07f1ffc00fff80bc54f94add
def v1023 : W := 0xe07f187e60fff80bc40f902d5
def v1024 : W := 0xe0871ffe73b33801454f94acc
def v1025 : W := 0xe07ffffc00fffa9f9aaf00055
def v1026 : W := 0xe07ff87c00fffa1bee0fd03f5
def v1027 : W := 0xe0fe07fc13fff80b814f0485d
def v1028 : W := 0xe0fe19fc63fff80b844f108d5
def v1029 : W := 0xe37fe6000000388e908000000
def v1030 : W := 0xe0ff1f8e73b3380bc54294acc
def v1031 : W := 0xe37e067c1cfff88f918f0605f
def v1032 : W := 0xe37fe67c00fff88f908f00055
def v1033 : W := 0xe37fe6139cc3f88ef180c630a
def v1034 : W := 0xe3fe0780000039ee90a000000
def v1035 : W := 0xe3fffffffffff88ff5cfd6bdf
def v1036 : W := 0xff7ffe7ffcfffe9fff9ffe3ff
def v1037 : W := 0xfc80007c63003d60001d29400
def v1038 : W := 0xfc7ff80000003a1a8a0000000
def v1039 : W := 0xfc7e187c60fffe1b8e1f380f5
def v1040 : W := 0xfc7e007fe0fffc0b801f28055
def v1041 : W := 0xfc61f87fe0fc3e106e1df83a0
def v1042 : W := 0xfc7ff863e0fc3e1aee10f83a0
def v1043 : W := 0xff00007d8c003d60001d29400
def v1044 : W := 0xfcfe19fc00fffb7b8a2f00055
def v1045 : W := 0xfcfe198000003b7a8a2000000
def v1046 : W := 0xfcfe007c63fffd6b801f29455
def v1047 : W := 0xfcfffffff3fffe1bef5ffcbfd
def v1048 : W := 0xff7ee00000003bfe9aa000000
def v1049 : W := 0xff7e007d8cfffd6b801f29455
def v1050 : W := 0xff7ee07c00fffbff9aaf00055
def v1051 : W := 0xff800063e0003d60001028000
def v1052 : W := 0xff80007d9f003d60001d29400
def v1053 : W := 0xff8000718c003d60001d29400
def v1054 : W := 0xff80006c63003d60001d29400
def v1055 : W := 0xff80007c7f003d60001d29400
def v1056 : W := 0xff80007def003d60001d29400
def v1057 : W := 0xff80007fffb33d61455fbdecc
def v1058 : W := 0xff811fffff003d60455dbde88
def v1059 : W := 0xff80007ffffffd61001f29455
def v1060 : W := 0xff80007ffffc3d60641df97a0
def v1061 : W := 0xff81187fffb03d60441db9680
def v1062 : W := 0xff81e67fff003de4719def70a
def v1063 : W := 0xff81e07fffc03d60601de9700
def v1064 : W := 0xff81f87fff003f706e1df97a0
def v1065 : W := 0xff8607ffff033d61015f2dc4c
def v1066 : W := 0xff86007fffb33d61001f29444
def v1067 : W := 0xff81ffffff003ff41abd29400
def v1068 : W := 0xff8619ffff303d61045f39cc4
def v1069 : W := 0xff9e07ffff003dee90bd29400
def v1070 : W := 0xff99e67fff003de4109d29400
def v1071 : W := 0xff99e600000039e4108000000
def v1072 : W := 0xff98e07fff40fde4309d6b502
def v1073 : W := 0xff98067fff03fde4119d2f40a
def v1074 : W := 0xff99e6139cc3f9e47180c630a
def v1075 : W := 0xff9e007fff03fd6b801f29455
def v1076 : W := 0xff9e0780000039ee90a000000
def v1077 : W := 0xffe1f80000003b700a0000000
def v1078 : W := 0xffe0187fff3c3f700e1d394a0
def v1079 : W := 0xff9ffffffff3fde575dffffce
def v1080 : W := 0xffe0e07fff4c3f702a1d69520
def v1081 : W := 0xffe1f87fff003f700a1d29400
def v1082 : W := 0xffe1f863e0fc3f706e10f83a0
def v1083 : W := 0xff80007fffc3fd60611def70a
def v1084 : W := 0xfc00007fe0003c00001d28000
def v1085 : W := 0xfff8e00000003bfe9aa000000
def v1086 : W := 0xffe7ffffffff3f716f5ffdfec
def v1087 : W := 0xffe619ffff003f7a8a3d29400
def v1088 : W := 0xffe6198000003b7a8a2000000
def v1089 : W := 0xfff9fe7ffffffff47f9dff7aa
def v1090 : W := 0xffff1ffffffffd6bc55fbdedd
def v1091 : W := 0xfffee78000003bfe9aa000000
def v1092 : W := 0xfffe1f8000003bfe9aa000000
def v1093 : W := 0xfffef98000003bfe9aa000000
def v1094 : W := 0xfffff87fffffff7bee1ff97f5
def v1095 : W := 0xffffe67ffffffdeff19fef75f
def v1096 : W := 0xffffff839c003bfefba0c630a
def v1097 : W := 0xffffff8210833bfedba084208
def v1098 : W := 0xffffff8000fc3bfefea0d03a0
def v1099 : W := 0xffffff8000c3fbfefba0c630a
def v1100 : W := 0xffffff8000b33bffdfe294acc
def v1101 : W := 0xffffff8000fffbff9aa200055
def v1102 : W := 0xffffff8273003bfedfe094a88
def v1103 : W := 0xffffff8260b03bfedea090280
def v1104 : W := 0xffffff8380c03bfefaa0c0300
def v1105 : W := 0xffffff8c00b33bff9aa200044
def v1106 : W := 0xffffff83ff003ffe9ab029400
def v1107 : W := 0xffffff83e0003ffefeb0f83a0
def v1108 : W := 0xffffff8c13033bff9be20484c
def v1109 : W := 0xffffffe1804c3ffebab068120
def v1110 : W := 0xffffff918c40fbfebaa042102
def v1111 : W := 0xffffff9ffff3fbffffe2d6bce
def v1112 : W := 0xffffffeff3ff3ffffff2fcbec
def v1113 : W := 0xffffffec003c3bff9aaf00055
def v1114 : W := 0xffffffe3e0003ffe9ab028000
def v1115 : W := 0xffffffec63003ffe9abd29400
def v1116 : W := 0xfffffff3fcfffffeffb0fe3aa
def v1117 : W := 0xffffffffffffc6957fd2febee
def v1118 : W := 0xffffffff9cfffbfffbafc635f
def v1119 : W := 0xfffffffe73fffbffdfef94add
def v1120 : W := 0xffffffffe0fffffffebff83f5
def v1121 : W := 0xffffffffffc3fffefbbdef70a
def v1122 : W := 0xffffffffffb33fffdfffbdecc
def v1123 : W := 0xfffffffffffc3ffefebdf97a0
def v1124 : W := 0xffffffffffffffff9abf29455
def v1125 : W := 0xffffff901c03fbfe9ba00600a
def v1126 : W := 0xffe6007fff3c3d6b801f29455
def v1127 : W := 0xdf79fe139cc3c2947b80c630a
def v1128 : W := 0x437fe6139cffc08ff182c635f

def ins6 : List W := [v0, v1, v2, v3, v4, v5]
theorem nd6 : ins6.Nodup := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem rows6 : ∀ j : Fin 100, Nat.testBit (4278124266 * 2 ^ 32 + 4277074944) (∑ i : Fin 6, if (ins6.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_0 : everyKey (fun q => !doneTest q) tree_0 = true := by decide +kernel
theorem closed_0 : Closed 0 tree_0 := closed_nil tree_0 ok_tree_0
def tree_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_1 : everyKey (rowOK 0 tree_0) tree_1 = true := by decide +kernel
theorem closed_1 : Closed 1 tree_1 := closed_next 0 (by decide) tree_1 tree_0 closed_0 ok_tree_1
def tree_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_2 : everyKey (rowOK 1 tree_1) tree_2 = true := by decide +kernel
theorem closed_2 : Closed 2 tree_2 := closed_next 1 (by decide) tree_2 tree_1 closed_1 ok_tree_2
def tree_3 : BinaryTree (List W) := (.node [v6,v7,v8,v4] (.node [v9,v1,v10,v11] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_3 : everyKey (rowOK 2 tree_2) tree_3 = true := by decide +kernel
theorem closed_3 : Closed 3 tree_3 := closed_next 2 (by decide) tree_3 tree_2 closed_2 ok_tree_3
def tree_4ll : BinaryTree (List W) := (.node [v12,v1,v13,v4,v5] (.node [v14,v0,v1,v10,v4] (.node [v15,v0,v1,v2,v16] (.node [v17,v15,v0,v1,v2] (.node [v18,v19,v20,v3,v4] (.node [v18,v1,v21,v3,v4] .nil .nil) .nil) (.node [v15,v0,v1,v2,v3] (.node [v15,v9,v1,v2,v3] .nil .nil) .nil)) (.node [v22,v23,v24,v4,v5] (.node [v22,v0,v25,v4,v5] (.node [v15,v1,v2,v26,v3] .nil .nil) .nil) (.node [v14,v0,v1,v27,v4] (.node [v28,v14,v0,v1,v2] .nil .nil) .nil))) (.node [v29,v25,v3,v4,v5] (.node [v30,v31,v0,v1,v2] (.node [v14,v0,v1,v2,v32] (.node [v14,v0,v1,v2,v4] .nil .nil) .nil) (.node [v30,v0,v1,v2,v33] (.node [v30,v0,v1,v2,v5] .nil .nil) .nil)) (.node [v9,v1,v10,v3,v4] (.node [v34,v2,v35,v3,v5] (.node [v36,v2,v37,v3,v4] .nil .nil) .nil) (.node [v9,v1,v2,v11,v38] (.node [v9,v1,v2,v16,v39] .nil .nil) .nil)))) (.node [v0,v1,v13,v40,v5] (.node [v0,v1,v41,v3,v4] (.node [v0,v42,v13,v4,v5] (.node [v0,v43,v1,v2,v3] (.node [v44,v2,v45,v4,v5] .nil .nil) .nil) (.node [v0,v1,v27,v32,v38] (.node [v0,v1,v46,v2,v5] .nil .nil) .nil)) (.node [v0,v1,v47,v3,v5] (.node [v0,v1,v47,v48,v3] (.node [v0,v1,v47,v49,v5] .nil .nil) .nil) (.node [v0,v1,v47,v50,v5] (.node [v0,v1,v47,v3,v51] .nil .nil) .nil))) (.node [v0,v1,v10,v32,v38] (.node [v0,v1,v13,v4,v52] (.node [v0,v1,v13,v4,v5] (.node [v0,v1,v13,v53,v4] .nil .nil) .nil) (.node [v0,v1,v10,v3,v54] (.node [v0,v1,v13,v55,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v56,v39] (.node [v0,v1,v2,v3,v57] (.node [v0,v1,v10,v11,v39] .nil .nil) .nil) (.node [v0,v1,v2,v58,v59] (.node [v0,v1,v2,v4,v60] .nil .nil) .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4ll : everyKey (rowOK 3 tree_3) tree_4ll = true := by decide +kernel
def tree_4lr : BinaryTree (List W) := (.node [v0,v61,v45,v4,v5] (.node [v0,v1,v2,v11,v62] (.node [v0,v1,v2,v63,v38] (.node [v0,v1,v2,v64,v39] (.node [v0,v1,v2,v65,v39] (.node [v0,v1,v2,v16,v39] .nil .nil) .nil) (.node [v0,v1,v2,v32,v38] (.node [v0,v1,v2,v66,v39] .nil .nil) .nil)) (.node [v0,v1,v2,v11,v67] (.node [v0,v1,v2,v68,v38] (.node [v0,v1,v2,v69,v38] .nil .nil) .nil) (.node [v0,v1,v2,v11,v70] (.node [v0,v1,v2,v11,v33] .nil .nil) .nil))) (.node [v0,v1,v2,v71,v38] (.node [v0,v1,v2,v11,v72] (.node [v0,v1,v2,v11,v73] (.node [v0,v1,v2,v11,v74] .nil .nil) .nil) (.node [v0,v1,v2,v75,v39] (.node [v0,v1,v2,v11,v76] .nil .nil) .nil)) (.node [v0,v13,v77,v4,v5] (.node [v0,v1,v78,v3,v4] (.node [v0,v1,v7,v8,v4] .nil .nil) .nil) (.node [v0,v79,v35,v3,v5] (.node [v0,v80,v37,v3,v4] .nil .nil) .nil)))) (.node [v0,v2,v77,v81,v5] (.node [v0,v2,v45,v81,v5] (.node [v0,v2,v45,v82,v4] (.node [v0,v2,v45,v83,v5] (.node [v0,v2,v84,v35,v5] .nil .nil) .nil) (.node [v0,v2,v45,v4,v85] (.node [v0,v2,v45,v4,v5] .nil .nil) .nil)) (.node [v0,v2,v35,v3,v86] (.node [v0,v2,v35,v3,v5] (.node [v0,v2,v35,v87,v3] .nil .nil) .nil) (.node [v0,v2,v37,v3,v4] (.node [v0,v2,v35,v88,v5] .nil .nil) .nil))) (.node [v0,v8,v25,v4,v5] (.node [v0,v45,v89,v4,v5] (.node [v0,v90,v37,v3,v4] (.node [v0,v2,v77,v58,v5] .nil .nil) .nil) (.node [v0,v7,v77,v3,v4] (.node [v0,v35,v91,v3,v5] .nil .nil) .nil)) (.node [v0,v77,v92,v55,v5] (.node [v0,v77,v92,v4,v52] (.node [v0,v77,v93,v4,v5] .nil .nil) .nil) (.node [v0,v89,v94,v4,v85] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lr : everyKey (rowOK 3 tree_3) tree_4lr = true := by decide +kernel
def tree_4l : BinaryTree (List W) := .node [v0,v1,v2,v95,v5] tree_4ll tree_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4l : everyKey (rowOK 3 tree_3) tree_4l = true := by
  change (_ && everyKey _ tree_4ll && everyKey _ tree_4lr) = true
  rw [ok_tree_4ll, ok_tree_4lr]
  decide +kernel
def tree_4rl : BinaryTree (List W) := (.node [v1,v2,v96,v97,v5] (.node [v98,v1,v2,v99,v5] (.node [v100,v2,v37,v3,v4] (.node [v0,v25,v3,v4,v5] (.node [v0,v91,v88,v101,v5] (.node [v0,v91,v3,v101,v86] .nil .nil) .nil) (.node [v0,v102,v3,v4,v5] (.node [v0,v103,v3,v4,v5] .nil .nil) .nil)) (.node [v23,v25,v3,v4,v5] (.node [v23,v8,v24,v4,v5] (.node [v104,v24,v3,v4,v5] .nil .nil) .nil) (.node [v105,v24,v3,v4,v5] (.node [v23,v24,v3,v4,v5] .nil .nil) .nil))) (.node [v1,v13,v106,v4,v5] (.node [v107,v2,v108,v3,v4] (.node [v109,v2,v99,v4,v5] (.node [v110,v1,v2,v99,v4] .nil .nil) .nil) (.node [v111,v2,v97,v3,v5] (.node [v112,v21,v3,v4,v5] .nil .nil) .nil)) (.node [v1,v113,v97,v3,v5] (.node [v1,v114,v108,v3,v4] (.node [v1,v115,v99,v4,v5] .nil .nil) .nil) (.node [v1,v2,v116,v108,v4] (.node [v1,v2,v117,v3,v54] .nil .nil) .nil)))) (.node [v1,v2,v26,v16,v39] (.node [v1,v2,v97,v3,v5] (.node [v1,v2,v99,v118,v5] (.node [v1,v2,v99,v4,v119] (.node [v1,v2,v99,v4,v5] .nil .nil) .nil) (.node [v1,v2,v97,v120,v3] (.node [v1,v2,v121,v108,v3] .nil .nil) .nil)) (.node [v1,v2,v108,v3,v4] (.node [v1,v2,v97,v122,v5] (.node [v1,v2,v97,v3,v123] .nil .nil) .nil) (.node [v1,v2,v108,v124,v4] (.node [v1,v2,v108,v3,v54] .nil .nil) .nil))) (.node [v1,v125,v97,v3,v5] (.node [v1,v126,v99,v4,v5] (.node [v1,v2,v127,v58,v5] (.node [v1,v2,v127,v4,v59] .nil .nil) .nil) (.node [v1,v106,v92,v55,v5] (.node [v1,v106,v92,v4,v52] .nil .nil) .nil)) (.node [v1,v21,v7,v3,v4] (.node [v1,v125,v122,v128,v5] (.node [v1,v125,v3,v128,v123] .nil .nil) .nil) (.node [v1,v21,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rl : everyKey (rowOK 3 tree_3) tree_4rl = true := by decide +kernel
def tree_4rr : BinaryTree (List W) := (.node [v129,v2,v3,v4,v5] (.node [v130,v2,v94,v81,v5] (.node [v19,v7,v20,v3,v4] (.node [v1,v131,v124,v4,v132] (.node [v1,v131,v3,v54,v132] (.node [v1,v131,v108,v3,v4] .nil .nil) .nil) (.node [v19,v21,v3,v4,v5] (.node [v1,v133,v134,v4,v5] .nil .nil) .nil)) (.node [v135,v20,v3,v4,v5] (.node [v136,v2,v99,v4,v5] (.node [v19,v20,v3,v4,v5] .nil .nil) .nil) (.node [v130,v2,v94,v4,v85] (.node [v130,v2,v45,v4,v5] .nil .nil) .nil))) (.node [v137,v2,v97,v3,v5] (.node [v138,v2,v3,v101,v86] (.node [v138,v2,v35,v3,v5] (.node [v139,v24,v3,v4,v5] .nil .nil) .nil) (.node [v140,v24,v3,v4,v5] (.node [v138,v2,v88,v101,v5] .nil .nil) .nil)) (.node [v137,v2,v122,v128,v5] (.node [v137,v2,v3,v128,v123] (.node [v137,v2,v3,v54,v5] .nil .nil) .nil) (.node [v129,v141,v3,v4,v5] (.node [v142,v20,v3,v4,v5] .nil .nil) .nil)))) (.node [v6,v143,v3,v4,v5] (.node [v144,v2,v124,v4,v132] (.node [v145,v2,v3,v4,v5] (.node [v146,v2,v3,v4,v5] (.node [v129,v143,v3,v4,v5] .nil .nil) .nil) (.node [v144,v2,v3,v54,v132] (.node [v144,v2,v108,v3,v4] .nil .nil) .nil)) (.node [v147,v2,v134,v4,v5] (.node [v147,v2,v3,v54,v5] (.node [v148,v20,v3,v4,v5] .nil .nil) .nil) (.node [v6,v149,v3,v4,v5] (.node [v147,v133,v3,v4,v5] .nil .nil) .nil))) (.node [v6,v20,v8,v4,v5] (.node [v6,v150,v3,v4,v5] (.node [v6,v151,v3,v4,v5] (.node [v6,v152,v3,v4,v5] .nil .nil) .nil) (.node [v6,v153,v3,v4,v5] (.node [v6,v7,v24,v3,v4] .nil .nil) .nil)) (.node [v154,v24,v3,v4,v5] (.node [v6,v155,v3,v4,v5] (.node [v6,v156,v3,v4,v5] .nil .nil) .nil) (.node [v20,v157,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rr : everyKey (rowOK 3 tree_3) tree_4rr = true := by decide +kernel
def tree_4r : BinaryTree (List W) := .node [v1,v158,v3,v4,v5] tree_4rl tree_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4r : everyKey (rowOK 3 tree_3) tree_4r = true := by
  change (_ && everyKey _ tree_4rl && everyKey _ tree_4rr) = true
  rw [ok_tree_4rl, ok_tree_4rr]
  decide +kernel
def tree_4 : BinaryTree (List W) := .node [v0,v89,v94,v81,v5] tree_4l tree_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4 : everyKey (rowOK 3 tree_3) tree_4 = true := by
  change (_ && everyKey _ tree_4l && everyKey _ tree_4r) = true
  rw [ok_tree_4l, ok_tree_4r]
  decide +kernel
theorem closed_4 : Closed 4 tree_4 := closed_next 3 (by decide) tree_4 tree_3 closed_3 ok_tree_4
def tree_5lllll : BinaryTree (List W) := (.node [v159,v0,v1,v160,v3,v4] (.node [v161,v0,v2,v37,v3,v4] (.node [v162,v1,v2,v163,v3,v4] (.node [v162,v1,v2,v164,v3,v4] (.node [v162,v165,v1,v2,v3,v4] (.node [v162,v0,v1,v10,v3,v4] .nil .nil) .nil) (.node [v162,v1,v2,v108,v3,v4] .nil .nil)) (.node [v161,v0,v80,v166,v3,v4] (.node [v161,v36,v2,v166,v3,v4] (.node [v167,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v161,v0,v2,v166,v3,v4] .nil .nil))) (.node [v159,v9,v1,v2,v3,v4] (.node [v161,v100,v2,v166,v3,v4] (.node [v161,v0,v90,v166,v3,v4] (.node [v161,v0,v2,v168,v3,v4] .nil .nil) .nil) (.node [v169,v1,v2,v164,v3,v4] .nil .nil)) (.node [v159,v0,v1,v170,v3,v4] (.node [v159,v0,v1,v171,v3,v4] .nil .nil) (.node [v159,v0,v1,v41,v3,v4] .nil .nil)))) (.node [v172,v0,v1,v2,v11,v5] (.node [v173,v0,v1,v2,v3,v4] (.node [v159,v0,v1,v7,v3,v4] (.node [v159,v0,v1,v174,v3,v4] (.node [v159,v0,v1,v2,v3,v54] .nil .nil) .nil) (.node [v159,v0,v1,v131,v3,v4] .nil .nil)) (.node [v18,v0,v1,v2,v3,v4] (.node [v18,v175,v1,v20,v3,v4] .nil .nil) (.node [v176,v0,v1,v171,v3,v4] .nil .nil))) (.node [v177,v0,v1,v2,v118,v5] (.node [v177,v0,v110,v1,v2,v4] (.node [v177,v14,v0,v1,v2,v4] (.node [v177,v178,v0,v1,v2,v4] .nil .nil) .nil) (.node [v177,v0,v1,v2,v4,v179] .nil .nil)) (.node [v180,v0,v1,v2,v3,v4] (.node [v177,v0,v1,v2,v32,v5] .nil .nil) (.node [v181,v182,v0,v1,v2,v3] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllll : everyKey (rowOK 4 tree_4) tree_5lllll = true := by decide +kernel
def tree_5llllr : BinaryTree (List W) := (.node [v175,v1,v20,v3,v4,v5] (.node [v183,v6,v2,v3,v4,v5] (.node [v184,v0,v1,v2,v3,v4] (.node [v181,v0,v1,v2,v16,v5] (.node [v181,v0,v1,v2,v3,v185] (.node [v181,v0,v186,v1,v2,v3] .nil .nil) .nil) (.node [v187,v0,v1,v2,v3,v4] .nil .nil)) (.node [v188,v1,v20,v3,v4,v5] (.node [v189,v6,v2,v3,v4,v5] (.node [v190,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v191,v0,v24,v3,v4,v5] .nil .nil))) (.node [v192,v6,v2,v3,v4,v5] (.node [v193,v6,v2,v3,v4,v5] (.node [v193,v6,v141,v3,v4,v5] (.node [v193,v129,v2,v3,v4,v5] .nil .nil) .nil) (.node [v193,v6,v143,v3,v4,v5] .nil .nil)) (.node [v175,v1,v21,v3,v4,v5] (.node [v175,v112,v20,v3,v4,v5] .nil .nil) (.node [v175,v1,v7,v20,v3,v4] .nil .nil)))) (.node [v194,v0,v24,v3,v4,v5] (.node [v194,v22,v0,v24,v4,v5] (.node [v195,v6,v2,v3,v4,v5] (.node [v195,v1,v20,v3,v4,v5] (.node [v175,v19,v20,v3,v4,v5] .nil .nil) .nil) (.node [v196,v0,v24,v3,v4,v5] .nil .nil)) (.node [v194,v0,v8,v24,v4,v5] (.node [v194,v29,v24,v3,v4,v5] .nil .nil) (.node [v194,v0,v25,v3,v4,v5] .nil .nil))) (.node [v197,v0,v24,v3,v4,v5] (.node [v198,v0,v24,v3,v4,v5] (.node [v199,v0,v24,v3,v4,v5] (.node [v194,v23,v24,v3,v4,v5] .nil .nil) .nil) (.node [v198,v6,v2,v3,v4,v5] .nil .nil)) (.node [v200,v1,v2,v201,v3,v5] (.node [v197,v1,v20,v3,v4,v5] .nil .nil) (.node [v200,v1,v2,v202,v3,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llllr : everyKey (rowOK 4 tree_4) tree_5llllr = true := by decide +kernel
def tree_5llll : BinaryTree (List W) := .node [v181,v15,v0,v1,v2,v3] tree_5lllll tree_5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llll : everyKey (rowOK 4 tree_4) tree_5llll = true := by
  change (_ && everyKey _ tree_5lllll && everyKey _ tree_5llllr) = true
  rw [ok_tree_5lllll, ok_tree_5llllr]
  decide +kernel
def tree_5lllrl : BinaryTree (List W) := (.node [v203,v0,v98,v1,v2,v5] (.node [v204,v0,v1,v205,v3,v51] (.node [v206,v0,v2,v35,v3,v5] (.node [v206,v0,v2,v207,v3,v5] (.node [v200,v137,v2,v3,v4,v5] (.node [v200,v1,v2,v208,v3,v5] .nil .nil) .nil) (.node [v206,v0,v2,v209,v3,v5] .nil .nil)) (.node [v204,v0,v1,v205,v48,v3] (.node [v204,v0,v1,v205,v49,v5] (.node [v206,v138,v2,v3,v4,v5] .nil .nil) .nil) (.node [v204,v0,v1,v205,v3,v5] .nil .nil))) (.node [v210,v0,v1,v2,v4,v5] (.node [v204,v0,v1,v211,v3,v5] (.node [v204,v0,v1,v212,v3,v5] (.node [v204,v0,v1,v205,v50,v5] .nil .nil) .nil) (.node [v204,v0,v1,v47,v3,v5] .nil .nil)) (.node [v203,v213,v0,v1,v2,v5] (.node [v214,v0,v1,v2,v4,v38] .nil .nil) (.node [v203,v30,v0,v1,v2,v5] .nil .nil)))) (.node [v203,v1,v2,v106,v4,v5] (.node [v203,v0,v1,v2,v4,v52] (.node [v203,v0,v1,v10,v4,v5] (.node [v203,v0,v1,v40,v2,v5] (.node [v203,v0,v1,v215,v2,v5] .nil .nil) .nil) (.node [v203,v0,v1,v2,v216,v5] .nil .nil)) (.node [v203,v0,v1,v2,v4,v33] (.node [v203,v0,v1,v2,v4,v119] .nil .nil) (.node [v203,v0,v2,v77,v4,v5] .nil .nil))) (.node [v17,v0,v1,v2,v4,v5] (.node [v217,v0,v1,v2,v4,v5] (.node [v218,v0,v1,v2,v4,v5] (.node [v219,v0,v1,v2,v4,v5] .nil .nil) .nil) (.node [v17,v0,v1,v2,v220,v39] .nil .nil)) (.node [v182,v221,v0,v1,v2,v3] (.node [v182,v15,v0,v1,v2,v3] .nil .nil) (.node [v182,v0,v222,v1,v2,v3] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrl : everyKey (rowOK 4 tree_4) tree_5lllrl = true := by decide +kernel
def tree_5lllrr : BinaryTree (List W) := (.node [v223,v1,v2,v224,v4,v5] (.node [v15,v0,v1,v2,v3,v5] (.node [v225,v0,v1,v2,v3,v5] (.node [v182,v0,v1,v2,v4,v16] (.node [v182,v0,v1,v2,v226,v3] (.node [v182,v0,v1,v10,v3,v4] .nil .nil) .nil) (.node [v227,v0,v1,v2,v3,v5] .nil .nil)) (.node [v15,v0,v1,v2,v3,v220] (.node [v15,v0,v1,v2,v3] .nil .nil) (.node [v15,v0,v1,v2,v3,v4] .nil .nil))) (.node [v223,v1,v115,v228,v4,v5] (.node [v223,v110,v1,v2,v228,v4] (.node [v223,v98,v1,v2,v228,v5] (.node [v15,v0,v1,v2,v3,v39] .nil .nil) .nil) (.node [v223,v109,v2,v228,v4,v5] .nil .nil)) (.node [v223,v1,v2,v228,v4,v119] (.node [v223,v1,v2,v228,v4,v5] .nil .nil) (.node [v223,v1,v2,v228,v118,v5] .nil .nil)))) (.node [v229,v0,v2,v230,v4,v5] (.node [v231,v6,v2,v3,v4,v5] (.node [v223,v1,v126,v228,v4,v5] (.node [v223,v1,v2,v99,v4,v5] (.node [v223,v1,v2,v232,v4,v5] .nil .nil) .nil) (.node [v223,v136,v2,v228,v4,v5] .nil .nil)) (.node [v229,v233,v0,v24,v4,v5] (.node [v234,v1,v20,v3,v4,v5] .nil .nil) (.node [v229,v0,v235,v2,v4,v5] .nil .nil))) (.node [v229,v0,v89,v3,v4,v5] (.node [v229,v0,v2,v8,v4,v5] (.node [v229,v0,v2,v45,v4,v5] (.node [v229,v0,v2,v236,v4,v5] .nil .nil) .nil) (.node [v229,v0,v2,v77,v4,v5] .nil .nil)) (.node [v233,v0,v1,v237,v4,v5] (.node [v238,v0,v2,v230,v4,v5] .nil .nil) (.node [v233,v0,v1,v239,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrr : everyKey (rowOK 4 tree_4) tree_5lllrr = true := by decide +kernel
def tree_5lllr : BinaryTree (List W) := .node [v182,v0,v1,v240,v2,v3] tree_5lllrl tree_5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllr : everyKey (rowOK 4 tree_4) tree_5lllr = true := by
  change (_ && everyKey _ tree_5lllrl && everyKey _ tree_5lllrr) = true
  rw [ok_tree_5lllrl, ok_tree_5lllrr]
  decide +kernel
def tree_5lll : BinaryTree (List W) := .node [v200,v1,v2,v97,v3,v5] tree_5llll tree_5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lll : everyKey (rowOK 4 tree_4) tree_5lll = true := by
  change (_ && everyKey _ tree_5llll && everyKey _ tree_5lllr) = true
  rw [ok_tree_5llll, ok_tree_5lllr]
  decide +kernel
def tree_5llrll : BinaryTree (List W) := (.node [v213,v0,v1,v2,v96,v5] (.node [v241,v0,v1,v2,v3,v4] (.node [v233,v0,v1,v89,v4,v5] (.node [v233,v0,v1,v242,v4,v5] (.node [v233,v0,v1,v2,v81,v5] (.node [v233,v0,v1,v13,v4,v5] .nil .nil) .nil) (.node [v233,v0,v1,v8,v4,v5] .nil .nil)) (.node [v243,v0,v1,v2,v3,v4] (.node [v244,v0,v1,v2,v4,v5] (.node [v233,v0,v77,v3,v4,v5] .nil .nil) .nil) (.node [v245,v0,v1,v237,v4,v5] .nil .nil))) (.node [v213,v30,v0,v1,v2,v5] (.node [v246,v0,v1,v2,v3,v4] (.node [v22,v0,v1,v2,v4,v5] (.node [v247,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v248,v0,v1,v2,v3,v39] .nil .nil)) (.node [v213,v0,v249,v1,v2,v5] (.node [v213,v9,v1,v2,v3,v5] .nil .nil) (.node [v213,v0,v1,v49,v2,v5] .nil .nil)))) (.node [v250,v0,v1,v2,v3,v5] (.node [v213,v0,v1,v125,v3,v5] (.node [v213,v0,v1,v2,v3,v51] (.node [v213,v0,v1,v2,v3,v123] (.node [v213,v0,v1,v2,v251,v5] .nil .nil) .nil) (.node [v213,v0,v1,v2,v3,v33] .nil .nil)) (.node [v252,v0,v1,v2,v3,v5] (.node [v213,v0,v137,v2,v3,v5] .nil .nil) (.node [v253,v0,v1,v2,v3,v5] .nil .nil))) (.node [v178,v9,v1,v2,v3,v4] (.node [v254,v0,v1,v2,v4,v5] (.node [v28,v0,v1,v2,v3,v5] (.node [v28,v0,v1,v2,v255,v38] .nil .nil) .nil) (.node [v178,v14,v0,v1,v2,v4] .nil .nil)) (.node [v178,v0,v1,v256,v2,v4] (.node [v178,v0,v257,v1,v2,v4] .nil .nil) (.node [v178,v0,v1,v2,v116,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrll : everyKey (rowOK 4 tree_4) tree_5llrll = true := by decide +kernel
def tree_5llrlr : BinaryTree (List W) := (.node [v30,v0,v1,v2,v11,v5] (.node [v14,v0,v1,v2,v4] (.node [v258,v0,v1,v2,v4,v5] (.node [v178,v0,v1,v131,v3,v4] (.node [v178,v0,v1,v2,v3,v32] (.node [v178,v0,v1,v2,v3,v54] .nil .nil) .nil) (.node [v178,v0,v144,v2,v3,v4] .nil .nil)) (.node [v14,v0,v1,v2,v255,v4] (.node [v259,v0,v1,v2,v4,v5] .nil .nil) (.node [v14,v0,v1,v2,v3,v4] .nil .nil))) (.node [v260,v0,v1,v2,v3,v4] (.node [v261,v0,v1,v2,v3,v4] (.node [v14,v0,v1,v2,v4,v38] (.node [v14,v0,v1,v2,v4,v5] .nil .nil) .nil) (.node [v262,v0,v1,v2,v3,v4] .nil .nil)) (.node [v30,v0,v1,v2,v3,v5] (.node [v30,v0,v1,v2,v263,v5] .nil .nil) (.node [v30,v0,v1,v2,v4,v5] .nil .nil)))) (.node [v264,v1,v113,v3,v128,v5] (.node [v265,v1,v2,v266,v4,v5] (.node [v31,v0,v1,v2,v3,v4] (.node [v31,v0,v1,v2,v263,v11] (.node [v30,v0,v1,v2,v5] .nil .nil) .nil) (.node [v265,v1,v2,v99,v4,v5] .nil .nil)) (.node [v264,v267,v1,v2,v3,v5] (.node [v268,v0,v1,v2,v4,v5] .nil .nil) (.node [v264,v111,v2,v3,v128,v5] .nil .nil))) (.node [v264,v1,v2,v3,v128,v5] (.node [v264,v1,v2,v120,v3,v128] (.node [v264,v1,v2,v97,v3,v5] (.node [v264,v1,v2,v96,v128,v5] .nil .nil) .nil) (.node [v264,v1,v2,v3,v54,v5] .nil .nil)) (.node [v264,v1,v2,v122,v128,v5] (.node [v264,v1,v2,v3,v128,v123] .nil .nil) (.node [v264,v1,v125,v3,v128,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrlr : everyKey (rowOK 4 tree_4) tree_5llrlr = true := by decide +kernel
def tree_5llrl : BinaryTree (List W) := .node [v178,v0,v1,v2,v269,v4] tree_5llrll tree_5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrl : everyKey (rowOK 4 tree_4) tree_5llrl = true := by
  change (_ && everyKey _ tree_5llrll && everyKey _ tree_5llrlr) = true
  rw [ok_tree_5llrll, ok_tree_5llrlr]
  decide +kernel
def tree_5llrrl : BinaryTree (List W) := (.node [v270,v1,v2,v3,v54,v5] (.node [v271,v19,v2,v3,v4,v5] (.node [v272,v1,v2,v266,v4,v5] (.node [v273,v1,v20,v3,v4,v5] (.node [v274,v6,v2,v3,v4,v5] (.node [v275,v1,v2,v164,v3,v4] .nil .nil) .nil) (.node [v276,v1,v2,v228,v4,v5] .nil .nil)) (.node [v271,v1,v277,v3,v4,v5] (.node [v271,v1,v115,v3,v4,v5] (.node [v271,v1,v278,v3,v4,v5] .nil .nil) .nil) (.node [v271,v1,v21,v3,v4,v5] .nil .nil))) (.node [v270,v279,v2,v3,v4,v5] (.node [v270,v280,v2,v3,v4,v5] (.node [v281,v1,v278,v3,v4,v5] (.node [v271,v136,v2,v3,v4,v5] .nil .nil) .nil) (.node [v270,v109,v2,v3,v4,v5] .nil .nil)) (.node [v270,v282,v2,v3,v4,v5] (.node [v270,v107,v2,v3,v4,v5] .nil .nil) (.node [v270,v1,v2,v7,v3,v4] .nil .nil)))) (.node [v283,v1,v2,v3,v4,v5] (.node [v270,v129,v2,v3,v4,v5] (.node [v270,v1,v126,v3,v4,v5] (.node [v270,v1,v143,v3,v4,v5] (.node [v270,v1,v2,v124,v4,v5] .nil .nil) .nil) (.node [v270,v1,v131,v3,v4,v5] .nil .nil)) (.node [v284,v1,v2,v3,v4,v5] (.node [v285,v280,v2,v3,v4,v5] .nil .nil) (.node [v286,v1,v2,v3,v4,v5] .nil .nil))) (.node [v287,v1,v2,v3,v4,v5] (.node [v288,v1,v2,v3,v4,v5] (.node [v29,v1,v2,v3,v4,v5] (.node [v289,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v290,v1,v2,v3,v4,v5] .nil .nil)) (.node [v291,v280,v2,v3,v4,v5] (.node [v292,v1,v278,v3,v4,v5] .nil .nil) (.node [v293,v0,v1,v10,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrl : everyKey (rowOK 4 tree_4) tree_5llrrl = true := by decide +kernel
def tree_5llrrr : BinaryTree (List W) := (.node [v294,v1,v2,v228,v4,v5] (.node [v293,v1,v2,v3,v4,v132] (.node [v293,v1,v2,v121,v3,v132] (.node [v293,v1,v2,v117,v3,v4] (.node [v293,v1,v114,v3,v4,v132] (.node [v293,v107,v2,v3,v4,v132] .nil .nil) .nil) (.node [v293,v1,v2,v116,v4,v132] .nil .nil)) (.node [v293,v1,v2,v3,v4,v295] (.node [v293,v1,v2,v108,v3,v4] .nil .nil) (.node [v293,v1,v2,v3,v4,v123] .nil .nil))) (.node [v293,v144,v2,v3,v4,v132] (.node [v293,v1,v131,v3,v4,v132] (.node [v293,v1,v2,v124,v4,v132] (.node [v293,v1,v2,v3,v54,v132] .nil .nil) .nil) (.node [v293,v137,v2,v3,v4,v5] .nil .nil)) (.node [v296,v6,v2,v3,v4,v5] (.node [v297,v1,v2,v201,v3,v5] .nil .nil) (.node [v298,v1,v20,v3,v4,v5] .nil .nil)))) (.node [v36,v6,v2,v3,v4,v5] (.node [v36,v107,v2,v3,v4,v5] (.node [v299,v1,v2,v3,v4,v5] (.node [v300,v1,v278,v3,v4,v5] (.node [v301,v1,v2,v266,v4,v5] .nil .nil) .nil) (.node [v36,v280,v2,v3,v4,v5] .nil .nil)) (.node [v36,v1,v2,v3,v4,v5] (.node [v36,v1,v80,v3,v4,v5] .nil .nil) (.node [v36,v1,v90,v3,v4,v5] .nil .nil))) (.node [v34,v1,v2,v84,v4,v5] (.node [v34,v302,v2,v3,v101,v5] (.node [v303,v1,v2,v3,v4,v5] (.node [v304,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v34,v1,v79,v3,v4,v5] .nil .nil)) (.node [v34,v1,v2,v3,v4,v5] (.node [v34,v1,v2,v87,v3,v4] .nil .nil) (.node [v34,v1,v2,v3,v4,v86] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrr : everyKey (rowOK 4 tree_4) tree_5llrrr = true := by decide +kernel
def tree_5llrr : BinaryTree (List W) := .node [v293,v305,v1,v2,v3,v4] tree_5llrrl tree_5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrr : everyKey (rowOK 4 tree_4) tree_5llrr = true := by
  change (_ && everyKey _ tree_5llrrl && everyKey _ tree_5llrrr) = true
  rw [ok_tree_5llrrl, ok_tree_5llrrr]
  decide +kernel
def tree_5llr : BinaryTree (List W) := .node [v264,v137,v2,v3,v128,v5] tree_5llrl tree_5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llr : everyKey (rowOK 4 tree_4) tree_5llr = true := by
  change (_ && everyKey _ tree_5llrl && everyKey _ tree_5llrr) = true
  rw [ok_tree_5llrl, ok_tree_5llrr]
  decide +kernel
def tree_5ll : BinaryTree (List W) := .node [v233,v0,v1,v306,v4,v5] tree_5lll tree_5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5ll : everyKey (rowOK 4 tree_4) tree_5ll = true := by
  change (_ && everyKey _ tree_5lll && everyKey _ tree_5llr) = true
  rw [ok_tree_5lll, ok_tree_5llr]
  decide +kernel
def tree_5lrlll : BinaryTree (List W) := (.node [v9,v1,v2,v3,v11,v5] (.node [v9,v1,v2,v201,v3,v5] (.node [v307,v1,v2,v3,v4,v5] (.node [v308,v1,v2,v3,v4,v5] (.node [v309,v1,v2,v3,v4,v5] (.node [v34,v1,v91,v3,v4,v5] .nil .nil) .nil) (.node [v310,v1,v2,v3,v4,v5] .nil .nil)) (.node [v9,v1,v311,v2,v3,v4] (.node [v9,v1,v312,v3,v4,v5] (.node [v9,v313,v2,v3,v4,v5] .nil .nil) .nil) (.node [v9,v1,v2,v314,v4,v5] .nil .nil))) (.node [v9,v1,v2,v3,v4,v132] (.node [v9,v1,v2,v3,v4,v5] (.node [v9,v1,v2,v3,v220,v39] (.node [v9,v1,v2,v164,v3,v4] .nil .nil) .nil) (.node [v9,v1,v2,v3,v4,v123] .nil .nil)) (.node [v9,v1,v2,v3,v54,v5] (.node [v9,v1,v2,v3,v4,v38] .nil .nil) (.node [v9,v1,v2,v3,v128,v5] .nil .nil)))) (.node [v12,v1,v40,v2,v3,v5] (.node [v315,v1,v2,v8,v4,v5] (.node [v9,v147,v2,v3,v4,v5] (.node [v9,v1,v133,v3,v4,v5] (.node [v9,v1,v2,v134,v4,v5] .nil .nil) .nil) (.node [v316,v1,v2,v3,v4,v5] .nil .nil)) (.node [v317,v1,v2,v3,v4,v5] (.node [v315,v1,v2,v3,v4,v5] .nil .nil) (.node [v12,v42,v2,v3,v4,v5] .nil .nil))) (.node [v12,v1,v2,v3,v4,v5] (.node [v12,v1,v278,v3,v4,v5] (.node [v12,v1,v318,v92,v4,v5] (.node [v12,v1,v53,v2,v3,v4] .nil .nil) .nil) (.node [v12,v1,v115,v3,v4,v5] .nil .nil)) (.node [v12,v1,v2,v3,v55,v5] (.node [v12,v1,v2,v3,v4,v52] .nil .nil) (.node [v12,v1,v20,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlll : everyKey (rowOK 4 tree_4) tree_5lrlll = true := by decide +kernel
def tree_5lrllr : BinaryTree (List W) := (.node [v0,v23,v24,v3,v4,v5] (.node [v44,v1,v2,v3,v81,v5] (.node [v44,v1,v61,v3,v4,v5] (.node [v44,v280,v2,v3,v4,v5] (.node [v44,v319,v2,v94,v4,v5] (.node [v320,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v44,v109,v2,v3,v4,v5] .nil .nil)) (.node [v44,v1,v2,v3,v4,v5] (.node [v44,v1,v2,v82,v3,v4] (.node [v44,v1,v2,v83,v3,v5] .nil .nil) .nil) (.node [v44,v1,v2,v3,v4,v85] .nil .nil))) (.node [v321,v1,v2,v3,v4,v5] (.node [v322,v1,v2,v3,v4,v5] (.node [v44,v6,v2,v3,v4,v5] (.node [v44,v1,v89,v3,v4,v5] .nil .nil) .nil) (.node [v323,v1,v2,v3,v4,v5] .nil .nil)) (.node [v324,v1,v2,v3,v4,v5] (.node [v325,v1,v2,v3,v4,v5] .nil .nil) (.node [v326,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v327,v1,v2,v3,v5] (.node [v0,v98,v1,v2,v3,v119] (.node [v0,v98,v1,v2,v96,v5] (.node [v0,v98,v110,v1,v2,v3] (.node [v0,v328,v1,v2,v3,v4] .nil .nil) .nil) (.node [v0,v98,v1,v2,v3,v5] .nil .nil)) (.node [v0,v329,v1,v2,v8,v5] (.node [v0,v98,v1,v2,v11,v5] .nil .nil) (.node [v0,v329,v1,v2,v3,v5] .nil .nil))) (.node [v0,v330,v1,v2,v8,v4] (.node [v0,v110,v1,v2,v3,v118] (.node [v0,v110,v1,v2,v3,v4] (.node [v0,v110,v1,v2,v116,v4] .nil .nil) .nil) (.node [v0,v110,v1,v2,v4,v38] .nil .nil)) (.node [v0,v331,v1,v2,v3,v4] (.node [v0,v330,v1,v2,v3,v4] .nil .nil) (.node [v0,v319,v61,v94,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrllr : everyKey (rowOK 4 tree_4) tree_5lrllr = true := by decide +kernel
def tree_5lrll : BinaryTree (List W) := .node [v12,v2,v77,v3,v4,v5] tree_5lrlll tree_5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrll : everyKey (rowOK 4 tree_4) tree_5lrll = true := by
  change (_ && everyKey _ tree_5lrlll && everyKey _ tree_5lrllr) = true
  rw [ok_tree_5lrlll, ok_tree_5lrllr]
  decide +kernel
def tree_5lrlrl : BinaryTree (List W) := (.node [v0,v302,v2,v88,v101,v5] (.node [v0,v332,v24,v3,v4,v5] (.node [v0,v319,v2,v94,v4,v5] (.node [v0,v319,v2,v77,v4,v5] (.node [v0,v319,v2,v82,v94,v4] (.node [v0,v319,v2,v83,v94,v5] .nil .nil) .nil) (.node [v0,v319,v2,v333,v4,v5] .nil .nil)) (.node [v0,v319,v89,v94,v4,v5] (.node [v0,v319,v2,v94,v81,v5] (.node [v0,v319,v2,v94,v4,v85] .nil .nil) .nil) (.node [v0,v334,v2,v166,v3,v4] .nil .nil))) (.node [v0,v302,v2,v35,v3,v5] (.node [v0,v302,v79,v3,v101,v5] (.node [v0,v335,v1,v2,v4,v5] (.node [v0,v336,v2,v207,v3,v5] .nil .nil) .nil) (.node [v0,v302,v2,v84,v101,v5] .nil .nil)) (.node [v0,v302,v2,v3,v101,v5] (.node [v0,v302,v2,v87,v3,v101] .nil .nil) (.node [v0,v302,v2,v3,v101,v86] .nil .nil)))) (.node [v0,v337,v338,v3,v4,v5] (.node [v0,v339,v2,v3,v101,v5] (.node [v0,v340,v24,v3,v4,v5] (.node [v0,v341,v2,v166,v3,v4] (.node [v0,v302,v91,v3,v101,v5] .nil .nil) .nil) (.node [v0,v342,v2,v230,v4,v5] .nil .nil)) (.node [v0,v337,v343,v3,v4,v5] (.node [v0,v339,v2,v94,v4,v5] .nil .nil) (.node [v0,v337,v344,v3,v4,v5] .nil .nil))) (.node [v0,v280,v2,v8,v4,v5] (.node [v0,v345,v343,v3,v4,v5] (.node [v0,v346,v343,v3,v4,v5] (.node [v0,v337,v25,v3,v4,v5] .nil .nil) .nil) (.node [v0,v347,v343,v3,v4,v5] .nil .nil)) (.node [v0,v280,v2,v3,v81,v5] (.node [v0,v280,v2,v3,v4,v85] .nil .nil) (.node [v0,v280,v90,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrl : everyKey (rowOK 4 tree_4) tree_5lrlrl = true := by decide +kernel
def tree_5lrlrr : BinaryTree (List W) := (.node [v0,v112,v2,v3,v4,v5] (.node [v0,v107,v114,v3,v4,v5] (.node [v0,v109,v126,v3,v4,v5] (.node [v0,v109,v115,v3,v4,v5] (.node [v0,v348,v2,v3,v4,v5] (.node [v0,v280,v89,v3,v4,v5] .nil .nil) .nil) (.node [v0,v109,v2,v3,v4,v5] .nil .nil)) (.node [v0,v349,v2,v3,v4,v5] (.node [v0,v313,v2,v3,v4,v5] .nil .nil) (.node [v0,v350,v2,v3,v4,v5] .nil .nil))) (.node [v0,v107,v2,v124,v4,v5] (.node [v0,v107,v2,v3,v4,v5] (.node [v0,v107,v2,v121,v3,v5] (.node [v0,v107,v2,v116,v4,v5] .nil .nil) .nil) (.node [v0,v107,v2,v3,v54,v5] .nil .nil)) (.node [v0,v351,v2,v3,v4,v5] (.node [v0,v107,v131,v3,v4,v5] .nil .nil) (.node [v0,v352,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v353,v2,v3,v4,v354] (.node [v0,v355,v2,v3,v4,v5] (.node [v0,v356,v2,v3,v4,v5] (.node [v0,v357,v2,v3,v4,v5] (.node [v0,v358,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v359,v343,v3,v4,v5] .nil .nil)) (.node [v0,v360,v2,v3,v4,v5] (.node [v0,v361,v2,v3,v4,v5] .nil .nil) (.node [v0,v353,v2,v37,v3,v4] .nil .nil))) (.node [v0,v111,v2,v120,v3,v4] (.node [v0,v111,v113,v3,v4,v5] (.node [v0,v362,v2,v3,v4,v5] (.node [v0,v363,v2,v3,v4,v354] .nil .nil) .nil) (.node [v0,v111,v2,v96,v4,v5] .nil .nil)) (.node [v0,v111,v2,v3,v4,v123] (.node [v0,v111,v2,v3,v4,v5] .nil .nil) (.node [v0,v111,v2,v122,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrr : everyKey (rowOK 4 tree_4) tree_5lrlrr = true := by decide +kernel
def tree_5lrlr : BinaryTree (List W) := .node [v0,v280,v143,v3,v4,v5] tree_5lrlrl tree_5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlr : everyKey (rowOK 4 tree_4) tree_5lrlr = true := by
  change (_ && everyKey _ tree_5lrlrl && everyKey _ tree_5lrlrr) = true
  rw [ok_tree_5lrlrl, ok_tree_5lrlrr]
  decide +kernel
def tree_5lrl : BinaryTree (List W) := .node [v0,v319,v2,v45,v4,v5] tree_5lrll tree_5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrl : everyKey (rowOK 4 tree_4) tree_5lrl = true := by
  change (_ && everyKey _ tree_5lrll && everyKey _ tree_5lrlr) = true
  rw [ok_tree_5lrll, ok_tree_5lrlr]
  decide +kernel
def tree_5lrrll : BinaryTree (List W) := (.node [v0,v1,v237,v364,v4,v5] (.node [v0,v42,v2,v3,v4,v52] (.node [v0,v365,v2,v3,v4,v5] (.node [v0,v366,v2,v3,v4,v5] (.node [v0,v367,v2,v3,v4,v5] (.node [v0,v368,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v369,v2,v3,v4,v354] .nil .nil)) (.node [v0,v42,v318,v92,v4,v5] (.node [v0,v42,v53,v2,v3,v4] (.node [v0,v42,v40,v2,v3,v5] .nil .nil) .nil) (.node [v0,v42,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v370,v2,v3,v5] (.node [v0,v371,v2,v3,v4,v5] (.node [v0,v372,v2,v3,v4,v5] (.node [v0,v42,v2,v3,v55,v5] .nil .nil) .nil) (.node [v0,v373,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v237,v13,v4,v5] (.node [v0,v1,v374,v2,v3,v4] .nil .nil) (.node [v0,v1,v237,v7,v3,v4] .nil .nil)))) (.node [v0,v1,v171,v8,v4,v5] (.node [v0,v1,v375,v3,v4,v5] (.node [v0,v1,v205,v47,v3,v5] (.node [v0,v1,v376,v3,v4,v5] (.node [v0,v1,v377,v2,v4,v5] .nil .nil) .nil) (.node [v0,v1,v205,v378,v3,v5] .nil .nil)) (.node [v0,v1,v171,v379,v3,v4] (.node [v0,v1,v171,v41,v3,v4] .nil .nil) (.node [v0,v1,v171,v10,v3,v4] .nil .nil))) (.node [v0,v1,v27,v3,v4,v5] (.node [v0,v1,v380,v3,v4,v5] (.node [v0,v1,v171,v3,v4,v52] (.node [v0,v1,v171,v3,v4,v381] .nil .nil) .nil) (.node [v0,v1,v27,v255,v4,v38] .nil .nil)) (.node [v0,v1,v382,v3,v4,v5] (.node [v0,v1,v383,v3,v4,v5] .nil .nil) (.node [v0,v1,v384,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrll : everyKey (rowOK 4 tree_4) tree_5lrrll = true := by decide +kernel
def tree_5lrrlr : BinaryTree (List W) := (.node [v0,v1,v40,v49,v2,v5] (.node [v0,v1,v47,v3,v5] (.node [v0,v1,v47,v385,v3,v5] (.node [v0,v1,v41,v3,v4,v5] (.node [v0,v1,v41,v3,v4] (.node [v0,v1,v41,v2,v3,v4] .nil .nil) .nil) (.node [v0,v1,v41,v3,v4,v386] .nil .nil)) (.node [v0,v1,v47,v3,v4,v5] (.node [v0,v1,v47,v2,v3,v5] .nil .nil) (.node [v0,v1,v47,v3,v387,v5] .nil .nil))) (.node [v0,v1,v13,v4,v5] (.node [v0,v1,v13,v3,v4,v5] (.node [v0,v1,v13,v2,v4,v5] (.node [v0,v1,v13,v318,v4,v5] .nil .nil) .nil) (.node [v0,v1,v13,v92,v4,v5] .nil .nil)) (.node [v0,v1,v40,v53,v2,v3] (.node [v0,v1,v388,v2,v3,v5] .nil .nil) (.node [v0,v1,v40,v318,v92,v5] .nil .nil)))) (.node [v0,v1,v389,v2,v3,v4] (.node [v0,v1,v390,v2,v3,v4] (.node [v0,v1,v40,v2,v11,v5] (.node [v0,v1,v40,v2,v3,v52] (.node [v0,v1,v40,v2,v3,v5] .nil .nil) .nil) (.node [v0,v1,v391,v2,v3,v5] .nil .nil)) (.node [v0,v1,v53,v2,v3,v4] (.node [v0,v1,v53,v318,v92,v4] .nil .nil) (.node [v0,v1,v53,v2,v3,v55] .nil .nil))) (.node [v0,v1,v318,v392,v4,v5] (.node [v0,v1,v318,v7,v3,v4] (.node [v0,v1,v318,v393,v4,v5] (.node [v0,v1,v318,v2,v81,v5] .nil .nil) .nil) (.node [v0,v1,v318,v89,v4,v5] .nil .nil)) (.node [v0,v1,v318,v92,v4,v5] (.node [v0,v1,v318,v93,v4,v5] .nil .nil) (.node [v0,v1,v318,v92,v4,v52] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrlr : everyKey (rowOK 4 tree_4) tree_5lrrlr = true := by decide +kernel
def tree_5lrrl : BinaryTree (List W) := .node [v0,v1,v41,v311,v3,v4] tree_5lrrll tree_5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrl : everyKey (rowOK 4 tree_4) tree_5lrrl = true := by
  change (_ && everyKey _ tree_5lrrll && everyKey _ tree_5lrrlr) = true
  rw [ok_tree_5lrrll, ok_tree_5lrrlr]
  decide +kernel
def tree_5lrrrl : BinaryTree (List W) := (.node [v0,v1,v394,v3,v4,v5] (.node [v0,v1,v343,v7,v3,v4] (.node [v0,v1,v49,v2,v11,v5] (.node [v0,v1,v49,v2,v4,v5] (.node [v0,v1,v49,v2,v48,v4] (.node [v0,v1,v395,v2,v4,v5] .nil .nil) .nil) (.node [v0,v1,v49,v2,v4,v51] .nil .nil)) (.node [v0,v1,v385,v3,v387,v5] (.node [v0,v1,v396,v2,v4,v5] (.node [v0,v1,v397,v2,v4,v5] .nil .nil) .nil) (.node [v0,v1,v398,v3,v387,v5] .nil .nil))) (.node [v0,v1,v399,v3,v4,v5] (.node [v0,v1,v278,v3,v4,v52] (.node [v0,v1,v278,v8,v4,v5] (.node [v0,v1,v400,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v278,v3,v55,v5] .nil .nil)) (.node [v0,v1,v312,v3,v4,v5] (.node [v0,v1,v115,v3,v4,v5] .nil .nil) (.node [v0,v1,v401,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v402,v3,v4,v5] (.node [v0,v1,v114,v124,v4,v5] (.node [v0,v1,v114,v3,v4,v5] (.node [v0,v1,v114,v121,v3,v5] (.node [v0,v1,v114,v116,v4,v5] .nil .nil) .nil) (.node [v0,v1,v114,v3,v54,v5] .nil .nil)) (.node [v0,v1,v403,v3,v4,v5] (.node [v0,v1,v404,v3,v4,v5] .nil .nil) (.node [v0,v1,v405,v3,v4,v5] .nil .nil))) (.node [v0,v1,v406,v3,v4,v5] (.node [v0,v1,v407,v3,v4,v5] (.node [v0,v1,v408,v3,v4,v5] (.node [v0,v1,v141,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v409,v3,v4,v5] .nil .nil)) (.node [v0,v1,v410,v3,v4,v5] (.node [v0,v1,v411,v3,v4,v5] .nil .nil) (.node [v0,v1,v311,v2,v3,v54] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrl : everyKey (rowOK 4 tree_4) tree_5lrrrl = true := by decide +kernel
def tree_5lrrrr : BinaryTree (List W) := (.node [v0,v1,v79,v84,v4,v5] (.node [v0,v1,v10,v3,v4,v52] (.node [v0,v1,v311,v3,v4,v386] (.node [v0,v1,v311,v3,v4,v52] (.node [v0,v1,v311,v8,v4,v5] (.node [v0,v1,v311,v131,v3,v4] .nil .nil) .nil) (.node [v0,v1,v311,v3,v4,v412] .nil .nil)) (.node [v0,v1,v10,v255,v4,v38] (.node [v0,v1,v413,v3,v4,v5] .nil .nil) (.node [v0,v1,v10,v3,v4,v5] .nil .nil))) (.node [v0,v1,v414,v3,v4,v5] (.node [v0,v1,v10,v4,v11,v5] (.node [v0,v1,v10,v3,v4,v39] (.node [v0,v1,v10,v3,v4,v386] .nil .nil) .nil) (.node [v0,v1,v415,v3,v4,v5] .nil .nil)) (.node [v0,v1,v416,v3,v4,v5] (.node [v0,v1,v80,v3,v4,v5] .nil .nil) (.node [v0,v1,v417,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v113,v3,v4,v123] (.node [v0,v1,v418,v3,v4,v5] (.node [v0,v1,v79,v3,v4,v86] (.node [v0,v1,v79,v3,v4,v5] (.node [v0,v1,v79,v87,v3,v4] .nil .nil) .nil) (.node [v0,v1,v79,v88,v4,v5] .nil .nil)) (.node [v0,v1,v113,v120,v3,v4] (.node [v0,v1,v113,v96,v4,v5] .nil .nil) (.node [v0,v1,v113,v3,v4,v5] .nil .nil))) (.node [v0,v1,v419,v3,v4,v5] (.node [v0,v1,v420,v3,v4,v5] (.node [v0,v1,v421,v3,v4,v5] (.node [v0,v1,v113,v122,v4,v5] .nil .nil) .nil) (.node [v0,v1,v422,v3,v4,v5] .nil .nil)) (.node [v0,v1,v423,v3,v4,v5] (.node [v0,v1,v424,v3,v4,v5] .nil .nil) (.node [v0,v1,v425,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrr : everyKey (rowOK 4 tree_4) tree_5lrrrr = true := by decide +kernel
def tree_5lrrr : BinaryTree (List W) := .node [v0,v1,v311,v426,v3,v4] tree_5lrrrl tree_5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrr : everyKey (rowOK 4 tree_4) tree_5lrrr = true := by
  change (_ && everyKey _ tree_5lrrrl && everyKey _ tree_5lrrrr) = true
  rw [ok_tree_5lrrrl, ok_tree_5lrrrr]
  decide +kernel
def tree_5lrr : BinaryTree (List W) := .node [v0,v1,v318,v92,v55,v5] tree_5lrrl tree_5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrr : everyKey (rowOK 4 tree_4) tree_5lrr = true := by
  change (_ && everyKey _ tree_5lrrl && everyKey _ tree_5lrrr) = true
  rw [ok_tree_5lrrl, ok_tree_5lrrr]
  decide +kernel
def tree_5lr : BinaryTree (List W) := .node [v0,v111,v125,v3,v4,v5] tree_5lrl tree_5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lr : everyKey (rowOK 4 tree_4) tree_5lr = true := by
  change (_ && everyKey _ tree_5lrl && everyKey _ tree_5lrr) = true
  rw [ok_tree_5lrl, ok_tree_5lrr]
  decide +kernel
def tree_5l : BinaryTree (List W) := .node [v34,v1,v2,v88,v4,v5] tree_5ll tree_5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5l : everyKey (rowOK 4 tree_4) tree_5l = true := by
  change (_ && everyKey _ tree_5ll && everyKey _ tree_5lr) = true
  rw [ok_tree_5ll, ok_tree_5lr]
  decide +kernel
def tree_5rllll : BinaryTree (List W) := (.node [v0,v1,v2,v84,v4,v5] (.node [v0,v1,v2,v48,v3,v4] (.node [v0,v1,v61,v3,v81,v5] (.node [v0,v1,v61,v3,v4,v5] (.node [v0,v1,v61,v82,v3,v4] (.node [v0,v1,v61,v83,v3,v5] .nil .nil) .nil) (.node [v0,v1,v61,v3,v4,v85] .nil .nil)) (.node [v0,v1,v427,v3,v4,v5] (.node [v0,v1,v428,v3,v4,v5] (.node [v0,v1,v429,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v430,v3,v4] .nil .nil))) (.node [v0,v1,v2,v431,v11,v5] (.node [v0,v1,v2,v432,v3,v5] (.node [v0,v1,v2,v433,v3,v4] (.node [v0,v1,v2,v48,v50,v4] .nil .nil) .nil) (.node [v0,v1,v2,v434,v3,v4] .nil .nil)) (.node [v0,v1,v2,v435,v4,v5] (.node [v0,v1,v2,v230,v81,v5] .nil .nil) (.node [v0,v1,v2,v84,v87,v4] .nil .nil)))) (.node [v0,v1,v2,v436,v3,v4] (.node [v0,v1,v2,v35,v3,v5] (.node [v0,v1,v2,v45,v4,v5] (.node [v0,v1,v2,v437,v4,v5] (.node [v0,v1,v2,v84,v4,v86] .nil .nil) .nil) (.node [v0,v1,v2,v207,v88,v5] .nil .nil)) (.node [v0,v1,v2,v7,v3,v4] (.node [v0,v1,v2,v37,v3,v4] .nil .nil) (.node [v0,v1,v2,v438,v3,v4] .nil .nil))) (.node [v0,v1,v2,v83,v82,v3] (.node [v0,v1,v2,v87,v88,v4] (.node [v0,v1,v2,v87,v3,v4] (.node [v0,v1,v2,v439,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v440,v3,v5] .nil .nil)) (.node [v0,v1,v2,v83,v3,v85] (.node [v0,v1,v2,v83,v3,v5] .nil .nil) (.node [v0,v1,v2,v441,v3,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllll : everyKey (rowOK 4 tree_4) tree_5rllll = true := by decide +kernel
def tree_5rlllr : BinaryTree (List W) := (.node [v0,v1,v2,v442,v4,v5] (.node [v0,v1,v2,v116,v121,v5] (.node [v0,v1,v2,v8,v4,v59] (.node [v0,v1,v2,v443,v3,v4] (.node [v0,v1,v2,v82,v3,v81] (.node [v0,v1,v2,v82,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v8,v4,v5] .nil .nil)) (.node [v0,v1,v2,v314,v4,v5] (.node [v0,v1,v2,v444,v4,v5] (.node [v0,v1,v2,v8,v58,v5] .nil .nil) .nil) (.node [v0,v1,v2,v445,v4,v5] .nil .nil))) (.node [v0,v1,v2,v96,v120,v4] (.node [v0,v1,v2,v116,v54,v5] (.node [v0,v1,v2,v116,v4,v38] (.node [v0,v1,v2,v116,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v446,v4,v5] .nil .nil)) (.node [v0,v1,v2,v96,v4,v123] (.node [v0,v1,v2,v96,v4,v5] .nil .nil) (.node [v0,v1,v2,v96,v11,v5] .nil .nil)))) (.node [v0,v1,v2,v108,v3,v4] (.node [v0,v1,v2,v121,v3,v5] (.node [v0,v1,v2,v201,v3,v123] (.node [v0,v1,v2,v447,v3,v39] (.node [v0,v1,v2,v99,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v448,v3,v5] .nil .nil)) (.node [v0,v1,v2,v97,v3,v5] (.node [v0,v1,v2,v121,v124,v5] .nil .nil) (.node [v0,v1,v2,v164,v3,v54] .nil .nil))) (.node [v0,v1,v2,v449,v3,v4] (.node [v0,v1,v2,v120,v122,v4] (.node [v0,v1,v2,v120,v3,v4] (.node [v0,v1,v2,v450,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v451,v3,v5] .nil .nil)) (.node [v0,v1,v2,v263,v11,v33] (.node [v0,v1,v2,v263,v11,v5] .nil .nil) (.node [v0,v1,v2,v452,v11,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlllr : everyKey (rowOK 4 tree_4) tree_5rlllr = true := by decide +kernel
def tree_5rlll : BinaryTree (List W) := .node [v0,v1,v2,v453,v3,v4] tree_5rllll tree_5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlll : everyKey (rowOK 4 tree_4) tree_5rlll = true := by
  change (_ && everyKey _ tree_5rllll && everyKey _ tree_5rlllr) = true
  rw [ok_tree_5rllll, ok_tree_5rlllr]
  decide +kernel
def tree_5rllrl : BinaryTree (List W) := (.node [v0,v1,v2,v3,v454,v5] (.node [v0,v1,v2,v455,v4,v38] (.node [v0,v1,v2,v255,v32,v38] (.node [v0,v1,v2,v456,v4,v5] (.node [v0,v1,v2,v457,v4,v5] (.node [v0,v1,v2,v458,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v255,v4,v38] .nil .nil)) (.node [v0,v1,v2,v459,v4,v5] (.node [v0,v1,v2,v460,v4,v38] (.node [v0,v1,v2,v461,v4,v38] .nil .nil) .nil) (.node [v0,v1,v2,v462,v4,v5] .nil .nil))) (.node [v0,v1,v2,v463,v4,v5] (.node [v0,v1,v2,v464,v4,v38] (.node [v0,v1,v2,v465,v4,v5] (.node [v0,v1,v2,v466,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v464,v11,v5] .nil .nil)) (.node [v0,v1,v2,v3,v467,v4] (.node [v0,v1,v2,v3,v468,v4] .nil .nil) (.node [v0,v1,v2,v3,v469,v4] .nil .nil)))) (.node [v0,v1,v2,v3,v470,v5] (.node [v0,v1,v2,v3,v471,v39] (.node [v0,v1,v2,v3,v472,v39] (.node [v0,v1,v2,v3,v220,v39] (.node [v0,v1,v2,v3,v473,v4] .nil .nil) .nil) (.node [v0,v1,v2,v3,v474,v5] .nil .nil)) (.node [v0,v1,v2,v3,v475,v5] (.node [v0,v1,v2,v3,v476,v39] .nil .nil) (.node [v0,v1,v2,v3,v477,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v478] (.node [v0,v1,v2,v3,v4,v479] (.node [v0,v1,v2,v3,v480,v5] (.node [v0,v1,v2,v3,v481,v39] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v482] .nil .nil)) (.node [v0,v1,v2,v3,v4,v483] (.node [v0,v1,v2,v3,v4,v484] .nil .nil) (.node [v0,v1,v2,v3,v4,v485] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrl : everyKey (rowOK 4 tree_4) tree_5rllrl = true := by decide +kernel
def tree_5rllrr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v486] (.node [v0,v1,v2,v3,v4,v487] (.node [v0,v1,v2,v3,v4,v488] (.node [v0,v1,v2,v3,v4,v489] (.node [v0,v1,v2,v3,v4,v490] (.node [v0,v1,v2,v3,v4,v491] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v492] .nil .nil)) (.node [v0,v1,v2,v3,v4,v493] (.node [v0,v1,v2,v3,v4,v494] .nil .nil) (.node [v0,v1,v2,v3,v4,v495] .nil .nil))) (.node [v0,v1,v2,v3,v4,v496] (.node [v0,v1,v2,v3,v4,v497] (.node [v0,v1,v2,v3,v4,v498] (.node [v0,v1,v2,v3,v4,v499] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v500] .nil .nil)) (.node [v0,v1,v2,v3,v4,v501] (.node [v0,v1,v2,v3,v4,v502] .nil .nil) (.node [v0,v1,v2,v3,v4,v123] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v86] (.node [v0,v1,v2,v3,v4,v503] (.node [v0,v1,v2,v3,v4,v504] (.node [v0,v1,v2,v3,v4,v505] (.node [v0,v1,v2,v3,v4,v506] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v85] .nil .nil)) (.node [v0,v1,v2,v3,v4,v507] (.node [v0,v1,v2,v3,v4,v508] .nil .nil) (.node [v0,v1,v2,v3,v4,v509] .nil .nil))) (.node [v0,v1,v2,v3,v4,v510] (.node [v0,v1,v2,v3,v4,v51] (.node [v0,v1,v2,v3,v4,v511] (.node [v0,v1,v2,v3,v4,v512] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v513] .nil .nil)) (.node [v0,v1,v2,v3,v4,v514] (.node [v0,v1,v2,v3,v4,v515] .nil .nil) (.node [v0,v1,v2,v3,v4,v516] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrr : everyKey (rowOK 4 tree_4) tree_5rllrr = true := by decide +kernel
def tree_5rllr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v5] tree_5rllrl tree_5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllr : everyKey (rowOK 4 tree_4) tree_5rllr = true := by
  change (_ && everyKey _ tree_5rllrl && everyKey _ tree_5rllrr) = true
  rw [ok_tree_5rllrl, ok_tree_5rllrr]
  decide +kernel
def tree_5rll : BinaryTree (List W) := .node [v0,v1,v2,v517,v11,v5] tree_5rlll tree_5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rll : everyKey (rowOK 4 tree_4) tree_5rll = true := by
  change (_ && everyKey _ tree_5rlll && everyKey _ tree_5rllr) = true
  rw [ok_tree_5rlll, ok_tree_5rllr]
  decide +kernel
def tree_5rlrll : BinaryTree (List W) := (.node [v0,v1,v2,v3,v518,v5] (.node [v0,v1,v2,v3,v4,v70] (.node [v0,v1,v2,v3,v4,v119] (.node [v0,v1,v2,v3,v4,v67] (.node [v0,v1,v2,v3,v4,v52] (.node [v0,v1,v2,v3,v4,v519] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v520] .nil .nil)) (.node [v0,v1,v2,v3,v4,v59] (.node [v0,v1,v2,v3,v4,v521] (.node [v0,v1,v2,v3,v4,v522] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v33] .nil .nil))) (.node [v0,v1,v2,v3,v4,v76] (.node [v0,v1,v2,v3,v4,v73] (.node [v0,v1,v2,v3,v4,v74] (.node [v0,v1,v2,v3,v4,v62] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v72] .nil .nil)) (.node [v0,v1,v2,v3,v523,v5] (.node [v0,v1,v2,v3,v524,v5] .nil .nil) (.node [v0,v1,v2,v3,v525,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v526,v5] (.node [v0,v1,v2,v3,v527,v5] (.node [v0,v1,v2,v3,v528,v5] (.node [v0,v1,v2,v3,v529,v5] (.node [v0,v1,v2,v3,v530,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v531,v5] .nil .nil)) (.node [v0,v1,v2,v3,v532,v5] (.node [v0,v1,v2,v3,v533,v5] .nil .nil) (.node [v0,v1,v2,v3,v534,v5] .nil .nil))) (.node [v0,v1,v2,v3,v54,v132] (.node [v0,v1,v2,v3,v535,v39] (.node [v0,v1,v2,v3,v536,v39] (.node [v0,v1,v2,v3,v537,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v54,v5] .nil .nil)) (.node [v0,v1,v2,v3,v128,v123] (.node [v0,v1,v2,v3,v54,v38] .nil .nil) (.node [v0,v1,v2,v3,v538,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrll : everyKey (rowOK 4 tree_4) tree_5rlrll = true := by decide +kernel
def tree_5rlrlr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v58,v5] (.node [v0,v1,v2,v3,v539,v5] (.node [v0,v1,v2,v3,v540,v5] (.node [v0,v1,v2,v3,v81,v5] (.node [v0,v1,v2,v3,v541,v5] (.node [v0,v1,v2,v3,v542,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v81,v85] .nil .nil)) (.node [v0,v1,v2,v3,v543,v5] (.node [v0,v1,v2,v3,v544,v5] .nil .nil) (.node [v0,v1,v2,v3,v545,v5] .nil .nil))) (.node [v0,v1,v2,v3,v118,v5] (.node [v0,v1,v2,v3,v546,v5] (.node [v0,v1,v2,v3,v55,v52] (.node [v0,v1,v2,v3,v55,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v547,v5] .nil .nil)) (.node [v0,v1,v2,v3,v548,v5] (.node [v0,v1,v2,v3,v118,v119] .nil .nil) (.node [v0,v1,v2,v3,v549,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v11,v51] (.node [v0,v1,v2,v3,v63,v5] (.node [v0,v1,v2,v3,v32,v5] (.node [v0,v1,v2,v3,v16,v39] (.node [v0,v1,v2,v3,v550,v39] .nil .nil) .nil) (.node [v0,v1,v2,v3,v32,v38] .nil .nil)) (.node [v0,v1,v2,v3,v68,v5] (.node [v0,v1,v2,v3,v69,v5] .nil .nil) (.node [v0,v1,v2,v3,v11,v123] .nil .nil))) (.node [v0,v1,v2,v551,v4,v5] (.node [v0,v1,v2,v552,v4,v5] (.node [v0,v1,v2,v3,v71,v5] (.node [v0,v1,v2,v3,v11,v33] .nil .nil) .nil) (.node [v0,v1,v2,v553,v4,v5] .nil .nil)) (.node [v0,v1,v2,v554,v4,v5] (.node [v0,v1,v2,v555,v4,v5] .nil .nil) (.node [v0,v1,v2,v556,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrlr : everyKey (rowOK 4 tree_4) tree_5rlrlr = true := by decide +kernel
def tree_5rlrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v557,v5] tree_5rlrll tree_5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrl : everyKey (rowOK 4 tree_4) tree_5rlrl = true := by
  change (_ && everyKey _ tree_5rlrll && everyKey _ tree_5rlrlr) = true
  rw [ok_tree_5rlrll, ok_tree_5rlrlr]
  decide +kernel
def tree_5rlrrl : BinaryTree (List W) := (.node [v0,v1,v2,v558,v11,v5] (.node [v0,v1,v2,v122,v4,v123] (.node [v0,v1,v2,v559,v4,v5] (.node [v0,v1,v2,v560,v4,v5] (.node [v0,v1,v2,v561,v4,v5] (.node [v0,v1,v2,v562,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v563,v11,v5] .nil .nil)) (.node [v0,v1,v2,v564,v4,v5] (.node [v0,v1,v2,v565,v4,v5] (.node [v0,v1,v2,v566,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v122,v4,v5] .nil .nil))) (.node [v0,v1,v2,v567,v4,v38] (.node [v0,v1,v2,v568,v4,v5] (.node [v0,v1,v2,v569,v4,v5] (.node [v0,v1,v2,v570,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v571,v4,v5] .nil .nil)) (.node [v0,v1,v2,v124,v54,v5] (.node [v0,v1,v2,v124,v4,v5] .nil .nil) (.node [v0,v1,v2,v134,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v94,v81,v5] (.node [v0,v1,v2,v572,v4,v5] (.node [v0,v1,v2,v573,v4,v5] (.node [v0,v1,v2,v574,v4,v5] (.node [v0,v1,v2,v575,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v576,v4,v5] .nil .nil)) (.node [v0,v1,v2,v88,v4,v86] (.node [v0,v1,v2,v88,v4,v5] .nil .nil) (.node [v0,v1,v2,v88,v101,v5] .nil .nil))) (.node [v0,v1,v2,v577,v4,v5] (.node [v0,v1,v2,v50,v4,v5] (.node [v0,v1,v2,v578,v4,v5] (.node [v0,v1,v2,v579,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v50,v4,v51] .nil .nil)) (.node [v0,v1,v2,v580,v4,v5] (.node [v0,v1,v2,v581,v4,v5] .nil .nil) (.node [v0,v1,v2,v582,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrl : everyKey (rowOK 4 tree_4) tree_5rlrrl = true := by decide +kernel
def tree_5rlrrr : BinaryTree (List W) := (.node [v0,v1,v2,v32,v5,v38] (.node [v0,v1,v2,v4,v66,v5] (.node [v0,v1,v2,v4,v16,v5] (.node [v0,v1,v2,v481,v11,v5] (.node [v0,v1,v2,v220,v16,v39] (.node [v0,v1,v2,v56,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v4,v550,v38] .nil .nil)) (.node [v0,v1,v2,v4,v65,v5] (.node [v0,v1,v2,v4,v16,v39] .nil .nil) (.node [v0,v1,v2,v4,v64,v5] .nil .nil))) (.node [v0,v1,v2,v4,v75,v5] (.node [v0,v1,v2,v4,v11,v119] (.node [v0,v1,v2,v4,v11,v52] (.node [v0,v1,v2,v4,v32,v38] .nil .nil) .nil) (.node [v0,v1,v2,v4,v11,v33] .nil .nil)) (.node [v0,v1,v2,v16,v5,v39] (.node [v0,v1,v2,v118,v5,v38] .nil .nil) (.node [v0,v1,v2,v16,v39] .nil .nil)))) (.node [v0,v1,v583,v3,v4,v5] (.node [v0,v1,v584,v3,v4,v5] (.node [v0,v1,v2,v11,v33] (.node [v0,v1,v2,v11,v5,v33] (.node [v0,v1,v2,v32,v38] .nil .nil) .nil) (.node [v0,v1,v2,v11,v38,v39] .nil .nil)) (.node [v0,v1,v585,v3,v4,v5] (.node [v0,v1,v586,v3,v4,v5] .nil .nil) (.node [v0,v1,v587,v3,v4,v5] .nil .nil))) (.node [v0,v1,v588,v3,v4,v5] (.node [v0,v1,v589,v3,v4,v5] (.node [v0,v1,v590,v3,v4,v5] (.node [v0,v1,v591,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v592,v3,v4,v5] .nil .nil)) (.node [v0,v1,v90,v3,v4,v5] (.node [v0,v1,v593,v3,v4,v5] .nil .nil) (.node [v0,v1,v594,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrr : everyKey (rowOK 4 tree_4) tree_5rlrrr = true := by decide +kernel
def tree_5rlrr : BinaryTree (List W) := .node [v0,v1,v2,v595,v4,v5] tree_5rlrrl tree_5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrr : everyKey (rowOK 4 tree_4) tree_5rlrr = true := by
  change (_ && everyKey _ tree_5rlrrl && everyKey _ tree_5rlrrr) = true
  rw [ok_tree_5rlrrl, ok_tree_5rlrrr]
  decide +kernel
def tree_5rlr : BinaryTree (List W) := .node [v0,v1,v2,v596,v4,v5] tree_5rlrl tree_5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlr : everyKey (rowOK 4 tree_4) tree_5rlr = true := by
  change (_ && everyKey _ tree_5rlrl && everyKey _ tree_5rlrr) = true
  rw [ok_tree_5rlrl, ok_tree_5rlrr]
  decide +kernel
def tree_5rl : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v597] tree_5rll tree_5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rl : everyKey (rowOK 4 tree_4) tree_5rl = true := by
  change (_ && everyKey _ tree_5rll && everyKey _ tree_5rlr) = true
  rw [ok_tree_5rll, ok_tree_5rlr]
  decide +kernel
def tree_5rrlll : BinaryTree (List W) := (.node [v0,v1,v125,v96,v4,v5] (.node [v0,v1,v126,v3,v4,v5] (.node [v0,v1,v598,v3,v4,v5] (.node [v0,v1,v152,v3,v4,v5] (.node [v0,v1,v143,v3,v4,v5] (.node [v0,v1,v599,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v600,v3,v4,v5] .nil .nil)) (.node [v0,v1,v601,v3,v4,v5] (.node [v0,v1,v602,v3,v4,v5] (.node [v0,v1,v603,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v604,v3,v4,v5] .nil .nil))) (.node [v0,v1,v605,v3,v4,v5] (.node [v0,v1,v84,v91,v4,v5] (.node [v0,v1,v606,v3,v4,v5] (.node [v0,v1,v151,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v607,v3,v4,v5] .nil .nil)) (.node [v0,v1,v608,v3,v4,v5] (.node [v0,v1,v609,v3,v387,v5] .nil .nil) (.node [v0,v1,v610,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v611,v3,v4,v5] (.node [v0,v1,v125,v122,v4,v5] (.node [v0,v1,v125,v3,v4,v123] (.node [v0,v1,v125,v3,v4,v5] (.node [v0,v1,v125,v120,v3,v4] .nil .nil) .nil) (.node [v0,v1,v125,v3,v11,v5] .nil .nil)) (.node [v0,v1,v612,v3,v4,v5] (.node [v0,v1,v150,v3,v4,v5] .nil .nil) (.node [v0,v1,v21,v3,v4,v5] .nil .nil))) (.node [v0,v1,v131,v121,v3,v5] (.node [v0,v1,v7,v3,v4,v386] (.node [v0,v1,v7,v24,v3,v4] (.node [v0,v1,v7,v131,v3,v4] .nil .nil) .nil) (.node [v0,v1,v131,v116,v4,v5] .nil .nil)) (.node [v0,v1,v131,v3,v4,v38] (.node [v0,v1,v131,v3,v4,v5] .nil .nil) (.node [v0,v1,v131,v3,v54,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlll : everyKey (rowOK 4 tree_4) tree_5rrlll = true := by decide +kernel
def tree_5rrllr : BinaryTree (List W) := (.node [v0,v1,v613,v3,v4,v5] (.node [v0,v1,v82,v89,v3,v4] (.node [v0,v1,v20,v3,v4,v52] (.node [v0,v1,v133,v3,v4,v5] (.node [v0,v1,v614,v3,v4,v5] (.node [v0,v1,v153,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v20,v8,v4,v5] .nil .nil)) (.node [v0,v1,v87,v91,v3,v4] (.node [v0,v1,v20,v3,v55,v5] .nil .nil) (.node [v0,v1,v83,v89,v3,v5] .nil .nil))) (.node [v0,v1,v615,v3,v4,v5] (.node [v0,v1,v616,v3,v4,v5] (.node [v0,v1,v8,v92,v4,v5] (.node [v0,v1,v8,v89,v4,v5] .nil .nil) .nil) (.node [v0,v1,v617,v3,v4,v5] .nil .nil)) (.node [v0,v1,v89,v3,v4,v85] (.node [v0,v1,v89,v3,v4,v5] .nil .nil) (.node [v0,v1,v89,v3,v81,v5] .nil .nil)))) (.node [v0,v1,v155,v3,v4,v5] (.node [v0,v1,v91,v3,v4,v5] (.node [v0,v1,v618,v3,v4,v5] (.node [v0,v1,v619,v3,v387,v5] (.node [v0,v1,v156,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v620,v3,v4,v5] .nil .nil)) (.node [v0,v1,v91,v88,v4,v5] (.node [v0,v1,v91,v3,v4,v86] .nil .nil) (.node [v0,v1,v621,v3,v4,v5] .nil .nil))) (.node [v0,v622,v2,v3,v4,v5] (.node [v0,v1,v3,v4,v623,v5] (.node [v0,v1,v624,v3,v4,v5] (.node [v0,v1,v25,v3,v4,v5] .nil .nil) .nil) (.node [v0,v625,v2,v3,v4,v5] .nil .nil)) (.node [v0,v626,v2,v3,v4,v5] (.node [v0,v627,v2,v3,v4,v5] .nil .nil) (.node [v0,v628,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrllr : everyKey (rowOK 4 tree_4) tree_5rrllr = true := by decide +kernel
def tree_5rrll : BinaryTree (List W) := .node [v0,v1,v131,v124,v4,v5] tree_5rrlll tree_5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrll : everyKey (rowOK 4 tree_4) tree_5rrll = true := by
  change (_ && everyKey _ tree_5rrlll && everyKey _ tree_5rrllr) = true
  rw [ok_tree_5rrlll, ok_tree_5rrllr]
  decide +kernel
def tree_5rrlrl : BinaryTree (List W) := (.node [v0,v629,v2,v3,v4,v5] (.node [v0,v630,v2,v3,v4,v5] (.node [v0,v19,v278,v3,v4,v5] (.node [v0,v631,v2,v3,v4,v5] (.node [v0,v632,v2,v3,v4,v5] (.node [v0,v633,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v634,v2,v3,v4,v5] .nil .nil)) (.node [v0,v635,v2,v3,v4,v5] (.node [v0,v19,v20,v3,v4,v5] (.node [v0,v19,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v636,v2,v3,v4,v5] .nil .nil))) (.node [v0,v136,v2,v3,v4,v5] (.node [v0,v637,v2,v3,v4,v5] (.node [v0,v638,v2,v3,v4,v5] (.node [v0,v639,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v136,v115,v3,v4,v5] .nil .nil)) (.node [v0,v135,v2,v3,v4,v5] (.node [v0,v136,v126,v3,v4,v5] .nil .nil) (.node [v0,v640,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v137,v2,v3,v11,v5] (.node [v0,v137,v2,v96,v4,v5] (.node [v0,v641,v2,v3,v4,v5] (.node [v0,v642,v2,v3,v4,v5] (.node [v0,v643,v2,v3,v101,v5] .nil .nil) .nil) (.node [v0,v137,v113,v3,v4,v5] .nil .nil)) (.node [v0,v137,v2,v3,v4,v5] (.node [v0,v137,v2,v120,v3,v4] .nil .nil) (.node [v0,v137,v2,v3,v4,v123] .nil .nil))) (.node [v0,v171,v77,v3,v4,v5] (.node [v0,v142,v2,v3,v4,v5] (.node [v0,v137,v125,v3,v4,v5] (.node [v0,v137,v2,v122,v4,v5] .nil .nil) .nil) (.node [v0,v644,v2,v3,v4,v5] .nil .nil)) (.node [v0,v645,v2,v3,v4,v5] (.node [v0,v129,v2,v3,v4,v5] .nil .nil) (.node [v0,v646,v2,v3,v4,v354] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrl : everyKey (rowOK 4 tree_4) tree_5rrlrl = true := by decide +kernel
def tree_5rrlrr : BinaryTree (List W) := (.node [v0,v53,v2,v77,v3,v4] (.node [v0,v647,v2,v3,v4,v5] (.node [v0,v144,v2,v3,v54,v5] (.node [v0,v144,v2,v3,v4,v5] (.node [v0,v144,v2,v121,v3,v5] (.node [v0,v144,v2,v116,v4,v5] .nil .nil) .nil) (.node [v0,v144,v2,v3,v4,v38] .nil .nil)) (.node [v0,v144,v131,v3,v4,v5] (.node [v0,v144,v2,v124,v4,v5] .nil .nil) (.node [v0,v148,v2,v3,v4,v5] .nil .nil))) (.node [v0,v6,v90,v3,v4,v5] (.node [v0,v6,v2,v3,v4,v85] (.node [v0,v6,v2,v8,v4,v5] (.node [v0,v147,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v6,v2,v3,v81,v5] .nil .nil)) (.node [v0,v6,v89,v3,v4,v5] (.node [v0,v6,v143,v3,v4,v5] .nil .nil) (.node [v0,v40,v2,v77,v3,v5] .nil .nil)))) (.node [v0,v2,v45,v4,v5] (.node [v0,v311,v77,v3,v4,v5] (.node [v0,v343,v25,v3,v4,v5] (.node [v0,v648,v24,v3,v4,v5] (.node [v0,v318,v77,v92,v4,v5] .nil .nil) .nil) (.node [v0,v278,v77,v3,v4,v5] .nil .nil)) (.node [v0,v2,v45,v3,v4,v5] (.node [v0,v2,v230,v45,v4,v5] .nil .nil) (.node [v0,v2,v45,v94,v4,v5] .nil .nil))) (.node [v0,v2,v649,v3,v4,v5] (.node [v0,v2,v35,v3,v101,v5] (.node [v0,v2,v35,v3,v4,v5] (.node [v0,v2,v207,v35,v3,v5] .nil .nil) .nil) (.node [v0,v2,v35,v3,v5] .nil .nil)) (.node [v0,v2,v37,v3,v4] (.node [v0,v2,v166,v37,v3,v4] .nil .nil) (.node [v0,v2,v37,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrr : everyKey (rowOK 4 tree_4) tree_5rrlrr = true := by decide +kernel
def tree_5rrlr : BinaryTree (List W) := .node [v0,v144,v114,v3,v4,v5] tree_5rrlrl tree_5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlr : everyKey (rowOK 4 tree_4) tree_5rrlr = true := by
  change (_ && everyKey _ tree_5rrlrl && everyKey _ tree_5rrlrr) = true
  rw [ok_tree_5rrlrl, ok_tree_5rrlrr]
  decide +kernel
def tree_5rrl : BinaryTree (List W) := .node [v0,v650,v2,v3,v4,v5] tree_5rrll tree_5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrl : everyKey (rowOK 4 tree_4) tree_5rrl = true := by
  change (_ && everyKey _ tree_5rrll && everyKey _ tree_5rrlr) = true
  rw [ok_tree_5rrll, ok_tree_5rrlr]
  decide +kernel
def tree_5rrrll : BinaryTree (List W) := (.node [v0,v24,v3,v651,v4,v5] (.node [v0,v2,v77,v4,v11,v5] (.node [v0,v2,v652,v3,v4,v5] (.node [v0,v2,v8,v94,v4,v5] (.node [v0,v2,v8,v77,v4,v5] (.node [v0,v2,v653,v3,v4,v5] .nil .nil) .nil) (.node [v0,v2,v654,v3,v4,v5] .nil .nil)) (.node [v0,v2,v77,v3,v4,v52] (.node [v0,v2,v77,v3,v4,v5] (.node [v0,v2,v655,v3,v4,v5] .nil .nil) .nil) (.node [v0,v2,v77,v3,v55,v5] .nil .nil))) (.node [v0,v77,v3,v92,v4,v5] (.node [v0,v2,v25,v3,v4,v5] (.node [v0,v2,v656,v3,v4,v5] (.node [v0,v2,v157,v3,v4,v5] .nil .nil) .nil) (.node [v0,v20,v77,v3,v4,v5] .nil .nil)) (.node [v0,v25,v24,v3,v4,v5] (.node [v0,v89,v3,v94,v4,v5] .nil .nil) (.node [v0,v25,v3,v4,v5] .nil .nil)))) (.node [v657,v1,v2,v3,v4,v5] (.node [v658,v1,v2,v3,v4,v5] (.node [v659,v1,v2,v3,v4,v5] (.node [v660,v1,v2,v3,v4,v5] (.node [v661,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v662,v1,v2,v3,v4,v5] .nil .nil)) (.node [v663,v1,v2,v3,v4,v5] (.node [v664,v1,v2,v3,v4,v5] .nil .nil) (.node [v665,v1,v2,v3,v4,v5] .nil .nil))) (.node [v666,v1,v2,v3,v4,v5] (.node [v100,v1,v2,v3,v4,v5] (.node [v100,v1,v80,v3,v4,v5] (.node [v667,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v100,v1,v90,v3,v4,v5] .nil .nil)) (.node [v668,v1,v2,v3,v4,v5] (.node [v669,v1,v2,v3,v4,v5] .nil .nil) (.node [v104,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrll : everyKey (rowOK 4 tree_4) tree_5rrrll = true := by decide +kernel
def tree_5rrrlr : BinaryTree (List W) := (.node [v1,v19,v20,v3,v4,v5] (.node [v670,v1,v2,v3,v4,v5] (.node [v23,v24,v3,v4,v5] (.node [v23,v1,v24,v3,v4,v5] (.node [v23,v1,v2,v3,v4,v5] (.node [v23,v1,v343,v3,v4,v5] .nil .nil) .nil) (.node [v23,v2,v24,v3,v4,v5] .nil .nil)) (.node [v671,v1,v2,v3,v4,v5] (.node [v105,v1,v2,v3,v4,v5] .nil .nil) (.node [v672,v1,v2,v3,v4,v5] .nil .nil))) (.node [v280,v129,v2,v3,v4,v5] (.node [v302,v138,v2,v3,v101,v5] (.node [v673,v6,v2,v3,v4,v5] (.node [v319,v130,v2,v94,v4,v5] .nil .nil) .nil) (.node [v674,v6,v2,v3,v4,v5] .nil .nil)) (.node [v107,v6,v2,v3,v4,v5] (.node [v109,v6,v2,v3,v4,v5] .nil .nil) (.node [v42,v2,v106,v3,v4,v5] .nil .nil)))) (.node [v1,v130,v2,v3,v4,v85] (.node [v1,v130,v61,v3,v4,v5] (.node [v1,v675,v2,v3,v4,v5] (.node [v1,v676,v2,v3,v4,v5] (.node [v1,v677,v2,v266,v4,v5] .nil .nil) .nil) (.node [v1,v678,v2,v3,v4,v5] .nil .nil)) (.node [v1,v130,v2,v82,v3,v4] (.node [v1,v130,v2,v83,v3,v5] .nil .nil) (.node [v1,v130,v2,v3,v4,v5] .nil .nil))) (.node [v1,v643,v2,v3,v128,v5] (.node [v1,v679,v2,v3,v4,v5] (.node [v1,v130,v89,v3,v4,v5] (.node [v1,v130,v2,v3,v81,v5] .nil .nil) .nil) (.node [v1,v139,v2,v3,v4,v5] .nil .nil)) (.node [v1,v680,v2,v3,v4,v5] (.node [v1,v681,v2,v3,v4,v5] .nil .nil) (.node [v1,v138,v79,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrlr : everyKey (rowOK 4 tree_4) tree_5rrrlr = true := by decide +kernel
def tree_5rrrl : BinaryTree (List W) := .node [v23,v337,v2,v3,v4,v5] tree_5rrrll tree_5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrl : everyKey (rowOK 4 tree_4) tree_5rrrl = true := by
  change (_ && everyKey _ tree_5rrrll && everyKey _ tree_5rrrlr) = true
  rw [ok_tree_5rrrll, ok_tree_5rrrlr]
  decide +kernel
def tree_5rrrrl : BinaryTree (List W) := (.node [v1,v682,v20,v3,v4,v5] (.node [v1,v6,v2,v7,v3,v4] (.node [v1,v138,v91,v3,v4,v5] (.node [v1,v138,v2,v3,v4,v86] (.node [v1,v138,v2,v3,v4,v5] (.node [v1,v138,v2,v87,v3,v4] .nil .nil) .nil) (.node [v1,v138,v2,v88,v4,v5] .nil .nil)) (.node [v1,v129,v2,v3,v4,v5] (.node [v1,v140,v2,v3,v4,v5] (.node [v1,v683,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1,v684,v2,v3,v4,v5] .nil .nil))) (.node [v1,v6,v131,v3,v4,v5] (.node [v1,v6,v143,v3,v4,v5] (.node [v1,v6,v2,v124,v4,v5] (.node [v1,v6,v2,v3,v54,v5] .nil .nil) .nil) (.node [v1,v6,v126,v3,v4,v5] .nil .nil)) (.node [v1,v53,v2,v106,v3,v4] (.node [v1,v40,v2,v106,v3,v5] .nil .nil) (.node [v1,v318,v106,v92,v4,v5] .nil .nil)))) (.node [v1,v2,v106,v3,v55,v5] (.node [v1,v2,v685,v3,v4,v5] (.node [v1,v2,v686,v266,v4,v5] (.node [v1,v115,v20,v3,v4,v5] (.node [v1,v278,v21,v3,v4,v5] .nil .nil) .nil) (.node [v1,v2,v687,v3,v4,v5] .nil .nil)) (.node [v1,v2,v106,v3,v4,v5] (.node [v1,v2,v688,v3,v4,v5] .nil .nil) (.node [v1,v2,v106,v3,v4,v52] .nil .nil))) (.node [v1,v2,v228,v99,v4,v5] (.node [v1,v2,v689,v3,v4,v5] (.node [v1,v2,v154,v3,v4,v5] (.node [v1,v2,v106,v4,v11,v5] .nil .nil) .nil) (.node [v1,v2,v21,v3,v4,v5] .nil .nil)) (.node [v1,v2,v99,v3,v4,v5] (.node [v1,v2,v8,v127,v4,v5] .nil .nil) (.node [v1,v2,v99,v266,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrl : everyKey (rowOK 4 tree_4) tree_5rrrrl = true := by decide +kernel
def tree_5rrrrr : BinaryTree (List W) := (.node [v1,v2,v690,v3,v4,v5] (.node [v1,v2,v164,v3,v4,v123] (.node [v1,v2,v97,v3,v4,v5] (.node [v1,v2,v201,v3,v54,v5] (.node [v1,v2,v201,v164,v3,v39] (.node [v1,v2,v201,v97,v3,v5] .nil .nil) .nil) (.node [v1,v2,v201,v3,v691,v5] .nil .nil)) (.node [v1,v2,v97,v3,v5] (.node [v1,v2,v97,v3,v128,v5] .nil .nil) (.node [v1,v2,v164,v108,v3,v4] .nil .nil))) (.node [v1,v2,v692,v3,v4,v5] (.node [v1,v2,v108,v3,v4,v5] (.node [v1,v2,v108,v3,v4] (.node [v1,v2,v164,v3,v4,v693] .nil .nil) .nil) (.node [v1,v2,v108,v3,v4,v132] .nil .nil)) (.node [v1,v2,v26,v3,v4,v5] (.node [v1,v2,v26,v3,v220,v39] .nil .nil) (.node [v1,v2,v694,v3,v4,v5] .nil .nil)))) (.node [v137,v2,v164,v3,v4,v5] (.node [v19,v2,v20,v3,v4,v5] (.node [v1,v21,v20,v3,v4,v5] (.node [v1,v2,v3,v127,v4,v5] (.node [v1,v2,v695,v3,v4,v5] .nil .nil) .nil) (.node [v1,v21,v3,v4,v5] .nil .nil)) (.node [v136,v2,v20,v3,v4,v5] (.node [v19,v20,v3,v4,v5] .nil .nil) (.node [v138,v2,v3,v4,v101,v5] .nil .nil))) (.node [v6,v2,v3,v4,v696,v5] (.node [v129,v2,v3,v4,v5] (.node [v129,v6,v2,v3,v4,v5] (.node [v137,v2,v3,v4,v128,v5] .nil .nil) .nil) (.node [v6,v2,v143,v3,v4,v5] .nil .nil)) (.node [v6,v20,v24,v3,v4,v5] (.node [v6,v143,v3,v4,v5] .nil .nil) (.node [v2,v106,v77,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrr : everyKey (rowOK 4 tree_4) tree_5rrrrr = true := by decide +kernel
def tree_5rrrr : BinaryTree (List W) := .node [v1,v2,v99,v4,v5] tree_5rrrrl tree_5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrr : everyKey (rowOK 4 tree_4) tree_5rrrr = true := by
  change (_ && everyKey _ tree_5rrrrl && everyKey _ tree_5rrrrr) = true
  rw [ok_tree_5rrrrl, ok_tree_5rrrrr]
  decide +kernel
def tree_5rrr : BinaryTree (List W) := .node [v1,v138,v2,v84,v4,v5] tree_5rrrl tree_5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrr : everyKey (rowOK 4 tree_4) tree_5rrr = true := by
  change (_ && everyKey _ tree_5rrrl && everyKey _ tree_5rrrr) = true
  rw [ok_tree_5rrrl, ok_tree_5rrrr]
  decide +kernel
def tree_5rr : BinaryTree (List W) := .node [v0,v2,v37,v3,v4,v354] tree_5rrl tree_5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rr : everyKey (rowOK 4 tree_4) tree_5rr = true := by
  change (_ && everyKey _ tree_5rrl && everyKey _ tree_5rrr) = true
  rw [ok_tree_5rrl, ok_tree_5rrr]
  decide +kernel
def tree_5r : BinaryTree (List W) := .node [v0,v1,v149,v3,v4,v5] tree_5rl tree_5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5r : everyKey (rowOK 4 tree_4) tree_5r = true := by
  change (_ && everyKey _ tree_5rl && everyKey _ tree_5rr) = true
  rw [ok_tree_5rl, ok_tree_5rr]
  decide +kernel
def tree_5 : BinaryTree (List W) := .node [v0,v1,v697,v3,v4,v5] tree_5l tree_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5 : everyKey (rowOK 4 tree_4) tree_5 = true := by
  change (_ && everyKey _ tree_5l && everyKey _ tree_5r) = true
  rw [ok_tree_5l, ok_tree_5r]
  decide +kernel
theorem closed_5 : Closed 5 tree_5 := closed_next 4 (by decide) tree_5 tree_4 closed_4 ok_tree_5
def tree_6lllll : BinaryTree (List W) := (.node [v698,v0,v1,v2,v3,v4,v5] (.node [v699,v0,v1,v2,v3,v4,v5] (.node [v700,v0,v1,v2,v3,v4,v5] (.node [v701,v0,v1,v2,v3,v4,v5] (.node [v702,v0,v1,v2,v3,v4,v5] (.node [v703,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v704,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v705,v0,v1,v2,v3,v4,v5] (.node [v706,v0,v1,v2,v3,v4,v5] (.node [v707,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v708,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v709,v0,v1,v2,v3,v4,v5] (.node [v710,v0,v1,v2,v3,v4,v5] (.node [v711,v0,v1,v2,v3,v4,v5] (.node [v712,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v713,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v714,v0,v1,v2,v3,v4,v5] (.node [v715,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v716,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v162,v0,v1,v2,v3,v4,v5] (.node [v162,v178,v0,v1,v2,v3,v4] (.node [v717,v0,v1,v2,v3,v4,v5] (.node [v718,v0,v1,v2,v3,v4,v5] (.node [v719,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v162,v159,v0,v1,v2,v3,v4] .nil .nil)) (.node [v162,v0,v1,v311,v2,v3,v4] (.node [v162,v293,v1,v2,v3,v4,v5] .nil .nil) (.node [v162,v0,v1,v2,v164,v3,v4] .nil .nil))) (.node [v720,v0,v1,v2,v3,v4,v5] (.node [v162,v1,v2,v164,v3,v4] (.node [v162,v0,v1,v2,v3,v4,v38] (.node [v162,v0,v1,v2,v3,v4,v132] .nil .nil) .nil) (.node [v162,v1,v2,v164,v3,v4,v5] .nil .nil)) (.node [v721,v0,v1,v2,v3,v4,v5] (.node [v722,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v723,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllll : everyKey (rowOK 5 tree_5) tree_6lllll = true := by decide +kernel
def tree_6llllr : BinaryTree (List W) := (.node [v724,v0,v1,v2,v3,v4,v5] (.node [v161,v0,v2,v166,v3,v4] (.node [v161,v0,v1,v2,v3,v4,v5] (.node [v161,v0,v1,v80,v3,v4,v5] (.node [v161,v0,v353,v2,v3,v4,v5] (.node [v161,v0,v280,v2,v3,v4,v5] .nil .nil) .nil) (.node [v161,v0,v1,v2,v166,v3,v4] .nil .nil)) (.node [v161,v0,v1,v90,v3,v4,v5] (.node [v161,v0,v1,v2,v3,v4,v354] .nil .nil) (.node [v161,v0,v6,v2,v3,v4,v5] .nil .nil))) (.node [v169,v0,v1,v2,v3,v4,v5] (.node [v725,v0,v1,v2,v3,v4,v5] (.node [v161,v100,v1,v2,v3,v4,v5] (.node [v161,v0,v2,v166,v3,v4,v5] .nil .nil) .nil) (.node [v726,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v727,v0,v1,v2,v3,v4,v5] (.node [v728,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v729,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v159,v0,v1,v2,v3,v4,v386] (.node [v159,v0,v1,v171,v3,v4,v5] (.node [v159,v0,v1,v171,v2,v3,v4] (.node [v159,v293,v0,v1,v2,v3,v4] (.node [v159,v182,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v159,v0,v1,v171,v3,v4] .nil .nil)) (.node [v159,v0,v1,v311,v3,v4,v5] (.node [v159,v0,v1,v278,v3,v4,v5] .nil .nil) (.node [v159,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v18,v0,v1,v2,v20,v3,v4] (.node [v730,v0,v1,v2,v3,v4,v5] (.node [v159,v0,v1,v20,v3,v4,v5] (.node [v159,v0,v1,v2,v3,v4,v39] .nil .nil) .nil) (.node [v731,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v18,v0,v1,v2,v3,v4,v5] (.node [v18,v0,v1,v2,v3,v4] .nil .nil) (.node [v732,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llllr : everyKey (rowOK 5 tree_5) tree_6llllr = true := by decide +kernel
def tree_6llll : BinaryTree (List W) := .node [v161,v36,v1,v2,v3,v4,v5] tree_6lllll tree_6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llll : everyKey (rowOK 5 tree_5) tree_6llll = true := by
  change (_ && everyKey _ tree_6lllll && everyKey _ tree_6llllr) = true
  rw [ok_tree_6lllll, ok_tree_6llllr]
  decide +kernel
def tree_6lllrl : BinaryTree (List W) := (.node [v181,v213,v0,v1,v2,v3,v5] (.node [v177,v0,v1,v2,v3,v4,v38] (.node [v177,v178,v0,v1,v2,v4] (.node [v177,v203,v0,v1,v2,v4,v5] (.node [v172,v0,v1,v2,v3,v4,v5] (.node [v176,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v177,v178,v0,v1,v2,v3,v4] .nil .nil)) (.node [v177,v0,v1,v2,v255,v4,v5] (.node [v177,v0,v1,v2,v228,v4,v5] (.node [v177,v178,v0,v1,v2,v4,v5] .nil .nil) .nil) (.node [v177,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v733,v0,v1,v2,v3,v4,v5] (.node [v734,v0,v1,v2,v3,v4,v5] (.node [v177,v0,v1,v2,v4,v11,v5] (.node [v177,v0,v1,v2,v266,v4,v5] .nil .nil) .nil) (.node [v735,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v181,v182,v0,v1,v2,v3,v4] (.node [v181,v182,v0,v1,v2,v3] .nil .nil) (.node [v181,v182,v0,v1,v2,v3,v5] .nil .nil)))) (.node [v736,v0,v1,v2,v3,v4,v5] (.node [v181,v0,v1,v2,v3,v128,v5] (.node [v181,v0,v1,v2,v3,v4,v5] (.node [v181,v0,v1,v2,v3,v220,v5] (.node [v181,v0,v1,v2,v201,v3,v5] .nil .nil) .nil) (.node [v181,v0,v1,v2,v3,v4,v39] .nil .nil)) (.node [v737,v0,v1,v2,v3,v4,v5] (.node [v181,v0,v1,v2,v3,v11,v5] .nil .nil) (.node [v738,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v739,v0,v1,v2,v3,v4,v5] (.node [v188,v0,v1,v2,v3,v4,v5] (.node [v189,v0,v1,v2,v3,v4,v5] (.node [v740,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v191,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v183,v0,v1,v2,v3,v4,v5] (.node [v741,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v742,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllrl : everyKey (rowOK 5 tree_5) tree_6lllrl = true := by decide +kernel
def tree_6lllrr : BinaryTree (List W) := (.node [v175,v0,v19,v2,v3,v4,v5] (.node [v192,v0,v1,v2,v3,v4,v5] (.node [v193,v0,v6,v2,v3,v4,v5] (.node [v193,v0,v1,v2,v3,v4,v5] (.node [v193,v0,v1,v141,v3,v4,v5] (.node [v193,v0,v280,v2,v3,v4,v5] .nil .nil) .nil) (.node [v193,v0,v1,v143,v3,v4,v5] .nil .nil)) (.node [v193,v6,v2,v3,v4,v5] (.node [v193,v1,v6,v2,v3,v4,v5] .nil .nil) (.node [v743,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v175,v0,v112,v2,v3,v4,v5] (.node [v744,v0,v1,v2,v3,v4,v5] (.node [v745,v0,v1,v2,v3,v4,v5] (.node [v746,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v175,v271,v1,v2,v3,v4,v5] .nil .nil)) (.node [v175,v0,v1,v2,v3,v4,v5] (.node [v175,v0,v1,v278,v3,v4,v5] .nil .nil) (.node [v175,v0,v1,v20,v3,v4,v5] .nil .nil)))) (.node [v196,v0,v1,v2,v3,v4,v5] (.node [v195,v0,v1,v2,v3,v4,v5] (.node [v747,v0,v1,v2,v3,v4,v5] (.node [v175,v1,v20,v3,v4,v5] (.node [v175,v1,v2,v20,v3,v4,v5] .nil .nil) .nil) (.node [v748,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v749,v0,v1,v2,v3,v4,v5] (.node [v750,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v751,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v194,v0,v1,v24,v3,v4,v5] (.node [v194,v0,v1,v343,v3,v4,v5] (.node [v194,v0,v337,v2,v3,v4,v5] (.node [v194,v29,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v194,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v194,v0,v24,v3,v4,v5] (.node [v194,v0,v2,v24,v3,v4,v5] .nil .nil) (.node [v194,v23,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllrr : everyKey (rowOK 5 tree_5) tree_6lllrr = true := by decide +kernel
def tree_6lllr : BinaryTree (List W) := .node [v193,v270,v1,v2,v3,v4,v5] tree_6lllrl tree_6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllr : everyKey (rowOK 5 tree_5) tree_6lllr = true := by
  change (_ && everyKey _ tree_6lllrl && everyKey _ tree_6lllrr) = true
  rw [ok_tree_6lllrl, ok_tree_6lllrr]
  decide +kernel
def tree_6lll : BinaryTree (List W) := .node [v752,v0,v1,v2,v3,v4,v5] tree_6llll tree_6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lll : everyKey (rowOK 5 tree_5) tree_6lll = true := by
  change (_ && everyKey _ tree_6llll && everyKey _ tree_6lllr) = true
  rw [ok_tree_6llll, ok_tree_6lllr]
  decide +kernel
def tree_6llrll : BinaryTree (List W) := (.node [v200,v1,v2,v201,v3,v4,v5] (.node [v753,v0,v1,v2,v3,v4,v5] (.node [v197,v0,v1,v2,v3,v4,v5] (.node [v198,v0,v1,v2,v3,v4,v5] (.node [v754,v0,v1,v2,v3,v4,v5] (.node [v755,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v756,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v757,v0,v1,v2,v3,v4,v5] (.node [v758,v0,v1,v2,v3,v4,v5] (.node [v759,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v760,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v200,v0,v1,v2,v3,v4,v5] (.node [v200,v270,v1,v2,v3,v4,v5] (.node [v200,v264,v1,v2,v3,v4,v5] (.node [v200,v213,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v200,v0,v1,v2,v201,v3,v5] .nil .nil)) (.node [v200,v0,v1,v2,v3,v11,v5] (.node [v200,v0,v1,v2,v3,v128,v5] .nil .nil) (.node [v200,v1,v6,v2,v3,v4,v5] .nil .nil)))) (.node [v206,v0,v302,v2,v3,v4,v5] (.node [v761,v0,v1,v2,v3,v4,v5] (.node [v762,v0,v1,v2,v3,v4,v5] (.node [v763,v0,v1,v2,v3,v4,v5] (.node [v200,v1,v2,v201,v3,v5] .nil .nil) .nil) (.node [v764,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v765,v0,v1,v2,v3,v4,v5] (.node [v766,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v767,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v206,v0,v6,v2,v3,v4,v5] (.node [v206,v0,v1,v2,v3,v4,v5] (.node [v206,v0,v1,v2,v207,v3,v5] (.node [v206,v0,v280,v2,v3,v4,v5] .nil .nil) .nil) (.node [v206,v0,v1,v2,v3,v101,v5] .nil .nil)) (.node [v206,v0,v2,v207,v3,v5] (.node [v206,v0,v2,v207,v3,v4,v5] .nil .nil) (.node [v768,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrll : everyKey (rowOK 5 tree_5) tree_6llrll = true := by decide +kernel
def tree_6llrlr : BinaryTree (List W) := (.node [v204,v0,v1,v24,v3,v4,v5] (.node [v204,v0,v1,v205,v2,v3,v5] (.node [v769,v0,v1,v2,v3,v4,v5] (.node [v770,v0,v1,v2,v3,v4,v5] (.node [v771,v0,v1,v2,v3,v4,v5] (.node [v772,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v773,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v774,v0,v1,v2,v3,v4,v5] (.node [v775,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v776,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v204,v0,v1,v278,v3,v4,v5] (.node [v204,v0,v1,v385,v3,v4,v5] (.node [v204,v0,v1,v205,v3,v5] (.node [v204,v0,v1,v205,v3,v4,v5] .nil .nil) .nil) (.node [v204,v0,v1,v343,v3,v4,v5] .nil .nil)) (.node [v204,v0,v1,v2,v3,v387,v5] (.node [v204,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v204,v0,v1,v20,v3,v4,v5] .nil .nil)))) (.node [v777,v0,v1,v2,v3,v4,v5] (.node [v778,v0,v1,v2,v3,v4,v5] (.node [v779,v0,v1,v2,v3,v4,v5] (.node [v780,v0,v1,v2,v3,v4,v5] (.node [v781,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v782,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v783,v0,v1,v2,v3,v4,v5] (.node [v784,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v785,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v203,v213,v0,v1,v2,v5] (.node [v203,v213,v0,v1,v2,v3,v5] (.node [v203,v233,v0,v1,v2,v4,v5] (.node [v214,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v203,v213,v0,v1,v2,v4,v5] .nil .nil)) (.node [v203,v0,v1,v2,v230,v4,v5] (.node [v203,v0,v1,v318,v2,v4,v5] .nil .nil) (.node [v203,v0,v1,v2,v228,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrlr : everyKey (rowOK 5 tree_5) tree_6llrlr = true := by decide +kernel
def tree_6llrl : BinaryTree (List W) := .node [v786,v0,v1,v2,v3,v4,v5] tree_6llrll tree_6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrl : everyKey (rowOK 5 tree_5) tree_6llrl = true := by
  change (_ && everyKey _ tree_6llrll && everyKey _ tree_6llrlr) = true
  rw [ok_tree_6llrll, ok_tree_6llrlr]
  decide +kernel
def tree_6llrrl : BinaryTree (List W) := (.node [v182,v0,v1,v2,v3,v4,v132] (.node [v787,v0,v1,v2,v3,v4,v5] (.node [v203,v0,v1,v2,v4,v5,v38] (.node [v203,v0,v1,v2,v266,v4,v5] (.node [v203,v0,v1,v2,v3,v11,v5] (.node [v203,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v203,v0,v1,v2,v94,v4,v5] .nil .nil)) (.node [v17,v0,v1,v2,v220,v4,v5] (.node [v17,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v17,v0,v1,v2,v4,v5] .nil .nil))) (.node [v182,v0,v1,v2,v166,v3,v4] (.node [v182,v178,v0,v1,v2,v3,v4] (.node [v788,v0,v1,v2,v3,v4,v5] (.node [v789,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v182,v0,v1,v311,v2,v3,v4] .nil .nil)) (.node [v182,v0,v1,v2,v3,v220,v4] (.node [v182,v0,v1,v2,v164,v3,v4] .nil .nil) (.node [v182,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v790,v0,v1,v2,v3,v4,v5] (.node [v791,v0,v1,v2,v3,v4,v5] (.node [v182,v0,v1,v2,v3,v5,v39] (.node [v182,v0,v1,v2,v3,v4,v38] (.node [v182,v0,v1,v2,v3,v4,v354] .nil .nil) .nil) (.node [v792,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v793,v0,v1,v2,v3,v4,v5] (.node [v794,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v795,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v223,v270,v1,v2,v3,v4,v5] (.node [v223,v265,v1,v2,v3,v4,v5] (.node [v796,v0,v1,v2,v3,v4,v5] (.node [v797,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v223,v271,v1,v2,v3,v4,v5] .nil .nil)) (.node [v223,v0,v1,v115,v3,v4,v5] (.node [v223,v0,v109,v2,v3,v4,v5] .nil .nil) (.node [v223,v0,v1,v2,v228,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrrl : everyKey (rowOK 5 tree_5) tree_6llrrl = true := by decide +kernel
def tree_6llrrr : BinaryTree (List W) := (.node [v229,v0,v337,v2,v3,v4,v5] (.node [v234,v0,v1,v2,v3,v4,v5] (.node [v223,v1,v2,v20,v3,v4,v5] (.node [v223,v0,v136,v2,v3,v4,v5] (.node [v223,v0,v1,v126,v3,v4,v5] (.node [v223,v0,v1,v2,v266,v4,v5] .nil .nil) .nil) (.node [v223,v1,v6,v2,v3,v4,v5] .nil .nil)) (.node [v223,v1,v2,v228,v4,v5] (.node [v223,v1,v2,v228,v3,v4,v5] .nil .nil) (.node [v231,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v798,v0,v1,v2,v3,v4,v5] (.node [v799,v0,v1,v2,v3,v4,v5] (.node [v800,v0,v1,v2,v3,v4,v5] (.node [v801,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v802,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v229,v233,v0,v1,v2,v4,v5] (.node [v803,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v229,v0,v319,v2,v3,v4,v5] .nil .nil)))) (.node [v804,v0,v1,v2,v3,v4,v5] (.node [v229,v0,v2,v230,v3,v4,v5] (.node [v229,v0,v1,v2,v3,v4,v5] (.node [v229,v0,v1,v2,v230,v4,v5] (.node [v229,v0,v1,v318,v2,v4,v5] .nil .nil) .nil) (.node [v229,v0,v1,v2,v94,v4,v5] .nil .nil)) (.node [v229,v0,v2,v24,v3,v4,v5] (.node [v229,v0,v2,v230,v4,v5] .nil .nil) (.node [v805,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v238,v0,v1,v2,v3,v4,v5] (.node [v806,v0,v1,v2,v3,v4,v5] (.node [v807,v0,v1,v2,v3,v4,v5] (.node [v808,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v809,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v810,v0,v1,v2,v3,v4,v5] (.node [v811,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v812,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrrr : everyKey (rowOK 5 tree_5) tree_6llrrr = true := by decide +kernel
def tree_6llrr : BinaryTree (List W) := .node [v223,v0,v1,v2,v3,v4,v5] tree_6llrrl tree_6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrr : everyKey (rowOK 5 tree_5) tree_6llrr = true := by
  change (_ && everyKey _ tree_6llrrl && everyKey _ tree_6llrrr) = true
  rw [ok_tree_6llrrl, ok_tree_6llrrr]
  decide +kernel
def tree_6llr : BinaryTree (List W) := .node [v203,v0,v1,v2,v263,v4,v5] tree_6llrl tree_6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llr : everyKey (rowOK 5 tree_5) tree_6llr = true := by
  change (_ && everyKey _ tree_6llrl && everyKey _ tree_6llrr) = true
  rw [ok_tree_6llrl, ok_tree_6llrr]
  decide +kernel
def tree_6ll : BinaryTree (List W) := .node [v199,v0,v1,v2,v3,v4,v5] tree_6lll tree_6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6ll : everyKey (rowOK 5 tree_5) tree_6ll = true := by
  change (_ && everyKey _ tree_6lll && everyKey _ tree_6llr) = true
  rw [ok_tree_6lll, ok_tree_6llr]
  decide +kernel
def tree_6lrlll : BinaryTree (List W) := (.node [v813,v0,v1,v2,v3,v4,v5] (.node [v233,v0,v1,v24,v3,v4,v5] (.node [v233,v0,v1,v318,v3,v4,v5] (.node [v233,v0,v1,v237,v3,v4,v5] (.node [v233,v0,v1,v237,v2,v4,v5] (.node [v233,v0,v319,v1,v2,v4,v5] .nil .nil) .nil) (.node [v233,v0,v1,v237,v4,v5] .nil .nil)) (.node [v233,v0,v1,v2,v92,v4,v5] (.node [v233,v0,v1,v2,v3,v4,v5] (.node [v233,v0,v1,v343,v3,v4,v5] .nil .nil) .nil) (.node [v233,v0,v1,v2,v4,v11,v5] .nil .nil))) (.node [v814,v0,v1,v2,v3,v4,v5] (.node [v815,v0,v1,v2,v3,v4,v5] (.node [v816,v0,v1,v2,v3,v4,v5] (.node [v817,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v818,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v245,v0,v1,v2,v3,v4,v5] (.node [v819,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v820,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v213,v0,v1,v2,v3,v4,v5] (.node [v213,v264,v0,v1,v2,v3,v5] (.node [v22,v0,v1,v2,v4,v5] (.node [v22,v0,v1,v2,v3,v4,v5] (.node [v22,v0,v1,v2,v24,v4,v5] .nil .nil) .nil) (.node [v248,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v213,v0,v1,v2,v207,v3,v5] (.node [v213,v0,v1,v205,v2,v3,v5] .nil .nil) (.node [v213,v0,v1,v2,v263,v3,v5] .nil .nil))) (.node [v28,v0,v1,v2,v255,v3,v5] (.node [v213,v0,v1,v2,v3,v5,v39] (.node [v213,v0,v1,v2,v3,v387,v5] (.node [v213,v0,v1,v2,v3,v101,v5] .nil .nil) .nil) (.node [v213,v0,v1,v2,v4,v11,v5] .nil .nil)) (.node [v28,v0,v1,v2,v3,v5] (.node [v28,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v821,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlll : everyKey (rowOK 5 tree_5) tree_6lrlll = true := by decide +kernel
def tree_6lrllr : BinaryTree (List W) := (.node [v822,v0,v1,v2,v3,v4,v5] (.node [v178,v0,v1,v2,v3,v4,v39] (.node [v178,v0,v1,v2,v255,v3,v4] (.node [v178,v0,v1,v171,v2,v3,v4] (.node [v178,v293,v0,v1,v2,v3,v4] (.node [v823,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v178,v0,v1,v2,v166,v3,v4] .nil .nil)) (.node [v178,v0,v1,v2,v3,v4,v354] (.node [v178,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v178,v0,v1,v2,v3,v4,v386] .nil .nil))) (.node [v824,v0,v1,v2,v3,v4,v5] (.node [v825,v0,v1,v2,v3,v4,v5] (.node [v826,v0,v1,v2,v3,v4,v5] (.node [v178,v0,v1,v2,v4,v5,v38] .nil .nil) .nil) (.node [v827,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v31,v0,v1,v2,v3,v4] (.node [v31,v0,v1,v2,v263,v3,v4] .nil .nil) (.node [v31,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v265,v1,v2,v266,v4,v5] (.node [v265,v0,v1,v2,v228,v4,v5] (.node [v828,v0,v1,v2,v3,v4,v5] (.node [v829,v0,v1,v2,v3,v4,v5] (.node [v830,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v831,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v265,v0,v1,v2,v266,v4,v5] (.node [v265,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v265,v1,v2,v3,v266,v4,v5] .nil .nil))) (.node [v832,v0,v1,v2,v3,v4,v5] (.node [v833,v0,v1,v2,v3,v4,v5] (.node [v834,v0,v1,v2,v3,v4,v5] (.node [v835,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v836,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v837,v0,v1,v2,v3,v4,v5] (.node [v838,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v839,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrllr : everyKey (rowOK 5 tree_5) tree_6lrllr = true := by decide +kernel
def tree_6lrll : BinaryTree (List W) := .node [v840,v0,v1,v2,v3,v4,v5] tree_6lrlll tree_6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrll : everyKey (rowOK 5 tree_5) tree_6lrll = true := by
  change (_ && everyKey _ tree_6lrlll && everyKey _ tree_6lrllr) = true
  rw [ok_tree_6lrlll, ok_tree_6lrllr]
  decide +kernel
def tree_6lrlrl : BinaryTree (List W) := (.node [v221,v0,v1,v2,v3,v4,v5] (.node [v264,v0,v1,v2,v3,v128,v5] (.node [v264,v0,v1,v2,v96,v4,v5] (.node [v264,v0,v111,v2,v3,v4,v5] (.node [v264,v293,v1,v2,v3,v4,v5] (.node [v841,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v264,v0,v1,v113,v3,v4,v5] .nil .nil)) (.node [v264,v0,v1,v2,v3,v4,v5] (.node [v264,v0,v1,v2,v120,v3,v4] (.node [v264,v0,v1,v2,v201,v3,v5] .nil .nil) .nil) (.node [v264,v0,v1,v2,v3,v4,v123] .nil .nil))) (.node [v264,v1,v2,v164,v3,v4,v5] (.node [v264,v0,v1,v125,v3,v4,v5] (.node [v264,v0,v1,v2,v122,v4,v5] (.node [v264,v0,v1,v2,v3,v11,v5] .nil .nil) .nil) (.node [v264,v0,v137,v2,v3,v4,v5] .nil .nil)) (.node [v264,v1,v2,v3,v128,v5] (.node [v264,v1,v2,v3,v4,v128,v5] .nil .nil) (.node [v275,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v271,v0,v1,v278,v3,v4,v5] (.node [v842,v0,v1,v2,v3,v4,v5] (.node [v276,v0,v1,v2,v3,v4,v5] (.node [v273,v0,v1,v2,v3,v4,v5] (.node [v274,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v272,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v843,v0,v1,v2,v3,v4,v5] (.node [v844,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v271,v270,v1,v2,v3,v4,v5] .nil .nil))) (.node [v271,v1,v278,v3,v4,v5] (.node [v271,v1,v6,v2,v3,v4,v5] (.node [v271,v0,v1,v20,v3,v4,v5] (.node [v271,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v271,v1,v278,v2,v3,v4,v5] .nil .nil)) (.node [v845,v0,v1,v2,v3,v4,v5] (.node [v271,v1,v2,v3,v266,v4,v5] .nil .nil) (.node [v281,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlrl : everyKey (rowOK 5 tree_5) tree_6lrlrl = true := by decide +kernel
def tree_6lrlrr : BinaryTree (List W) := (.node [v291,v0,v1,v2,v3,v4,v5] (.node [v270,v1,v2,v164,v3,v4,v5] (.node [v270,v0,v6,v2,v3,v4,v5] (.node [v270,v0,v280,v2,v3,v4,v5] (.node [v270,v293,v1,v2,v3,v4,v5] (.node [v846,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v270,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v270,v280,v2,v3,v4,v5] (.node [v270,v280,v1,v2,v3,v4,v5] .nil .nil) (.node [v270,v1,v2,v20,v3,v4,v5] .nil .nil))) (.node [v847,v0,v1,v2,v3,v4,v5] (.node [v848,v0,v1,v2,v3,v4,v5] (.node [v270,v1,v2,v3,v4,v128,v5] (.node [v270,v1,v2,v3,v266,v4,v5] .nil .nil) .nil) (.node [v285,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v29,v1,v2,v3,v4,v5] (.node [v29,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v292,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v293,v0,v1,v2,v3,v4,v38] (.node [v293,v0,v1,v2,v121,v3,v5] (.node [v293,v0,v1,v311,v2,v3,v4] (.node [v293,v0,v1,v114,v3,v4,v5] (.node [v293,v0,v107,v2,v3,v4,v5] .nil .nil) .nil) (.node [v293,v0,v1,v2,v116,v4,v5] .nil .nil)) (.node [v293,v0,v1,v2,v3,v4,v5] (.node [v293,v0,v1,v2,v164,v3,v4] .nil .nil) (.node [v293,v0,v1,v2,v3,v4,v132] .nil .nil))) (.node [v293,v1,v6,v2,v3,v4,v5] (.node [v293,v0,v1,v131,v3,v4,v5] (.node [v293,v0,v1,v2,v124,v4,v5] (.node [v293,v0,v1,v2,v3,v54,v5] .nil .nil) .nil) (.node [v293,v0,v144,v2,v3,v4,v5] .nil .nil)) (.node [v293,v1,v2,v3,v4,v5,v132] (.node [v293,v1,v2,v201,v3,v4,v5] .nil .nil) (.node [v293,v1,v2,v3,v4,v132] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlrr : everyKey (rowOK 5 tree_5) tree_6lrlrr = true := by decide +kernel
def tree_6lrlr : BinaryTree (List W) := .node [v849,v0,v1,v2,v3,v4,v5] tree_6lrlrl tree_6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlr : everyKey (rowOK 5 tree_5) tree_6lrlr = true := by
  change (_ && everyKey _ tree_6lrlrl && everyKey _ tree_6lrlrr) = true
  rw [ok_tree_6lrlrl, ok_tree_6lrlrr]
  decide +kernel
def tree_6lrl : BinaryTree (List W) := .node [v850,v0,v1,v2,v3,v4,v5] tree_6lrll tree_6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrl : everyKey (rowOK 5 tree_5) tree_6lrl = true := by
  change (_ && everyKey _ tree_6lrll && everyKey _ tree_6lrlr) = true
  rw [ok_tree_6lrll, ok_tree_6lrlr]
  decide +kernel
def tree_6lrrll : BinaryTree (List W) := (.node [v44,v319,v1,v2,v3,v4,v5] (.node [v34,v302,v1,v2,v3,v4,v5] (.node [v300,v0,v1,v2,v3,v4,v5] (.node [v294,v0,v1,v2,v3,v4,v5] (.node [v298,v0,v1,v2,v3,v4,v5] (.node [v296,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v301,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v36,v1,v2,v3,v4,v5] (.node [v36,v0,v1,v2,v3,v4,v5] (.node [v851,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v34,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v12,v0,v1,v2,v3,v4,v5] (.node [v9,v1,v2,v3,v4,v5] (.node [v9,v0,v1,v2,v3,v4,v5] (.node [v34,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v9,v1,v2,v3,v4,v5,v39] .nil .nil)) (.node [v12,v1,v2,v3,v4,v5] (.node [v12,v1,v318,v2,v3,v4,v5] .nil .nil) (.node [v44,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v852,v1,v2,v3,v4,v5] (.node [v0,v853,v1,v2,v3,v4,v5] (.node [v0,v100,v1,v2,v3,v4,v5] (.node [v0,v0,v1,v2,v3,v4,v5] (.node [v44,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v165,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v23,v1,v2,v3,v4,v5] (.node [v0,v854,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v855,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v856,v1,v2,v3,v4,v5] (.node [v0,v857,v1,v2,v3,v4,v5] (.node [v0,v186,v1,v2,v3,v4,v5] (.node [v0,v858,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v859,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v98,v1,v2,v3,v4,v5] (.node [v0,v98,v1,v2,v228,v3,v5] .nil .nil) (.node [v0,v98,v1,v2,v3,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrll : everyKey (rowOK 5 tree_5) tree_6lrrll = true := by decide +kernel
def tree_6lrrlr : BinaryTree (List W) := (.node [v0,v319,v1,v2,v3,v81,v5] (.node [v0,v860,v1,v2,v3,v4,v5] (.node [v0,v861,v1,v2,v3,v4,v5] (.node [v0,v110,v1,v2,v3,v4,v5] (.node [v0,v110,v1,v2,v3,v4] (.node [v0,v110,v1,v2,v228,v3,v4] .nil .nil) .nil) (.node [v0,v305,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v862,v1,v2,v3,v4,v5] (.node [v0,v863,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v864,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v319,v1,v2,v83,v3,v5] (.node [v0,v319,v1,v61,v3,v4,v5] (.node [v0,v319,v1,v318,v2,v4,v5] (.node [v0,v319,v280,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v319,v1,v2,v230,v4,v5] .nil .nil)) (.node [v0,v319,v1,v2,v3,v4,v5] (.node [v0,v319,v1,v2,v82,v3,v4] .nil .nil) (.node [v0,v319,v1,v2,v3,v4,v85] .nil .nil)))) (.node [v0,v332,v1,v2,v3,v4,v5] (.node [v0,v319,v2,v94,v4,v5] (.node [v0,v319,v6,v2,v3,v4,v5] (.node [v0,v319,v1,v89,v3,v4,v5] (.node [v0,v319,v1,v2,v94,v4,v5] .nil .nil) .nil) (.node [v0,v319,v2,v3,v94,v4,v5] .nil .nil)) (.node [v0,v257,v1,v2,v3,v4,v5] (.node [v0,v334,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v673,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v865,v1,v2,v3,v4,v5] (.node [v0,v866,v1,v2,v3,v4,v5] (.node [v0,v249,v1,v2,v3,v4,v5] (.node [v0,v336,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v867,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v302,v1,v79,v3,v4,v5] (.node [v0,v868,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v302,v1,v2,v84,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrlr : everyKey (rowOK 5 tree_5) tree_6lrrlr = true := by decide +kernel
def tree_6lrrl : BinaryTree (List W) := .node [v0,v267,v1,v2,v3,v4,v5] tree_6lrrll tree_6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrl : everyKey (rowOK 5 tree_5) tree_6lrrl = true := by
  change (_ && everyKey _ tree_6lrrll && everyKey _ tree_6lrrlr) = true
  rw [ok_tree_6lrrll, ok_tree_6lrrlr]
  decide +kernel
def tree_6lrrrl : BinaryTree (List W) := (.node [v0,v337,v280,v2,v3,v4,v5] (.node [v0,v341,v1,v2,v3,v4,v5] (.node [v0,v302,v1,v2,v88,v4,v5] (.node [v0,v302,v1,v2,v3,v4,v86] (.node [v0,v302,v1,v2,v3,v4,v5] (.node [v0,v302,v1,v2,v87,v3,v4] .nil .nil) .nil) (.node [v0,v302,v1,v2,v3,v101,v5] .nil .nil)) (.node [v0,v302,v2,v3,v4,v101,v5] (.node [v0,v302,v1,v91,v3,v4,v5] .nil .nil) (.node [v0,v302,v2,v3,v101,v5] .nil .nil))) (.node [v0,v869,v1,v2,v3,v4,v5] (.node [v0,v340,v1,v2,v3,v4,v5] (.node [v0,v674,v1,v2,v3,v4,v5] (.node [v0,v222,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v342,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v339,v1,v2,v3,v4,v5] (.node [v0,v870,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v871,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v345,v1,v2,v3,v4,v5] (.node [v0,v337,v343,v2,v3,v4,v5] (.node [v0,v337,v1,v24,v3,v4,v5] (.node [v0,v337,v1,v2,v3,v4,v5] (.node [v0,v337,v1,v343,v3,v4,v5] .nil .nil) .nil) (.node [v0,v337,v6,v2,v3,v4,v5] .nil .nil)) (.node [v0,v337,v2,v3,v94,v4,v5] (.node [v0,v337,v343,v3,v4,v5] .nil .nil) (.node [v0,v346,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v280,v2,v24,v3,v4,v5] (.node [v0,v280,v1,v2,v3,v4,v5] (.node [v0,v872,v1,v2,v3,v4,v5] (.node [v0,v347,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v280,v2,v230,v3,v4,v5] .nil .nil)) (.node [v0,v280,v2,v3,v4,v5,v354] (.node [v0,v280,v2,v3,v4,v101,v5] .nil .nil) (.node [v0,v109,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrrl : everyKey (rowOK 5 tree_5) tree_6lrrrl = true := by decide +kernel
def tree_6lrrrr : BinaryTree (List W) := (.node [v0,v873,v1,v2,v3,v4,v5] (.node [v0,v353,v1,v2,v3,v4,v5] (.node [v0,v112,v2,v3,v4,v5] (.node [v0,v107,v2,v3,v4,v5] (.node [v0,v107,v1,v2,v3,v4,v5] (.node [v0,v279,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v112,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v282,v1,v2,v3,v4,v5] (.node [v0,v359,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v353,v1,v2,v166,v3,v4] .nil .nil))) (.node [v0,v874,v1,v2,v3,v4,v5] (.node [v0,v353,v2,v3,v4,v354] (.node [v0,v353,v2,v3,v4,v5,v354] (.node [v0,v353,v1,v2,v3,v4,v354] .nil .nil) .nil) (.node [v0,v875,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v876,v1,v2,v3,v4,v5] (.node [v0,v877,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v363,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v878,v1,v2,v3,v4,v5] (.node [v0,v369,v1,v2,v3,v4,v5] (.node [v0,v111,v1,v2,v3,v4,v5] (.node [v0,v879,v1,v2,v3,v4,v5] (.node [v0,v880,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v111,v2,v3,v4,v5] .nil .nil)) (.node [v0,v42,v318,v2,v3,v4,v5] (.node [v0,v42,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v42,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v881,v2,v3,v4,v5] (.node [v0,v1,v882,v2,v3,v4,v5] (.node [v0,v1,v883,v2,v3,v4,v5] (.node [v0,v1,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v884,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v885,v2,v3,v4,v5] (.node [v0,v1,v19,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v886,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrrr : everyKey (rowOK 5 tree_5) tree_6lrrrr = true := by decide +kernel
def tree_6lrrr : BinaryTree (List W) := .node [v0,v109,v2,v3,v4,v5] tree_6lrrrl tree_6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrr : everyKey (rowOK 5 tree_5) tree_6lrrr = true := by
  change (_ && everyKey _ tree_6lrrrl && everyKey _ tree_6lrrrr) = true
  rw [ok_tree_6lrrrl, ok_tree_6lrrrr]
  decide +kernel
def tree_6lrr : BinaryTree (List W) := .node [v0,v302,v1,v2,v207,v3,v5] tree_6lrrl tree_6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrr : everyKey (rowOK 5 tree_5) tree_6lrr = true := by
  change (_ && everyKey _ tree_6lrrl && everyKey _ tree_6lrrr) = true
  rw [ok_tree_6lrrl, ok_tree_6lrrr]
  decide +kernel
def tree_6lr : BinaryTree (List W) := .node [v297,v0,v1,v2,v3,v4,v5] tree_6lrl tree_6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lr : everyKey (rowOK 5 tree_5) tree_6lr = true := by
  change (_ && everyKey _ tree_6lrl && everyKey _ tree_6lrr) = true
  rw [ok_tree_6lrl, ok_tree_6lrr]
  decide +kernel
def tree_6l : BinaryTree (List W) := .node [v887,v0,v1,v2,v3,v4,v5] tree_6ll tree_6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6l : everyKey (rowOK 5 tree_5) tree_6l = true := by
  change (_ && everyKey _ tree_6ll && everyKey _ tree_6lr) = true
  rw [ok_tree_6ll, ok_tree_6lr]
  decide +kernel
def tree_6rllll : BinaryTree (List W) := (.node [v0,v1,v239,v2,v3,v4,v5] (.node [v0,v1,v888,v2,v3,v4,v5] (.node [v0,v1,v215,v2,v3,v4,v5] (.node [v0,v1,v136,v2,v3,v4,v5] (.node [v0,v1,v889,v2,v3,v4,v5] (.node [v0,v1,v890,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v235,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v891,v2,v3,v4,v5] (.node [v0,v1,v892,v2,v3,v4,v5] (.node [v0,v1,v893,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v894,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v237,v2,v3,v4,v5] (.node [v0,v1,v237,v278,v3,v4,v5] (.node [v0,v1,v237,v318,v2,v4,v5] (.node [v0,v1,v237,v171,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v237,v311,v3,v4,v5] .nil .nil)) (.node [v0,v1,v237,v3,v92,v4,v5] (.node [v0,v1,v237,v20,v3,v4,v5] .nil .nil) (.node [v0,v1,v895,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v896,v2,v3,v4,v5] (.node [v0,v1,v897,v2,v3,v4,v5] (.node [v0,v1,v898,v2,v3,v4,v5] (.node [v0,v1,v899,v2,v3,v4,v5] (.node [v0,v1,v677,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v900,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v901,v2,v3,v4,v5] (.node [v0,v1,v130,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v902,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v205,v2,v3,v4,v5] (.node [v0,v1,v205,v385,v2,v3,v5] (.node [v0,v1,v205,v49,v2,v4,v5] (.node [v0,v1,v903,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v205,v2,v48,v3,v4] .nil .nil)) (.node [v0,v1,v205,v2,v3,v11,v5] (.node [v0,v1,v205,v2,v3,v4,v51] .nil .nil) (.node [v0,v1,v205,v2,v50,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllll : everyKey (rowOK 5 tree_5) tree_6rllll = true := by decide +kernel
def tree_6rlllr : BinaryTree (List W) := (.node [v0,v1,v171,v3,v4,v5,v386] (.node [v0,v1,v904,v2,v3,v4,v5] (.node [v0,v1,v905,v2,v3,v4,v5] (.node [v0,v1,v643,v2,v3,v4,v5] (.node [v0,v1,v211,v2,v3,v4,v5] (.node [v0,v1,v212,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v240,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v138,v2,v3,v4,v5] (.node [v0,v1,v906,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v907,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v171,v311,v2,v3,v4] (.node [v0,v1,v171,v318,v3,v4,v5] (.node [v0,v1,v306,v2,v3,v4,v5] (.node [v0,v1,v137,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v171,v343,v3,v4,v5] .nil .nil)) (.node [v0,v1,v171,v2,v3,v4,v38] (.node [v0,v1,v171,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v171,v24,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v908,v2,v3,v4,v5] (.node [v0,v1,v27,v3,v4,v5,v38] (.node [v0,v1,v27,v2,v3,v4,v5] (.node [v0,v1,v909,v2,v3,v4,v5] (.node [v0,v1,v910,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v27,v3,v4,v5] .nil .nil)) (.node [v0,v1,v911,v2,v3,v4,v5] (.node [v0,v1,v170,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v160,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v646,v2,v3,v4,v5] (.node [v0,v1,v912,v2,v3,v4,v5] (.node [v0,v1,v913,v2,v3,v4,v5] (.node [v0,v1,v914,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v915,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v144,v2,v3,v4,v5] (.node [v0,v1,v916,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v6,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlllr : everyKey (rowOK 5 tree_5) tree_6rlllr = true := by decide +kernel
def tree_6rlll : BinaryTree (List W) := .node [v0,v1,v205,v3,v4,v387,v5] tree_6rllll tree_6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlll : everyKey (rowOK 5 tree_5) tree_6rlll = true := by
  change (_ && everyKey _ tree_6rllll && everyKey _ tree_6rlllr) = true
  rw [ok_tree_6rllll, ok_tree_6rlllr]
  decide +kernel
def tree_6rllrl : BinaryTree (List W) := (.node [v0,v1,v318,v20,v3,v4,v5] (.node [v0,v1,v917,v2,v3,v4,v5] (.node [v0,v1,v53,v2,v3,v4] (.node [v0,v1,v40,v2,v3,v5] (.node [v0,v1,v40,v2,v3,v4,v5] (.node [v0,v1,v40,v318,v2,v3,v5] .nil .nil) .nil) (.node [v0,v1,v53,v318,v2,v3,v4] .nil .nil)) (.node [v0,v1,v918,v2,v3,v4,v5] (.node [v0,v1,v919,v2,v3,v4,v5] (.node [v0,v1,v53,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v920,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v318,v2,v3,v4,v52] (.node [v0,v1,v318,v311,v3,v4,v5] (.node [v0,v1,v318,v278,v3,v4,v5] (.node [v0,v1,v921,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v318,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v318,v2,v92,v4,v5] (.node [v0,v1,v318,v2,v3,v55,v5] .nil .nil) (.node [v0,v1,v318,v2,v4,v11,v5] .nil .nil)))) (.node [v0,v1,v49,v2,v4,v5] (.node [v0,v1,v682,v2,v3,v4,v5] (.node [v0,v1,v379,v2,v3,v4,v5] (.node [v0,v1,v318,v92,v4,v5] (.node [v0,v1,v318,v3,v92,v4,v5] .nil .nil) .nil) (.node [v0,v1,v256,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v378,v2,v3,v4,v5] (.node [v0,v1,v648,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v49,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v385,v2,v3,v4,v5] (.node [v0,v1,v922,v2,v3,v4,v5] (.node [v0,v1,v923,v2,v3,v4,v5] (.node [v0,v1,v924,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v925,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v385,v3,v4,v387,v5] (.node [v0,v1,v385,v2,v3,v387,v5] .nil .nil) (.node [v0,v1,v385,v3,v387,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllrl : everyKey (rowOK 5 tree_5) tree_6rllrl = true := by decide +kernel
def tree_6rllrr : BinaryTree (List W) := (.node [v0,v1,v926,v2,v3,v4,v5] (.node [v0,v1,v343,v278,v3,v4,v5] (.node [v0,v1,v927,v2,v3,v4,v5] (.node [v0,v1,v928,v2,v3,v4,v5] (.node [v0,v1,v929,v2,v3,v4,v5] (.node [v0,v1,v930,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v931,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v398,v2,v3,v4,v5] (.node [v0,v1,v932,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v933,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v343,v3,v4,v387,v5] (.node [v0,v1,v343,v20,v3,v4,v5] (.node [v0,v1,v343,v2,v3,v4,v5] (.node [v0,v1,v343,v311,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v343,v3,v92,v4,v5] .nil .nil)) (.node [v0,v1,v934,v2,v3,v4,v5] (.node [v0,v1,v344,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v935,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v114,v3,v4,v5] (.node [v0,v1,v115,v2,v3,v4,v5] (.node [v0,v1,v278,v3,v4,v387,v5] (.node [v0,v1,v278,v24,v3,v4,v5] (.node [v0,v1,v278,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v278,v3,v4,v5,v386] .nil .nil)) (.node [v0,v1,v936,v2,v3,v4,v5] (.node [v0,v1,v115,v3,v4,v5] .nil .nil) (.node [v0,v1,v114,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v311,v2,v3,v4,v5] (.node [v0,v1,v338,v2,v3,v4,v5] (.node [v0,v1,v141,v3,v4,v5] (.node [v0,v1,v141,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v277,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v311,v2,v3,v4,v39] (.node [v0,v1,v311,v2,v3,v4,v386] .nil .nil) (.node [v0,v1,v311,v24,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllrr : everyKey (rowOK 5 tree_5) tree_6rllrr = true := by decide +kernel
def tree_6rllr : BinaryTree (List W) := .node [v0,v1,v937,v2,v3,v4,v5] tree_6rllrl tree_6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllr : everyKey (rowOK 5 tree_5) tree_6rllr = true := by
  change (_ && everyKey _ tree_6rllrl && everyKey _ tree_6rllrr) = true
  rw [ok_tree_6rllrl, ok_tree_6rllrr]
  decide +kernel
def tree_6rll : BinaryTree (List W) := .node [v0,v1,v938,v2,v3,v4,v5] tree_6rlll tree_6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rll : everyKey (rowOK 5 tree_5) tree_6rll = true := by
  change (_ && everyKey _ tree_6rlll && everyKey _ tree_6rllr) = true
  rw [ok_tree_6rlll, ok_tree_6rllr]
  decide +kernel
def tree_6rlrll : BinaryTree (List W) := (.node [v0,v1,v939,v2,v3,v4,v5] (.node [v0,v1,v80,v3,v4,v5] (.node [v0,v1,v940,v2,v3,v4,v5] (.node [v0,v1,v941,v2,v3,v4,v5] (.node [v0,v1,v942,v2,v3,v4,v5] (.node [v0,v1,v311,v3,v4,v386] .nil .nil) .nil) (.node [v0,v1,v943,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v10,v3,v4,v5,v38] (.node [v0,v1,v10,v3,v4,v5] (.node [v0,v1,v10,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v80,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v113,v3,v4,v5] (.node [v0,v1,v944,v2,v3,v4,v5] (.node [v0,v1,v79,v3,v4,v5] (.node [v0,v1,v79,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v113,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v61,v2,v3,v4,v5] (.node [v0,v1,v945,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v61,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v393,v3,v4,v5] (.node [v0,v1,v2,v946,v3,v4,v5] (.node [v0,v1,v2,v90,v3,v4,v5] (.node [v0,v1,v2,v174,v3,v4,v5] (.node [v0,v1,v2,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v947,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v948,v3,v4,v5] (.node [v0,v1,v2,v143,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v949,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v242,v3,v4,v5] (.node [v0,v1,v2,v426,v3,v4,v5] (.node [v0,v1,v2,v48,v3,v4,v5] (.node [v0,v1,v2,v48,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v126,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v950,v3,v4,v5] (.node [v0,v1,v2,v951,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v952,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrll : everyKey (rowOK 5 tree_5) tree_6rlrll = true := by decide +kernel
def tree_6rlrlr : BinaryTree (List W) := (.node [v0,v1,v2,v207,v3,v4,v5] (.node [v0,v1,v2,v84,v3,v4,v5] (.node [v0,v1,v2,v953,v3,v4,v5] (.node [v0,v1,v2,v230,v3,v4,v5] (.node [v0,v1,v2,v954,v3,v4,v5] (.node [v0,v1,v2,v431,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v230,v4,v11,v5] .nil .nil)) (.node [v0,v1,v2,v686,v3,v4,v5] (.node [v0,v1,v2,v236,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v955,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v956,v3,v4,v5] (.node [v0,v1,v2,v957,v3,v4,v5] (.node [v0,v1,v2,v958,v3,v4,v5] (.node [v0,v1,v2,v84,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v106,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v959,v3,v4,v5] (.node [v0,v1,v2,v960,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v961,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v962,v3,v4,v5] (.node [v0,v1,v2,v963,v3,v4,v5] (.node [v0,v1,v2,v964,v3,v4,v5] (.node [v0,v1,v2,v209,v3,v4,v5] (.node [v0,v1,v2,v207,v3,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v609,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v965,v3,v4,v5] (.node [v0,v1,v2,v966,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v967,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v166,v3,v4,v38] (.node [v0,v1,v2,v968,v3,v4,v5] (.node [v0,v1,v2,v125,v3,v4,v5] (.node [v0,v1,v2,v969,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v166,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v970,v3,v4,v5] (.node [v0,v1,v2,v166,v3,v4,v39] .nil .nil) (.node [v0,v1,v2,v971,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrlr : everyKey (rowOK 5 tree_5) tree_6rlrlr = true := by decide +kernel
def tree_6rlrl : BinaryTree (List W) := .node [v0,v1,v2,v972,v3,v4,v5] tree_6rlrll tree_6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrl : everyKey (rowOK 5 tree_5) tree_6rlrl = true := by
  change (_ && everyKey _ tree_6rlrll && everyKey _ tree_6rlrlr) = true
  rw [ok_tree_6rlrll, ok_tree_6rlrlr]
  decide +kernel
def tree_6rlrrl : BinaryTree (List W) := (.node [v0,v1,v2,v83,v3,v5] (.node [v0,v1,v2,v7,v20,v3,v4] (.node [v0,v1,v2,v973,v3,v4,v5] (.node [v0,v1,v2,v168,v3,v4,v5] (.node [v0,v1,v2,v974,v3,v4,v5] (.node [v0,v1,v2,v975,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v976,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v977,v3,v4,v5] (.node [v0,v1,v2,v978,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v979,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v20,v3,v4,v5] (.node [v0,v1,v2,v117,v3,v4,v5] (.node [v0,v1,v2,v7,v3,v4,v5] (.node [v0,v1,v2,v7,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v131,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v87,v3,v4,v5] (.node [v0,v1,v2,v87,v3,v4] .nil .nil) (.node [v0,v1,v2,v83,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v228,v4,v5,v38] (.node [v0,v1,v2,v228,v3,v4,v5] (.node [v0,v1,v2,v980,v3,v4,v5] (.node [v0,v1,v2,v82,v3,v4,v5] (.node [v0,v1,v2,v82,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v981,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v228,v3,v118,v5] (.node [v0,v1,v2,v228,v3,v4,v119] .nil .nil) (.node [v0,v1,v2,v228,v4,v11,v5] .nil .nil))) (.node [v0,v1,v2,v8,v4,v5] (.node [v0,v1,v2,v8,v24,v4,v5] (.node [v0,v1,v2,v232,v3,v4,v5] (.node [v0,v1,v2,v224,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v8,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v116,v4,v5] (.node [v0,v1,v2,v116,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v96,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrrl : everyKey (rowOK 5 tree_5) tree_6rlrrl = true := by decide +kernel
def tree_6rlrrr : BinaryTree (List W) := (.node [v0,v1,v2,v982,v3,v4,v5] (.node [v0,v1,v2,v201,v3,v5,v39] (.node [v0,v1,v2,v983,v3,v4,v5] (.node [v0,v1,v2,v77,v3,v4,v5] (.node [v0,v1,v2,v984,v3,v4,v5] (.node [v0,v1,v2,v985,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v986,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v447,v3,v4,v5] (.node [v0,v1,v2,v89,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v201,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v121,v3,v5] (.node [v0,v1,v2,v619,v3,v4,v5] (.node [v0,v1,v2,v987,v3,v4,v5] (.node [v0,v1,v2,v202,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v121,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v988,v3,v4,v5] (.node [v0,v1,v2,v989,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v990,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v26,v3,v4,v5] (.node [v0,v1,v2,v164,v3,v4,v39] (.node [v0,v1,v2,v208,v3,v4,v5] (.node [v0,v1,v2,v91,v3,v4,v5] (.node [v0,v1,v2,v991,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v164,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v992,v3,v4,v5] (.node [v0,v1,v2,v993,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v163,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v994,v3,v4,v5] (.node [v0,v1,v2,v995,v3,v4,v5] (.node [v0,v1,v2,v996,v3,v4,v5] (.node [v0,v1,v2,v997,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v998,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v999,v3,v4,v5] (.node [v0,v1,v2,v1000,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v1001,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrrr : everyKey (rowOK 5 tree_5) tree_6rlrrr = true := by decide +kernel
def tree_6rlrr : BinaryTree (List W) := .node [v0,v1,v2,v96,v4,v5] tree_6rlrrl tree_6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrr : everyKey (rowOK 5 tree_5) tree_6rlrr = true := by
  change (_ && everyKey _ tree_6rlrrl && everyKey _ tree_6rlrrr) = true
  rw [ok_tree_6rlrrl, ok_tree_6rlrrr]
  decide +kernel
def tree_6rlr : BinaryTree (List W) := .node [v0,v1,v2,v1002,v3,v4,v5] tree_6rlrl tree_6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlr : everyKey (rowOK 5 tree_5) tree_6rlr = true := by
  change (_ && everyKey _ tree_6rlrl && everyKey _ tree_6rlrr) = true
  rw [ok_tree_6rlrl, ok_tree_6rlrr]
  decide +kernel
def tree_6rl : BinaryTree (List W) := .node [v0,v1,v311,v3,v4,v5,v386] tree_6rll tree_6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rl : everyKey (rowOK 5 tree_5) tree_6rl = true := by
  change (_ && everyKey _ tree_6rll && everyKey _ tree_6rlr) = true
  rw [ok_tree_6rll, ok_tree_6rlr]
  decide +kernel
def tree_6rrlll : BinaryTree (List W) := (.node [v0,v1,v2,v1003,v3,v4,v5] (.node [v0,v1,v2,v263,v3,v11,v5] (.node [v0,v1,v2,v1004,v3,v4,v5] (.node [v0,v1,v2,v120,v3,v4] (.node [v0,v1,v2,v24,v3,v4,v5] (.node [v0,v1,v2,v1005,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v120,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v263,v3,v4,v5] (.node [v0,v1,v2,v1006,v3,v4,v5] (.node [v0,v1,v2,v1007,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v263,v3,v4,v33] .nil .nil))) (.node [v0,v1,v2,v1008,v3,v4,v5] (.node [v0,v1,v2,v269,v3,v4,v5] (.node [v0,v1,v2,v263,v11,v5] (.node [v0,v1,v2,v263,v4,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v226,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v1009,v3,v4,v5] (.node [v0,v1,v2,v452,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v517,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v461,v3,v4,v5] (.node [v0,v1,v2,v255,v4,v5,v38] (.node [v0,v1,v2,v255,v3,v4,v38] (.node [v0,v1,v2,v255,v3,v4,v5] (.node [v0,v1,v2,v458,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v255,v3,v32,v5] .nil .nil)) (.node [v0,v1,v2,v251,v3,v4,v5] (.node [v0,v1,v2,v255,v4,v38] .nil .nil) (.node [v0,v1,v2,v1010,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v464,v3,v4,v5] (.node [v0,v1,v2,v1011,v3,v4,v5] (.node [v0,v1,v2,v460,v3,v4,v5] (.node [v0,v1,v2,v1012,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v455,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v1013,v3,v4,v5] (.node [v0,v1,v2,v1014,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v1015,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlll : everyKey (rowOK 5 tree_5) tree_6rrlll = true := by decide +kernel
def tree_6rrllr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v567,v4,v5] (.node [v0,v1,v2,v3,v1016,v4,v5] (.node [v0,v1,v2,v3,v1017,v4,v5] (.node [v0,v1,v2,v3,v1018,v4,v5] (.node [v0,v1,v2,v3,v1019,v4,v5] (.node [v0,v1,v2,v3,v1020,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v1021,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v1022,v4,v5] (.node [v0,v1,v2,v3,v1023,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v651,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v1024,v4,v5] (.node [v0,v1,v2,v3,v1025,v4,v5] (.node [v0,v1,v2,v3,v185,v4,v5] (.node [v0,v1,v2,v3,v1026,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v563,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v1027,v4,v5] (.node [v0,v1,v2,v3,v122,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v1028,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v1029,v4,v5] (.node [v0,v1,v2,v3,v575,v4,v5] (.node [v0,v1,v2,v3,v266,v4,v5] (.node [v0,v1,v2,v3,v124,v4,v5] (.node [v0,v1,v2,v3,v1030,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v558,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v1031,v4,v5] (.node [v0,v1,v2,v3,v88,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v333,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v50,v4,v5] (.node [v0,v1,v2,v3,v94,v4,v5] (.node [v0,v1,v2,v3,v1032,v4,v5] (.node [v0,v1,v2,v3,v1033,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v579,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v364,v4,v5] (.node [v0,v1,v2,v3,v1034,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v1035,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrllr : everyKey (rowOK 5 tree_5) tree_6rrllr = true := by decide +kernel
def tree_6rrll : BinaryTree (List W) := .node [v0,v1,v2,v3,v3,v4,v5] tree_6rrlll tree_6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrll : everyKey (rowOK 5 tree_5) tree_6rrll = true := by
  change (_ && everyKey _ tree_6rrlll && everyKey _ tree_6rrllr) = true
  rw [ok_tree_6rrlll, ok_tree_6rrllr]
  decide +kernel
def tree_6rrlrl : BinaryTree (List W) := (.node [v0,v1,v2,v3,v1036,v4,v5] (.node [v0,v1,v2,v3,v1037,v4,v5] (.node [v0,v1,v2,v3,v1038,v4,v5] (.node [v0,v1,v2,v3,v1039,v4,v5] (.node [v0,v1,v2,v3,v1040,v4,v5] (.node [v0,v1,v2,v3,v1041,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v392,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v93,v4,v5] (.node [v0,v1,v2,v3,v1042,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v92,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v1043,v4,v5] (.node [v0,v1,v2,v3,v1044,v4,v5] (.node [v0,v1,v2,v3,v1045,v4,v5] (.node [v0,v1,v2,v3,v1046,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v1047,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v1048,v4,v5] (.node [v0,v1,v2,v3,v1049,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v1050,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v1051,v4,v5] (.node [v0,v1,v2,v3,v216,v4,v5] (.node [v0,v1,v2,v3,v220,v5,v39] (.node [v0,v1,v2,v3,v220,v4,v39] (.node [v0,v1,v2,v3,v220,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v220,v39] .nil .nil)) (.node [v0,v1,v2,v3,v471,v4,v5] (.node [v0,v1,v2,v3,v472,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v476,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v1052,v4,v5] (.node [v0,v1,v2,v3,v481,v4,v5] (.node [v0,v1,v2,v3,v1053,v4,v5] (.node [v0,v1,v2,v3,v1054,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v1055,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v4,v5] (.node [v0,v1,v2,v3,v1056,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v1057,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlrl : everyKey (rowOK 5 tree_5) tree_6rrlrl = true := by decide +kernel
def tree_6rrlrr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v81,v5] (.node [v0,v1,v2,v3,v4,v179,v5] (.node [v0,v1,v2,v3,v4,v1058,v5] (.node [v0,v1,v2,v3,v4,v696,v5] (.node [v0,v1,v2,v3,v4,v1059,v5] (.node [v0,v1,v2,v3,v4,v1060,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1061,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v1062,v5] (.node [v0,v1,v2,v3,v4,v1063,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v1064,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v536,v5] (.node [v0,v1,v2,v3,v4,v1065,v5] (.node [v0,v1,v2,v3,v4,v1066,v5] (.node [v0,v1,v2,v3,v4,v1067,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1068,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v54,v5] (.node [v0,v1,v2,v3,v4,v535,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v128,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v1069,v5] (.node [v0,v1,v2,v3,v4,v1070,v5] (.node [v0,v1,v2,v3,v4,v1071,v5] (.node [v0,v1,v2,v3,v4,v1072,v5] (.node [v0,v1,v2,v3,v4,v1073,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1074,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v1075,v5] (.node [v0,v1,v2,v3,v4,v101,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v1076,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v1077,v5] (.node [v0,v1,v2,v3,v4,v1078,v5] (.node [v0,v1,v2,v3,v4,v55,v5] (.node [v0,v1,v2,v3,v4,v1079,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1080,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v1081,v5] (.node [v0,v1,v2,v3,v4,v1082,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v387,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlrr : everyKey (rowOK 5 tree_5) tree_6rrlrr = true := by decide +kernel
def tree_6rrlr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v1083,v5] tree_6rrlrl tree_6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlr : everyKey (rowOK 5 tree_5) tree_6rrlr = true := by
  change (_ && everyKey _ tree_6rrlrl && everyKey _ tree_6rrlrr) = true
  rw [ok_tree_6rrlrl, ok_tree_6rrlrr]
  decide +kernel
def tree_6rrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v1084,v4,v5] tree_6rrll tree_6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrl : everyKey (rowOK 5 tree_5) tree_6rrl = true := by
  change (_ && everyKey _ tree_6rrll && everyKey _ tree_6rrlr) = true
  rw [ok_tree_6rrll, ok_tree_6rrlr]
  decide +kernel
def tree_6rrrll : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5,v5] (.node [v0,v1,v2,v3,v4,v32,v5] (.node [v0,v1,v2,v3,v4,v1085,v5] (.node [v0,v1,v2,v3,v4,v1086,v5] (.node [v0,v1,v2,v3,v4,v1087,v5] (.node [v0,v1,v2,v3,v4,v1088,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v118,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v550,v5] (.node [v0,v1,v2,v3,v4,v1089,v5] (.node [v0,v1,v2,v3,v4,v691,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v16,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v1090,v5] (.node [v0,v1,v2,v3,v4,v1091,v5] (.node [v0,v1,v2,v3,v4,v1092,v5] (.node [v0,v1,v2,v3,v4,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1093,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v1094,v5] (.node [v0,v1,v2,v3,v4,v1095,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v5,v1096] (.node [v0,v1,v2,v3,v4,v5,v1097] (.node [v0,v1,v2,v3,v4,v5,v1098] (.node [v0,v1,v2,v3,v4,v5,v1099] (.node [v0,v1,v2,v3,v4,v5,v1100] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1101] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v1102] (.node [v0,v1,v2,v3,v4,v5,v1103] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v1104] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v295] (.node [v0,v1,v2,v3,v4,v5,v1105] (.node [v0,v1,v2,v3,v4,v5,v1106] (.node [v0,v1,v2,v3,v4,v5,v1107] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1108] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v132] (.node [v0,v1,v2,v3,v4,v5,v123] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v85] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrll : everyKey (rowOK 5 tree_5) tree_6rrrll = true := by decide +kernel
def tree_6rrrlr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5,v33] (.node [v0,v1,v2,v3,v4,v5,v1109] (.node [v0,v1,v2,v3,v4,v5,v51] (.node [v0,v1,v2,v3,v4,v5,v354] (.node [v0,v1,v2,v3,v4,v5,v86] (.node [v0,v1,v2,v3,v4,v5,v1110] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v381] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v52] (.node [v0,v1,v2,v3,v4,v5,v1111] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v412] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v1112] (.node [v0,v1,v2,v3,v4,v5,v1113] (.node [v0,v1,v2,v3,v4,v5,v386] (.node [v0,v1,v2,v3,v4,v5,v1114] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1115] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v693] (.node [v0,v1,v2,v3,v4,v5,v119] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v1116] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v5,v1117] (.node [v0,v1,v2,v3,v4,v5,v39] (.node [v0,v1,v2,v3,v4,v5,v1118] (.node [v0,v1,v2,v3,v4,v5,v1119] (.node [v0,v1,v2,v3,v4,v5,v38] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1120] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v1121] (.node [v0,v1,v2,v3,v4,v5,v1122] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v1123] .nil .nil))) (.node [v0,v1,v2,v3,v4,v86] (.node [v0,v1,v2,v3,v4,v132,v39] (.node [v0,v1,v2,v3,v4,v123] (.node [v0,v1,v2,v3,v4,v5,v1124] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v85] .nil .nil)) (.node [v0,v1,v2,v3,v4,v354,v39] (.node [v0,v1,v2,v3,v4,v354,v38] .nil .nil) (.node [v0,v1,v2,v3,v4,v51] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrlr : everyKey (rowOK 5 tree_5) tree_6rrrlr = true := by decide +kernel
def tree_6rrrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v5,v1125] tree_6rrrll tree_6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrl : everyKey (rowOK 5 tree_5) tree_6rrrl = true := by
  change (_ && everyKey _ tree_6rrrll && everyKey _ tree_6rrrlr) = true
  rw [ok_tree_6rrrll, ok_tree_6rrrlr]
  decide +kernel
def tree_6rrrrl : BinaryTree (List W) := (.node [v0,v1,v2,v88,v4,v5] (.node [v0,v1,v2,v3,v55,v5] (.node [v0,v1,v2,v3,v54,v5] (.node [v0,v1,v2,v3,v4,v33] (.node [v0,v1,v2,v3,v4,v119] (.node [v0,v1,v2,v3,v4,v386,v38] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v38,v39] .nil .nil)) (.node [v0,v1,v2,v3,v81,v5] (.node [v0,v1,v2,v3,v128,v5,v39] .nil .nil) (.node [v0,v1,v2,v3,v101,v11,v5] .nil .nil))) (.node [v0,v1,v2,v122,v4,v5] (.node [v0,v1,v2,v3,v32,v5] (.node [v0,v1,v2,v3,v118,v5] (.node [v0,v1,v2,v3,v387,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v11,v5,v39] .nil .nil)) (.node [v0,v1,v2,v266,v4,v11,v5] (.node [v0,v1,v2,v124,v4,v5] .nil .nil) (.node [v0,v1,v2,v266,v4,v5,v38] .nil .nil)))) (.node [v0,v1,v125,v3,v4,v5] (.node [v0,v1,v2,v4,v11,v5,v38] (.node [v0,v1,v2,v220,v4,v16,v5] (.node [v0,v1,v2,v50,v4,v5] (.node [v0,v1,v2,v94,v4,v11,v5] .nil .nil) .nil) (.node [v0,v1,v2,v4,v16,v5] .nil .nil)) (.node [v0,v1,v143,v3,v4,v5] (.node [v0,v1,v90,v3,v4,v5] .nil .nil) (.node [v0,v1,v126,v3,v4,v5] .nil .nil))) (.node [v0,v1,v89,v3,v4,v5] (.node [v0,v1,v20,v3,v4,v387,v5] (.node [v0,v1,v20,v24,v3,v4,v5] (.node [v0,v1,v131,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v20,v3,v4,v5,v386] .nil .nil)) (.node [v0,v1,v24,v3,v92,v4,v5] (.node [v0,v1,v91,v3,v4,v5] .nil .nil) (.node [v0,v1,v24,v3,v4,v387,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrrl : everyKey (rowOK 5 tree_5) tree_6rrrrl = true := by decide +kernel
def tree_6rrrrr : BinaryTree (List W) := (.node [v302,v1,v138,v2,v3,v4,v5] (.node [v0,v343,v2,v24,v3,v4,v5] (.node [v0,v6,v2,v24,v3,v4,v5] (.node [v0,v144,v2,v3,v4,v5] (.node [v0,v137,v2,v3,v4,v5] (.node [v0,v136,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v6,v2,v230,v3,v4,v5] .nil .nil)) (.node [v0,v6,v2,v3,v4,v5,v354] (.node [v0,v6,v2,v3,v4,v101,v5] .nil .nil) (.node [v0,v318,v2,v77,v3,v4,v5] .nil .nil))) (.node [v0,v2,v24,v3,v94,v4,v5] (.node [v0,v2,v166,v3,v4,v5,v354] (.node [v0,v2,v207,v3,v4,v101,v5] (.node [v0,v2,v230,v3,v94,v4,v5] .nil .nil) .nil) (.node [v0,v2,v77,v3,v4,v5] .nil .nil)) (.node [v23,v1,v2,v3,v4,v5] (.node [v100,v1,v2,v3,v4,v5] .nil .nil) (.node [v319,v1,v130,v2,v3,v4,v5] .nil .nil)))) (.node [v1,v278,v2,v20,v3,v4,v5] (.node [v1,v6,v2,v164,v3,v4,v5] (.node [v1,v138,v2,v3,v4,v5] (.node [v1,v130,v2,v3,v4,v5] (.node [v280,v1,v6,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1,v6,v2,v20,v3,v4,v5] .nil .nil)) (.node [v1,v6,v2,v3,v4,v128,v5] (.node [v1,v6,v2,v3,v266,v4,v5] .nil .nil) (.node [v1,v318,v2,v106,v3,v4,v5] .nil .nil))) (.node [v1,v2,v201,v3,v4,v128,v5] (.node [v1,v2,v228,v3,v266,v4,v5] (.node [v1,v2,v20,v3,v266,v4,v5] (.node [v1,v2,v106,v3,v4,v5] .nil .nil) .nil) (.node [v1,v2,v201,v164,v3,v4,v5] .nil .nil)) (.node [v1,v2,v26,v3,v4,v5] (.node [v1,v2,v164,v3,v4,v5,v132] .nil .nil) (.node [v1,v2,v26,v3,v4,v5,v39] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrrr : everyKey (rowOK 5 tree_5) tree_6rrrrr = true := by decide +kernel
def tree_6rrrr : BinaryTree (List W) := .node [v0,v19,v2,v3,v4,v5] tree_6rrrrl tree_6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrr : everyKey (rowOK 5 tree_5) tree_6rrrr = true := by
  change (_ && everyKey _ tree_6rrrrl && everyKey _ tree_6rrrrr) = true
  rw [ok_tree_6rrrrl, ok_tree_6rrrrr]
  decide +kernel
def tree_6rrr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v52] tree_6rrrl tree_6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrr : everyKey (rowOK 5 tree_5) tree_6rrr = true := by
  change (_ && everyKey _ tree_6rrrl && everyKey _ tree_6rrrr) = true
  rw [ok_tree_6rrrl, ok_tree_6rrrr]
  decide +kernel
def tree_6rr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v1126,v5] tree_6rrl tree_6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rr : everyKey (rowOK 5 tree_5) tree_6rr = true := by
  change (_ && everyKey _ tree_6rrl && everyKey _ tree_6rrr) = true
  rw [ok_tree_6rrl, ok_tree_6rrr]
  decide +kernel
def tree_6r : BinaryTree (List W) := .node [v0,v1,v2,v1127,v3,v4,v5] tree_6rl tree_6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6r : everyKey (rowOK 5 tree_5) tree_6r = true := by
  change (_ && everyKey _ tree_6rl && everyKey _ tree_6rr) = true
  rw [ok_tree_6rl, ok_tree_6rr]
  decide +kernel
def tree_6 : BinaryTree (List W) := .node [v0,v1,v1128,v2,v3,v4,v5] tree_6l tree_6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6 : everyKey (rowOK 5 tree_5) tree_6 = true := by
  change (_ && everyKey _ tree_6l && everyKey _ tree_6r) = true
  rw [ok_tree_6l, ok_tree_6r]
  decide +kernel
theorem closed_6 : Closed 6 tree_6 := closed_next 5 (by decide) tree_6 tree_5 closed_5 ok_tree_6
def tree_7l : BinaryTree (List W) := (.node [v233,v0,v1,v2,v3,v4,v5] (.node [v194,v0,v1,v2,v3,v4,v5] (.node [v177,v0,v1,v2,v3,v4,v5] (.node [v161,v0,v1,v2,v3,v4,v5] (.node [v162,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v159,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v193,v0,v1,v2,v3,v4,v5] (.node [v181,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v175,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v203,v0,v1,v2,v3,v4,v5] (.node [v206,v0,v1,v2,v3,v4,v5] (.node [v200,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v204,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v223,v0,v1,v2,v3,v4,v5] (.node [v182,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v229,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v319,v1,v2,v3,v4,v5] (.node [v264,v0,v1,v2,v3,v4,v5] (.node [v178,v0,v1,v2,v3,v4,v5] (.node [v213,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v265,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v270,v0,v1,v2,v3,v4,v5] (.node [v271,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v293,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v353,v1,v2,v3,v4,v5] (.node [v0,v337,v1,v2,v3,v4,v5] (.node [v0,v302,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v280,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v205,v2,v3,v4,v5] (.node [v0,v1,v237,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7l : everyKey (rowOK 6 tree_6) tree_7l = true := by decide +kernel
def tree_7r : BinaryTree (List W) := (.node [v0,v1,v2,v263,v3,v4,v5] (.node [v0,v1,v2,v207,v3,v4,v5] (.node [v0,v1,v343,v2,v3,v4,v5] (.node [v0,v1,v318,v2,v3,v4,v5] (.node [v0,v1,v6,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v385,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v311,v2,v3,v4,v5] (.node [v0,v1,v278,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v230,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v201,v3,v4,v5] (.node [v0,v1,v2,v20,v3,v4,v5] (.node [v0,v1,v2,v166,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v228,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v24,v3,v4,v5] (.node [v0,v1,v2,v164,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v4,v387,v5] (.node [v0,v1,v2,v3,v92,v4,v5] (.node [v0,v1,v2,v3,v266,v4,v5] (.node [v0,v1,v2,v255,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v94,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v128,v5] (.node [v0,v1,v2,v3,v220,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v101,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v386] (.node [v0,v1,v2,v3,v4,v5,v132] (.node [v0,v1,v2,v3,v4,v11,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v354] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v39] (.node [v0,v1,v2,v3,v4,v5,v38] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7r : everyKey (rowOK 6 tree_6) tree_7r = true := by decide +kernel
def tree_7 : BinaryTree (List W) := .node [v0,v1,v171,v2,v3,v4,v5] tree_7l tree_7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7 : everyKey (rowOK 6 tree_6) tree_7 = true := by
  change (_ && everyKey _ tree_7l && everyKey _ tree_7r) = true
  rw [ok_tree_7l, ok_tree_7r]
  decide +kernel
theorem closed_7 : Closed 7 tree_7 := closed_next 6 (by decide) tree_7 tree_6 closed_6 ok_tree_7
def tree_8 : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_8 : everyKey (rowOK 7 tree_7) tree_8 = true := by decide +kernel
theorem closed_8 : Closed 8 tree_8 := closed_next 7 (by decide) tree_8 tree_7 closed_7 ok_tree_8
theorem lower6 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins6.toFinset := @no_build 8 tree_8 ins6 nd6 (by decide) closed_8 (by decide +kernel)
def gates6 : List Gate := [⟨.or, [2, 0]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [12, 11]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [14, 13]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem upper6 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277074944) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates6, 15, by simp [gates6], rfl, by decide +kernel⟩

end PEqualNP.Outside.L_meta_17077

open PEqualNP.Outside.L_meta_17077 in
theorem PEqualNP.Outside.L_meta_17077 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124266 * 2 ^ 32 + 4277074944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124266 * 2 ^ 32 + 4277074944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, basis, size, computes⟩ := h
  obtain ⟨gates, output, mono, bound, correct⟩ :=
    replace (4278124266 * 2 ^ 32 + 4277074944) 10 ins6 nd6 rows6 rfl
      lower6 upper6 C.gates C.output basis computes
  exact ⟨⟨gates, output⟩, mono, bound.trans size, correct⟩
